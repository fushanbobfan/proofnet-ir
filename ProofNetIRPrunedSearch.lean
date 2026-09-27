import ProofNetIR
import Std.Data.HashMap

open Lean ProofNetIR

namespace ProofNetIRPrunedSearch

/-! Pruned arms of the matched search v0.2 for one-sided unit-free MLL
sequents. Both arms receive only the sequent and run under one wall-clock
budget:

- `focusedStrict`: focused sequent search in Andreoli's discipline. Pars are
  decomposed eagerly; a positive formula (a tensor or a positive atom) is
  chosen and kept in focus through its tensors; a positive atom in focus
  closes only against exactly its dual; a negative formula in focus is
  released. Every branch must satisfy two necessary conditions of
  provability, per-name atom balance and `2 * tensors + 2 = atoms`, and the
  context splits of a tensor are enumerated as multisets under both.
- `netsPruned`: axiom-linking search. A sequent that is unbalanced or whose
  tensor count is not `atoms / 2 - 1` is refuted at once, since no correct
  net has it. Partial nets are checked by Danos's contraction, applied after
  every axiom: tensor and axiom edges merge their endpoints' nodes, and a par
  whose two premises lie in one node merges that node with the par's own. An
  axiom whose endpoints already share a node, or a par with a premise in the
  par's own node, closes a cycle in some switching, and the partial net is
  abandoned. The unlinked atom with the fewest partners outside its node is
  linked first, and each complete linking is decided by
  `Certificate.unificationCheck`.

`--strict-only` runs `focusedStrict` alone, which the corpus builder uses to
decide candidate negatives under a long budget. `--dev-bases seed count`
prints generated bases for development instead, in the format of
`proofnet_ir_search_corpus`. -/

/-- The v0.1 arms' key: a formula's sorted-key JSON text. -/
partial def formulaKey : Formula → String
  | .atom name positive =>
      "{\"kind\":\"atom\",\"name\":" ++ (Json.str name).compress ++ ",\"positive\":" ++
        (if positive then "true" else "false") ++ "}"
  | .tensor left right =>
      "{\"kind\":\"tensor\",\"left\":" ++ formulaKey left ++ ",\"right\":" ++ formulaKey right ++ "}"
  | .par left right =>
      "{\"kind\":\"par\",\"left\":" ++ formulaKey left ++ ",\"right\":" ++ formulaKey right ++ "}"

instance : Inhabited Formula := ⟨.atom "" true⟩

structure Keyed where
  key : String
  formula : Formula
  deriving Inhabited

instance : BEq Keyed := ⟨fun a b => a.key == b.key⟩
instance : Hashable Keyed := ⟨fun a => hash a.key⟩

def keyed (formula : Formula) : Keyed := { key := formulaKey formula, formula }

def canonical (state : List Keyed) : List Keyed :=
  state.mergeSort fun a b => decide (a.key ≤ b.key)

structure Budget where
  deadline : Nat
  exceeded : Bool := false

/-! ## Necessary conditions as vectors

A formula's vector has one coordinate per atom name (plus one for a positive
occurrence, minus one for a negative one) and a last coordinate
`2 * tensors - atoms`. A provable sequent sums to zero on every name and to
`-2` on the last coordinate. -/

partial def collectNames (acc : Array String) : Formula → Array String
  | .atom name _ => if acc.contains name then acc else acc.push name
  | .tensor left right => collectNames (collectNames acc left) right
  | .par left right => collectNames (collectNames acc left) right

def zeros (width : Nat) : Array Int := (List.replicate width (0 : Int)).toArray

partial def addVector (names : Array String) (acc : Array Int) : Formula → Array Int
  | .atom name positive =>
      let index := (names.findIdx? (· == name)).getD 0
      let acc := acc.modify index fun x => x + (if positive then 1 else -1)
      acc.modify names.size fun x => x - 1
  | .tensor left right =>
      (addVector names (addVector names acc left) right).modify names.size fun x => x + 2
  | .par left right => addVector names (addVector names acc left) right

def vectorOf (names : Array String) (formula : Formula) : Array Int :=
  addVector names (zeros (names.size + 1)) formula

def sumVectors (names : Array String) (state : List Formula) : Array Int :=
  state.foldl (addVector names) (zeros (names.size + 1))

def addInto (a b : Array Int) : Array Int := (a.zip b).map fun (x, y) => x + y

def scale (k : Nat) (a : Array Int) : Array Int := a.map (· * (k : Int))

/-- The sum of a provable sequent. -/
def target (width : Nat) : Array Int := (zeros width).set! (width - 1) (-2)

/-! ## Strict focusing -/

structure StrictStats where
  proveCalls : Nat := 0
  focusCalls : Nat := 0
  cacheHits : Nat := 0
  decides : Nat := 0
  splits : Nat := 0
  infeasible : Nat := 0

structure StrictCtx where
  budget : Budget
  names : Array String
  steps : Nat := 0
  stats : StrictStats := {}
  proveMemo : Std.HashMap (List Keyed) Bool := {}
  focusMemo : Std.HashMap (List Keyed × Keyed) Bool := {}

abbrev StrictM := StateRefT StrictCtx IO

def strictTick : StrictM Unit := do
  if (← get).budget.exceeded then throw (IO.userError "budget")
  modify fun c => { c with steps := c.steps + 1 }
  let steps := (← get).steps
  let deadline := (← get).budget.deadline
  if steps % 64 == 0 then
    if (← IO.monoNanosNow) > deadline then
      modify fun c => { c with budget := { c.budget with exceeded := true } }
      throw (IO.userError "budget")

partial def decompose : List Formula → List Formula
  | [] => []
  | .par left right :: rest => decompose (left :: right :: rest)
  | formula :: rest => formula :: decompose rest

def isPositive : Formula → Bool
  | .tensor _ _ => true
  | .atom _ positive => positive
  | .par _ _ => false

/-- Groups of identical formulas in a sorted context, with multiplicities. -/
def groupsOf (context : List Keyed) : Array (Keyed × Nat) :=
  context.foldl (fun acc k =>
    match acc.back? with
    | some (last, count) =>
        if last.key == k.key then acc.pop.push (last, count + 1) else acc.push (k, 1)
    | none => acc.push (k, 1)) #[]

mutual

/-- Provability of a sequent: eager par decomposition, the necessary
conditions, then a decision on each distinct positive formula. -/
partial def prove (input : List Formula) : StrictM Bool := do
  let state := canonical ((decompose input).map keyed)
  if let some value := (← get).proveMemo[state]? then
    modify fun c => { c with stats := { c.stats with cacheHits := c.stats.cacheHits + 1 } }
    return value
  modify fun c => { c with stats := { c.stats with proveCalls := c.stats.proveCalls + 1 } }
  strictTick
  let names := (← get).names
  let result ←
    if sumVectors names (state.map (·.formula)) != target (names.size + 1) then do
      modify fun c => { c with stats := { c.stats with infeasible := c.stats.infeasible + 1 } }
      pure false
    else
      decideFrom state 0 []
  modify fun c => { c with proveMemo := c.proveMemo.insert state result }
  return result

partial def decideFrom (state : List Keyed) (index : Nat) (tried : List String) : StrictM Bool := do
  match state[index]? with
  | none => return false
  | some k =>
      if isPositive k.formula && !tried.contains k.key then
        modify fun c => { c with stats := { c.stats with decides := c.stats.decides + 1 } }
        if ← focus (state.eraseIdx index) k then return true
        decideFrom state (index + 1) (k.key :: tried)
      else
        decideFrom state (index + 1) tried

/-- Provability of `⊢ context ⇓ goal`. -/
partial def focus (context : List Keyed) (goal : Keyed) : StrictM Bool := do
  match goal.formula with
  | .atom name true =>
      return match context with
        | [single] => single.formula == .atom name false
        | _ => false
  | .atom _ false => prove (goal.formula :: context.map (·.formula))
  | .par _ _ => prove (goal.formula :: context.map (·.formula))
  | .tensor left right =>
      let memoKey := (context, goal)
      if let some value := (← get).focusMemo[memoKey]? then
        modify fun c => { c with stats := { c.stats with cacheHits := c.stats.cacheHits + 1 } }
        return value
      modify fun c => { c with stats := { c.stats with focusCalls := c.stats.focusCalls + 1 } }
      strictTick
      let result ← match left, right with
        | .atom name true, _ =>
            match context.findIdx? (·.formula == .atom name false) with
            | some i => focus (context.eraseIdx i) (keyed right)
            | none => pure false
        | _, .atom name true =>
            match context.findIdx? (·.formula == .atom name false) with
            | some i => focus (context.eraseIdx i) (keyed left)
            | none => pure false
        | _, _ => splitSearch context left right
      modify fun c => { c with focusMemo := c.focusMemo.insert memoKey result }
      return result

/-- The context splits of a tensor in focus, as multisets whose left part
satisfies the necessary conditions together with the left formula. -/
partial def splitSearch (context : List Keyed) (left right : Formula) : StrictM Bool := do
  let names := (← get).names
  let width := names.size + 1
  let groups := groupsOf context
  let vectors := groups.map fun (k, _) => vectorOf names k.formula
  let n := groups.size
  let mut low : Array (Array Int) := (List.replicate (n + 1) (zeros width)).toArray
  let mut high : Array (Array Int) := (List.replicate (n + 1) (zeros width)).toArray
  for g in (List.range n).reverse do
    let v := scale groups[g]!.2 vectors[g]!
    low := low.set! g (addInto low[g + 1]! (v.map fun x => min 0 x))
    high := high.set! g (addInto high[g + 1]! (v.map fun x => max 0 x))
  let goal := addInto (target width) ((vectorOf names left).map fun x => -x)
  splitFrom groups vectors low high goal left right 0 #[] (zeros width)

partial def splitFrom (groups : Array (Keyed × Nat)) (vectors low high : Array (Array Int))
    (goal : Array Int) (left right : Formula) (g : Nat) (chosen : Array Nat) (sum : Array Int) :
    StrictM Bool := do
  strictTick
  if g == groups.size then
    if sum != goal then return false
    modify fun c => { c with stats := { c.stats with splits := c.stats.splits + 1 } }
    let mut leftContext : List Keyed := []
    let mut rightContext : List Keyed := []
    for i in [0:groups.size] do
      let (k, m) := groups[i]!
      let c := chosen[i]!
      leftContext := leftContext ++ List.replicate c k
      rightContext := rightContext ++ List.replicate (m - c) k
    if ← focus leftContext (keyed left) then
      if ← focus rightContext (keyed right) then return true
    return false
  let lo := low[g]!
  let hi := high[g]!
  let feasible := (List.range goal.size).all fun j =>
    let need := goal[j]! - sum[j]!
    lo[j]! ≤ need && need ≤ hi[j]!
  if !feasible then return false
  let m := groups[g]!.2
  let v := vectors[g]!
  for c in [0:m + 1] do
    if ← splitFrom groups vectors low high goal left right (g + 1) (chosen.push c) (addInto sum (scale c v)) then
      return true
  return false

end

/-! ## Pruned linking search -/

/-- The occurrence forest as a certificate skeleton: formulas by preorder id,
connective links, conclusions, and the atom vertices in id order. -/
structure Skeleton where
  formulas : Array Formula
  links : List Link
  conclusions : List Vertex
  atoms : List Vertex

private partial def addSkeleton (formulas : Array Formula) (links : List Link) : Formula →
    Array Formula × List Link × Vertex
  | .atom name positive =>
      (formulas.push (.atom name positive), links, formulas.size)
  | .tensor left right =>
      let id := formulas.size
      let formulas := formulas.push (.tensor left right)
      let (formulas, links, leftId) := addSkeleton formulas links left
      let (formulas, links, rightId) := addSkeleton formulas links right
      (formulas, links ++ [Link.tensor leftId rightId id], id)
  | .par left right =>
      let id := formulas.size
      let formulas := formulas.push (.par left right)
      let (formulas, links, leftId) := addSkeleton formulas links left
      let (formulas, links, rightId) := addSkeleton formulas links right
      (formulas, links ++ [Link.par leftId rightId id], id)

def Skeleton.ofSequent (sequent : List Formula) : Skeleton := Id.run do
  let mut formulas : Array Formula := #[]
  let mut links : List Link := []
  let mut conclusions : List Vertex := []
  for formula in sequent do
    let (next, nextLinks, id) := addSkeleton formulas links formula
    formulas := next
    links := nextLinks
    conclusions := conclusions ++ [id]
  let atoms := (List.range formulas.size).filter fun id => formulas[id]!.isAtom
  return { formulas, links, conclusions, atoms }

partial def root (parent : Array Nat) (x : Nat) : Nat :=
  let p := parent[x]!
  if p == x then x else root parent p

def join (parent : Array Nat) (x y : Nat) : Array Nat :=
  let rx := root parent x
  let ry := root parent y
  if rx == ry then parent else parent.set! rx ry

structure ParLink where
  left : Vertex
  right : Vertex
  node : Vertex

def parLinks (skeleton : Skeleton) : List ParLink :=
  skeleton.links.filterMap fun link => match link with
    | .par left right node => some { left, right, node }
    | _ => none

/-- Danos's contraction to a fixpoint: `none` when a par has a premise in its
own node, a cycle in the switching that selects that premise. -/
partial def contract (parent : Array Nat) (pending : List ParLink) : Option (Array Nat × List ParLink) :=
  if pending.any (fun p => root parent p.left == root parent p.node || root parent p.right == root parent p.node) then
    none
  else
    match pending.find? (fun p => root parent p.left == root parent p.right) with
    | some p => contract (join parent p.left p.node) (pending.filter fun q => q.node != p.node)
    | none => some (parent, pending)

/-- Union-find over the tensor edges; par edges are left out. -/
def tensorForest (skeleton : Skeleton) : Array Nat := Id.run do
  let mut parent := (List.range skeleton.formulas.size).toArray
  for link in skeleton.links do
    match link with
    | .tensor left right conclusion => parent := join (join parent left conclusion) right conclusion
    | _ => pure ()
  return parent

def tensorCount (skeleton : Skeleton) : Nat :=
  skeleton.links.foldl (fun n link => match link with | .tensor _ _ _ => n + 1 | _ => n) 0

def balancedAtoms (skeleton : Skeleton) : Bool :=
  let atoms := skeleton.atoms.map fun v => skeleton.formulas[v]!
  atoms.all fun atom => match atom with
    | .atom name _ =>
        (atoms.filter (· == .atom name true)).length == (atoms.filter (· == .atom name false)).length
    | _ => true

structure PrunedStats where
  partialNodes : Nat := 0
  candidates : Nat := 0
  cycleRejections : Nat := 0
  switchingCycles : Nat := 0
  deadEnds : Nat := 0

structure PrunedCtx where
  budget : Budget
  stats : PrunedStats := {}

abbrev PrunedM := StateRefT PrunedCtx IO

def prunedTick : PrunedM Unit := do
  let (exceeded, nodes, limit) :=
    ((← get).budget.exceeded, (← get).stats.partialNodes, (← get).budget.deadline)
  if exceeded then throw (IO.userError "budget")
  if nodes % 64 == 0 then
    if (← IO.monoNanosNow) > limit then
      modify fun c => { c with budget := { c.budget with exceeded := true } }
      throw (IO.userError "budget")

/-- Link the most constrained unlinked atom with each admissible partner in
vertex order; decide each complete linking with the public decision. -/
partial def prunedSearch (skeleton : Skeleton) (parent : Array Nat) (pending : List ParLink)
    (unlinked : List Vertex) (chosen : List Link) : PrunedM Bool := do
  modify fun c => { c with stats := { c.stats with partialNodes := c.stats.partialNodes + 1 } }
  prunedTick
  if unlinked.isEmpty then
    modify fun c => { c with stats := { c.stats with candidates := c.stats.candidates + 1 } }
    let certificate : Certificate :=
      { formulas := skeleton.formulas, links := skeleton.links ++ chosen,
        conclusions := skeleton.conclusions }
    return certificate.unificationCheck
  let mut best : Vertex := 0
  let mut bestPartners : List Vertex := []
  let mut bestRejected : Nat := 0
  let mut first := true
  for v in unlinked do
    let dual := skeleton.formulas[v]!.dual
    let rv := root parent v
    let duals := unlinked.filter fun w => skeleton.formulas[w]! == dual
    let partners := duals.filter fun w => root parent w != rv
    if first || partners.length < bestPartners.length then
      best := v
      bestPartners := partners
      bestRejected := duals.length - partners.length
      first := false
    if partners.isEmpty then break
  modify fun c => { c with stats := { c.stats with cycleRejections := c.stats.cycleRejections + bestRejected } }
  if bestPartners.isEmpty then
    modify fun c => { c with stats := { c.stats with deadEnds := c.stats.deadEnds + 1 } }
    return false
  for w in bestPartners do
    match contract (join parent best w) pending with
    | none =>
        modify fun c => { c with stats := { c.stats with switchingCycles := c.stats.switchingCycles + 1 } }
    | some (next, remaining) =>
        let link := if best < w then Link.axiom best w else Link.axiom w best
        let rest := unlinked.filter fun u => u != best && u != w
        if ← prunedSearch skeleton next remaining rest (chosen ++ [link]) then
          return true
  return false

/-! ## Runner -/

structure Task where
  id : String
  sequent : List Formula

private def parseTask (line : String) : Except String Task := do
  let json ← Json.parse line
  let id ← (json.getObjVal? "id") >>= Json.getStr?
  let sequentJson ← (json.getObjVal? "sequent") >>= Json.getArr?
  let sequent ← sequentJson.toList.mapM fun value =>
    match Certificate.formulaFromJson value with
    | .ok formula => pure formula
    | .error error => throw s!"{error.path}: {error.message}"
  return { id, sequent }

private def outcome (found : Option Bool) (elapsed : Nat) (counters : List (String × Json)) : Json :=
  Json.mkObj ([
    ("found", match found with | some true => Json.bool true | _ => Json.bool false),
    ("refuted", match found with | some false => Json.bool true | _ => Json.bool false),
    ("timeout", match found with | none => Json.bool true | _ => Json.bool false),
    ("elapsedNs", toJson elapsed)] ++ counters)

def runFocusedStrict (task : Task) (budgetNs : Nat) : IO Json := do
  let start ← IO.monoNanosNow
  let names := task.sequent.foldl collectNames #[]
  let attempt : StrictM (Option Bool) := do
    try
      let value ← prove task.sequent
      pure (some value)
    catch _ => pure none
  let (result, ctx) ← attempt.run { budget := { deadline := start + budgetNs }, names }
  let elapsed := (← IO.monoNanosNow) - start
  return outcome result elapsed [
    ("proveCalls", toJson ctx.stats.proveCalls), ("focusCalls", toJson ctx.stats.focusCalls),
    ("cacheHits", toJson ctx.stats.cacheHits), ("decides", toJson ctx.stats.decides),
    ("splits", toJson ctx.stats.splits), ("infeasible", toJson ctx.stats.infeasible)]

def runNetsPruned (task : Task) (budgetNs : Nat) : IO Json := do
  let start ← IO.monoNanosNow
  let skeleton := Skeleton.ofSequent task.sequent
  let admissible := balancedAtoms skeleton && 2 * tensorCount skeleton + 2 == skeleton.atoms.length
  if !admissible then
    let elapsed := (← IO.monoNanosNow) - start
    return outcome (some false) elapsed [
      ("rootRefutation", toJson true), ("partialNodes", toJson (0 : Nat)),
      ("candidates", toJson (0 : Nat)), ("cycleRejections", toJson (0 : Nat)),
      ("switchingCycles", toJson (0 : Nat)), ("deadEnds", toJson (0 : Nat))]
  let attempt : PrunedM (Option Bool) := do
    try
      let (parent, pending) := (contract (tensorForest skeleton) (parLinks skeleton)).getD
        (tensorForest skeleton, parLinks skeleton)
      let value ← prunedSearch skeleton parent pending skeleton.atoms []
      pure (some value)
    catch _ => pure none
  let (result, ctx) ← attempt.run { budget := { deadline := start + budgetNs } }
  let elapsed := (← IO.monoNanosNow) - start
  return outcome result elapsed [
    ("rootRefutation", toJson false), ("partialNodes", toJson ctx.stats.partialNodes),
    ("candidates", toJson ctx.stats.candidates), ("cycleRejections", toJson ctx.stats.cycleRejections),
    ("switchingCycles", toJson ctx.stats.switchingCycles), ("deadEnds", toJson ctx.stats.deadEnds)]

def run (budgetMs : Nat) (strictOnly : Bool) : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let lines := payload.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  if lines.isEmpty then
    throw <| IO.userError "pruned search received no tasks"
  let budgetNs := budgetMs * 1_000_000
  for line in lines do
    match parseTask line with
    | .error message => throw <| IO.userError s!"task parse failed: {message}"
    | .ok task =>
        if strictOnly then
          let strictResult ← runFocusedStrict task budgetNs
          IO.println (Json.mkObj [
            ("id", task.id), ("budgetMs", budgetMs), ("focusedStrict", strictResult)]).compress
        else
          let netsResult ← runNetsPruned task budgetNs
          let strictResult ← runFocusedStrict task budgetNs
          IO.println (Json.mkObj [
            ("id", task.id), ("budgetMs", budgetMs),
            ("netsPruned", netsResult), ("focusedStrict", strictResult)]).compress
        (← IO.getStdout).flush

/-- Generated bases for development, disjoint from the registered corpus
when the seeds are. -/
def devBases (seed count : Nat) : IO Unit := do
  let mut index := 0
  for depth in [2, 3, 4] do
    for offset in List.range count do
      let current := seed + index
      let tree := CutFreeDerivation.generate current depth
      let some elaborated := tree.elaborate?
        | throw <| IO.userError s!"invalid generated base at seed {current}"
      IO.println (Json.mkObj [
        ("id", s!"dev-base-{index}"), ("seed", current), ("depth", depth), ("offset", offset),
        ("sequent", .arr (elaborated.sequent.toArray.map Certificate.formulaJson))]).compress
      index := index + 1

end ProofNetIRPrunedSearch

def main (args : List String) : IO Unit :=
  match args with
  | "--dev-bases" :: seed :: count :: _ =>
      ProofNetIRPrunedSearch.devBases (seed.toNat?.getD 30000) (count.toNat?.getD 10)
  | _ =>
      let budget := match args.dropWhile (· != "--budget-ms") with
        | _ :: value :: _ => value.toNat?.getD 5000
        | _ => 5000
      ProofNetIRPrunedSearch.run budget (args.contains "--strict-only")
