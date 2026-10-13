import ProofNetIR
import Std.Data.HashMap
import Std.Data.HashSet

open Lean ProofNetIR

namespace ProofNetIRRevisitWitness

/-! The revisit-witness experiment: the branches behind a sample of the strictly focused search's revisits.

The search is revisit-provenance-v0.1's (`ProofNetIRRevisitProvenance.lean`, itself focused-revisits-v0.1's
`strictMemo`), copied here with its control flow unchanged, so that every counter and every class it reports is the
same. A branch now also keeps its rules in full: the tensor applied, the premise the branch enters, and the multiset
of formulas the rule sends to the other premise. Each query keeps, besides the signatures that class its revisits, the
first `keep` distinct branches that met it. A revisit of the `tensors` class (every earlier branch decomposed a
different multiset of tensors) is written out, with the query and those earlier branches, when a draw seeded by the
task's id and the revisit's rank falls below the task's sampling rate, so that a stratified sample of the class can be
examined branch against branch. Formulas are compared by their keys, as the memo tables compare them; the output
names each key by its rank in a table written once per task. -/

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

/-- A formula with its key and the key's hash, computed once. -/
structure Keyed where
  key : String
  formula : Formula
  keyHash : UInt64
  deriving Inhabited

instance : BEq Keyed := ⟨fun a b => a.key == b.key⟩
instance : Hashable Keyed := ⟨fun a => a.keyHash⟩

def keyed (formula : Formula) : Keyed :=
  let key := formulaKey formula
  { key, formula, keyHash := hash key }

def canonical (state : List Keyed) : List Keyed :=
  state.mergeSort fun a b => decide (a.key ≤ b.key)

structure Budget where
  deadline : Nat
  exceeded : Bool := false

/-! ## Necessary conditions as vectors (as in matched-search-v0.2) -/

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

/-! ## Branches -/

/-- The splitmix64 finalizer, so that sums of hashes identify multisets. -/
def mix (z : UInt64) : UInt64 :=
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

/-- An order-independent signature of a multiset of events: two sums of mixed 64-bit event hashes. -/
structure Sig where
  a : UInt64 := 0
  b : UInt64 := 0
  deriving BEq, Hashable, Inhabited

def Sig.add (s : Sig) (event : UInt64) : Sig :=
  { a := s.a + mix event, b := s.b + mix (event ^^^ 0x9e3779b97f4a7c15) }

/-- The hash of a multiset of formulas, independent of their order. -/
def multisetHash (formulas : List Keyed) : UInt64 :=
  formulas.foldl (fun acc k => acc + mix (k.keyHash ^^^ 0x51ed270b27190a4b)) 0

/-- A tensor rule on a branch: the tensor, the premise the branch enters (0 left, 1 right), and the formulas sent to
the other premise. -/
structure Step where
  tensor : String
  side : Nat
  sent : List String
  deriving Inhabited

structure Branch where
  rules : Sig := {}
  tensors : Sig := {}
  steps : List Step := []  -- the latest rule first
  deriving Inhabited

/-- The branch after a tensor rule on `goal` that enters premise `side` (0 left, 1 right) and sends `other` to the other
premise. The signatures are revisit-provenance-v0.1's. -/
def Branch.step (branch : Branch) (goal : Keyed) (side : UInt64) (other : List Keyed) : Branch :=
  let rule := mix (mix (goal.keyHash + 0x2545f4914f6cdd1d) ^^^ (side + 1) * 0x632be59bd9b4e019 ^^^ multisetHash other)
  { rules := branch.rules.add rule, tensors := branch.tensors.add (mix (goal.keyHash ^^^ 0x7e57a11ce5000001)),
    steps := { tensor := goal.key, side := side.toNat, sent := other.map (·.key) } :: branch.steps }

/-- How many distinct branches a query keeps in full. -/
def keep : Nat := 4

/-- The branches that met a query: by rules and by tensors, as revisit-provenance-v0.1 records them, and the first
`keep` distinct ones in full. -/
structure Seen where
  rules : Std.HashSet Sig := {}
  tensors : Std.HashSet Sig := {}
  kept : Array (List Step) := #[]
  deriving Inhabited

def Seen.first (branch : Branch) : Seen :=
  { rules := ({} : Std.HashSet Sig).insert branch.rules, tensors := ({} : Std.HashSet Sig).insert branch.tensors,
    kept := #[branch.steps] }

/-- The class of a revisit (0 permutation, 1 splits, 2 tensors) and the record with this branch added. -/
def classify (seen : Seen) (branch : Branch) : Nat × Seen :=
  let cls := if seen.rules.contains branch.rules then 0 else if seen.tensors.contains branch.tensors then 1 else 2
  let kept := if cls != 0 && seen.kept.size < keep then seen.kept.push branch.steps else seen.kept
  (cls, { rules := seen.rules.insert branch.rules, tensors := seen.tensors.insert branch.tensors, kept })

/-! ## Strict focusing with provenance and a sample of tensors revisits -/

structure Stats where
  proveCalls : Nat := 0
  focusCalls : Nat := 0
  cacheHits : Nat := 0
  proveHits : Nat := 0
  focusHits : Nat := 0
  decides : Nat := 0
  splits : Nat := 0
  infeasible : Nat := 0
  provePermutation : Nat := 0
  proveSplits : Nat := 0
  proveTensors : Nat := 0
  focusPermutation : Nat := 0
  focusSplits : Nat := 0
  focusTensors : Nat := 0

def Stats.proveHit (s : Stats) (cls : Nat) : Stats :=
  let s := { s with cacheHits := s.cacheHits + 1, proveHits := s.proveHits + 1 }
  match cls with
  | 0 => { s with provePermutation := s.provePermutation + 1 }
  | 1 => { s with proveSplits := s.proveSplits + 1 }
  | _ => { s with proveTensors := s.proveTensors + 1 }

def Stats.focusHit (s : Stats) (cls : Nat) : Stats :=
  let s := { s with cacheHits := s.cacheHits + 1, focusHits := s.focusHits + 1 }
  match cls with
  | 0 => { s with focusPermutation := s.focusPermutation + 1 }
  | 1 => { s with focusSplits := s.focusSplits + 1 }
  | _ => { s with focusTensors := s.focusTensors + 1 }

structure Ctx where
  budget : Budget
  names : Array String
  salt : UInt64
  perMille : Nat
  steps : Nat := 0
  stats : Stats := {}
  proveMemo : Std.HashMap (List Keyed) Bool := {}
  focusMemo : Std.HashMap (List Keyed × Keyed) Bool := {}
  proveSeen : Std.HashMap (List Keyed) Seen := {}
  focusSeen : Std.HashMap (List Keyed × Keyed) Seen := {}
  tensorsRank : Nat := 0
  samples : Array Json := #[]
  keyIds : Std.HashMap String Nat := {}
  keyList : Array String := #[]

abbrev M := StateRefT Ctx IO

def tick : M Unit := do
  if (← get).budget.exceeded then throw (IO.userError "budget")
  modify fun c => { c with steps := c.steps + 1 }
  let steps := (← get).steps
  let deadline := (← get).budget.deadline
  if steps % 64 == 0 then
    if (← IO.monoNanosNow) > deadline then
      modify fun c => { c with budget := { c.budget with exceeded := true } }
      throw (IO.userError "budget")

/-- The rank of a key in the task's table, added on first use. -/
def idOf (key : String) : M Nat := do
  if let some i := (← get).keyIds[key]? then return i
  let i := (← get).keyList.size
  modify fun c => { c with keyIds := c.keyIds.insert key i, keyList := c.keyList.push key }
  return i

def stepJson (step : Step) : M Json := do
  let sent ← step.sent.mapM idOf
  return Json.arr #[toJson (← idOf step.tensor), toJson step.side, toJson sent]

/-- A branch in the order its rules were applied. -/
def branchJson (steps : List Step) : M Json := do
  return Json.arr (← steps.reverse.mapM stepJson).toArray

/-- Counts a tensors revisit and writes it out when its draw falls below the task's rate. Changes no search state. -/
def sample (table : String) (query : List Keyed) (goal : Option Keyed) (branch : Branch) (seen : Seen) : M Unit := do
  let rank := (← get).tensorsRank
  modify fun c => { c with tensorsRank := rank + 1 }
  let c ← get
  if (mix (c.salt ^^^ mix (rank.toUInt64 + 0x3c6ef372fe94f82b)) % 1000).toNat < c.perMille then
    let queryIds ← query.mapM fun k => idOf k.key
    let goalJson ← match goal with
      | some g => do pure (toJson (← idOf g.key))
      | none => pure Json.null
    let current ← branchJson branch.steps
    let earlier ← seen.kept.mapM branchJson
    let record := Json.mkObj [("rank", toJson rank), ("table", toJson table), ("query", toJson queryIds),
      ("goal", goalJson), ("current", current), ("earlier", Json.arr earlier),
      ("distinctEarlier", toJson seen.rules.size)]
    modify fun c => { c with samples := c.samples.push record }

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

/-- Provability of a sequent: eager par decomposition, the necessary conditions, then a decision on each distinct
positive formula. -/
partial def prove (input : List Formula) (branch : Branch) : M Bool := do
  let state := canonical ((decompose input).map keyed)
  if let some value := (← get).proveMemo[state]? then
    let seen := (← get).proveSeen.getD state {}
    let (cls, seen') := classify seen branch
    if cls == 2 then sample "prove" state none branch seen
    modify fun c => { c with stats := c.stats.proveHit cls, proveSeen := c.proveSeen.insert state seen' }
    return value
  modify fun c => { c with stats := { c.stats with proveCalls := c.stats.proveCalls + 1 },
                           proveSeen := c.proveSeen.insert state (Seen.first branch) }
  tick
  let names := (← get).names
  let result ←
    if sumVectors names (state.map (·.formula)) != target (names.size + 1) then do
      modify fun c => { c with stats := { c.stats with infeasible := c.stats.infeasible + 1 } }
      pure false
    else
      decideFrom state 0 [] branch
  modify fun c => { c with proveMemo := c.proveMemo.insert state result }
  return result

partial def decideFrom (state : List Keyed) (index : Nat) (tried : List String) (branch : Branch) : M Bool := do
  match state[index]? with
  | none => return false
  | some k =>
      if isPositive k.formula && !tried.contains k.key then
        modify fun c => { c with stats := { c.stats with decides := c.stats.decides + 1 } }
        if ← focus (state.eraseIdx index) k branch then return true
        decideFrom state (index + 1) (k.key :: tried) branch
      else
        decideFrom state (index + 1) tried branch

/-- Provability of `⊢ context ⇓ goal`. -/
partial def focus (context : List Keyed) (goal : Keyed) (branch : Branch) : M Bool := do
  match goal.formula with
  | .atom name true =>
      return match context with
        | [single] => single.formula == .atom name false
        | _ => false
  | .atom _ false => prove (goal.formula :: context.map (·.formula)) branch
  | .par _ _ => prove (goal.formula :: context.map (·.formula)) branch
  | .tensor left right =>
      let memoKey := (context, goal)
      if let some value := (← get).focusMemo[memoKey]? then
        let seen := (← get).focusSeen.getD memoKey {}
        let (cls, seen') := classify seen branch
        if cls == 2 then sample "focus" context (some goal) branch seen
        modify fun c => { c with stats := c.stats.focusHit cls, focusSeen := c.focusSeen.insert memoKey seen' }
        return value
      modify fun c => { c with stats := { c.stats with focusCalls := c.stats.focusCalls + 1 },
                               focusSeen := c.focusSeen.insert memoKey (Seen.first branch) }
      tick
      let result ← match left, right with
        | .atom name true, _ =>
            match context.findIdx? (·.formula == .atom name false) with
            | some i => focus (context.eraseIdx i) (keyed right) (branch.step goal 1 [context[i]!])
            | none => pure false
        | _, .atom name true =>
            match context.findIdx? (·.formula == .atom name false) with
            | some i => focus (context.eraseIdx i) (keyed left) (branch.step goal 0 [context[i]!])
            | none => pure false
        | _, _ => splitSearch context goal left right branch
      modify fun c => { c with focusMemo := c.focusMemo.insert memoKey result }
      return result

/-- The context splits of a tensor in focus, as multisets whose left part satisfies the necessary conditions
together with the left formula. -/
partial def splitSearch (context : List Keyed) (goal : Keyed) (left right : Formula) (branch : Branch) : M Bool := do
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
  let target' := addInto (target width) ((vectorOf names left).map fun x => -x)
  splitFrom groups vectors low high target' goal left right branch 0 #[] (zeros width)

partial def splitFrom (groups : Array (Keyed × Nat)) (vectors low high : Array (Array Int))
    (target' : Array Int) (goal : Keyed) (left right : Formula) (branch : Branch) (g : Nat) (chosen : Array Nat)
    (sum : Array Int) : M Bool := do
  tick
  if g == groups.size then
    if sum != target' then return false
    modify fun c => { c with stats := { c.stats with splits := c.stats.splits + 1 } }
    let mut leftContext : List Keyed := []
    let mut rightContext : List Keyed := []
    for i in [0:groups.size] do
      let (k, m) := groups[i]!
      let c := chosen[i]!
      leftContext := leftContext ++ List.replicate c k
      rightContext := rightContext ++ List.replicate (m - c) k
    if ← focus leftContext (keyed left) (branch.step goal 0 rightContext) then
      if ← focus rightContext (keyed right) (branch.step goal 1 leftContext) then return true
    return false
  let lo := low[g]!
  let hi := high[g]!
  let feasible := (List.range target'.size).all fun j =>
    let need := target'[j]! - sum[j]!
    lo[j]! ≤ need && need ≤ hi[j]!
  if !feasible then return false
  let m := groups[g]!.2
  let v := vectors[g]!
  for c in [0:m + 1] do
    if ← splitFrom groups vectors low high target' goal left right branch (g + 1) (chosen.push c)
        (addInto sum (scale c v)) then
      return true
  return false

end

/-! ## Runner -/

structure Task where
  id : String
  sequent : List Formula
  perMille : Nat

private def parseTask (line : String) : Except String Task := do
  let json ← Json.parse line
  let id ← (json.getObjVal? "id") >>= Json.getStr?
  let sequentJson ← (json.getObjVal? "sequent") >>= Json.getArr?
  let sequent ← sequentJson.toList.mapM fun value =>
    match Certificate.formulaFromJson value with
    | .ok formula => pure formula
    | .error error => throw s!"{error.path}: {error.message}"
  let perMille := match (json.getObjVal? "samplePerMille") >>= Json.getNat? with
    | .ok value => value
    | .error _ => 0
  return { id, sequent, perMille }

def runTask (task : Task) (budgetNs : Nat) : IO Json := do
  let start ← IO.monoNanosNow
  let names := task.sequent.foldl collectNames #[]
  let attempt : M (Option Bool) := do
    try
      let value ← prove task.sequent {}
      pure (some value)
    catch _ => pure none
  let (result, ctx) ← attempt.run { budget := { deadline := start + budgetNs }, names, salt := hash task.id,
                                    perMille := task.perMille }
  let elapsed := (← IO.monoNanosNow) - start
  let s := ctx.stats
  return Json.mkObj [
    ("found", match result with | some true => Json.bool true | _ => Json.bool false),
    ("refuted", match result with | some false => Json.bool true | _ => Json.bool false),
    ("timeout", match result with | none => Json.bool true | _ => Json.bool false),
    ("elapsedNs", toJson elapsed),
    ("proveCalls", toJson s.proveCalls), ("focusCalls", toJson s.focusCalls), ("decides", toJson s.decides),
    ("splits", toJson s.splits), ("infeasible", toJson s.infeasible), ("cacheHits", toJson s.cacheHits),
    ("proveHits", toJson s.proveHits), ("focusHits", toJson s.focusHits),
    ("provePermutation", toJson s.provePermutation), ("proveSplits", toJson s.proveSplits),
    ("proveTensors", toJson s.proveTensors), ("focusPermutation", toJson s.focusPermutation),
    ("focusSplits", toJson s.focusSplits), ("focusTensors", toJson s.focusTensors),
    ("tensorsRevisits", toJson ctx.tensorsRank), ("samples", Json.arr ctx.samples),
    ("keys", toJson ctx.keyList)]

def run (budgetMs : Nat) : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let lines := payload.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  if lines.isEmpty then
    throw <| IO.userError "revisit witness received no tasks"
  let budgetNs := budgetMs * 1_000_000
  for line in lines do
    match parseTask line with
    | .error message => throw <| IO.userError s!"task parse failed: {message}"
    | .ok task =>
        let result ← runTask task budgetNs
        IO.println (Json.mkObj [("id", task.id), ("budgetMs", budgetMs), ("strictMemo", result)]).compress
        (← IO.getStdout).flush

end ProofNetIRRevisitWitness

def main (args : List String) : IO Unit :=
  let budget := match args.dropWhile (· != "--budget-ms") with
    | _ :: value :: _ => value.toNat?.getD 5000
    | _ => 5000
  ProofNetIRRevisitWitness.run budget
