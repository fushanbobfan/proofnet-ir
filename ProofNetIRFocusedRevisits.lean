import ProofNetIR
import Std.Data.HashMap
import Std.Data.HashSet

open Lean ProofNetIR

namespace ProofNetIRFocusedRevisits

/-! The focused-revisits experiment: how much of the rule-order redundancy that strict focusing leaves does the
strictly focused search of matched-search-v0.2 meet, and what does merging it buy.

Both arms are `focusedStrict` of `ProofNetIRPrunedSearch.lean`, copied here unchanged so that the registered file
stays as it was, with one switch:

- `strictMemo` consults and fills the two memo tables, one for sequents and one for a tensor in focus with its
  context, exactly as matched-search-v0.2 did; a query answered from a table is a revisit, and `proveHits` and
  `focusHits` count them separately.
- `strictNoMemo` neither consults nor fills them, so every revisit is explored again. A set of the queries met so
  far counts revisits (`proveRevisits`, `focusRevisits`) without pruning anything.

A query is a call of `prove` (a sequent after eager par decomposition, as a sorted multiset of formulas) or of
`focus` on a tensor goal (its context and goal). -/

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

/-! ## Strict focusing with a memo switch -/

structure StrictStats where
  proveCalls : Nat := 0
  focusCalls : Nat := 0
  cacheHits : Nat := 0
  proveHits : Nat := 0
  focusHits : Nat := 0
  proveRevisits : Nat := 0
  focusRevisits : Nat := 0
  decides : Nat := 0
  splits : Nat := 0
  infeasible : Nat := 0

structure StrictCtx where
  budget : Budget
  names : Array String
  memo : Bool
  steps : Nat := 0
  stats : StrictStats := {}
  proveMemo : Std.HashMap (List Keyed) Bool := {}
  focusMemo : Std.HashMap (List Keyed × Keyed) Bool := {}
  seenProve : Std.HashSet (List Keyed) := {}
  seenFocus : Std.HashSet (List Keyed × Keyed) := {}

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

/-- Provability of a sequent: eager par decomposition, the necessary conditions, then a decision on each distinct
positive formula. -/
partial def prove (input : List Formula) : StrictM Bool := do
  let state := canonical ((decompose input).map keyed)
  if (← get).memo then
    if let some value := (← get).proveMemo[state]? then
      modify fun c => { c with stats := { c.stats with cacheHits := c.stats.cacheHits + 1,
                                                       proveHits := c.stats.proveHits + 1 } }
      return value
  else if (← get).seenProve.contains state then
    modify fun c => { c with stats := { c.stats with proveRevisits := c.stats.proveRevisits + 1 } }
  else
    modify fun c => { c with seenProve := c.seenProve.insert state }
  modify fun c => { c with stats := { c.stats with proveCalls := c.stats.proveCalls + 1 } }
  strictTick
  let names := (← get).names
  let result ←
    if sumVectors names (state.map (·.formula)) != target (names.size + 1) then do
      modify fun c => { c with stats := { c.stats with infeasible := c.stats.infeasible + 1 } }
      pure false
    else
      decideFrom state 0 []
  if (← get).memo then
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
      if (← get).memo then
        if let some value := (← get).focusMemo[memoKey]? then
          modify fun c => { c with stats := { c.stats with cacheHits := c.stats.cacheHits + 1,
                                                           focusHits := c.stats.focusHits + 1 } }
          return value
      else if (← get).seenFocus.contains memoKey then
        modify fun c => { c with stats := { c.stats with focusRevisits := c.stats.focusRevisits + 1 } }
      else
        modify fun c => { c with seenFocus := c.seenFocus.insert memoKey }
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
      if (← get).memo then
        modify fun c => { c with focusMemo := c.focusMemo.insert memoKey result }
      return result

/-- The context splits of a tensor in focus, as multisets whose left part satisfies the necessary conditions
together with the left formula. -/
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

def runStrict (task : Task) (budgetNs : Nat) (memo : Bool) : IO Json := do
  let start ← IO.monoNanosNow
  let names := task.sequent.foldl collectNames #[]
  let attempt : StrictM (Option Bool) := do
    try
      let value ← prove task.sequent
      pure (some value)
    catch _ => pure none
  let (result, ctx) ← attempt.run { budget := { deadline := start + budgetNs }, names, memo }
  let elapsed := (← IO.monoNanosNow) - start
  let s := ctx.stats
  let common := [("proveCalls", toJson s.proveCalls), ("focusCalls", toJson s.focusCalls),
    ("decides", toJson s.decides), ("splits", toJson s.splits), ("infeasible", toJson s.infeasible)]
  return outcome result elapsed <| common ++ if memo then
      [("cacheHits", toJson s.cacheHits), ("proveHits", toJson s.proveHits), ("focusHits", toJson s.focusHits)]
    else
      [("proveRevisits", toJson s.proveRevisits), ("focusRevisits", toJson s.focusRevisits)]

def run (budgetMs : Nat) : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let lines := payload.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  if lines.isEmpty then
    throw <| IO.userError "focused revisits received no tasks"
  let budgetNs := budgetMs * 1_000_000
  for line in lines do
    match parseTask line with
    | .error message => throw <| IO.userError s!"task parse failed: {message}"
    | .ok task =>
        let memoResult ← runStrict task budgetNs true
        let noMemoResult ← runStrict task budgetNs false
        IO.println (Json.mkObj [
          ("id", task.id), ("budgetMs", budgetMs),
          ("strictMemo", memoResult), ("strictNoMemo", noMemoResult)]).compress
        (← IO.getStdout).flush

end ProofNetIRFocusedRevisits

def main (args : List String) : IO Unit :=
  let budget := match args.dropWhile (· != "--budget-ms") with
    | _ :: value :: _ => value.toNat?.getD 5000
    | _ => 5000
  ProofNetIRFocusedRevisits.run budget
