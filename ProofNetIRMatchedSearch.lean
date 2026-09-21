import ProofNetIR
import Std.Data.HashMap

open Lean ProofNetIR

namespace ProofNetIRMatchedSearch

/-! Equal-information matched search for one-sided unit-free MLL sequents.

Every input line is a JSON object with an `id` and a `sequent`. Three arms run
on the same input, in the same process, each under the same wall-clock budget:

- `focused`: the committed focused sequent search of `scripts/focused_search.py`
  reproduced step for step, including its canonical state order, its memo on
  multiset states, its eager par phase, and its enumeration of every resource
  split of a chosen tensor;
- `focusedBalanced`: the same search with per-name atom-balance pruning of
  states and splits, so that the comparison does not rest on a baseline that
  lacks an obvious cut;
- `nets`: net-space search, enumerating the axiom linkings of the forest in the
  order of the committed generator and deciding each with the public decision
  `unificationCheck`, stopping at the first accepted linking.

Each arm reports whether it found a proof, whether it refuted the sequent by
exhaustion, whether it hit the budget, its elapsed nanoseconds, and its own
operation counts. -/

/-- The Python baseline orders formulas by their sorted-key JSON text. -/
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

private def keyed (formula : Formula) : Keyed := { key := formulaKey formula, formula }

private def canonical (state : List Keyed) : List Keyed :=
  state.mergeSort fun a b => decide (a.key ≤ b.key)

/-- Per-name atom balance of a formula: positive occurrences count one, negative
occurrences count minus one. -/
private partial def balanceOf : Formula → List (String × Int)
  | .atom name positive => [(name, if positive then 1 else -1)]
  | .tensor left right => merge (balanceOf left) (balanceOf right)
  | .par left right => merge (balanceOf left) (balanceOf right)
where
  merge (a b : List (String × Int)) : List (String × Int) :=
    b.foldl (fun acc (name, value) =>
      match acc.find? (·.1 == name) with
      | some (_, existing) => (acc.filter (·.1 != name)) ++ [(name, existing + value)]
      | none => acc ++ [(name, value)]) a

private def balanced (state : List Keyed) : Bool :=
  (state.foldl (fun acc k => balanceOf.merge acc (balanceOf k.formula)) []).all (·.2 == 0)

structure Budget where
  deadline : Nat
  exceeded : Bool := false

structure FocusedStats where
  calls : Nat := 0
  cacheHits : Nat := 0
  parSteps : Nat := 0
  tensorChoices : Nat := 0
  partitions : Nat := 0
  deriving Repr

structure FocusedCtx where
  budget : Budget
  stats : FocusedStats := {}
  memo : Std.HashMap (List Keyed) Bool := {}
  prune : Bool

abbrev FocusedM := StateRefT FocusedCtx IO

private def checkBudget : FocusedM Unit := do
  let ctx ← get
  if ctx.budget.exceeded then throw (IO.userError "budget")
  if ctx.stats.calls % 64 == 0 then
    let now ← IO.monoNanosNow
    if now > ctx.budget.deadline then
      set { ctx with budget := { ctx.budget with exceeded := true } }
      throw (IO.userError "budget")

private def isAxiom (state : List Keyed) : Bool :=
  match state with
  | [a, b] => a.formula.isAtom && b.formula == a.formula.dual
  | _ => false

/-- The committed focused search: memoized on canonical multiset states, eager
par on the first par in canonical order, then every tensor with every resource
split in mask order; the first proof found ends the search. With `prune`, an
unbalanced state fails at once and unbalanced splits are skipped. -/
partial def focused (input : List Keyed) : FocusedM Bool := do
  let state := canonical input
  let ctx ← get
  match ctx.memo[state]? with
  | some value =>
      modify fun c => { c with stats := { c.stats with cacheHits := c.stats.cacheHits + 1 } }
      return value
  | none =>
    modify fun c => { c with stats := { c.stats with calls := c.stats.calls + 1 } }
    checkBudget
    if ctx.prune && !balanced state then
      modify fun c => { c with memo := c.memo.insert state false }
      return false
    match state.findIdx? (fun k => match k.formula with | .par _ _ => true | _ => false) with
    | some index =>
        modify fun c => { c with stats := { c.stats with parSteps := c.stats.parSteps + 1 } }
        let k := state[index]!
        let (left, right) := match k.formula with
          | .par l r => (l, r)
          | _ => (k.formula, k.formula)
        let expanded := state.take index ++ [keyed left, keyed right] ++ state.drop (index + 1)
        let result ← focused expanded
        modify fun c => { c with memo := c.memo.insert state result }
        return result
    | none =>
      if isAxiom state then
        modify fun c => { c with memo := c.memo.insert state true }
        return true
      let mut found := false
      for tensorIndex in List.range state.length do
        if found then break
        let k := state[tensorIndex]!
        match k.formula with
        | .tensor left right =>
            modify fun c => { c with stats := { c.stats with tensorChoices := c.stats.tensorChoices + 1 } }
            let context := state.take tensorIndex ++ state.drop (tensorIndex + 1)
            let n := context.length
            for mask in [0 : 2 ^ n] do
              if found then break
              modify fun c => { c with stats := { c.stats with partitions := c.stats.partitions + 1 } }
              let leftContext := (List.range n).filterMap fun i =>
                if (mask >>> i) % 2 == 1 then some context[i]! else none
              let rightContext := (List.range n).filterMap fun i =>
                if (mask >>> i) % 2 == 1 then none else some context[i]!
              let leftState := keyed left :: leftContext
              let rightState := keyed right :: rightContext
              if ctx.prune && (!balanced leftState || !balanced rightState) then
                continue
              if ← focused leftState then
                if ← focused rightState then
                  found := true
        | _ => pure ()
      modify fun c => { c with memo := c.memo.insert state found }
      return found

structure NetStats where
  partialNodes : Nat := 0
  candidates : Nat := 0
  deriving Repr

structure NetCtx where
  budget : Budget
  stats : NetStats := {}

abbrev NetM := StateRefT NetCtx IO

private def checkNetBudget : NetM Unit := do
  let ctx ← get
  if ctx.budget.exceeded then throw (IO.userError "budget")
  if ctx.stats.partialNodes % 64 == 0 then
    let now ← IO.monoNanosNow
    if now > ctx.budget.deadline then
      set { ctx with budget := { ctx.budget with exceeded := true } }
      throw (IO.userError "budget")

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

/-- Net-space search in the committed generator's order: the first remaining
atom is paired with each later dual atom in vertex order, recursively; each
complete linking is decided by the public decision. -/
partial def netSearch (skeleton : Skeleton) (remaining : List Vertex) (chosen : List Link) :
    NetM Bool := do
  modify fun c => { c with stats := { c.stats with partialNodes := c.stats.partialNodes + 1 } }
  checkNetBudget
  match remaining with
  | [] =>
      modify fun c => { c with stats := { c.stats with candidates := c.stats.candidates + 1 } }
      let certificate : Certificate :=
        { formulas := skeleton.formulas, links := skeleton.links ++ chosen,
          conclusions := skeleton.conclusions }
      return certificate.unificationCheck
  | first :: rest =>
      let target := skeleton.formulas[first]!.dual
      let mut found := false
      for second in rest do
        if found then break
        if skeleton.formulas[second]! == target then
          let tail := rest.filter (· != second)
          if ← netSearch skeleton tail (chosen ++ [Link.axiom first second]) then
            found := true
      return found

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

def runFocused (task : Task) (budgetNs : Nat) (prune : Bool) : IO Json := do
  let start ← IO.monoNanosNow
  let attempt : FocusedM (Option Bool) := do
    try
      let value ← focused (task.sequent.map keyed)
      pure (some value)
    catch _ => pure none
  let (result, ctx) ← attempt.run { budget := { deadline := start + budgetNs }, prune }
  let elapsed := (← IO.monoNanosNow) - start
  return outcome result elapsed [
    ("calls", toJson ctx.stats.calls), ("cacheHits", toJson ctx.stats.cacheHits),
    ("parSteps", toJson ctx.stats.parSteps), ("tensorChoices", toJson ctx.stats.tensorChoices),
    ("partitions", toJson ctx.stats.partitions)]

def runNets (task : Task) (budgetNs : Nat) : IO Json := do
  let start ← IO.monoNanosNow
  let skeleton := Skeleton.ofSequent task.sequent
  let attempt : NetM (Option Bool) := do
    try
      let value ← netSearch skeleton skeleton.atoms []
      pure (some value)
    catch _ => pure none
  let (result, ctx) ← attempt.run { budget := { deadline := start + budgetNs } }
  let elapsed := (← IO.monoNanosNow) - start
  return outcome result elapsed [
    ("partialNodes", toJson ctx.stats.partialNodes), ("candidates", toJson ctx.stats.candidates)]

/-- Runs the arms on every task; `netsOnly` serves corpus certification, where
only the exhaustive net-space outcome matters. -/
def run (budgetMs : Nat) (netsOnly : Bool) : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let lines := payload.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  if lines.isEmpty then
    throw <| IO.userError "matched search received no tasks"
  let budgetNs := budgetMs * 1_000_000
  for line in lines do
    match parseTask line with
    | .error message => throw <| IO.userError s!"task parse failed: {message}"
    | .ok task =>
        let netsResult ← runNets task budgetNs
        if netsOnly then
          IO.println (Json.mkObj [
            ("id", task.id), ("budgetMs", budgetMs), ("nets", netsResult)]).compress
        else
          let focusedResult ← runFocused task budgetNs false
          let balancedResult ← runFocused task budgetNs true
          IO.println (Json.mkObj [
            ("id", task.id),
            ("budgetMs", budgetMs),
            ("focused", focusedResult),
            ("focusedBalanced", balancedResult),
            ("nets", netsResult)]).compress

end ProofNetIRMatchedSearch

def main (args : List String) : IO Unit :=
  let budget := match args with
    | "--budget-ms" :: value :: _ => value.toNat?.getD 5000
    | _ => 5000
  ProofNetIRMatchedSearch.run budget (args.contains "--nets-only")
