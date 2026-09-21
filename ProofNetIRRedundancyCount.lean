import ProofNetIR
import Std.Data.HashMap

open Lean ProofNetIR

namespace ProofNetIRRedundancyCount

/-! Exact search-redundancy counts for one-sided unit-free MLL sequents.

Every input line is a JSON object with an `id` and a `sequent` (an array of
formulas in the v0.2 wire encoding). The occurrence forest of the sequent is
fixed, every occurrence is distinct, and exchange is absorbed by working on
sets of occurrences. For each task the output line reports:

- `dAll`: cut-free derivations in the plain calculus (axiom, tensor with every
  context split, par, any rule order);
- `dWeak`: derivations of the committed focused baseline, whose par phase is one
  deterministic step before a tensor and its context split are chosen;
- `dFoc`: derivations of the tensor-persistent focused calculus, where the
  focus continues through the positive subformulas of the chosen tensor and
  releases at an atom or a par;
- `nets`: correct proof nets of the sequent, the axiom linkings of the forest
  accepted by the public decision `unificationCheck` (equal to `check` by
  theorem).

Counts are exact whole numbers. A task whose memoized recursion exceeds the
state budget, or whose candidate linkings exceed the linking budget, is
reported as excluded with the partial information available. -/

/-- One occurrence of the forest. `left` and `right` are meaningful only for
connectives; `name` only for atoms. -/
structure Occurrence where
  formula : Formula
  kind : Nat
  left : Nat
  right : Nat
  name : Nat
  positive : Bool
  balance : Array Int
  deriving Repr

instance : Inhabited Occurrence :=
  ⟨{ formula := .atom "" true, kind := 0, left := 0, right := 0, name := 0, positive := true,
     balance := #[] }⟩

def kindAtom : Nat := 0
def kindTensor : Nat := 1
def kindPar : Nat := 2

structure Forest where
  occurrences : Array Occurrence
  roots : List Nat
  names : Array String

/-- Budget of memoized states per count and per task. -/
def stateBudget : Nat := 3_000_000

/-- Budget of candidate axiom linkings per task. -/
def linkingBudget : Nat := 1_000_000

structure Build where
  occurrences : Array Occurrence := #[]
  names : Array String := #[]

private def nameIndex (build : Build) (name : String) : Build × Nat :=
  match build.names.findIdx? (· == name) with
  | some index => (build, index)
  | none => ({ build with names := build.names.push name }, build.names.size)

/-- Preorder occurrence numbering; balance vectors are filled after all names
are known. -/
private def placeholder (formula : Formula) (kind : Nat) : Occurrence :=
  { formula, kind, left := 0, right := 0, name := 0, positive := true, balance := #[] }

private partial def addFormula (build : Build) : Formula → Build × Nat
  | .atom name positive =>
      let (build, index) := nameIndex build name
      let id := build.occurrences.size
      let occurrence : Occurrence :=
        { formula := .atom name positive, kind := kindAtom, left := 0, right := 0,
          name := index, positive, balance := #[] }
      ({ build with occurrences := build.occurrences.push occurrence }, id)
  | .tensor left right => addConnective build (.tensor left right) kindTensor left right
  | .par left right => addConnective build (.par left right) kindPar left right
where
  addConnective (build : Build) (formula : Formula) (kind : Nat) (left right : Formula) :
      Build × Nat :=
    let id := build.occurrences.size
    let build := { build with occurrences := build.occurrences.push (placeholder formula kind) }
    let (build, leftId) := addFormula build left
    let (build, rightId) := addFormula build right
    let occurrence := build.occurrences[id]!
    let updated : Occurrence := { occurrence with left := leftId, right := rightId }
    ({ build with occurrences := build.occurrences.set! id updated }, id)

private def addVectors (a b : Array Int) : Array Int :=
  (Array.range a.size).map fun index => a[index]! + b[index]!

/-- Balance vectors bottom-up: later ids are descendants of earlier ids, so a
reverse pass sees children before parents. -/
private def fillBalances (build : Build) : Array Occurrence := Id.run do
  let size := build.names.size
  let mut occurrences := build.occurrences
  for step in List.range occurrences.size do
    let id := occurrences.size - 1 - step
    let occurrence := occurrences[id]!
    let balance :=
      if occurrence.kind == kindAtom then
        (Array.replicate size (0 : Int)).set! occurrence.name
          (if occurrence.positive then 1 else -1)
      else
        addVectors occurrences[occurrence.left]!.balance occurrences[occurrence.right]!.balance
    occurrences := occurrences.set! id { occurrence with balance }
  return occurrences

def Forest.ofSequent (sequent : List Formula) : Forest := Id.run do
  let mut build : Build := {}
  let mut roots : List Nat := []
  for formula in sequent do
    let (next, id) := addFormula build formula
    build := next
    roots := roots ++ [id]
  return { occurrences := fillBalances build, roots, names := build.names }

/-- A state is the set of occurrence ids forming the current sequent. -/
abbrev State := UInt64

def State.has (state : State) (id : Nat) : Bool :=
  (state >>> id.toUInt64) &&& 1 == 1

def State.insert (state : State) (id : Nat) : State :=
  state ||| (1 <<< id.toUInt64)

def State.erase (state : State) (id : Nat) : State :=
  state &&& ~~~(1 <<< id.toUInt64)

def State.members (state : State) (size : Nat) : List Nat :=
  (List.range size).filter (State.has state)

def State.ofList (ids : List Nat) : State :=
  ids.foldl State.insert 0

/-- Sum of the balance vectors of the members. -/
def stateBalance (forest : Forest) (state : State) : Array Int :=
  (State.members state forest.occurrences.size).foldl
    (fun acc id => addVectors acc forest.occurrences[id]!.balance)
    (Array.replicate forest.names.size 0)

def balanced (vector : Array Int) : Bool :=
  vector.all (· == 0)

/-- The exact axiom case: two dual atom occurrences of one name. -/
def isAxiomState (forest : Forest) (state : State) : Bool :=
  match State.members state forest.occurrences.size with
  | [a, b] =>
      let x := forest.occurrences[a]!
      let y := forest.occurrences[b]!
      x.kind == kindAtom && y.kind == kindAtom && x.name == y.name && x.positive != y.positive
  | _ => false

structure Counting where
  forest : Forest
  memoAll : Std.HashMap UInt64 Nat := {}
  memoWeak : Std.HashMap UInt64 Nat := {}
  memoFoc : Std.HashMap (UInt64 × Nat) Nat := {}
  states : Nat := 0
  exceeded : Bool := false

abbrev CountM := StateM Counting

private def tick : CountM Bool := do
  let counting ← get
  if counting.exceeded then
    return false
  if counting.states ≥ stateBudget then
    set { counting with exceeded := true }
    return false
  set { counting with states := counting.states + 1 }
  return true

/-- Depth-first choice of context members with per-name suffix-range pruning. -/
private partial def chooseSubsets (forest : Forest) (context : Array Nat) (target : Array Int)
    (suffixPos suffixNeg : Array (Array Int)) (index : Nat) (partialSum : Array Int)
    (chosen : State) (acc : List State) : List State :=
  let size := target.size
  if index == context.size then
    if partialSum == target then chosen :: acc else acc
  else
    let feasible := (List.range size).all fun name =>
      partialSum[name]! + suffixNeg[index]![name]! ≤ target[name]! &&
        target[name]! ≤ partialSum[name]! + suffixPos[index]![name]!
    if !feasible then acc
    else
      let id := context[index]!
      let withIt := chooseSubsets forest context target suffixPos suffixNeg (index + 1)
        (addVectors partialSum forest.occurrences[id]!.balance) (State.insert chosen id) acc
      chooseSubsets forest context target suffixPos suffixNeg (index + 1) partialSum chosen withIt

/-- All context subsets whose balance equals `target`, by branch and bound on
the per-name suffix ranges. -/
private def balancedSubsets (forest : Forest) (context : Array Nat)
    (target : Array Int) : List State := Id.run do
  let size := forest.names.size
  let count := context.size
  let mut suffixPos : Array (Array Int) := Array.replicate (count + 1) (Array.replicate size 0)
  let mut suffixNeg : Array (Array Int) := Array.replicate (count + 1) (Array.replicate size 0)
  for step in List.range count do
    let index := count - 1 - step
    let balance := forest.occurrences[context[index]!]!.balance
    let nextPos := suffixPos[index + 1]!
    let nextNeg := suffixNeg[index + 1]!
    suffixPos := suffixPos.set! index ((Array.range size).map fun name =>
      nextPos[name]! + max balance[name]! 0)
    suffixNeg := suffixNeg.set! index ((Array.range size).map fun name =>
      nextNeg[name]! + min balance[name]! 0)
  return chooseSubsets forest context target suffixPos suffixNeg 0 (Array.replicate size 0) 0 []

/-- Splits of `state - tensor` into a balanced left premise around `left` and a
balanced right premise around `right`, as (leftState, rightState) pairs. -/
private def tensorSplits (forest : Forest) (state : State) (tensor : Nat) :
    List (State × State) :=
  let occurrence := forest.occurrences[tensor]!
  let context := (State.members (State.erase state tensor) forest.occurrences.size).toArray
  let target := forest.occurrences[occurrence.left]!.balance.map (- ·)
  (balancedSubsets forest context target).map fun chosen =>
    let rest := context.foldl
      (fun acc id => if State.has chosen id then acc else State.insert acc id) (0 : State)
    (State.insert chosen occurrence.left, State.insert rest occurrence.right)

/-- Plain calculus: every rule order. -/
partial def countAll (state : State) : CountM Nat := do
  let counting ← get
  match counting.memoAll[state]? with
  | some value => return value
  | none =>
    if !(← tick) then return 0
    let forest := counting.forest
    let value ← do
      if !balanced (stateBalance forest state) then pure 0
      else if isAxiomState forest state then pure 1
      else
        let mut total := 0
        for id in State.members state forest.occurrences.size do
          let occurrence := forest.occurrences[id]!
          if occurrence.kind == kindPar then
            total := total + (← countAll (State.insert (State.insert (State.erase state id) occurrence.left) occurrence.right))
          else if occurrence.kind == kindTensor then
            for (leftState, rightState) in tensorSplits forest state id do
              let leftCount ← countAll leftState
              if leftCount != 0 then
                total := total + leftCount * (← countAll rightState)
        pure total
    modify fun counting => { counting with memoAll := counting.memoAll.insert state value }
    return value

/-- The committed baseline: the par phase is one deterministic step. -/
partial def countWeak (state : State) : CountM Nat := do
  let counting ← get
  match counting.memoWeak[state]? with
  | some value => return value
  | none =>
    if !(← tick) then return 0
    let forest := counting.forest
    let members := State.members state forest.occurrences.size
    let value ← do
      if !balanced (stateBalance forest state) then pure 0
      else
        match members.find? fun id => forest.occurrences[id]!.kind == kindPar with
        | some id =>
            let occurrence := forest.occurrences[id]!
            countWeak (State.insert (State.insert (State.erase state id) occurrence.left) occurrence.right)
        | none =>
            if isAxiomState forest state then pure 1
            else
              let mut total := 0
              for id in members do
                if forest.occurrences[id]!.kind == kindTensor then
                  for (leftState, rightState) in tensorSplits forest state id do
                    let leftCount ← countWeak leftState
                    if leftCount != 0 then
                      total := total + leftCount * (← countWeak rightState)
              pure total
    modify fun counting => { counting with memoWeak := counting.memoWeak.insert state value }
    return value

/-- Tensor-persistent focusing. `focus` is the occurrence that must be
decomposed next, or `forest.occurrences.size` when the focus is free. -/
partial def countFoc (state : State) (focus : Nat) : CountM Nat := do
  let counting ← get
  match counting.memoFoc[(state, focus)]? with
  | some value => return value
  | none =>
    if !(← tick) then return 0
    let forest := counting.forest
    let free := forest.occurrences.size
    let members := State.members state free
    let continueOn (premise : State) (sub : Nat) : CountM Nat :=
      if forest.occurrences[sub]!.kind == kindTensor then countFoc premise sub
      else countFoc premise free
    let focusOn (tensor : Nat) : CountM Nat := do
      let occurrence := forest.occurrences[tensor]!
      let mut total := 0
      for (leftState, rightState) in tensorSplits forest state tensor do
        let leftCount ← continueOn leftState occurrence.left
        if leftCount != 0 then
          total := total + leftCount * (← continueOn rightState occurrence.right)
      pure total
    let value ← do
      if !balanced (stateBalance forest state) then pure 0
      else if focus != free then focusOn focus
      else
        match members.find? fun id => forest.occurrences[id]!.kind == kindPar with
        | some id =>
            let occurrence := forest.occurrences[id]!
            countFoc (State.insert (State.insert (State.erase state id) occurrence.left) occurrence.right) free
        | none =>
            if isAxiomState forest state then pure 1
            else
              let mut total := 0
              for id in members do
                if forest.occurrences[id]!.kind == kindTensor then
                  total := total + (← focusOn id)
              pure total
    modify fun counting => { counting with memoFoc := counting.memoFoc.insert (state, focus) value }
    return value

private def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Candidate axiom linkings: every bijection between the positive and negative
occurrences of each name; `none` when a name is unbalanced, which is a definite
zero, not a budget exclusion. -/
private def linkingCount (forest : Forest) : Option Nat := Id.run do
  let mut total := 1
  for name in List.range forest.names.size do
    let positives := (List.range forest.occurrences.size).filter fun id =>
      let o := forest.occurrences[id]!
      o.kind == kindAtom && o.name == name && o.positive
    let negatives := (List.range forest.occurrences.size).filter fun id =>
      let o := forest.occurrences[id]!
      o.kind == kindAtom && o.name == name && !o.positive
    if positives.length != negatives.length then return none
    total := total * factorial positives.length
  return some total

private partial def bijections : List Nat → List Nat → List (List (Nat × Nat))
  | [], _ => [[]]
  | p :: ps, negatives =>
      negatives.flatMap fun n =>
        (bijections ps (negatives.erase n)).map fun rest => (p, n) :: rest

private def certificateOf (forest : Forest) (axioms : List (Nat × Nat)) : Certificate :=
  let connectives := (List.range forest.occurrences.size).filterMap fun id =>
    let o := forest.occurrences[id]!
    if o.kind == kindTensor then some (Link.tensor o.left o.right id)
    else if o.kind == kindPar then some (Link.par o.left o.right id)
    else none
  { formulas := forest.occurrences.map (·.formula)
    links := axioms.map (fun (p, n) => Link.axiom p n) ++ connectives
    conclusions := forest.roots }

/-- Correct nets of the forest, by enumerating the candidate linkings and
deciding each with the public decision. -/
private def countNets (forest : Forest) : Nat := Id.run do
  let mut perName : List (List (List (Nat × Nat))) := []
  for name in List.range forest.names.size do
    let positives := (List.range forest.occurrences.size).filter fun id =>
      let o := forest.occurrences[id]!
      o.kind == kindAtom && o.name == name && o.positive
    let negatives := (List.range forest.occurrences.size).filter fun id =>
      let o := forest.occurrences[id]!
      o.kind == kindAtom && o.name == name && !o.positive
    perName := perName ++ [bijections positives negatives]
  let combos := perName.foldl (fun acc choices => acc.flatMap fun prefix' =>
    choices.map fun choice => prefix' ++ choice) [[]]
  let mut accepted := 0
  for axioms in combos do
    if (certificateOf forest axioms).unificationCheck then
      accepted := accepted + 1
  return accepted

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

def runTask (task : Task) : Json := Id.run do
  let forest := Forest.ofSequent task.sequent
  let size := forest.occurrences.size
  let atoms := (List.range size).filter fun id => forest.occurrences[id]!.kind == kindAtom
  if size > 64 then
    return Json.mkObj [("id", task.id), ("excluded", "occurrences exceed 64")]
  let root : State := State.ofList forest.roots
  let free := size
  let (dAll, allCounting) := Id.run ((countAll root).run { forest })
  let (dWeak, weakCounting) := Id.run ((countWeak root).run { forest })
  let (dFoc, focCounting) := Id.run ((countFoc root free).run { forest })
  let linkings := linkingCount forest
  let (nets, netsExcluded) :=
    match linkings with
    | none => (0, false)
    | some count => if count > linkingBudget then (0, true) else (countNets forest, false)
  return Json.mkObj [
    ("id", task.id),
    ("occurrences", size),
    ("atoms", atoms.length),
    ("names", forest.names.size),
    ("conclusions", forest.roots.length),
    ("dAll", toString dAll),
    ("dAllExcluded", allCounting.exceeded),
    ("dAllStates", allCounting.states),
    ("dWeak", toString dWeak),
    ("dWeakExcluded", weakCounting.exceeded),
    ("dWeakStates", weakCounting.states),
    ("dFoc", toString dFoc),
    ("dFocExcluded", focCounting.exceeded),
    ("dFocStates", focCounting.states),
    ("linkings", toString (linkings.getD 0)),
    ("nets", toString nets),
    ("netsExcluded", netsExcluded)]

def run : IO Unit := do
  let payload ← (← IO.getStdin).readToEnd
  let lines := payload.splitOn "\n" |>.filter fun line => !line.trimAscii.isEmpty
  if lines.isEmpty then
    throw <| IO.userError "redundancy counter received no tasks"
  for line in lines do
    match parseTask line with
    | .error message => throw <| IO.userError s!"task parse failed: {message}"
    | .ok task => IO.println (runTask task).compress

end ProofNetIRRedundancyCount

def main : IO Unit := ProofNetIRRedundancyCount.run
