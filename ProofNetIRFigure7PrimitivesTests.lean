import ProofNetIR.SequentialSchedulerBridge

namespace ProofNetIR

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState

namespace Figure7PrimitivesTests

private def stackFixture : SequentialStackState where
  marks := #[none, none]
  nextAge := 1
  sigma := [0]
  ready := [[0]]
  waiting := #[.undefined, .undefined]

private def stackExpected : SequentialStackState where
  marks := #[some 0, none]
  nextAge := 1
  sigma := [0]
  ready := [[]]
  waiting := #[.undefined, .undefined]

/-- Popping the last vertex retains the now-empty old top ready bucket. -/
example :
    stackFixture.popReadyMark? =
      .ok {
        vertex := 0
        rawAge := 0
        remainingTop := []
        after := stackExpected } := by
  rfl

/-- Retaining the exhausted bucket is semantic: the next local pop observes
the empty top bucket instead of silently dropping to an older bucket. -/
example :
    stackExpected.popReadyMark? = .error .emptyTopBucket := by
  rfl

private def layeredStackFixture : SequentialStackState where
  marks := Array.replicate 10 none
  nextAge := 4
  sigma := [0, 3]
  ready := [[9], [1, 2]]
  waiting := Array.replicate 10 .undefined

private def layeredStackExpected : SequentialStackState where
  marks :=
    (Array.replicate 10 none).setIfInBounds 1 (some 3)
  nextAge := 4
  sigma := [0, 3]
  ready := [[9], [2]]
  waiting := Array.replicate 10 .undefined

/-- The deterministic refinement selects the head of the last ready bucket and
uses the last sigma boundary; it does not fall back to the older bucket or
boundary at the front of either outer list. -/
example :
    layeredStackFixture.popReadyMark? =
      .ok {
        vertex := 1
        rawAge := 3
        remainingTop := [2]
        after := layeredStackExpected } := by
  rfl

private def stackOutOfBounds : SequentialStackState where
  marks := #[]
  nextAge := 1
  sigma := [0]
  ready := [[7]]
  waiting := #[.undefined]

/-- A missing mark slot is reported as out of bounds, not as unmarked. -/
example :
    stackOutOfBounds.popReadyMark? =
      .error (.markOutOfBounds 7) := by
  rfl

private def stackAlreadyMarked : SequentialStackState where
  marks := #[some 9]
  nextAge := 10
  sigma := [0]
  ready := [[0]]
  waiting := Array.replicate 10 .undefined

/-- An allocated marked slot reports its exact previous raw age. -/
example :
    stackAlreadyMarked.popReadyMark? =
      .error (.alreadyMarked 0 9) := by
  rfl

private def coreFixture : UnificationState where
  marks := #[none, none]
  parents := #[0]
  components := #[none]
  startedAxioms := 1
  firedConnectives := 4

private def coreExpected : UnificationState where
  marks := #[some 0, none]
  parents := #[0]
  components := #[none]
  startedAxioms := 1
  firedConnectives := 4

/-- The production primitive changes only the requested raw mark. -/
example :
    coreFixture.markReadyRaw? 0 0 = .ok coreExpected := by
  rfl

/-- Production out-of-bounds and already-marked failures are distinct. -/
example :
    ({ coreFixture with marks := #[] } :
        UnificationState).markReadyRaw? 0 0 =
      .error (.markOutOfBounds 0) := by
  rfl

example :
    ({ coreFixture with marks := #[some 0] } :
        UnificationState).markReadyRaw? 0 0 =
      .error (.alreadyMarked 0 0) := by
  rfl

end Figure7PrimitivesTests

end ProofNetIR

def main : IO Unit :=
  IO.println "Figure-7 pop/raw-mark primitive tests passed"
