/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentEdgeTargetAvoidance

namespace ProofNetIR

/-!
# Figure-7 commitment-edge target-avoidance consumer

This consumer invokes the target carrier and both adjacent-edge theorems. The
calls supply the child-event untouched law explicitly for future tensor and
ready-head par conclusions and consume the resulting avoiding paths.
-/

open SequentialFigure7
open SequentialSchedulerBridge
open SequentialSchedulerState

#check CanonicalTagHistory.CommitmentEdgeTargetAvoidingPath
#check CanonicalTagHistory.commitmentEdge_referencePath_avoiding
#check CanonicalTagHistory.commitmentEdge_referencePath_avoiding_parConclusion

/-- Invoke the public result predicate directly. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (parent child : RawTokenAge) (target : Vertex) : Prop :=
  tagHistory.CommitmentEdgeTargetAvoidingPath parent child target

/-- Invoke the theorem with its exact future-candidate and untouched inputs. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (candidate : FutureNewCandidateAt certificate state)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childUntouched : ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger → event.rawAge = child →
        ¬ event.Touched candidate.tensor.conclusion) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      candidate.tensor.conclusion := by
  exact tagHistory.commitmentEdge_referencePath_avoiding invariant candidate
    parentAt childAt childUntouched

/-- Invoke the ready-head par-conclusion specialization. -/
example {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate state)
    (input : ReadyHeadInput state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    {position parent child : RawTokenAge}
    (parentAt : state.stack.sigma[position]? = some parent)
    (childAt : state.stack.sigma[position + 1]? = some child)
    (childUntouched : ∀ {event : ReservationEvent certificate},
      event ∈ tagHistory.reservationLedger → event.rawAge = child →
        ¬ event.Touched consumer.conclusion) :
    tagHistory.CommitmentEdgeTargetAvoidingPath parent child
      consumer.conclusion := by
  exact tagHistory.commitmentEdge_referencePath_avoiding_parConclusion
    invariant input consumer parEq parentAt childAt childUntouched

#print axioms CanonicalTagHistory.commitmentEdge_referencePath_avoiding_parConclusion

end ProofNetIR

/- Run the standalone commitment-edge target-avoidance API smoke consumer. -/
def main : IO Unit :=
  IO.println "Figure-7 commitment-edge target-avoidance API consumer passed."
