/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7CommitmentIntervalParGuardReentryFailure

/-!
# Commitment-interval par-guard re-entry failure consumer

Consumes both typed public theorems, reconstructs every interval-outcome branch,
and destructs and rebuilds every field of the older marked re-entry target.
-/

namespace ProofNetIR
namespace SequentialFigure7
namespace Consumer

open SequentialSchedulerBridge
open SequentialSchedulerState

private theorem markedTargetRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state} {component : UnificationComponent}
    {owned : List Vertex} {endpoint : Vertex}
    (target :
      ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input component
        owned endpoint) :
    ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory input component
      owned endpoint := by
  rcases target with
    ⟨path, directed, markedAge, pathStarts, finishOwned, directedMembership,
      parentEdge, targetNeSelected, targetMarked, rawMarked,
      representativeActive⟩
  rcases parentEdge with
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩
  exact ⟨path, directed, markedAge, pathStarts, finishOwned,
    directedMembership,
    ⟨linkIndex, kind, storedLeft, storedRight, conclusion, sourceEq,
      targetFrontier, targetNotGlobal, linkLookup, targetPremise,
      conclusionOutside⟩,
    targetNeSelected, targetMarked, rawMarked, representativeActive⟩

private theorem outcomeRoundTrip
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    {tagHistory : CanonicalTagHistory certificate history}
    {input : ReadyHeadInput state}
    {consumer : ConnectiveBelow certificate input.vertex}
    {position edgeCount : Nat} {first : RawTokenAge} {status : Prop}
    (outcome :
      tagHistory.CommitmentIntervalParTraceOutcome input consumer position
        edgeCount first status)
    (statusRoundTrip : status → status) :
    tagHistory.CommitmentIntervalParTraceOutcome input consumer position
      edgeCount first status := by
  cases outcome with
  | avoiding path => exact .avoiding path
  | equalSelected offset parent child event offsetLt parentAt childAt
      notAvoiding membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalSelected offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | equalMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childEq side beforeTrace afterTrace trace =>
      exact .equalMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childEq side beforeTrace afterTrace trace
  | olderMate offset parent child event offsetLt parentAt childAt notAvoiding
      membership eventAge childLt side beforeTrace afterTrace trace oldStatus =>
      exact .olderMate offset parent child event offsetLt parentAt childAt
        notAvoiding membership eventAge childLt side beforeTrace afterTrace trace
        (statusRoundTrip oldStatus)

private theorem nopRoundTrip
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : NopStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? = some none ∧
          ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  apply outcomeRoundTrip
    (step.commitmentInterval_parTraceReentryMarkedOutcome connected tagHistory
      invariant componentLookup occurrence positive firstAt lastAt noTail)
  rintro ⟨mateOutside, mateUnmarked, target⟩
  exact ⟨mateOutside, mateUnmarked, markedTargetRoundTrip target⟩

private theorem waitRoundTrip
    {certificate : Certificate} {before after : ReservationState}
    {history : ExecutedHistory certificate before}
    (connected : certificate.ReferenceSwitchingConnected)
    (tagHistory : CanonicalTagHistory certificate history)
    (invariant : SchedulerInvariant certificate before)
    (step : WaitStep certificate before after)
    {component : UnificationComponent} {usedLinks owned : List Nat}
    (componentLookup :
      before.core.components[step.prepared.stackResult.rawAge]? =
        some (some component))
    (occurrence :
      Certificate.ComponentOccurrenceWitness certificate component
        usedLinks owned)
    {position edgeCount : Nat} {first : RawTokenAge}
    (positive : 0 < edgeCount)
    (firstAt : before.stack.sigma[position]? = some first)
    (lastAt :
      before.stack.sigma[position + edgeCount]? =
        some step.prepared.stackResult.rawAge)
    (noTail :
      ¬ ∃ pending,
        pending ∈ step.prepared.stackResult.remainingTop ∧
          pending ∉ certificate.conclusions) :
    tagHistory.CommitmentIntervalParTraceOutcome
      step.prepared.readyHeadInput step.consumer position edgeCount first
        (step.consumer.mate ∉ owned ∧
          before.core.marks[step.consumer.mate]? =
            some (some step.mateRawAge) ∧
          before.core.representative step.mateRawAge <
            step.prepared.stackResult.rawAge ∧
          ActiveCarrierExternalReentryMarkedHistoricalTarget tagHistory
            step.prepared.readyHeadInput component owned step.consumer.mate) := by
  apply outcomeRoundTrip
    (step.commitmentInterval_parTraceReentryMarkedOutcome connected tagHistory
      invariant componentLookup occurrence positive firstAt lastAt noTail)
  rintro ⟨mateOutside, mateMarked, representativeOlder, target⟩
  exact ⟨mateOutside, mateMarked, representativeOlder,
    markedTargetRoundTrip target⟩

end Consumer
end SequentialFigure7
end ProofNetIR

#print axioms ProofNetIR.SequentialFigure7.NopStep.commitmentInterval_parTraceReentryMarkedOutcome
#print axioms ProofNetIR.SequentialFigure7.WaitStep.commitmentInterval_parTraceReentryMarkedOutcome

def main : IO Unit :=
  IO.println "Figure-7 par-guard re-entry failure target: kernel-green"
