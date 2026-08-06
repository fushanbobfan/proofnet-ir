import ProofNetIR.SequentialFigure7StableEnabled
import ProofNetIR.SequentialFigure7UnifyPayloadEnabled

namespace ProofNetIR

/-!
# Marked-tensor adjacency for Figure-7 unification

This module isolates the extra input-only scheduler fact needed to refine the
marked-tensor alternative returned by `readyHead_enabled_or_tensor_mark_cases`
into `UnifyPayloadEnabled`.  A mate mark alone is insufficient: the active
sigma boundary must have an actual predecessor, and the marked mate's raw age
must resolve to that predecessor.

The result is a local applicability bridge under the complete state-only
`SchedulerInvariant`.  It makes no reachability, progress, completeness,
fallback-removal, or complexity claim.
-/

namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

/-- Input-only evidence that one raw age belongs to the interval represented
by the boundary immediately preceding the active sigma boundary.

The witness stores only queries of the supplied sigma stack.  In particular,
it stores no executor result, post-state, history, or reachability evidence. -/
structure SigmaPredecessorInput (sigma : List RawTokenAge)
    (activeBoundary mateRawAge previousBoundary : RawTokenAge) : Type where
  active_top :
    sigma.getLast? = some activeBoundary
  previous_top :
    sigma.dropLast.getLast? = some previousBoundary
  mate_boundary :
    sigmaBoundary? sigma mateRawAge = some previousBoundary

namespace SigmaPredecessorInput

/-- An active top and its supplied predecessor give the exact adjacent
two-level suffix required by `UnifyPayloadInput`. -/
theorem sigma_two_levels
    {sigma : List RawTokenAge}
    {activeBoundary mateRawAge previousBoundary : RawTokenAge}
    (input :
      SigmaPredecessorInput sigma activeBoundary mateRawAge
        previousBoundary) :
    ∃ sigmaPrefix,
      sigma = sigmaPrefix ++ [previousBoundary, activeBoundary] := by
  rcases List.getLast?_eq_some_iff.mp input.active_top with
    ⟨activePrefix, sigmaEquation⟩
  have previousTop :
      activePrefix.getLast? = some previousBoundary := by
    simpa [sigmaEquation] using input.previous_top
  rcases List.getLast?_eq_some_iff.mp previousTop with
    ⟨sigmaPrefix, prefixEquation⟩
  refine ⟨sigmaPrefix, ?_⟩
  rw [sigmaEquation, prefixEquation]
  simp [List.append_assoc]

end SigmaPredecessorInput

/-- A marked exact tensor consumer is unification-enabled once the mate age is
known to lie in the interval represented by the predecessor of the active
sigma boundary.

The complete scheduler invariant is used only for the valid increasing sigma
partition.  The theorem remains a local input correspondence and does not
assert that its predecessor evidence is reachable or universally available. -/
theorem markedTensor_unifyPayloadEnabled
    {certificate : Certificate} {before : ReservationState}
    (invariant : SchedulerInvariant certificate before)
    (head : ReadyHeadInput before)
    (consumer : ConnectiveBelow certificate head.vertex)
    (tensorKind : consumer.kind = .tensor)
    {mateRawAge previousBoundary : RawTokenAge}
    (mateMarked :
      before.core.marks[consumer.mate]? = some (some mateRawAge))
    (adjacency :
      SigmaPredecessorInput before.stack.sigma head.rawAge mateRawAge
        previousBoundary) :
    UnifyPayloadEnabled certificate before := by
  rcases adjacency.sigma_two_levels with
    ⟨sigmaPrefix, sigmaEquation⟩
  let tensorConsumer : TensorBelow := {
    linkIndex := consumer.linkIndex
    storedLeft := consumer.storedLeft
    storedRight := consumer.storedRight
    conclusion := consumer.conclusion
    side := consumer.side }
  have consumerValid :
      tensorConsumer.Valid certificate certificate.consumerIndex
        head.vertex := by
    refine ⟨consumer.consumer_eq, ?_, ?_, ?_⟩
    · simpa [tensorConsumer, SequentialConnectiveKind.asLink,
        tensorKind] using consumer.link_eq
    · simpa [tensorConsumer, SequentialConnectiveKind.asLink,
        tensorKind] using consumer.wellFormed
    · simpa [tensorConsumer, TensorBelow.premise] using
        consumer.premise_eq
  have tensorMateMarked :
      before.core.marks[tensorConsumer.mate]? =
        some (some mateRawAge) := by
    simpa [tensorConsumer, TensorBelow.mate, ConnectiveBelow.mate] using
      mateMarked
  have lower : previousBoundary ≤ mateRawAge :=
    sigmaBoundary?_le adjacency.mate_boundary
  have previousLtActive : previousBoundary < head.rawAge := by
    have increasing :=
      invariant.stack_wellShaped.sigma_partition.strictIncreasing
    rw [sigmaEquation] at increasing
    simpa [List.append_assoc] using
      (List.pairwise_append.mp increasing).2.1
  have upper : mateRawAge < head.rawAge := by
    apply Nat.lt_of_not_ge
    intro activeLe
    have activeLePrevious :
        head.rawAge ≤ previousBoundary :=
      sigmaBoundary?_greatest
        invariant.stack_wellShaped.sigma_partition.strictIncreasing
        adjacency.mate_boundary head.rawAge
        (List.mem_of_getLast? head.sigma_top) activeLe
    exact (Nat.not_le_of_gt previousLtActive) activeLePrevious
  exact ⟨{
    vertex := head.vertex
    readyTail := head.readyTail
    consumer := tensorConsumer
    mateRawAge := mateRawAge
    sigmaPrefix := sigmaPrefix
    previousBoundary := previousBoundary
    activeBoundary := head.rawAge
    top_ready := head.top_ready
    sigma_two_levels := sigmaEquation
    consumer_valid := consumerValid
    mate_marked := tensorMateMarked
    lower := lower
    upper := upper }⟩

end SequentialFigure7

end ProofNetIR
