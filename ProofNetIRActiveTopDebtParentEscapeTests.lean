/-
Copyright (c) 2026 ProofNet-IR contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ProofNet-IR contributors
-/

import ProofNetIR.SequentialFigure7ActiveTopDebtParentEscape

set_option warningAsError true

/-!
# Active-top debt parent-escape consumer

This executable consumer destructs the complete escape payload, exercises the
non-exclusive tail-or-escape reduction in both branches, and checks the exact
failure-conditioned parent-escape theorem.
-/

namespace ProofNetIR
namespace SequentialFigure7

open SequentialSchedulerState
open SequentialSchedulerState.SequentialStackState
open SequentialSchedulerBridge

example
    {certificate : Certificate} {state : ReservationState}
    {component : UnificationComponent} {owned : List Vertex}
    {selected : Vertex}
    (escape :
      ActiveCarrierParentEscape certificate state component owned selected) :
    ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
        (kind : SequentialConnectiveKind)
        (storedLeft storedRight conclusion : Vertex),
      premise ≠ selected ∧
        premise ∈ component.frontier ∧
        state.core.marks[premise]? = some (some markedAge) ∧
        premise ∉ certificate.conclusions ∧
        certificate.links[linkIndex]? =
          some (kind.asLink storedLeft storedRight conclusion) ∧
        premise ∈
          (kind.asLink storedLeft storedRight conclusion).premises ∧
        conclusion ∉ owned := by
  rcases escape with
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      premiseNotGlobal, linkLookup, premiseMembership,
      conclusionNotOwned⟩
  exact
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      premiseNotGlobal, linkLookup, premiseMembership,
      conclusionNotOwned⟩

example
    {certificate : Certificate} {state : ReservationState}
    {history : ExecutedHistory certificate state}
    (tagHistory : CanonicalTagHistory certificate history)
    {component : UnificationComponent} {owned : List Vertex}
    {selected : Vertex}
    (escape :
      ActiveCarrierParentEscape certificate state component owned selected) :
    ∃ (premise : Vertex) (markedAge : RawTokenAge) (linkIndex : Nat)
        (kind : SequentialConnectiveKind)
        (storedLeft storedRight conclusion : Vertex),
      premise ≠ selected ∧
        premise ∈ component.frontier ∧
        state.core.marks[premise]? = some (some markedAge) ∧
        tagHistory.RawMarked markedAge premise ∧
        premise ∉ certificate.conclusions ∧
        certificate.links[linkIndex]? =
          some (kind.asLink storedLeft storedRight conclusion) ∧
        premise ∈
          (kind.asLink storedLeft storedRight conclusion).premises ∧
        conclusion ∉ owned := by
  rcases ActiveCarrierParentEscape.authenticMarkedPremise tagHistory escape with
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      authentic, premiseNotGlobal, linkLookup, premiseMembership,
      conclusionNotOwned⟩
  exact
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      authentic, premiseNotGlobal, linkLookup, premiseMembership,
      conclusionNotOwned⟩

example
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      state.core.components[input.rawAge]? = some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted state.core input.rawAge
          component owned ∧
        ((∃ pending,
            pending ∈ input.readyTail ∧
              pending ∉ certificate.conclusions) ∨
          ActiveCarrierParentEscape certificate state component owned
            input.vertex) := by
  rcases input.readyTail_nonconclusion_or_parentEscape
      correct invariant consumer parEq with
    ⟨component, usedLinks, owned, componentLookup, occurrence,
      accounted, tail | escape⟩
  · exact
      ⟨component, usedLinks, owned, componentLookup, occurrence,
        accounted, Or.inl tail⟩
  · exact
      ⟨component, usedLinks, owned, componentLookup, occurrence,
        accounted, Or.inr escape⟩

example
    {certificate : Certificate} {state : ReservationState}
    (input : ReadyHeadInput state)
    (correct : certificate.DeclarativelyCorrect)
    (invariant : SchedulerInvariant certificate state)
    (consumer : ConnectiveBelow certificate input.vertex)
    (parEq : consumer.kind = .par)
    (noTail :
      ¬ ∃ pending,
        pending ∈ input.readyTail ∧
          pending ∉ certificate.conclusions) :
    ∃ (component : UnificationComponent) (usedLinks owned : List Nat),
      state.core.components[input.rawAge]? = some (some component) ∧
        Certificate.ComponentOccurrenceWitness certificate component
          usedLinks owned ∧
        Certificate.OwnedOccurrenceAccounted state.core input.rawAge
          component owned ∧
        ActiveCarrierParentEscape certificate state component owned
          input.vertex := by
  rcases input.parentEscape_of_no_readyTail
      correct invariant consumer parEq noTail with
    ⟨component, usedLinks, owned, componentLookup, occurrence,
      accounted, escape⟩
  rcases escape with
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      premiseNotGlobal, linkLookup, premiseMembership,
      conclusionNotOwned⟩
  refine
    ⟨component, usedLinks, owned, componentLookup, occurrence, accounted, ?_⟩
  exact
    ⟨premise, markedAge, linkIndex, kind, storedLeft, storedRight,
      conclusion, premiseNeSelected, premiseFrontier, premiseMarked,
      premiseNotGlobal, linkLookup, premiseMembership,
      conclusionNotOwned⟩

#print axioms ActiveCarrierParentEscape
#print axioms ActiveCarrierParentEscape.authenticMarkedPremise
#print axioms ReadyHeadInput.readyTail_nonconclusion_or_parentEscape
#print axioms ReadyHeadInput.parentEscape_of_no_readyTail

end SequentialFigure7
end ProofNetIR

def main : IO Unit :=
  IO.println "active-top debt parent-escape consumer: kernel-green"
