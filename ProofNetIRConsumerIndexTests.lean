import ProofNetIR.SequentialConsumerIndex

open ProofNetIR

namespace ProofNetIRConsumerIndexTests

def p : Formula := .atom "p" true
def pDual : Formula := p.dual
def q : Formula := .atom "q" true
def qDual : Formula := q.dual

/-- A small structurally well-formed certificate whose tensor consumes
occurrences `0` and `2` in their stored left/right order. -/
def validCertificate : Certificate where
  formulas := #[p, pDual, q, qDual, .tensor p q]
  links := [
    .axiom 0 1,
    .axiom 2 3,
    .tensor 0 2 4
  ]
  conclusions := [4, 1, 3]

theorem validCertificate_structural :
    validCertificate.StructurallyWellFormed :=
  validCertificate.wellFormed_iff_structurallyWellFormed.mp
    (by native_decide)

def storedLeftResult : TensorBelow where
  linkIndex := 2
  storedLeft := 0
  storedRight := 2
  conclusion := 4
  side := .storedLeft

def storedRightResult : TensorBelow where
  linkIndex := 2
  storedLeft := 0
  storedRight := 2
  conclusion := 4
  side := .storedRight

example :
    validCertificate.consumerIndex.uniqueConsumer? 0 = some 2 := by
  simpa [Certificate.consumerIndex] using
    ConsumerIndex.build_uniqueConsumer?_eq_some
      validCertificate_structural
      (link := .tensor 0 2 4)
      (linkIndex := 2)
      (premise := 0)
      (by native_decide)
      (by native_decide)
      (by native_decide)

example :
    validCertificate.tensorBelow? 0 =
      some storedLeftResult := by
  native_decide

example :
    validCertificate.tensorBelow? 2 =
      some storedRightResult := by
  native_decide

example : storedLeftResult.premise = 0 := by native_decide
example : storedLeftResult.mate = 2 := by native_decide
example : storedRightResult.premise = 2 := by native_decide
example : storedRightResult.mate = 0 := by native_decide

/-- A conclusion occurrence has no submitted connective consumer. -/
example :
    validCertificate.tensorBelow? 4 =
      none := by
  native_decide

/-- Out-of-range canonical queries fail closed. -/
example : validCertificate.tensorBelow? 99 = none := by
  native_decide

/-- Two distinct candidate consumers fail the table-relative singleton guard.
This explicitly exercises the low-level API, not the canonical scheduler API. -/
def nonuniqueIndex : ConsumerIndex :=
  #[[2, 1], [], [], [], []]

example :
    tensorBelow? validCertificate nonuniqueIndex 0 = none := by
  native_decide

/-- A unique table-relative candidate that is not a tensor is rejected. -/
def axiomIndex : ConsumerIndex :=
  #[[0], [], [], [], []]

example :
    tensorBelow? validCertificate axiomIndex 0 = none := by
  native_decide

/-- An occurrence indexed by a low-level table to a tensor that does not consume
it is rejected. -/
def wrongPremiseIndex : ConsumerIndex :=
  #[[], [], [], [2], []]

example :
    tensorBelow? validCertificate wrongPremiseIndex 3 = none := by
  native_decide

/-- Reusing one occurrence as both stored tensor premises is locally malformed
and cannot manufacture a self-mate. -/
def selfTensorCertificate : Certificate where
  formulas := #[p, .tensor p p]
  links := [.tensor 0 0 1]
  conclusions := [1]

def selfTensorIndex : ConsumerIndex := #[[0], []]

example : selfTensorCertificate.consumerIndex.bucket 0 = [0, 0] := by
  native_decide

example :
    selfTensorCertificate.tensorBelow? 0 = none := by
  native_decide

/-- The low-level table-relative query also rejects the malformed self tensor,
even if a caller supplies a collapsed singleton bucket. -/
example :
    tensorBelow? selfTensorCertificate selfTensorIndex 0 = none := by
  native_decide

/-- A tensor whose conclusion carries the wrong formula is rejected even when
the caller supplies a singleton candidate bucket. -/
def wrongFormulaCertificate : Certificate where
  formulas := #[p, q, .par p q]
  links := [.tensor 0 1 2]
  conclusions := [2]

def wrongFormulaIndex : ConsumerIndex := #[[0], [0], []]

example :
    wrongFormulaCertificate.tensorBelow? 0 = none := by
  native_decide

example :
    tensorBelow? wrongFormulaCertificate wrongFormulaIndex 0 = none := by
  native_decide

/-- Out-of-bounds tensor premises also fail the independent local guard. -/
def outOfBoundsCertificate : Certificate where
  formulas := #[p, q, .tensor p q]
  links := [.tensor 0 99 2]
  conclusions := [2]

def outOfBoundsIndex : ConsumerIndex := #[[0], [], []]

example :
    outOfBoundsCertificate.tensorBelow? 0 = none := by
  native_decide

example :
    tensorBelow? outOfBoundsCertificate outOfBoundsIndex 0 = none := by
  native_decide

/-- A par consumer can be unique without being a tensor below the queried
occurrence. -/
def parCertificate : Certificate where
  formulas := #[p, q, .par p q]
  links := [.par 0 1 2]
  conclusions := [2]

example : parCertificate.tensorBelow? 0 = none := by
  native_decide

/-- Two independently well-formed tensor links consume the same occurrence.
The canonical index exposes both, so the canonical query rejects the
certificate-global ambiguity. -/
def doubleConsumerCertificate : Certificate where
  formulas := #[p, q, .tensor p q, q, .tensor p q]
  links := [
    .tensor 0 1 2,
    .tensor 0 3 4
  ]
  conclusions := [2, 4]

example :
    doubleConsumerCertificate.consumerIndex.bucket 0 = [1, 0] := by
  native_decide

example :
    doubleConsumerCertificate.tensorBelow? 0 = none := by
  native_decide

/-- The same malformed certificate demonstrates why the low-level query is
only table-relative: a forged partial table can hide the second consumer. -/
def forgedPartialDoubleConsumerIndex : ConsumerIndex :=
  #[[0], [0], [], [], []]

def forgedFirstTensorResult : TensorBelow where
  linkIndex := 0
  storedLeft := 0
  storedRight := 1
  conclusion := 2
  side := .storedLeft

example :
    tensorBelow? doubleConsumerCertificate
        forgedPartialDoubleConsumerIndex 0 =
      some forgedFirstTensorResult := by
  native_decide

def run : IO Unit :=
  IO.println "consumer-index orientation and fail-closed tests passed"

end ProofNetIRConsumerIndexTests

def main : IO Unit :=
  ProofNetIRConsumerIndexTests.run
