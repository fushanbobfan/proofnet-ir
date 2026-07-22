import Lean.Data.Json
import ProofNetIR

open Lean ProofNetIR

namespace ProofNetIRAuditCertificates

def formulaJson : Formula → Json
  | .atom name positive => Json.mkObj [
      ("tag", "atom"), ("name", name), ("positive", positive)]
  | .tensor left right => Json.mkObj [
      ("tag", "tensor"), ("left", formulaJson left),
      ("right", formulaJson right)]
  | .par left right => Json.mkObj [
      ("tag", "par"), ("left", formulaJson left),
      ("right", formulaJson right)]

def linkJson : Link → Json
  | .axiom left right => Json.mkObj [
      ("tag", "axiom"), ("left", left), ("right", right)]
  | .tensor left right conclusion => Json.mkObj [
      ("tag", "tensor"), ("left", left), ("right", right),
      ("conclusion", conclusion)]
  | .par left right conclusion => Json.mkObj [
      ("tag", "par"), ("left", left), ("right", right),
      ("conclusion", conclusion)]

def certificateJson (certificate : Certificate) : Json := Json.mkObj [
  ("formulas", .arr (certificate.formulas.map formulaJson)),
  ("links", .arr (certificate.links.toArray.map linkJson)),
  ("conclusions", .arr (certificate.conclusions.toArray.map
    (fun value : Vertex => Json.num (JsonNumber.fromNat value)))),
  ("accepted", certificate.check)]

def casesForFormula (index : Nat) (formula : Formula) : List (String × Certificate) :=
  let valid := identityCertificate formula
  [ (s!"{index}:valid", valid),
    (s!"{index}:drop-first-link", Mutation.dropFirstLink.apply valid),
    (s!"{index}:duplicate-first-link", Mutation.duplicateFirstLink.apply valid),
    (s!"{index}:self-axiom", (Mutation.replaceFirstAxiomRight 0).apply valid) ]

def auditCases : List (String × Certificate) :=
  (Formula.enumerate ["p", "q"] 2).take 250 |>.zipIdx |>.flatMap fun
    (formula, index) => casesForFormula index formula

def run : IO Unit := do
  for (caseId, certificate) in auditCases do
    let line := Json.mkObj [
      ("id", caseId),
      ("certificate", certificateJson certificate)]
    IO.println line.compress

end ProofNetIRAuditCertificates

def main : IO Unit := ProofNetIRAuditCertificates.run
