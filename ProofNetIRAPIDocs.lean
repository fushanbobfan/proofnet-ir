import ProofNetIR
import Lean

open Lean

namespace ProofNetIRAPIDocs

structure Section where
  title : String
  declarations : List Name

def sections : List Section := [
  {
    title := "Core certificate model"
    declarations := [
      `ProofNetIR.Formula,
      `ProofNetIR.Link,
      `ProofNetIR.Certificate,
      `ProofNetIR.Certificate.StructurallyWellFormed,
      `ProofNetIR.Certificate.DeclarativelyCorrect
    ]
  },
  {
    title := "Checking"
    declarations := [
      `ProofNetIR.Certificate.wellFormed,
      `ProofNetIR.Certificate.check,
      `ProofNetIR.Certificate.wellFormed_iff_structurallyWellFormed,
      `ProofNetIR.Certificate.check_iff_declarativelyCorrect
    ]
  },
  {
    title := "First-order derivations"
    declarations := [
      `ProofNetIR.CutFreeDerivation,
      `ProofNetIR.CutFreeDerivation.infer?,
      `ProofNetIR.CutFreeDerivation.build?_exists_of_infer?,
      `ProofNetIR.CutFreeDerivation.infer?_eq_some_iff_build?_conclusions,
      `ProofNetIR.CutFreeDerivation.build?_formulaConsistent,
      `ProofNetIR.CutFreeDerivation.build?_structurallyWellFormed,
      `ProofNetIR.CutFreeDerivation.build?_switchingCorrect,
      `ProofNetIR.CutFreeDerivation.build?_declarativelyCorrect,
      `ProofNetIR.CutFreeDerivation.build?_check,
      `ProofNetIR.CutFreeDerivation.build?_conclusionFormulas?,
      `ProofNetIR.CutFreeDerivation.desequentialize?,
      `ProofNetIR.CutFreeDerivation.desequentialize?_conclusionFormulas?,
      `ProofNetIR.CutFreeDerivation.desequentialize?_declarativelyCorrect,
      `ProofNetIR.CutFreeDerivation.desequentialize?_check,
      `ProofNetIR.CutFreeDerivation.desequentialize?_exists_with_labels_of_infer?,
      `ProofNetIR.CutFreeDerivation.desequentialize?_exists_checked_of_infer?,
      `ProofNetIR.CutFreeDerivation.CheckedCertificate,
      `ProofNetIR.CutFreeDerivation.desequentializeChecked?,
      `ProofNetIR.CutFreeDerivation.desequentializeChecked?_exists_of_infer?,
      `ProofNetIR.CutFreeDerivation.ElaboratedCertificate,
      `ProofNetIR.CutFreeDerivation.elaborate?,
      `ProofNetIR.CutFreeDerivation.elaborate?_exists_of_infer?
    ]
  },
  {
    title := "Equivalence and canonical keys"
    declarations := [
      `ProofNetIR.VertexRenaming,
      `ProofNetIR.Certificate.ReindexEquivalent,
      `ProofNetIR.Certificate.LinkPermutationEquivalent,
      `ProofNetIR.Certificate.ProofNetEquivalent,
      `ProofNetIR.Certificate.reindexEquivalent?,
      `ProofNetIR.Certificate.reindexEquivalent?_eq_true_iff_of_check,
      `ProofNetIR.Certificate.proofNetEquivalent?,
      `ProofNetIR.Certificate.proofNetEquivalent?_eq_true_iff,
      `ProofNetIR.Certificate.proofNetIdentityCandidateCount,
      `ProofNetIR.CutFreeDerivation.CheckedCertificate.sameProofNet?,
      `ProofNetIR.CutFreeDerivation.CheckedCertificate.sameProofNet?_eq_true_iff,
      `ProofNetIR.Certificate.proofNetCanonicalFamily,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalFamily,
      `ProofNetIR.Certificate.proofNetEquivalent_iff_canonicalFamily_of_check,
      `ProofNetIR.Certificate.equivalenceCanonicalString
    ]
  },
  {
    title := "Sequentialization"
    declarations := [
      `ProofNetIR.SequentializationResult,
      `ProofNetIR.ExecutableSequentializationResult,
      `ProofNetIR.SequentializationError,
      `ProofNetIR.Certificate.sequentialization_of_check,
      `ProofNetIR.Certificate.sequentialize,
      `ProofNetIR.Certificate.sequentialize_complete,
      `ProofNetIR.ExecutableSequentializationResult.kernelDerivation,
      `ProofNetIR.ExecutableSequentializationResult.proofNetEquivalent
    ]
  },
  {
    title := "Serialization and untrusted input"
    declarations := [
      `ProofNetIR.ParseError,
      `ProofNetIR.ParseResult,
      `ProofNetIR.Certificate.canonicalString,
      `ProofNetIR.Certificate.fromString,
      `ProofNetIR.Certificate.checkedFromString,
      `ProofNetIR.Certificate.migrateV02StringToV03
    ]
  },
  {
    title := "Persistent and linear LeanProp bridge"
    declarations := [
      `ProofNetIR.LeanProp.Assumptions,
      `ProofNetIR.LeanProp.ContextPermutation,
      `ProofNetIR.LeanProp.ContextPermutation.toListPerm,
      `ProofNetIR.LeanProp.Derivation,
      `ProofNetIR.LeanProp.Derivation.linearAxiomCount,
      `ProofNetIR.LeanProp.Derivation.linearAxiomCount_eq_length,
      `ProofNetIR.LeanProp.Derivation.toProof,
      `ProofNetIR.LeanProp.Derivation.close
    ]
  }
]

def normalizeNewlines (value : String) : String :=
  value.replace "\r\n" "\n"

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque definition"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive type"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def renderDeclaration (environment : Environment) (name : Name) : IO String := do
  let some info := environment.find? name
    | throw <| IO.userError s!"public API declaration not found: {name}"
  if info.isUnsafe then
    throw <| IO.userError s!"unsafe declaration entered public API manifest: {name}"
  let typeFormat ← PrettyPrinter.ppExprLegacy environment {} {} {} info.type
  let some doc ← findSimpleDocString? environment name (includeBuiltin := false)
    | throw <| IO.userError s!"public API declaration lacks a docstring: {name}"
  return s!"### `{name}`\n\nKind: {declarationKind info}.\n\n{doc.trimAscii.toString}\n\n```lean\n{name} : {typeFormat}\n```\n\n"

def renderSection (environment : Environment) (apiSection : Section) : IO String := do
  let declarations ← apiSection.declarations.mapM (renderDeclaration environment)
  return s!"## {apiSection.title}\n\n{String.join declarations}"

def render (environment : Environment) : IO String := do
  let renderedSections ← sections.mapM (renderSection environment)
  return normalizeNewlines <|
    "# ProofNet-IR public API reference\n\n" ++
    "<!-- Generated by ProofNetIRAPIDocs.lean. Do not edit by hand. -->\n\n" ++
    "This reference is generated from the kernel-loaded Lean environment. " ++
    "The curated manifest records the supported public boundary; generation " ++
    "fails if a listed declaration disappears or becomes unsafe. Regenerate " ++
    "with `lake exe proofnet_ir_api_docs` and verify drift with " ++
    "`lake exe proofnet_ir_api_docs --check`.\n\n" ++
    String.join renderedSections

end ProofNetIRAPIDocs

unsafe def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let environment ← Lean.importModules #[{ module := `ProofNetIR }] {}
    (loadExts := true)
  let generated ← ProofNetIRAPIDocs.render environment
  let output : System.FilePath := "docs" / "api-reference.md"
  if args == ["--check"] then
    let existing ← IO.FS.readFile output
    unless ProofNetIRAPIDocs.normalizeNewlines existing == generated do
      throw <| IO.userError
        "docs/api-reference.md is stale; run `lake exe proofnet_ir_api_docs`"
    IO.println "ProofNet-IR generated API reference is current"
  else if args.isEmpty then
    IO.FS.writeFile output generated
    IO.println s!"generated {output}"
  else
    throw <| IO.userError
      "usage: lake exe proofnet_ir_api_docs [--check]"
