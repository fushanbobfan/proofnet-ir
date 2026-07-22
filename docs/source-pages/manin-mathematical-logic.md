# Page audit in progress: Manin, *A Course in Mathematical Logic for Mathematicians*

Audit started: 2026-07-22

## Source identity and protocol

- Local source: `Manin, Logic for Mathematicians.pdf`
- SHA-256: `79baf1ed4e817e0b081180e55d17b26765a41a00f5819b8eab5dca58be9351ee`
- Visible edition: second edition, Springer, 2010; Chapters I-VIII translated
  by Neal Koblitz, with new chapters by Boris Zilber and Yuri I. Manin.
- Extent: 389 physical PDF pages.
- Text extraction: 388 pages have extractable text. Physical page 1 has no
  extracted text and was therefore rendered and checked visually as the cover.
- Current direct ordered reading: physical pages 1-96. This is an in-progress
  page audit, not a completed-source claim.

## Page-by-page matrix for the completed interval

| Physical page | Printed page / section | Content read or inspected | ProofNet-IR consequence |
|---:|---|---|---|
| 1 | cover | Rendered cover: title, author, second-edition and collaborator information. | Accounts for the extraction anomaly; no mathematical claim. |
| 2 | series front matter | Graduate Texts in Mathematics series and editorial board. | Bibliographic metadata only. |
| 3 | title page | Full title, Manin, second edition, Koblitz translation, and new chapters by Zilber and Manin. | Establishes source identity and mixed authorship by chapter. |
| 4 | copyright page | Authors/contributor, publication identifiers, edition history, and subject classification. | Provenance only; no proof-net theorem. |
| 5 | dedication | Dedication to Nikita, Fedor, and Mitya. | Accounted for; no mathematical claim. |
| 6 | vii / Preface to second edition | Three-decade update: model theory, category-theoretic foundations, computer science; identifies new Parts IV and Chapter IX. | Category/computation motivation is background, not direct evidence for MLL correctness. |
| 7 | viii / Preface to second edition | Model-theory overview; linear formal languages as finite strings; nonlinear languages such as drawings and scores resist formalization. | Directly motivates formalizing graphical syntax instead of treating diagrams informally. |
| 8 | ix / Preface to second edition | Decorated graphs and commutative diagrams as nonlinear categorical language; Chapter IX and classical/quantum computing overview. | Supports a graph-as-formal-language framing, but states no proof-net criterion. |
| 9 | x / Preface to second edition | Mathematical truth, the book's digressions, and the new final digression. | Philosophical context only. |
| 10 | xi / Preface to first edition | Intended mathematical audience; semantics before deducibility; predicate logic, undefinability, and quantum-logic scope. | Reinforces separating semantics from syntax; outside the project's MLL theorem. |
| 11 | xii / Preface to first edition | Independence, recursive functions, Diophantine enumerable sets, complexity, and incompleteness roadmap. | Broad textbook roadmap; no current code dependency. |
| 12 | xiii / Preface to first edition | Incompleteness presentation, Higman's theorem, authorial motivation, acknowledgments, and chapter-dependency graph. | Dependency-graph presentation is visual organization, not a graph-proof identity theorem. |
| 13 | xv / contents | Part I through early Chapter III: formal languages, truth, deducibility, completeness, and forcing. | Maps later syntax/semantics material; no theorem imported. |
| 14 | xvi / contents | Later forcing/constructibility, computability, Diophantine sets, complexity, and start of incompleteness. | Accounts for broad scope outside MLL. |
| 15 | xvii / contents | Incompleteness, recursive groups, Chapter IX graphs/computation, model theory, reading and index. | Identifies Chapter IX section 5 as the direct graph-language interval. |
| 16 | Part I divider | `Provability` part page. | Accounted for; no mathematical claim. |
| 17 | 3 / I.1 | Alphabet, expressions as finite sequences, texts, language, syntax, and semantics. | Establishes a conventional linear-language baseline against which graph syntax must be separately formalized. |
| 18 | 4 / I.1 | Formal versus algorithmic languages, expressiveness, metalanguage, normalized formal texts as mathematical objects, and material notation. | Supports separating certificate syntax, semantics, and implementation representation. |
| 19 | 5 / I.1-I.2 | Abbreviated notation; trinity of formal text, written text, and interpretation; start of first-order languages. | Direct warning not to identify serialization with the abstract certificate or its semantics. |
| 20 | 6 / I.2 | Recursive definitions of terms/formulas and alphabet table for first-order languages. | Methodological support for explicit inductive syntax; outside the MLL formula grammar. |
| 21 | 7 / I.2 | Recursive formula formation and standard interpretations of arithmetic/set-theory terms. | Shows syntax construction before semantic interpretation. |
| 22 | 8 / I.2 | Formula interpretations, normalization/abbreviation tradeoffs, and formulas rather than notations as mathematical objects. | Supports canonical serialization as a representation contract, not proof identity itself. |
| 23 | 9 / Names; I.3 | Object/name/metaname distinctions and start of translation between formal language and mathematical argot. | Reinforces keeping occurrence IDs, formula labels, and printed names distinct. |
| 24 | 10 / I.3 | Translation is creative and nonunique; set-theory examples depend on a specified semantic universe. | Warns that pretty-printing or informal translation cannot substitute for a formal semantics theorem. |
| 25 | 11 / I.3 | Vacuous quantifiers, products, and fully normalized expansion of an abbreviated formula. | Demonstrates the scale and fallibility of surface encodings; motivates checked parsers. |
| 26 | 12 / I.3 | Functions as graphs, Dedekind finiteness, natural numbers as finite ordinals, and need for language extensions. | Graph representation must specify what structure is preserved; mere set encoding is not canonical proof identity. |
| 27 | 13 / I.3 | Encoding topology and arithmetic predicates; quantifier scopes reuse variable names safely. | Supports explicit scoping and occurrence discipline in any richer future syntax. |
| 28 | 14 / I.3 | Arithmetic translation of exponentiation and Riemann hypothesis; expressibility becomes a mathematical problem. | Warns that a proposed serialization/translation needs a theorem, not plausibility. |
| 29 | 15 / I.3; Syntax digression | Higher-order languages, definability limits, first-order encodings, and syntax from finitely many generators. | Broad expressiveness context; no transfer to proof-net completeness. |
| 30 | 16 / Syntax digression | Economy-versus-readability tradeoff; a one-connective dialect; Bourbaki's non-linear superlinear binding notation. | Relevant to API/serialization tradeoffs and explicit parsing rules. |
| 31 | 17 / Syntax digression | Very large abbreviation, class terms, linear/discrete languages, formal graph theory, and diagrams as information-bearing pictures. | Strong motivation for formal graph syntax; explicitly says ordinary drawings lack formal description except formalized graph theory. |
| 32 | 18 / Syntax digression | Snake-lemma diagram and the nonunique loss incurred by linearizing a two-dimensional picture; matrix-structured book example. | Supports the project's macro motivation, but not a proof-net equivalence or canonicalization theorem. |
| 33 | 19 / II.1 | Sequences, concatenation, occurrences, substitution, and parentheses bijections. | Occurrences are first-class positions; directly relevant to distinguishing equal labels at distinct vertices. |
| 34 | 20 / II.1 | Uniqueness of parentheses bijection and recursive term/formula alternatives. | Models the kind of unambiguous parser theorem required for a library interface. |
| 35 | 21 / II.1 | Unique Reading Lemma and an inductive syntactic-analysis algorithm. | Shows executable parsing needs a uniqueness proof; analogous engineering requirement only. |
| 36 | 22 / II.1 | Completion of unique reading; inductive free/bound occurrences, quantifier scope, and capture avoidance. | Reinforces explicit occurrence identity and verified transformations. |
| 37 | 23 / II.1-II.2 | Closed formulas, capture-avoidance intuition, and formal interpretations as primary/secondary mappings. | Supports a strict syntax/semantics boundary and hygienic transformations. |
| 38 | 24 / II.2 | Interpretations of constants, operations, relations, variables, terms, and atomic formulas. | Demonstrates compositional semantics; methodological comparison only. |
| 39 | 25 / II.2 | Inductive truth functions, quantifier variations, models, and standard arithmetic/set interpretations. | Reinforces that acceptance needs an explicitly defined semantics. |
| 40 | 26 / II.2 | Definable sets and closure characterization for arithmetic definability. | Outside MLL; no implementation consequence beyond semantics discipline. |
| 41 | 27 / II.2 | Truth depends only on free variables; closed formulas have interpretation-independent assignment values. | General compositional-semantics lesson only. |
| 42 | 28 / II.2-II.3 | Countability bound on definable sets; completeness/consistency/deduction closure of true formulas. | No proof-net dependency. |
| 43 | 29 / II.3 | Modus ponens/generalization, tautologies as decidable logical polynomials, and examples. | Separates executable decidability from a semantic closure theorem. |
| 44 | 30 / II.3 | Truth-table verification and logical quantifier axioms. | Classical first-order material outside current fragment. |
| 45 | 31 / II.3 | Gödelian sets, truth theorem direction, and proof of quantifier-axiom validity. | Illustrates distinct soundness and converse/completeness obligations. |
| 46 | 32 / II.3 | Capture-sensitive inductive completion of the specialization proof. | Reinforces exact hypotheses in transformation theorems. |
| 47 | 33 / Natural Logic | Limits of imposing formal logic on natural language and logico-semantic word classes. | Warns against treating informal linguistic analogy as mathematical validation. |
| 48 | 34 / Natural Logic | Natural-language connective ambiguity, formal implication versus modus ponens, and algorithmic modality. | Directly supports strict connective naming/scope rather than surface-word analogies. |
| 49 | 35 / II.3 | Luria's Zasetsky case study on asemia, syntactic organization, symbol meaning, and preserved metalinguistic reflection. | Human ability to discuss a formal system does not imply reliable low-level checking; kernel verification remains essential. |
| 50 | 36 / II.3-II.4.1 | Completion of the case study; rejection of the claim that a human can trivially check symbolic proofs; formal definition of deduction and of a fully annotated deduction description. | Distinguishes a bare sequence from a checkable witness carrying rule and premise indices, analogous to requiring proof-bearing API output. |
| 51 | 37 / II.4.1-4.3 | Soundness motivation for formal deduction, completeness as a separate converse, inconsistency/explosion, and ways to establish deducibility or independence. | Reinforces separate soundness/completeness obligations and the need not to replace an explicit witness with an existence claim silently. |
| 52 | 38 / II.4.3-4.5 | Proof-existence versus proof-object discussion, conjunction lemma, and the deduction lemma with explicit induction cases. | Supports keeping proposition-level existence distinct from executable reconstruction and auditing every induction branch. |
| 53 | 39 / II.4.5-4.6 | Completion of the deduction lemma and equality axioms, including substitution across selected free occurrences. | Highlights exact side conditions and occurrence sensitivity in transformation theorems. |
| 54 | 40 / II.4.6 | Detailed equality-axiom deductions and quotient-model compatibility argument. | Equality or quotient claims require explicit preservation proofs; this is methodological evidence, not a proof-net identity theorem. |
| 55 | 41 / II.4.6-4.7 | Completion of quotient interpretation and arithmetic axiom schemata, including induction. | A schema is a family of obligations, not one finite test; no direct MLL dependency. |
| 56 | 42 / II.4.7-4.8 | Formal versus informal induction strength and initial Zermelo-Fraenkel axioms with an extensionality calculation. | Warns that encoded formal scope can be strictly weaker than informal intent; current fragment boundaries must remain explicit. |
| 57 | 43 / II.4.8-4.9 | Model-relative set axioms, hereditarily finite sets, the axiom of infinity, and introduction of replacement. | No direct proof-net theorem; illustrates how one extension changes the semantic universe and proof obligations. |
| 58 | 44 / II.4.9 | Replacement and separation schemata, inaccessible-cardinal motivation, and the tension between formal language and intended interpretation. | Supports documenting intended semantics rather than treating a passing formal game as sufficient library meaning. |
| 59 | 45 / II.4.9-4.10; Proof digression | Axiom of choice, decidable axiom recognition versus generability, and the social/explicit character of proof acceptance. | Directly motivates a decidable checker plus a distinct theorem connecting it to the declarative specification. |
| 60 | 46 / Proof digression | Formal-deduction hygiene, external checks, differing logical commitments, and levels of proof existence. | Supports independent checking and the distinction between `Nonempty` existence and an executable returned derivation. |
| 61 | 47 / Proof digression | Human error in long formal deductions, reproducibility, computer-assisted checking, and the historical Fermat computation example. | Testing and reputation are not substitutes for a small trusted kernel; long generated proofs need machine rechecking. |
| 62 | 48 / Proof digression | Swinnerton-Dyer's computer-assisted enumeration example, hardware/software/data risks, and redundancy-based confidence. | Independent reruns and diverse validation are empirical safeguards, not mathematical completeness proofs. |
| 63 | 49 / Proof digression; II.5.1 | Independent recomputation as experimental verification, the value of explanatory proofs, and a finite tautology basis. | Justifies differential audits while keeping them categorically separate from Lean theorems. |
| 64 | 50 / II.5.1-5.4 | Fundamental lemma for valuation-forced formulas and the induction reducing tautology derivability to a finite basis. | Finite exhaustive search needs an explicit coverage lemma; this directly parallels the new occurrence-enumerator completeness proof. |
| 65 | 51 / II.5.4 | Completion of the Fundamental Lemma by enumerating connective/truth-value cases and deriving each required formula. | A finite case table is meaningful only with a proof that all cases are covered; analogous to exhaustive regression plus an enumeration theorem. |
| 66 | 52 / II.5.5-5.7 | Boolean algebras, examples, and Boolean-valued extensions of propositional truth functions. | Semantics can be generalized only after operations and laws are restated; no direct MLL consequence. |
| 67 | 53 / II.5.8; Kennings | Boolean validity of tautologies via the finite basis and MP preservation; contrast between generative grammars and probabilistic speech. | Shows how a finite generator proof transports validity; the linguistic discussion remains motivation rather than theorem-proving evidence. |
| 68 | 54 / Kennings | Recursive substitution rules for complex kennings and their decomposition into simple kennings. | Illustrates explicit compositional syntax, but not proof-net sequentialization or proof identity. |
| 69 | 55 / Kennings; II.6.1 | Completion and exercises on maximal kennings; setup for Gödel completeness. | The maximum-length exercise is an analogy for termination bounds only; no imported result. |
| 70 | 56 / II.6.2-6.3 | Completeness theorem, cardinality bound, deducibility/independence corollary, and proof via models or inconsistency. | Reinforces that soundness and completeness are converse theorems with different witnesses and assumptions. |
| 71 | 57 / II.6.4-6.8 | Sufficient alphabets, Henkin witnesses, completion and language-extension lemmas, and the need to alternate constructions. | Local constructions can interfere globally; totality arguments must track invariants across every iteration. |
| 72 | 58 / II.6.9 | Term-model construction and induction proving closed-formula truth exactly matches membership in a complete consistent set. | Exemplifies a representation-to-semantics iff proved by structural induction, not inferred from construction. |
| 73 | 59 / II.6.9-6.10 | Quantifier cases for the term model and maximal consistent extension via Zorn's lemma. | Explicit witnesses and consistency hypotheses remain essential; classical existence is not executable search. |
| 74 | 60 / II.6.11-6.12 | Adding ranked witness constants while preserving consistency and iterating completion/sufficiency. | A useful warning that one pass can destroy another invariant; relevant to staged library proofs. |
| 75 | 61 / II.6.12-6.14; II.7.1 | Limit construction, deduction of completeness, equality quotient, and transition to countable submodels. | Quotienting needs a preservation theorem; no claim about the project's graph equivalence follows automatically. |
| 76 | 62 / II.7.2-7.4 | Absoluteness, Löwenheim-Skolem, and construction of a small subset preserving selected formulas. | Preserving a selected observation set is weaker than arbitrary structural isomorphism; equivalence APIs must state the preserved interface. |
| 77 | 63 / II.7.5-7.7 | Countable set-theory models, Mostowski collapse statement, and transfinite construction. | Demonstrates the need to distinguish internal representation from external interpretation. |
| 78 | 64 / II.7.7-7.8 | Completion of Mostowski collapse and start of Skolem's paradox. | Isomorphism and uniqueness require explicit hypotheses; reinforces narrow, proved certificate equivalence. |
| 79 | 65 / II.7.8 | Model-relative power sets, Cantor's theorem, countable models, and the interpretive content of Skolem's paradox. | Passing the same formal sentence in different models need not preserve informal meaning; library semantics must be fixed. |
| 80 | 66 / II.8.1-8.3 | Conservative language extensions by definable function symbols and an explicit translation back to the poorer language. | API sugar or new serialization should come with a translation/conservativity or migration theorem. |
| 81 | 67 / II.8.3 | Inductive elimination of a newly defined function symbol and the distinction between an explicit translation and an easier but ineffective semantic proof. | A nonconstructive conservativity proof does not itself yield a usable converter; executable APIs need algorithms in addition to existence. |
| 82 | 68 / II.8.3-8.4 | Normal-model correspondence and truth-preserving translation proof for definitional extensions. | A migration path should preserve semantics in both directions under stated model assumptions. |
| 83 | 69 / II.8.4; II.9.1-9.2 | Examples of definable notation, then SELF syntax for minimal self-reference and the setup for Tarski-style undefinability. | New notation is safe only with a conservativity result; self-reference material has no direct MLL dependency. |
| 84 | 70 / II.9.3-9.5 | Names, displays, standard interpretations, and diagonal formulas proving no property captures exactly its true or false formulas. | Formal syntax must separate object, name, and serialization; reflection claims require a carefully delimited metalanguage. |
| 85 | 71 / II.10.1-10.3 | Smullyan arithmetic syntax with class terms and simultaneous rank-indexed syntax/semantics definitions. | Mutually staged representations need a well-founded construction and unique-reading argument. |
| 86 | 72 / II.10.3 | Continuation of rank-indexed term/formula formation, bound occurrences, and truth interpretation. | Supports explicit scoping and termination measures in richer future front ends. |
| 87 | 73 / II.10.3-10.4 | Expressive equivalence of two arithmetic languages via truth/free-variable preserving translations. | Representation equivalence may be non-invertible while still preserving a specified interface; this is narrower than graph isomorphism. |
| 88 | 74 / II.10.4-II.11.1 | Completion of bidirectional translations and Gödel numbering of expressions. | Stable encoding needs unique decoding and preservation theorems; numbering itself is not semantic identity. |
| 89 | 75 / II.11.1-11.5 | Labels, displays, diagonalization, and the Tarski-Smulleyan undefinability theorem. | A serialization capable of self-description still cannot collapse truth into one internal predicate; no direct proof-net result. |
| 90 | 76 / II.11.5-11.6 | Generalization to broader arithmetic languages and discussion of numbering independence and definable provability. | Robust claims should not depend on a clever encoding accident; canonicalization tests must accompany representation-level theorems. |
| 91 | 77 / II.11.6-11.7; Self-reference | Algorithmic proof recognition, definability of provability, incompleteness, and performative self-reference. | Directly supports the project's separation of decidable proof checking from semantic truth and completeness claims. |
| 92 | 78 / Self-reference; II.12.1-12.2 | Self-reference in algorithms, then motivation and physical setup for quantum logic. | Looping/feedback requires explicit termination controls; quantum material is outside project scope. |
| 93 | 79 / II.12.2-12.4 | Orthohelium spin measurements, hidden-variable assumptions, and the Kochen-Specker noncolorability statement. | Illustrates a global obstruction not detectable from isolated local assignments, but it is not evidence for switching correctness. |
| 94 | 80 / II.12.4-12.5 | Link from spin assignments to Kochen-Specker, followed by the Hilbert-space language of quantum mechanics. | General local/global analogy only; no theorem transfers to proof nets. |
| 95 | 81 / II.12.5-12.7 | Observables, compatible operators, symmetries, and the hydrogen-atom example. | No direct project dependency; reinforces keeping mathematical language and physical interpretation separate. |
| 96 | 82 / II.12.8 | Two-layer interpretation of free evolution, observation, probability, and post-measurement state. | Demonstrates that one syntax can have layered operational interpretation; outside current certificate semantics. |

## Current claim boundary

The completed interval supports the motivation for treating diagrams and
decorated graphs as formal languages whose syntax and semantics must be stated
precisely. It does not state the Danos-Regnier switching criterion, MLL proof-net
correctness, or a sequentialization theorem. The remaining 293 pages are not
yet represented as directly read in order.
