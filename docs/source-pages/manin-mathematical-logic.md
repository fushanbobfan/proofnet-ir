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
- Current direct ordered reading: physical pages 1-288. This is an in-progress
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
| 97 | 83 / II.12.8-12.10 | Completion of the measurement discussion and definition of quantum propositions as partially compatible Boolean structures. | Shows that changing the ambient logic changes which operations are total; it supplies no MLL switching theorem. |
| 98 | 84 / II.12.10-12.12 | Closed subspaces of a Hilbert space as a partial Boolean algebra and the non-embedding theorem for dimension at least three. | A local Boolean view need not extend globally; this is an analogy only, not a proof-net counterexample. |
| 99 | 85 / II.12.13 | First finite Kochen-Specker graph and its orthogonal realization constraints. Rendered and inspected the labelled graph visually. | Confirms that diagram labels and incidences carry proof data; no result transfers to MLL. |
| 100 | 86 / II.12.14 | Large assembled graph used in the finite noncolorability argument. Rendered and inspected its circular network and subgraphs visually. | Reinforces that a graph theorem depends on exact incidence, not an informal picture or serialization order. |
| 101 | 87 / II.12.12 proof | Propagation through the finite graph forces a contradiction and proves the non-embedding theorem. | Exemplifies a finite global obstruction; unrelated to Danos-Regnier switchings. |
| 102 | 88 / II.12.15-12.16 | Quantum tautologies, modular-structure encodings, admissible sequences, and the Gelfand-Ponomarev representation direction. | Representation theorems require explicit preserved structure; no graph-canonicalization claim follows for ProofNet-IR. |
| 103 | 89 / II.12.16; Orthohelium; von Neumann universe | Approximate symmetries and Hilbert-space/spin reinterpretation of orthohelium, then transition to the cumulative universe. | Physical reinterpretation remains separate from formal semantics; no current code dependency. |
| 104 | 90 / von Neumann universe | Sets versus classes, Russell-style size restrictions, and motivation for constructing the universe in stages. | Supports size and representation discipline only. |
| 105 | 91 / von Neumann universe | Partial, linear, and well orders; initial segments; and comparison of well-ordered sets. | Well-founded descent is methodological support for termination measures, not the project's sequentialization proof. |
| 106 | 92 / von Neumann universe | Unique order isomorphisms, universal ordering difficulties, and von Neumann's canonical ordinal representatives. | Canonical representatives require a proved uniqueness principle; useful boundary for the library's narrower canonical keys. |
| 107 | 93 / von Neumann universe | Successor and limit ordinals, transfinite induction/recursion, and cardinal representatives. | Clarifies the kind of well-founded recursion obligation used in total search, without supplying an MLL result. |
| 108 | 94 / von Neumann universe | Rank hierarchy, definition of the cumulative universe, and closure/transitivity properties. | Supports explicit universes and rank measures; outside proof nets. |
| 109 | 95 / von Neumann universe | Kuratowski pairs, products, relations, functions, and closure of the universe under standard set constructions. | Encodings must be accompanied by preservation claims; set encodings alone do not define proof identity. |
| 110 | 96 / von Neumann universe | Foundation/no descending membership chains and comparison of the intuitive universe with the formal language of set theory. | Reinforces separating metatheoretic interpretation from the checked object language. |
| 111 | 97 / Truth as Value and Duty | Mathematical truth, testimony, reproducibility, and the special status of mathematical verification. | Motivates independently replayable Lean artifacts but is philosophical rather than theorem evidence. |
| 112 | 98 / Truth as Value and Duty | Rigidity of mathematical constants across calculations and the contrast between finite computation and ideal infinite objects. | Tests provide finite evidence; they are not substitutes for universal kernel theorems. |
| 113 | 99 / Truth as Value and Duty | Truth as a human value, scepticism/relativism, and the relation between texts and accepted claims. | Supports transparent claim boundaries and auditable provenance only. |
| 114 | 100 / Truth as Value and Duty | Formal-rule accounts of proof contrasted with compressed mathematical practice, discovery, experimentation, and error. | Directly supports retaining machine-checkable proof terms beneath explanatory documentation. |
| 115 | 101 / Truth as Value and Duty | Theories, models, metaphors, and mathematics as a language for the physical world. | A motivating metaphor cannot validate a proof-net criterion; formal statements remain authoritative. |
| 116 | 102 / Truth as Value and Duty | Computerized black-box models, representation replacing the represented activity, and financial-model caution. | Warns against confusing serialized certificates, benchmark scores, or model output with mathematical correctness. |
| 117 | 103 / Truth as Value and Duty | Mathematical truth among competing values and the shift from set-theoretic foundations toward categories and homotopy. | Broad foundations context; no direct current-fragment theorem. |
| 118 | III divider; III.1 | Start of the continuum problem: cardinal comparison, Cantor's ideas, and the continuum hypothesis. | New chapter accounted for; unrelated to MLL correctness. |
| 119 | 106 / III.1.2-1.4 | Cantor-Schroeder-Bernstein, comparison via well-ordering, and the role of choice. | Classical existence and executable construction remain distinct obligations. |
| 120 | 107 / III.1.4-1.6 | Well-ordering construction, diagonal proof that the power set is larger, CH/GCH, and independence statements. | Separates relative consistency/model results from internal algorithmic evidence. |
| 121 | 108 / III.1.7-1.8 | Goedel's constructible-universe idea and Cohen/Scott-Solovay Boolean-valued strategy. | Demonstrates that a completeness or independence claim depends on a precisely fixed semantics. |
| 122 | 109 / III.1.9-1.12 | Random-variable model, almost-sure Boolean truth, statement of the main theorem, and obstacles to naive interpretation. | A checker-specific truth notion must be defined and proved stable under rules; analogical background only. |
| 123 | 110 / III.1.12; III.2.1 | Why intermediate cardinality is subtle in the random model, roadmap, and need for a second-order real language. | Reinforces that an informal construction can change meaning under interpretation. |
| 124 | 111 / III.2.2-2.5 | Syntax of `L2 Real` and formulas for integers, CH, and completeness. | Expressibility is an explicit language-design problem; current ProofNet-IR scope must stay stated. |
| 125 | 112 / III.2.6-2.7 | Complete Boolean algebra of truth values and the interpretation set of random variables/functionals. | Generalized truth values are outside the current Boolean checker, but illustrate explicit semantic domains. |
| 126 | 113 / III.2.7-2.8 | Compositional truth function for atoms, connectives, and quantifiers; assignment-invariance lemma begins. | Models the syntax-to-semantics recursion and free-variable invariance pattern. |
| 127 | 114 / III.2.8-2.9; III.3.1-3.4 | Closed-formula truth, fundamental lemma, non-deducibility theorem, and preservation of truth under rules. | Strongly reinforces separate rule-preservation, axiom-validity, and countermodel obligations. |
| 128 | 115 / III.3.5-3.6 | Sketch for special axioms, omitted hard choice/completeness checks, a field-axiom example, and start of falsifying CH. | Omitted textbook steps cannot be silently imported as machine-checked evidence; no project theorem depends on them. |
| 129 | 116 / III.3.6-3.7 | Construction of a functional whose random zero set has intermediate size and its correctness lemma. | Demonstrates a witness construction with explicit admissibility obligations. |
| 130 | 117 / III.3.7-3.8 | Correctness proof, random-set interpretation, and setup for ruling out a surjection onto all reals. | Shows why apparent set-size intuition must be re-proved inside the chosen semantics. |
| 131 | 118 / III.3.8-3.9 | Countable-chain-condition contradiction for the first CH alternative and computation of the model's integers. | Independent combinatorial invariants can close a semantic proof; no transfer to switching correctness. |
| 132 | 119 / III.3.9-3.10 | Completion of the integer truth-value lemma and start of the second CH alternative. | A derived semantic predicate needs both inequalities/directions, paralleling exact checker specifications. |
| 133 | 120 / III.3.10; III.4.1-4.2 | Countable-chain contradiction for the second alternative and introduction of Boolean-valued universes by transfinite recursion. | Total recursive constructions require explicit stages, invariants, and a domain measure. |
| 134 | 121 / III.4.2 | Rank-indexed data for `V^B`, new elements, extensionality condition, and recursive Boolean membership/equality. | Extensionality is built into the representation and then proved adequate; relevant as a design lesson for certificate equivalence. |
| 135 | 122 / III.4.2-4.4 | Verification of the recursion and low-rank examples with nontrivial Boolean membership probabilities. | Representation equations need closure proofs before downstream claims can rely on them. |
| 136 | 123 / III.4.4 | Further low-rank computations and the specialization `B = {0,1}` toward ordinary sets. | A special case can validate intuition but does not establish arbitrary representation isomorphism. |
| 137 | 124 / III.4.4; III.5.1 | Completion of the ordinary-set map, truth semantics for `L1 Set`, and start of the equality/membership compatibility lemma. | A semantic equivalence requires explicit preservation in both membership and equality. |
| 138 | 125 / III.5.1 | Rank induction proving transitivity and substitution laws for Boolean equality and membership. | Mirrors the need to prove every equivalence relation supports each public operation. |
| 139 | 126 / III.5.1-5.2 | Completion of the compatibility lemma and proof that extensionality is Boolean-true. | Extensionality is a theorem under the recursive definitions, not a naming convention. |
| 140 | 127 / III.5.3-5.4; III.6.1-6.2 | Equality axioms, observational equivalence of random sets, and definition of random classes. | Observational equivalence is explicitly delimited; this cautions against calling the current canonical key full graph isomorphism. |
| 141 | 128 / III.6.3 | Random-class examples, rank truncation, Boolean set operations, and separation via intersection with a set. | A class-like predicate is not automatically representable by a finite/set object; constructive conversion needs proof. |
| 142 | 129 / III.6.4-6.5 | Formula-defined random classes and construction proving the pairing axiom Boolean-true. | Existence is obtained by a formula plus a bounded representative proof, a useful library-proof pattern only. |
| 143 | 130 / III.6.6 | Construction proving the union axiom Boolean-true through rank restriction and extensionality. | Shows the bookkeeping required for semantic closure; outside MLL. |
| 144 | 131 / III.6.7 | Power-set construction begins, using a rank-bounded representative and equality estimate. | The proof is unfinished on this page and is recorded as such; no project dependency. |
| 145 | 132 / III.6.7-6.8; III.7.1 | Completion of power set, rank-minimal proof of regularity, and introduction to collecting random sets. | Minimal-rank contradiction is a termination pattern only; no MLL result. |
| 146 | 133 / III.7.2 | Collection and gluing lemmas for Boolean-valued sets, with leastness properties. | A constructed representative is specified by an observable universal property, not storage identity. |
| 147 | 134 / III.7.2-7.4 | Completion of collection/gluing, proof of infinity, and a witness lemma for nonempty random classes. | Existence, equivalence, and leastness are distinct proof obligations. |
| 148 | 135 / III.7.4-7.6 | Choice-based witness construction, replacement statement, and reduction to a unit interval Boolean algebra. | Relies explicitly on choice; the project's axiom audit must continue to expose such trust dependencies. |
| 149 | 136 / III.7.6-7.7 | Restriction to `B_a` and rank-bounded construction proving replacement. | Localizing a semantic argument requires a preservation map and exact truth equations. |
| 150 | 137 / III.7.7-7.8 | Completion of replacement and construction of a Boolean-valued choice function. | A witness-producing API needs the same kind of explicit admissibility and output invariants. |
| 151 | 138 / III.7.9-7.11 | Verification that the constructed relation is a functional graph with the intended domain. | Each public invariant must be proved separately; one aggregate test is insufficient. |
| 152 | 139 / III.7.12 | Domain reduction and induction for the element-selection clause of choice. | Reinforces explicit induction coverage and extensional transport. |
| 153 | 140 / III.7.12; III.8.1-8.2 | Completion of choice, canonical embedding of ordinary sets, and Boolean-algebra conditions for falsifying CH. | Canonical maps are defined only up to a stated equivalence here; a useful warning for serialization claims. |
| 154 | 141 / III.8.2-8.5 | Regular-open Boolean algebra construction (proof omitted) and distinct random subsets lemma. | The omitted theorem is not machine-checked evidence; no project claim depends on it. |
| 155 | 142 / III.8.5-8.7 | Topological proof of distinctness, formal negation of CH, and unique-object reduction lemma. | Formalization must replace abbreviated prose with exact formulas and hypotheses. |
| 156 | 143 / III.8.7-8.11 | Application of the reduction lemma and countable-chain-condition argument against a surjection. | Uniqueness reduces a quantified proof only after its formal deduction is supplied. |
| 157 | 144 / III.8.11-8.12 | Completion of the first non-surjection and start of the second via many distinct subsets. | Cardinal counting is background only. |
| 158 | 145 / III.8.12; III.9.1-9.2 | Completion of the CH countermodel and transition from Boolean-valued models to forcing/generic extensions. | Different proof presentations can encode the same result only after a bridge construction is shown. |
| 159 | 146 / III.9.2-9.3 | Countable transitive model, generic finite restrictions, and density conditions ensuring a total surjection. | Local finite approximations require a global invariant and coverage condition. |
| 160 | 147 / III.9.3-9.6 | Dense sets, abstract forcing conditions, generic-set existence, and roadmap to `M[G]`. | Search completeness analogously needs an explicit notion of what every candidate family must meet. |
| 161 | 148 / III.9.6-9.9 | Completion of a poset to a Boolean algebra, generic maximal ideal, and relativized Boolean universe. | Equivalence between representations is a theorem with a construction, not an informal identification. |
| 162 | 149 / III.9.9-9.13 | Construction and model theorem for `M[G]`, CH example, and setup for Easton's theorem. | Model-building scope remains unrelated to current proof nets. |
| 163 | 150 / III.9.14 | Easton's and Silver's cardinal-exponentiation results and limits of GCH behavior. | No current code dependency. |
| 164 | 151 / IV.1.1-1.2 | Constructible universe `L`, eight primitive set operations, rank construction, and definition of constructible sets. | Explicit generators plus transfinite closure illustrate a presentation, not an MLL calculus. |
| 165 | 152 / IV.1.2-1.4 | Interpretation of constructibility, finite-rank agreement with `V`, and cardinality of each `L_alpha`. | “Constructible” here is not finitistic/executable; terminology must not be transferred casually. |
| 166 | 153 / IV.1.5-1.7 | Transitivity, big-class property, and well-ordering scheme for effective ordinal numbering. | Canonical numbering requires a proved global well-order and is far stronger than a stable serialization order. |
| 167 | 154 / IV.1.7-1.8 | Important-triple well-order, recursive numbering `N`, and correctness/surjectivity proof begins. | A numbering is useful only with totality and coverage proofs. |
| 168 | 155 / IV.1.8; IV.2.1-2.3 | Completion of enumeration of `L`, model-relative truth, definable sets, and closure proposition. | Separates encoding coverage from semantic absoluteness. |
| 169 | 156 / IV.2.3 | Structural induction showing atomic and connective-defined subsets stay in a transitive closed class. | Every syntax constructor needs its own preservation case. |
| 170 | 157 / IV.2.3-2.4 | Quantifier projection case and absoluteness lemma for restricted quantifiers. | Unbounded search is controlled by a rank bound; analogous to explicit search bounds in executable APIs. |
| 171 | 158 / IV.2.4-2.5; IV.3.1 | Sigma-zero formulas, constructibility of ordinals, and proof that ZF is `L`-true begins. | Absolute fragments depend on syntactic restrictions that must be recorded. |
| 172 | 159 / IV.3.1 | Verification of set-theory axioms through power set and infinity in `L`. | Closure of a representation under operations is a family of theorems, not one label. |
| 173 | 160 / IV.3.1-3.3 | Replacement, statement of absolute numbering formula, and universal choice function. | The key numbering theorem is postponed; dependency ordering must remain visible. |
| 174 | 161 / IV.3.3-3.4; IV.4.1 | Completion of choice and careful formulation of GCH relative to internal cardinality. | Model-relative cardinality illustrates why a library must fix the equivalence observed by clients. |
| 175 | 162 / IV.4.2-4.3 | Absolute constructibility formula and lemma placing subsets at a controlled rank. | A representation membership predicate needs an explicit absoluteness/preservation theorem. |
| 176 | 163 / IV.4.4-4.5 | Deduction of GCH in `L` and constructible downward Löwenheim-Skolem construction. | Long metatheoretic prerequisites remain outside ProofNet-IR. |
| 177 | 164 / IV.4.6; IV.5.1 | Constructible Mostowski collapse and plan for expanding the long constructibility formulas into absolute blocks. | Building and checking formulas in named blocks is directly relevant to maintainable formalization practice. |
| 178 | 165 / IV.5.1-5.7 | Explicit absolute formulas for the primitive set operations. | Surface abbreviations are safe only after their expanded forms and preservation facts are audited. |
| 179 | 166 / IV.5.8-5.11 | Image/closure formulas, construction of `Phi`, and definition of a closure sequence. | A staged executable closure must expose its induction invariant. |
| 180 | 167 / IV.5.11-5.14 | Closure sequences, `J`, successor constructibility, and transfinite constructing sequences. | Unrestricted quantifiers require an existence/uniqueness argument, not a hidden search assumption. |
| 181 | 168 / IV.5.14-5.17 | Absolute `L(x,y)`, consistency of `V=L`, and formal cardinality deduction. | Explicitly distinguishes semantic explanation from a formal derivation. |
| 182 | 169 / IV.5.18 | Absolute formula enumerating important triples and successor/limit cases. | Exhaustive constructor cases must be demonstrably complete. |
| 183 | 170 / IV.5.18-5.19 | Limit cases and construction of the absolute numbering sequence `S(N,x)`. | Limit handling and coordinate encodings need separate verification. |
| 184 | 171 / IV.5.19-5.20; IV.6.1-6.3 | Completion of `N(x,y)` and syntactic definitions of relativization/internal models. | A semantic proof and a fully internal syntactic proof are not interchangeable artifacts. |
| 185 | 172 / IV.6.4-6.8; IV.7 | Translation of semantic statements to relativized ZF deductions and warning about unwritten enormous formal proofs. | Strongly motivates kernel checking while acknowledging that explanation is still required for auditability. |
| 186 | 173 / IV.7.1 | Competing views of continuum, constructivism, ineffective existence, and alternate semantics. | The project must state whether APIs are constructive algorithms or classical existence theorems. |
| 187 | 174 / IV.7.1-7.2 | Boolean-valued alternatives, Cohen's view, and Goedel's pragmatic criterion for new axioms. | Empirical fruitfulness is evidence of utility, never a substitute for logical soundness. |
| 188 | 175 / IV.7.3 | Woodin's `H(k)` program, expanded logic, axiom star, and conclusion `2^aleph0 = aleph2`. | Historical update only; no project dependency. |
| 189 | Part II divider | Divider introducing computability. | Accounted for; no mathematical claim. |
| 190 | 179 / V.1.1-1.2 | Proof versus computation roadmap, algorithms as processes, and partial functions over positive integer tuples. | Directly relevant to distinguishing existence of a derivation from an executable sequentializer. |
| 191 | 180 / V.1.2-1.4 | Definitions of computable, semicomputable, and noncomputable partial functions. | Supports precise termination/error contracts for the public runtime. |
| 192 | 181 / V.1.4 | Domain characteristic functions, counting evidence for noncomputability, arithmetic-truth example, and a Fermat semidecision procedure. | A semidecision procedure is not a total API; ProofNet-IR's accepted-input totality theorem closes that distinction only in its documented fragment. |
| 193 | 182 / V.1.4-1.6 | Fermat update, a semicomputable noncomputable Diophantine example, critique of informal program notions, and weakest Church thesis. | Corrects the historical Fermat example and distinguishes empirical thesis from formal theorem. |
| 194 | 183 / V.1.7; V.2.1-2.3 | Significance of Church's thesis, basic partial-recursive functions, composition, juxtaposition, and recursion. | Executable closure under constructors needs exact domain equations. |
| 195 | 184 / V.2.3-2.4 | Recursive domains, minimization operator, and partial/primitive recursive descriptions. | The minimization operator is where partiality enters; analogous API search must state its totality domain. |
| 196 | 185 / V.2.5-2.6 | Usual Church thesis, computable versus semicomputable, and mass-problem undecidability. | Logical totality claims must not rest on Church's thesis alone. |
| 197 | 186 / V.2.6-2.7 | Heuristic use of Church's thesis and preservation of semicomputability by minimization. | Informal algorithm arguments are useful discovery aids but require formal closure proofs. |
| 198 | 187 / V.2.7; V.3.1-3.2 | Evidence from recursive descriptions, Turing equivalence and other models, then basic recursive arithmetic examples. | Cross-model agreement is evidence, while the Lean theorem remains fragment-specific proof. |
| 199 | 188 / V.3.2-3.4 | Recursive sums/products and truncated predecessor/difference. | Multiple descriptions of one function caution against identifying programs with mathematical functions. |
| 200 | 189 / V.3.5-3.8 | Polynomial, step, remainder, and conditional-recursion constructions. | Branch conditions must be exhaustive and mutually exclusive. |
| 201 | 190 / V.3.8-3.11 | Quotient, integer square root, min/max via conditional recursion. | Engineering examples only. |
| 202 | 191 / V.3.12-3.14; V.4.1 | Bounded sums/products, argument transformations, componentwise recursion, and recursively enumerable sets. | Encodings and projections require preservation under every argument transformation. |
| 203 | 192 / V.4.1-4.4 | Equivalent level-set definitions and theorem characterizing enumerable sets as projections of primitive-recursive levels. | A representation theorem has two directions; directly supports maintaining both proof-net translations. |
| 204 | 193 / V.4.4-4.5 | Projection-codimension cases and statement of a recursive tuple-numbering bijection. | Tuple encoding needs a computable inverse, not just injectivity. |
| 205 | 194 / V.4.5-4.8 | Construction of Cantor tuple encodings and closure of primitive-enumerable sets. | Canonical encoding is backed by explicit round-trip properties here. |
| 206 | 195 / V.4.8-4.9 | Graph closure under constructors and Goedel function encoding finite sequences. | Arbitrarily long finite witness traces can be encoded, but decoding and coverage must be proved. |
| 207 | 196 / V.4.9-4.10 | Chinese-remainder proof of sequence encoding and minimization stability setup. | Witness packing is a theorem, not an informal serialization trick. |
| 208 | 197 / V.4.10 | Primitive-enumerable graph proof for minimization using encoded intermediate witnesses. | Shows the complexity of proving search-graph closure exactly. |
| 209 | 198 / V.4.10-4.11 | Completion of minimization and recursive-step graph encoding. | Every intermediate recursive state is represented and checked. |
| 210 | 199 / V.4.11-4.12 | Completion of recursion stability and generative meaning of recursively enumerable sets. | Enumerating all positives says nothing about terminating on negatives. |
| 211 | 200 / V.4.13-4.15 | Decidable sets, characteristic-function theorem, and graph characterization of partial recursion. | A decidable checker requires both positive and negative termination; current Boolean checker supplies that in scope. |
| 212 | 201 / V.4.16-4.19; V.5.1 | Normal-form corollaries, finite decidability, and recursive-geometry structure. | Normal forms and finite cases are useful tests but not full performance guarantees. |
| 213 | 202 / V.5.2-5.6 | Quasitopology, restriction/gluing, recursive morphisms, and invariance questions. | Storage-independent equivalence must specify the ambient structure preserved. |
| 214 | 203 / V.5.6 | Recursive bijections between infinite enumerable sets and limitations of intrinsic classification. | A bijection of carriers alone can erase essential embedding information; relevant to graph identity boundaries. |
| 215 | 204 / V.5.7-5.8 | Enumerable families, versality, and diagonal construction of an enumerable undecidable set. | Broad family coverage can enable diagonal failure cases; motivates adversarial generation. |
| 216 | 205 / V.5.9-5.11 | Enumerable unions, infinite gluing, recursive products, and boundary maps. | Family-level closure requires a total-space theorem. |
| 217 | 206 / V.5.11-5.13 | Recursive Cech analogy, simple enumerable sets, and maximal elements modulo finite sets. | Geometric analogy is explicitly exploratory, not a proof-net result. |
| 218 | 207 / VI.1.1-1.2 | Diophantine sets and statement/roadmap of the Davis-Putnam-Robinson-Matiyasevich theorem. | Major computability theorem outside current project scope. |
| 219 | 208 / VI.1.3-1.4 | Hilbert's tenth problem, effective reduction, constructive nature of the representation, and prime-value polynomials. | “Effective” is supported by an explicit transformation, a useful API standard. |
| 220 | 209 / VI.1.5-1.9; VI.2.1 | Positive-value representation and examples, then proof plan via bounded quantification. | Examples are consequences of the theorem, not independent correctness evidence. |
| 221 | 210 / VI.2.1-2.2 | Enumerable, D-, and Diophantine classes and closure under bounded universal quantification. | Intermediate classes make proof dependencies explicit. |
| 222 | 211 / VI.2.2-2.4; VI.3 | Goedel encoding closes bounded quantification, proof plan, and reduction to primitive-recursive graphs. | Finite witness vectors can be packed only after a proved decoding property. |
| 223 | 212 / VI.3.1-3.3 | Graphs of basic recursive functions as D-sets and Diophantine graph of the Goedel remainder function. | Constructor-preservation proof pattern only. |
| 224 | 213 / VI.3.4 | Recursion graph is a D-set via initial, step, and bounded universal constraints. | Exhaustive initial/recursive decomposition mirrors a total recursive proof. |
| 225 | 214 / VI.4.1-4.3 | Reduction of bounded universal quantification to exponential, factorial, and binomial Diophantine graphs. | Long dependency chain is recorded rather than collapsed into the headline theorem. |
| 226 | 215 / VI.4.3 | Forward inclusion using large coprime moduli and encoded witnesses. | Completeness direction depends on explicit lifting of every bounded witness. |
| 227 | 216 / VI.4.3 | Reverse inclusion via prime divisors and size bounds, then reduction conclusion. | Soundness direction uses independent bounds; both directions are necessary. |
| 228 | 217 / VI.5.1-5.2 | Pell equations and exponentially growing solution coordinates for a special Diophantine set. | Number-theory construction only. |
| 229 | 218 / VI.5.3-5.5 | Diophantine encoding of a Pell-solution index and forward construction. | Auxiliary witnesses are fully enumerated before projection. |
| 230 | 219 / VI.5.5-5.7 | Reverse implication using congruence and solution-index lemmas. | Equality recovery depends on bounds plus congruence, not congruence alone. |
| 231 | 220 / VI.5.8 | Proofs of the Pell sequence congruence and divisibility lemmas. | No project dependency. |
| 232 | 221 / VI.6; VI.7.1 | Diophantine graph of exponentiation and start of binomial/factorial graphs. | No project dependency. |
| 233 | 222 / VI.7.2-7.5 | Binomial remainder lemma and Diophantine factorial construction. | No project dependency. |
| 234 | 223 / VI.7.6-7.8; VI.8.1 | Generalized binomial graph completes DPRM, then versal-family existence theorem. | Completion is tied to the earlier reductions; headline theorem alone hides many hypotheses. |
| 235 | 224 / VI.8.1 | Effective enumeration of polynomials and construction of a versal family of enumerable sets. | Effective universality requires a uniform total-space proof. |
| 236 | 225 / VI.8.1-8.2 | Versal families of higher-arity sets/functions and nonuniqueness of indexing. | A universal enumeration is not a canonical identity; crucial distinction for generated certificates. |
| 237 | 226 / VI.9.1-9.3 | Relative Kolmogorov complexity, optimal enumerable families, and invariance up to multiplicative constants. | Complexity depends on representation except up to a stated equivalence and constant. |
| 238 | 227 / VI.9.4-9.5 | Construction of an optimal family and integer-complexity examples. | Performance comparisons require a fixed cost model and admitted invariance notion. |
| 239 | 228 / VI.9.5-9.8 | Complexity examples and composition bounds. | Supports reporting asymptotic search cost rather than one benchmark number. |
| 240 | 229 / VI.9.8-9.9 | Proof of composition bounds and statement that Kolmogorov complexity is not computable. | Exact intrinsic proof complexity cannot generally be a computable library metric. |
| 241 | 230 / VI.9.9-9.10 | Proof of noncomputability of complexity and consequences for first appearances in optimal families. | No algorithm can generally certify minimal representation length; avoid “smallest proof” claims. |
| 242 | 231 / VI.9.10 | Distinction between program length, execution time, parallelism, and practical complexity. | Existing runtime budget is a regression guard, not evidence of scalable asymptotics. |
| 243 | Part III divider | Divider introducing provability and computability. | Accounted for; no mathematical claim. |
| 244 | 235 / VII.1.1-1.2 | Arithmetic encoding of syntax and definitions of numberings/equivalent numberings. | A canonical representation is canonical only relative to a specified effective equivalence class. |
| 245 | 236 / VII.1.2-1.6 | Equivalence properties, recursion relative to numberings, invariance, and compatible tuple numberings. | Representation independence requires computable translations both ways. |
| 246 | 237 / VII.1.7-1.9 | Compatible product encodings and admissible numberings of expressions with length, coordinate, and concatenation operations. | A serialization contract should expose decidable membership and computable structural operations. |
| 247 | 238 / VII.1.9 | Proof that compatible expression numberings are equivalent and prime-factor encoding begins. | Uniqueness is up to effective equivalence, not literal code equality. |
| 248 | 239 / VII.1.9-1.10 | Decidability/admissibility of the prime encoding and invariant syntactic operations. | Directly rules out calling the current key a solution to arbitrary graph isomorphism. |
| 249 | 240 / VII.1.10; VII.2.1-2.3 | Canonical numbering via finite protoalphabets and setup of truth versus enumerable provability. | Canonical encodings still depend on a declared syntactic universe. |
| 250 | 241 / VII.2.3-2.5; VII.3.1-3.2 | Enumerability of proofs, nonenumerability of rich truth, general incompleteness, and Tarski reductions. | A decidable proof checker can never be conflated with a general truth decider. |
| 251 | 242 / VII.3.2-3.3 | Concrete nonenumerable family of true arithmetic formulas from an undecidable enumerable set. | Uniform generated cases may expose limits no finite test suite can close. |
| 252 | 243 / VII.3.4-3.5; VII.4.1 | Transfer to richer languages, Diophantine consequences, and syntactic-analysis setup. | Translation preserves the limit only when it preserves truth and is recursive. |
| 253 | 244 / VII.4.1-4.2 | Goedel numbering assumptions and a computable matching-parenthesis function. | Parser operations need decidable domains and explicit failure behavior. |
| 254 | 245 / VII.4.3 | Recursive syntactic analysis deciding concatenations of terms. | Structural recognition is proved by a terminating recursion, not samples. |
| 255 | 246 / VII.4.3 | Conversion of recursion over arbitrary smaller encodings to ordinary primitive recursion. | Well-founded recursive calls need a stored-history invariant. |
| 256 | 247 / VII.4.3-4.5 | Decidability of terms, atomic formulas, and all formulas. | A parser library should similarly prove grammar recognition exactness. |
| 257 | 248 / VII.4.5-4.7 | Formula recognizer, single-position substitution, and free-variable decision. | Substitution and occurrence identity must remain separate from label equality. |
| 258 | 249 / VII.4.7-4.9; VII.5.1 | Capture avoidance, simultaneous free substitution, and general axioms/rules setup. | Reinforces occurrence-sensitive transformations and explicit capture conditions. |
| 259 | 250 / VII.5.1-5.4 | Enumerability of deducible expressions and realization of generalization/modus ponens. | A proof-producing runtime should enumerate only outputs justified by checked rules. |
| 260 | 251 / VII.5.4-5.7 | Enumerability of tautology, quantifier, and equality axiom schemes. | A schema is handled by a uniform generator plus side-condition decision procedure. |
| 261 | 252 / VII.5.7-5.8; VII.6.1-6.2 | Special axiom schemes and definition of the arithmetical hierarchy. | Background only. |
| 262 | 253 / VII.6.2 | Hierarchy characterization by quantifier alternation and closure proof. | Bound-variable renaming is required to combine projected witnesses correctly. |
| 263 | 254 / VII.6.2-6.4 | Strictness of the arithmetical hierarchy by diagonalization. | No finite checker can be promoted beyond its stated decision problem. |
| 264 | 255 / VII.6.4; VII.7.1-7.3 | Quantifier-complexity remarks and setup for productive truth/self-reference. | Complexity classifications are representation-sensitive background. |
| 265 | 256 / VII.7.3-7.4 | Effective diagonal/self-reference lemma and comparison of Tarski and Goedel arguments. | Reflection claims require an explicitly delimited metalanguage and numbering. |
| 266 | 257 / VII.7.4-7.7 | Productive truth and effective construction of a new true unprovable formula from any enumerable subsystem. | Prevents interpreting library completeness outside the precise proof-net theorem. |
| 267 | 258 / VII.7.7-7.10 | Feferman transfinite axiom progressions and omitted exhaustion theorem. | The cited theorem is not locally proved; no project dependency. |
| 268 | 259 / VII.8.1-8.3 | Proof-length speedup principles and abstract deduction-complexity data. | Proof size is a separate metric from formula size and runtime. |
| 269 | 260 / VII.8.3-8.4 | Decidability and recursive-bounds axioms for deduction complexity, then speedup theorem. | Any performance theorem needs an explicit cost model and computable measurement. |
| 270 | 261 / VII.8.4 | Proof of unbounded proof-length reduction after adding an independent axiom. | Benchmark speedups do not establish intrinsic superiority of one proof representation. |
| 271 | 263 / VIII.1.1-1.2 | Free-group words, computable reduction, and enumerable subgroup preliminaries. | Algebraic word machinery outside MLL. |
| 272 | 264 / VIII.1.2-1.6 | Recursive groups, Higman embedding theorem, and universal finitely presented groups. | No current project dependency. |
| 273 | 265 / VIII.1.6-1.8 | Universal groups and finitely presented groups with undecidable word problem. | A finite presentation need not give a decidable equality checker; analogous warning for compact certificates. |
| 274 | 266 / VIII.1.8-1.9; VIII.2.1-2.2 | Natural recursive groups, relation to DPRM, and free products with amalgamation. | No current project dependency. |
| 275 | 267 / VIII.2.3-2.4 | Canonical expansions and subgroup intersections in amalgamated products; presentation notation. | Canonical normal forms require a uniqueness theorem. |
| 276 | 268 / VIII.2.4-2.6 | HNN extensions and embedding theorem proof begins. | No current project dependency. |
| 277 | 269 / VIII.2.6-2.7 | Completion and generalization to iterated HNN extensions/subgroups. | No current project dependency. |
| 278 | 270 / VIII.2.7; VIII.3.1 | Embedding/intersection proof and start of two-generator embedding. | Tracks repeated embeddings explicitly, a useful formalization discipline. |
| 279 | 271 / VIII.3.1; VIII.4.1 | Completion of effective two-generator embedding and equivalent definitions of benign subgroups. | Equivalent characterizations need explicit maps and intersection equalities. |
| 280 | 272 / VIII.4.1-4.2 | Benign subgroup equivalence and quotient embedding lemma. | No current project dependency. |
| 281 | 273 / VIII.4.2-4.4 | Completion of quotient lemma, reduction of Higman's theorem, and closure properties. | Long algebraic reduction chain outside MLL. |
| 282 | 274 / VIII.4.4-4.5 | Benign subgroups closed under intersections/generated joins and homomorphic images. | Closure claims are proved operation by operation. |
| 283 | 275 / VIII.5.1-5.3 | Bounded word systems and first reduction for benign enumerable subgroups. | No current project dependency. |
| 284 | 276 / VIII.5.4 | DPRM reduction of an enumerable exponent set to elementary polynomial equations. | No current project dependency. |
| 285 | 277 / VIII.5.4-5.5 | Decomposition of polynomial equations and second subgroup reduction. | No current project dependency. |
| 286 | 278 / VIII.5.5-5.6 | Completion of the reduction and construction of multiple HNN extensions. | No current project dependency. |
| 287 | 279 / VIII.5.6-5.8 | Finitely presented extension, finitely generated witness subgroups, and conjugation equations. | No current project dependency. |
| 288 | 280 / VIII.5.8; VIII.6.1 | Completion of intersection proof and final Higman reduction begins. | No current project dependency. |

## Current claim boundary

The completed interval supports the motivation for treating diagrams and
decorated graphs as formal languages whose syntax and semantics must be stated
precisely. It does not state the Danos-Regnier switching criterion, MLL proof-net
correctness, or a sequentialization theorem. The remaining 101 pages are not
yet represented as directly read in order.
