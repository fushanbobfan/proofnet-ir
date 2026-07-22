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
- Current direct ordered reading: physical pages 1-48. This is an in-progress
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

## Current claim boundary

The completed interval supports the motivation for treating diagrams and
decorated graphs as formal languages whose syntax and semantics must be stated
precisely. It does not state the Danos-Regnier switching criterion, MLL proof-net
correctness, or a sequentialization theorem. The remaining 341 pages are not
yet represented as directly read in order.
