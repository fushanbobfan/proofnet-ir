# Completed page audit: Pfenning, *Linear Logic*

Audit started: 2026-07-22

## Source identity and page accounting

- Local source: `linearlogic.pdf`
- SHA-256: `5d5a29d68c13c530243075b60f9ff9e64ea6ac1885a752323c6f4b0beb96fa96`
- Visible edition: Frank Pfenning, draft of January 26, 2002.
- Extent: 336 physical PDF pages.
- Exact duplicate audit: SHA-256 hashes of both decoded PDF content streams
  and independently extracted page text give 168 duplicate pairs and 168
  unique pages. Physical pages 11-20 repeat 1-10; physical pages 179-336
  repeat 21-178. Every duplicate group has exactly two members.
- Reading unit: physical pages 1-10 and 21-178, for 168 unique pages.
- Current direct ordered text reading: 168/168 unique pages (physical 1-10 and
  21-178). This count is based on direct page-order reading, not the prior
  theorem/section sweep.
- Visual status: all 168 unique pages were rendered from the original PDF and
  inspected in page order. The pass covered every displayed-rule page, the
  automata and Petri-net diagrams, the solitaire-board figures, and the
  bibliography; physical pages 40, 66, and 114 were also checked at full-page
  resolution as representative symbol-, graph-, and figure-heavy pages.

## Page-by-page matrix for the completed text interval

| Physical page | Printed page / section | Content read | ProofNet-IR consequence |
|---:|---|---|---|
| 1 | cover | Author, draft date, course provenance, rough-draft and citation warning. | Useful background source, but not an archival authority for proof-net sequentialization. |
| 2 | ii | Intentionally sparse verso carrying only draft footer. | Accounted for; no mathematical claim. |
| 3 | contents | Chapters 1-5: natural deduction, sequent calculus, proof search/focusing, and logic programming. | Establishes where the directly relevant operational material occurs. |
| 4 | contents | Chapters 6-7 and bibliography: proof terms, type checking, linear type theory, logical frameworks. | Motivates a separately checked proof object rather than trusting a graph producer. |
| 5 | 1 / Introduction | Practical versus merely eliminable logical structure; proofs as constructions; judgment/proof before truth in the constructive presentation. | Supports the design principle that executable evidence and kernel proof objects matter; it is not a proof-net theorem. |
| 6 | 2 / Introduction | Constructive intuitionistic scope, historical caveat, references to Girard/surveys, and the blocks-world state example. | Warns that these notes are intuitionistic and broader than the project's classical one-sided MLL fragment. |
| 7 | 3 / Introduction | Blocks-world predicates; failure of persistent ordinary assumptions to model state; cumbersome temporal workaround. | Motivates explicit resource occurrences, not any switching criterion. |
| 8 | 4 / Introduction | Linear hypothetical judgment, exchange, exact-once use, hypothesis/substitution principles, and tensor introduction as a resource split. | Directly supports occurrence identity, exchange, and exact resource ownership in the certificate structure. |
| 9 | 5 / Introduction | Tensor elimination; additive conjunction/internal choice; resource duplication is only apparent because one alternative is chosen. | Confirms that additives use different proof-net behavior and must remain outside the current MLL claim. |
| 10 | 6 / Introduction | Linear implication rules; blocks-world action axioms; incomplete-goal problem; top introduction. | Implication/quantifiers/top are outside the implemented formula grammar. |
| 11 | duplicate of 1 | Exact content-stream and text duplicate. | No new reading unit. |
| 12 | duplicate of 2 | Exact content-stream and text duplicate. | No new reading unit. |
| 13 | duplicate of 3 | Exact content-stream and text duplicate. | No new reading unit. |
| 14 | duplicate of 4 | Exact content-stream and text duplicate. | No new reading unit. |
| 15 | duplicate of 5 | Exact content-stream and text duplicate. | No new reading unit. |
| 16 | duplicate of 6 | Exact content-stream and text duplicate. | No new reading unit. |
| 17 | duplicate of 7 | Exact content-stream and text duplicate. | No new reading unit. |
| 18 | duplicate of 8 | Exact content-stream and text duplicate. | No new reading unit. |
| 19 | duplicate of 9 | Exact content-stream and text duplicate. | No new reading unit. |
| 20 | duplicate of 10 | Exact content-stream and text duplicate. | No new reading unit. |
| 21 | 7 / Introduction | Top as additive unit, unit `1` and its elimination, sample valid judgment, and setup of an invalid arbitrary judgment. | Units are explicitly outside the current unit-free representation. |
| 22 | 8 / Introduction | Resource-count contradiction showing the arbitrary tensor-to-with judgment cannot hold. | Reinforces that unused linear resources must be rejected. |
| 23 | 9 / 2.1 | Natural-deduction chapter scope; judgments, propositions, verifications, and Martin-Loef-style meaning explanations. | General proof-theoretic method only; the implemented object logic is later checked independently. |
| 24 | 10 / 2.1 | Conjunction introduction/eliminations and local soundness by reduction. | Distinguishes proof-rule soundness from mere syntax checking. |
| 25 | 11 / 2.1-2.2 | Local completeness by expansion; start of linear hypothetical judgments. | The soundness/completeness distinction informs the separate Boolean iff and sequentialization theorems. |
| 26 | 12-13 / 2.2-2.3 | Labeled occurrences, linear substitution and hypothesis; tensor natural-deduction rules and nondeterministic resource splitting. | Explicitly validates treating equal formula labels at distinct occurrences as different resources. |
| 27 | 14 / 2.3 | Tensor local reduction/expansion; additive conjunction rules. | Tensor is in scope; additive conjunction is not silently identified with par. |
| 28 | 15 / 2.3 | Additive conjunction reductions; linear implication reduction and expansion. | Confirms broader source scope; neither connective is part of current MLL syntax except tensor. |
| 29 | 16 / 2.3 | Unit, top, and additive disjunction introductions. | Again confirms that units/additives require separate representations. |
| 30 | 17 / 2.3 | Additive disjunction reductions, zero, and universal quantification. | Outside current claim; no transfer to multiplicative proof-net correctness. |
| 31 | 18 / 2.3 | Universal and existential quantifier reduction/expansion; end of purely linear operators. | Quantifiers remain an explicit future fragment. |
| 32 | 19 / 2.3-2.4 | Multiplicative/additive resource classification; validity and unrestricted hypotheses. | Supports the project's fragment boundary and later persistent-context staging. |
| 33 | 20 / 2.4 | Dual unrestricted/linear contexts and distinct substitution principles. | Persistent hypotheses cannot be folded into the current linear ownership discipline without a new semantics. |
| 34 | 21 / 2.4 | Restated truth substitution/hypothesis rules and blocks-world encoding with unrestricted action rules. | Confirms the need for an explicit persistent layer in any later extension. |
| 35 | 22 / 2.4 | Worked resource evolution in the blocks-world derivation. | Illustrates proof/resource traces but supplies no proof-net identity theorem. |
| 36 | 22 / 2.4 | Completion of the worked plan and transition to connectives for unrestricted assumptions. | Outside the MLL core. |
| 37 | 23 / 2.4 | Unrestricted implication and of-course modality, including local reductions/expansions. | Exponentials are explicitly unsupported and cannot be claimed from v0.4. |
| 38 | 24 / 2.4 | Completion of bang, full connective grammar, and start of the rule summary. | Useful scope cross-check; current `Formula` implements only atoms, tensor, and par. |
| 39 | 25 / rule summary | Continuation of additive/quantifier/exponential rule summary. | No new current-fragment theorem. |
| 40 | 26 / example | Menu encoding showing distinct uses of internal and external choice and unlimited coffee via bang. | Demonstrates why informal "or" cannot justify conflating additives or exponentials with par. |
| 41 | 27 / 2.5 | Sequential finite-automaton encoding and its stated adequacy theorem. | An adequacy statement must relate syntax to an external model; checker acceptance alone is not enough. |
| 42 | 28 / 2.5 | Inductive encodings of character, concatenation, unit, and union regular expressions. | Example of representation design outside the current MLL certificate semantics. |
| 43 | 29 / 2.5 | Equivalent union encodings, empty language, Kleene star, and synchronized intersection using tensor. | Shows that operational encodings may be extensionally equivalent while structurally different. |
| 44 | 30 / 2.5 | Full-language encoding, algebraic caveat, internal nondeterministic choice, and concurrent adequacy proposal. | Supports reporting operational assumptions and not confusing a correctness statement with a concurrency characterization. |
| 45 | 31 / 2.5 | Concurrent cases, fairness/scheduling caveat, and transition to backward chaining. | Search strategy and fairness are empirical/operational issues, not consequences of proof-net correctness. |
| 46 | 32 / 2.5 | Backward-chaining automaton adequacy and initial regular-expression cases. | Reinforces that proof orientation changes the search procedure without changing the represented language. |
| 47 | 33 / 2.5 | Backward encodings for union/zero/star; intersection difficulty; statement of forward adequacy proof. | Explicitly records a hard case instead of treating representation symmetry as automatic. |
| 48 | 34 / 2.5 | Forward adequacy proof for character, concatenation, and unit cases. | Demonstrates induction plus resource substitution; no direct proof-net result. |
| 49 | 35 / 2.5 | Forward adequacy proof for union, zero, and star. | Broad proof-search example only. |
| 50 | 36 / 2.5-2.6 | Intersection/full-language cases; difficulty of the converse due to resource splitting and guessed intermediate formulas; motivation for normal deductions. | Directly motivates focused/cut-free baselines and warns against comparing proof nets only to naive unrestricted search. |
| 51 | 37 / 2.6 | Nonlocal detours, rule permutation, global soundness, and the subformula property. | Supports cut-free/subformula-bounded experimental scope. |
| 52 | 38 / 2.6 | Global completeness/long normal forms and mutually recursive normal/atomic judgments. | A normal-form theorem is distinct from proof-net sequentialization. |
| 53 | 39 / 2.6 | Normal-form inference rules for multiplicatives, additives, and quantifiers. | Confirms different polarities and resource behavior across fragments. |
| 54 | 40 / 2.6 | Exponential/coercion rules, soundness of normal derivations, and atomic substitution principles. | The source itself postpones completeness to a later normalization theorem; local rule plausibility is insufficient. |
| 55 | 41 / 2.7 | Exercises on validity restrictions, derived bang/implication, missing connectives, blocks world, and distributivity. | Scope/accounting only; no theorem imported. |
| 56 | 42 / 2.7 | Interaction-law and equivalence exercises. | Highlights that connective equations require proofs in both directions. |
| 57 | 43 / 2.7 | Continuation of equivalence exercise and a nondeterministic-automaton modeling exercise. | No current core dependency. |
| 58 | 44 / chapter verso | Intentionally blank transition page. | Accounted for; no mathematical claim. |
| 59 | 45 / Chapter 3 and 3.1 | Sequent calculus as bottom-up search for normal deductions; cut and cut elimination preview; split into resource and goal judgments. | Closest source support so far for the independent one-sided kernel calculus and focused baseline, but not for proof nets. |
| 60 | 46 / 3.1 | Resource factories, exact-once initial rule, cut as later admissible rule, copy, and occurrence labels. | Strongly supports occurrence-sensitive contexts and the separation between cut-free rules and later cut admissibility. |
| 61 | 47 / 3.1 | Full sequent-rule summary for multiplicative and additive connectives. | Confirms resource splitting for tensor and single-context decomposition for the additive rules; current one-sided classical MLL remains a translated subfragment. |
| 62 | 48 / 3.1 | Quantifier/exponential rules and statement of sequent-derivation soundness into normal natural deductions. | Demonstrates that soundness requires a translation theorem, not visual similarity of inference rules. |
| 63 | 49 / 3.1 | Representative soundness cases and strengthened completeness statement. | The strengthened induction hypothesis is a useful warning about hidden generality needed in reverse translations. |
| 64 | 50 / 3.1 | Representative completeness cases for coercion, additive elimination, and linear/unrestricted hypotheses. | No proof-net theorem, but supports keeping reverse construction separate from checker soundness. |
| 65 | 51 / 3.2 | Petri-net definition and multiset/token encoding with repeated atomic resources. | Repeated formula labels must remain distinct occurrences, exactly as the certificate array does. |
| 66 | 52 / Figure 3.1 | Petri-net structure diagrams: sequence, conflict, concurrency, synchronization, and merging. | Visual inspection remains pending; text establishes only the figure's role. |
| 67 | 53 / 3.2 | Weighted-arc example and reachability adequacy statement. | Adjacent application; it does not validate proof-net switching semantics. |
| 68 | 54 / 3.3 | Linear/unrestricted cut rules as lemmas; natural-deduction coercion and translations. | Supports treating cuts as a separate extension rather than silently admitting them in unit-free cut-free MLL. |
| 69 | 55 / 3.3 | Substitution plus soundness/completeness theorems for derivations with cut. | Reinforces that cut-bearing and cut-free systems require an explicit correspondence theorem. |
| 70 | 56 / 3.4 | Cut-elimination motivation, subformula consequence, consistency intuition, and admissible-versus-derived distinction. | Directly supports finite cut-free search; it does not by itself prove proof-net correctness. |
| 71 | 57 / 3.4 | Admissibility-of-cut theorem, nested induction measure, and five case classes. | Shows the need to expose termination measures and principal/commutative cases in formal recursive proofs. |
| 72 | 58 / 3.4 | Initial, tensor-principal, copy, and left/right commutative cut cases. | Core proof-theory background only. |
| 73 | 59 / 3.4-3.5 | Cut-elimination theorem, normalization consequence, and start of consistency. | Supports the subformula-bounded baseline and strict cut-free scope. |
| 74 | 60 / 3.5 | Consistency, disjunction property, and a non-derivability argument by last-rule analysis. | Last-rule analysis is analogous in style to inverse-rule reasoning, but not a proof of net sequentialization. |
| 75 | 61 / 3.6 | Pi-calculus syntax, structural congruence, and an explicit warning that the example was not proved correct. | Strong methodological reminder to label unproved encodings; no current project dependency. |
| 76 | 62 / 3.6 | Process-state encoding in linear/unrestricted contexts; fork, exit, and restriction setup. | Adjacent concurrency application only. |
| 77 | 63 / 3.6 | Restriction, replication, process sums, and why internal choice alone gives the wrong semantics. | Demonstrates that a plausible connective mapping can be semantically wrong without adequacy proof. |
| 78 | 64 / 3.6 | Reaction/silent rules and transition to asynchronous pi-calculus. | No core dependency. |
| 79 | 65 / 3.6 | Asynchronous rules, an alternative implication-based encoding, and polyadic caveat. | No core dependency. |
| 80 | 66 / 3.7 | Exercises on distributivity, admissibility, cut cases, Petri inhibitors, and new connective rules. | Accounted for; no theorem imported. |
| 81 | 67 / 3.7 | Exercises on direct asynchronous-pi embedding and adequacy. | Accounted for; reinforces that an encoding needs an adequacy theorem. |
| 82 | 68 / chapter verso | Intentionally blank transition page. | Accounted for; no mathematical claim. |
| 83 | 69 / Chapter 4 and 4.1 | Proof-search applications, no-silver-bullet warning, and bottom-up search setup. | Requires experiments to report search choices and failure modes rather than assuming graphical syntax is easier. |
| 84 | 70 / 4.1 | Strong/weak invertibility and Theorem 4.1's rule classification. | Establishes the principled baseline for eager invertible steps. |
| 85 | 71 / 4.1 | Completeness of atomic initial sequents and a generic search procedure. | Supports reducing identity bureaucracy while preserving completeness. |
| 86 | 72 / 4.1-4.2 | Conjunctive, disjunctive, resource, universal, and existential choices; two-phase focusing. | Gives the experiment taxonomy: proof nets chiefly target resource/rule-order choices, not all nondeterminism. |
| 87 | 73 / 4.2 | Andreoli provenance, nontrivial correctness warning, polarity classes, and ordered inversion context. | Prevents using a deliberately weak unfocused baseline as the main comparison. |
| 88 | 74 / 4.2 | Right-asynchronous rules, transition to left inversion, and ordered left decomposition. | Details the bureaucracy that focusing removes before proof-net comparison. |
| 89 | 75 / 4.2 | Decision judgments and focused non-invertible right rules. | Baseline must count focus decisions and resource splits separately. |
| 90 | 76 / 4.2 | Focused left rules, atomic closure/phase switching, and focusing soundness statement. | The notes state soundness but explicitly say completeness of this intuitionistic presentation had not yet been proved there. |
| 91 | 77 / 4.2-4.3 | Completion of focusing soundness; summary of eliminated choices; start of unification. | Any claim that this source proves completeness of the exact implemented baseline would be too strong. |
| 92 | 78 / 4.3 | Logic variables, unification history/complexity, and residuation interface. | Quantifier search is outside current MLL experiments but illustrates separating a general search engine from specialized solvers. |
| 93 | 79 / 4.3 | Residual unification logic and its inference rules. | No core dependency. |
| 94 | 80 / 4.3 | Residuated sequent rules and soundness theorem. | Shows how executable constraints need a formal soundness bridge. |
| 95 | 81 / 4.3 | Soundness cases and the generalized substitution needed for completeness. | Another example where reverse completeness needs a stronger invariant than the forward theorem. |
| 96 | 82 / 4.3 | Completeness lemma cases and equality-residuation completeness. | No current-fragment dependency. |
| 97 | 83 / 4.3 | Algorithmic unification judgments, continuations, and existential-variable introduction. | Provides algorithm-specification methodology only. |
| 98 | 84 / 4.3 | Constant and variable unification rules, occurs check, determinism, and lexicographic termination measure. | Relevant engineering lesson: executable completeness needs an explicit terminating algorithm, not only existential witnesses. |
| 99 | 85 / 4.3 | Termination proof, continuation grammar, substitutions, and unification soundness lemma. | Reinforces the newly documented gap between v0.4's `Nonempty` theorem and an executable sequentializer. |
| 100 | 86 / 4.3 | Unification soundness and generalized completeness lemma. | No direct proof-net theorem. |
| 101 | 87 / 4.3 | Completion of unification completeness and the universal/existential dependency counterexample. | Shows why apparently constructive search can still need carefully scoped dependencies. |
| 102 | 88 / 4.3 | Parameter contexts and annotated existential variables. | No core dependency. |
| 103 | 89 / 4.3 | Variable restriction, scoped continuations, and termination extension. | Supports demanding a precise executable invariant for future sequentialization. |
| 104 | 90 / 4.3 | Admissible substitutions and timestamp optimization for parameter dependencies. | Engineering background only. |
| 105 | 91 / Chapter 5 | Proofs-as-programs versus proof-search-as-computation; limits of executable specifications. | Direct warning that a sound proof formalism is not automatically a useful program. |
| 106 | 92 / 5.1 | Goal-directed LHHF fragment and relation to focusing/uniform proofs. | Defines the stronger baseline family relevant to experiments. |
| 107 | 93 / 5.1 | Uniform-proof goal and procedure-call rules. | Operational baseline detail, not proof-net semantics. |
| 108 | 94 / 5.1-5.2 | Claimed uniform-proof correspondence and start of operational choice policy. | Notes contain placeholders for formal citation/detail, so use cautiously. |
| 109 | 95 / 5.2 | Disjunctive/resource nondeterminism, depth-first incompleteness, and success/fail/run trichotomy. | Experiments must separate finite failure from timeout/nontermination. |
| 110 | 96 / 5.2-5.3 | Explicit statement that logic programming is not a general theorem prover; start of input/output resource management. | Strong boundary against claiming end-to-end utility from logical soundness alone. |
| 111 | 97 / 5.3 | I/O resource judgments, consumption flags, and phased rules. | Demonstrates an executable alternative to guessing resource partitions. |
| 112 | 98 / 5.3 | Focus rules, query boundary, subtraction relation, and soundness theorem. | Supports including deterministic resource-management baselines where applicable. |
| 113 | 99 / 5.3-5.4 | Completeness theorem plus nontermination/enumeration examples. | Reinforces measuring search order and divergence. |
| 114 | 100 / 5.4 | List-permutation program and solitaire setup. | Application example only. |
| 115 | 101 / 5.4 | Solitaire board representation and six move rules. | No proof-net dependency. |
| 116 | 102 / 5.4 | Adequate but non-LHHF encoding; uncurrying and continuation-passing translation. | Shows provability-preserving translations may change operational behavior. |
| 117 | 103 / 5.4-5.5 | Compiled solitaire clauses and introduction to logical compilation. | No core dependency. |
| 118 | 104 / 5.5 | Resolution and residual-subgoal judgments. | Methodology for separating source syntax from executable search instructions. |
| 119 | 105 / 5.5 | Residuation of implication, choice, truth, and unrestricted implication. | Adjacent algorithm design only. |
| 120 | 106 / 5.5 | Quantifier residuation, resolution correctness statement, and even-number example. | Correctness is left as an exercise; not authoritative for project theorems. |
| 121 | 107 / 5.5-5.6 | WAM-style optimization observation and exercises on correctness/new connectives. | No core dependency. |
| 122 | 108 / 5.6 | Exercises on compilation, Hanoi, and regex execution. | Accounted for; no theorem imported. |
| 123 | 109 / Chapter 6 | Analytic judgments, proof terms, Curry-Howard, and linear lambda-calculus motivation. | Motivates separately checkable proof terms and the trusted-kernel boundary. |
| 124 | 110 / 6.1 | Independent proof checking, proof-term design criteria, and hypotheses. | Directly supports making graph producers untrusted and checking reconstructed objects. |
| 125 | 111 / 6.1 | Proof terms for linear implication, tensor, and unit with beta/eta laws. | Broader intuitionistic system, not the project's one-sided MLL syntax. |
| 126 | 112 / 6.1 | Additive product, sum, and falsehood proof terms. | Confirms additives need distinct constructors/semantics. |
| 127 | 113 / 6.1 | Exponential terms and proof-term grammar. | Explicitly outside current scope. |
| 128 | 114 / 6.1 | Beta/eta summaries and proof-term erasure/uniqueness theorem. | Shows proof identity depends on the chosen term representation. |
| 129 | 115 / 6.1 | Derivation ambiguity from top/weakening, substitution, and subject reduction. | Current unit-free fragment avoids this specific ambiguity; broader identity claims require new quotients. |
| 130 | 116 / 6.2 | Algorithmic type checking, sequential resource consumption, and slack introduced by top. | Supports current unit-free scope and need for diagnostic executable APIs. |
| 131 | 117 / 6.2 | Input/output modes and multiplicative checking rules. | Demonstrates that executable checkers should document inputs, outputs, and invariants. |
| 132 | 118 / 6.2 | Additive coordination and slack rules. | Outside current fragment. |
| 133 | 119 / 6.2 | Exponential rules and generalized algorithmic-checking lemma. | No core dependency. |
| 134 | 120 / 6.2-6.3 | Algorithmic type-checking iff and operational-semantics setup. | Existence plus iff validation is the standard future bar for an executable sequentializer. |
| 135 | 121 / 6.3 | Call-by-value rules for linear functions, tensor, and unit. | Runtime semantics only. |
| 136 | 122 / 6.3 | Lazy additive products/top and eager sums. | Outside current proof-net fragment. |
| 137 | 123 / 6.3 | Void, unrestricted function, modal evaluation, and value grammar. | No core dependency. |
| 138 | 124 / 6.3 | Boolean encoding, patterns, and conditional typing alternatives. | No core dependency. |
| 139 | 125 / 6.3 | Well-typed conditional, subject reduction, and evaluation relation. | General independent-checking methodology only. |
| 140 | 126 / 6.3-6.4 | Determinacy and introduction of recursive types. | No core dependency. |
| 141 | 127 / 6.4 | Recursive type fold/unfold and fixpoint rules. | Explicitly leaves logical normalization; irrelevant to current cut-free MLL theorem. |
| 142 | 128 / 6.4 | Natural-number encodings, addition, and multiplication. | No core dependency. |
| 143 | 129 / 6.4 | Copy/delete/promote and lazy naturals. | Illustrates structural operations absent from linear MLL. |
| 144 | 130 / 6.4 | Eager/lazy list definitions. | No core dependency. |
| 145 | 131 / 6.4-6.5 | Lazy-list variants and a typed non-normalizing recursive example. | Reinforces that fragment extensions can destroy termination. |
| 146 | 132 / 6.5 | Logical-relations termination proof motivation. | Methodological evidence for explicit termination proofs. |
| 147 | 133 / 6.5 | Typed reducibility predicates and substitution generalization. | No direct proof-net theorem. |
| 148 | 134 / 6.5 | Logical-relations lemma and relations for all types. | No core dependency. |
| 149 | 135 / 6.5 | Representative logical-relations cases and termination theorem. | General formal-methods background only. |
| 150 | 136 / 6.6 | Exercises on typing, strictness, substitution, and faithful sequent terms. | The faithful-term exercise is conceptually adjacent to proof identity but not a proved source result. |
| 151 | 137 / 6.6 | Exercises on cut reductions, patterns, and subject reduction. | Accounted for; no theorem imported. |
| 152 | 138 / 6.6 | Exercises on recursion, lists, laziness, and nontermination. | Accounted for. |
| 153 | 139 / 6.6 | Strictness and affine-logic translation exercises. | Confirms affine weakening requires a different system. |
| 154 | 140 / chapter verso | Intentionally blank transition page. | Accounted for; no mathematical claim. |
| 155 | 141 / Chapter 7 and 7.1 | Logic versus type theory; internal proof/program judgment; propositional type grammar. | Supports separating object-logic proof data from certificate data. |
| 156 | 142 / 7.1 | Typed universal quantification and dependent function introduction. | Quantifiers/dependency remain outside current scope. |
| 157 | 143 / 7.1 | Dependent-function elimination and existential introduction. | No core dependency. |
| 158 | 144 / 7.1 | Dependent existential elimination and type-family judgments. | No core dependency. |
| 159 | 145 / 7.1-7.2 | Type formation and indexed natural numbers. | No core dependency. |
| 160 | 146 / 7.2 | Natural-number case and iteration constructs. | No core dependency. |
| 161 | 147 / 7.2 | Length-indexed list formation/introduction. | No core dependency. |
| 162 | 148 / 7.2 | Dependent list case and iteration. | No core dependency. |
| 163 | 149 / 7.2 | Append with computed indices and need for equality reasoning. | Illustrates why API result types and conversions must state exact equalities. |
| 164 | 150 / 7.2 | Type conversion, intensional/extensional equality tradeoff, and explicit equality proofs. | Supports favoring decidable narrow equivalence over vague arbitrary isomorphism claims. |
| 165 | 151 / 7.3 | Logical frameworks, LF limitations for state/concurrency, and LLF motivation. | Adjacent library architecture only. |
| 166 | 152 / 7.3 | Imperative-language syntax and higher-order abstract syntax setup. | No core dependency. |
| 167 | 153 / 7.3 | Command representation and affine operational state. | No core dependency. |
| 168 | 154 / 7.3 | Evaluation type families and the linear framework fragment. | No core dependency. |
| 169 | 155 / 7.3 | Definitional equality and execution judgments. | Shows decidable equality is essential for a usable dependent API. |
| 170 | 156 / 7.3 | Operational command rules for sequencing, parallelism, assignment, and allocation. | No core dependency. |
| 171 | 157 / 7.3 | Loop encodings and substitution through higher-order abstract syntax. | No core dependency. |
| 172 | 158 / 7.3 | Concurrency/proof-equality limitation and eta-canonical forms. | Directly warns that provability-preserving translations need not preserve proof identity. |
| 173 | 159 / bibliography | References A through early B, including Andreoli 1992. | Bibliographic lead only; primary sources must be checked separately. |
| 174 | 160 / bibliography | References B through D. | Bibliographic lead only. |
| 175 | 161 / bibliography | References G through HP, including Girard 1987 and proof-search references. | Bibliographic lead only. |
| 176 | 162 / bibliography | References HT through MNPS. | Bibliographic lead only. |
| 177 | 163 / bibliography | References MOM through SHD. | Bibliographic lead only. |
| 178 | 164 / bibliography | References Statman through Xi/Pfenning. | Bibliographic lead only. |

## Current claim boundary

The completed interval supports exact resource ownership, occurrence identity,
exchange, and the need to separate logic fragments. It does **not** state the
Danos-Regnier criterion, proof-net correctness, or a proof-net
sequentialization theorem. Those project claims therefore continue to depend on
the direct proof-net sources, representation comparison, and Lean proofs.

The ordered text and rendered-image passes are complete for all 168 unique
pages. The exact duplicate audit accounts for the remaining 168 physical
pages, so this source is complete at the page-audit level. This does not turn it
into a direct authority for proof-net correctness or sequentialization.
