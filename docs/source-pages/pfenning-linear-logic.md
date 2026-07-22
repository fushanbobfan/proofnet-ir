# Page audit in progress: Pfenning, *Linear Logic*

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
- Current direct ordered reading: 30/168 unique pages (physical 1-10 and
  21-40). The remaining pages are not marked complete merely because a prior
  theorem/section sweep covered them.
- Visual status: the text and displayed-rule layout in this interval is still
  awaiting the all-page rendered-image pass. Therefore this document remains
  explicitly in progress.

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

## Current claim boundary

The completed interval supports exact resource ownership, occurrence identity,
exchange, and the need to separate logic fragments. It does **not** state the
Danos-Regnier criterion, proof-net correctness, or a proof-net
sequentialization theorem. Those project claims therefore continue to depend on
the direct proof-net sources, representation comparison, and Lean proofs.

No cover-to-cover completion claim may be made until physical pages 41-178 have
been read in order and every diagram/rule page in the unique set has been
rendered and checked visually.
