# Completed page audit: Park, *Open Book Decompositions with Page a Four-Punctured Sphere*

Audit started: 2026-07-22
Audit completed: 2026-07-22

## Source identity and protocol

- Local source: `paper1.pdf`
- Author: Harahm Park.
- Manuscript date: 22 January 2026.
- SHA-256: `7b756a8759e10173d0089d1fa9dad4bb6b8362ff91a08f48797bcb2d7b29388`
- Extent: 76 physical PDF pages, all with extractable text.
- Direct ordered reading is complete for all 76 pages, including the appendices
  and references. Pages 1--74 were rendered at 100 dpi and inspected in order.
  This covers every surface diagram, movie frame, Heegaard diagram, decorated
  Type A/D graph, program listing, and experimental table. `pdfimages -list`
  independently located the raster content. Pages 75--76 contain references
  only and were checked from extracted text.

## Page-by-page matrix

| Physical page | Section | Content read or inspected | ProofNet-IR consequence |
|---:|---|---|---|
| 1 | abstract; contents; §1 | Two-part program: overtwisted right-veering monodromies and bordered-contact-invariant classification; full section map. | Establishes a contact-topology source, not an MLL or proof-net authority. |
| 2 | §1 | Giroux context; disk, annulus, pair-of-pants, punctured-torus precedents; four-punctured-sphere case; Theorems 1.1--1.2. | The theorem vocabulary and correctness notions are domain-specific. |
| 3 | §1; Part 1; §2 | Theorem 1.3, conventions, acknowledgments, and start of curves/arcs/mapping classes; rendered Figure 2.1. | Generated computations helped discovery, but final mathematical claims require separate proofs. |
| 4 | §2 | Plane cover, slopes, Farey tessellation, and action of the mapping class group; rendered Figures 2.2--2.3. | A useful example of explicit combinatorial encodings with a geometric semantics, not proof-net canonicalization. |
| 5 | §§2--3 | Relative mapping class group, matrix projection, FDTC identity criterion, and Proposition 3.1; rendered Figure 2.4. | Equality is characterized inside this particular group representation only. |
| 6 | §3 | Proof of Proposition 3.1, reducible/pseudo-Anosov cases, conjugation, and subtractive continued fractions. | Proof architecture depends on PSL(2,Z), not graph switching. |
| 7 | §3 | Definition of the slope sequence and Lemma 3.3(a--c); determinant and monotonicity proof begins. | Arithmetic recursion is unrelated to proof-net sequentialization fuel. |
| 8 | §3 | Completion of Lemma 3.3 and Lemma 3.4(d--g) setup. | Background only. |
| 9 | §3 | Parity proof for Lemma 3.4 and Farey-path Remark 3.5. | Background only. |
| 10 | §3 | Theorem 3.6 and beginning of its transverse-overtwisted-disk movie proof; rendered Figure 3.1. | A constructive witness proof, but its witness language is open-book foliations. |
| 11 | §3 | Initial arcs/hairs, elliptic and hyperbolic singularities, general position; rendered Figures 3.2--3.4. | Shows why diagrams need explicit incidence/sign data; no MLL theorem follows. |
| 12 | §3 | Labeled arcs, hair moves, slope sequence, and Stage 1; rendered Figure 3.5. | Local graphical moves are governed by separate geometric invariants. |
| 13 | §3 | Stage 1 movie frames and transition to Stage 2; rendered Figures 3.6--3.9. | Visual audit confirms the proof is diagram-dependent. |
| 14 | §3 | Open-book foliation and Stage 2 endpoint/FDTC control; rendered Figure 3.10. | A possible future proof-graph case study, not current library evidence. |
| 15 | §3 | Example Stage 2 shifts for slopes -7/5 and -10/7; rendered first part of Figure 3.11. | Background only. |
| 16 | §3 | Final shifts and FDTC realization; rendered continuation of Figure 3.11. | Background only. |
| 17 | §3 | Page matching, disk/Euler-characteristic justification, and complete foliation; rendered Figures 3.11--3.12. | The explicit end-to-end witness suggests test fixtures, but does not validate ProofNet-IR. |
| 18 | §3 | Definitions of G--/G++ and transverse overtwisted disk; conclusion of Theorem 3.6; Remark 3.7. | Graphs here encode separatrices, not proof-net links or switchings. |
| 19 | §3 | Boundary-based region, Proposition 3.8, and positive-factorization proof; rendered Figure 3.13. | The counter-boundary on Theorem 3.6 is source-specific. |
| 20 | §3 | Lantern-relation completion, proof of Theorem 1.2, and Theorem 3.9 statement; rendered Figure 3.14. | No project theorem dependency. |
| 21 | §3 | Theorem 3.9(1) movie setup, slopes, and example; rendered Figure 3.15. | Background only. |
| 22 | §3 | Positive singularity shifts; rendered Figure 3.16. | Background only. |
| 23 | §3 | Negative singularities and continued movie construction; rendered Figure 3.17. | Background only. |
| 24 | §3 | Abbreviated parallel-arc moves and slope shifts; rendered start of Figure 3.18. | Background only. |
| 25 | §3 | Further shifts, twist, and FDTC realization; rendered continuation of Figure 3.18. | Background only. |
| 26 | §3 | Final shifts and page matching; rendered end of Figure 3.18. | Background only. |
| 27 | §3 | Completion of Theorem 3.9(1), proof strategy for (2), and example setup. | Explicitly a separate constructive topology proof. |
| 28 | §3 | Twist move and arc shifts for Theorem 3.9(2); rendered Figure 3.19 frames. | Background only. |
| 29 | §3 | Further positive and negative singularity moves; rendered Figure 3.19 frames. | Background only. |
| 30 | §3 | Final singularities and slope shifts; rendered Figure 3.19 frames. | Background only. |
| 31 | §3 | Page matching, completion of Theorem 3.9, Remark 3.11, and Proposition 3.12; rendered Figures 3.19--3.20. | Source distinguishes a proved family from excluded cases; useful claim-discipline example. |
| 32 | §3 | Proof of Proposition 3.12 using FDTC quasi-morphism and positive twists; rendered Figure 3.21. | No project theorem dependency. |
| 33 | §§3--4 | Open limitations, Sage-assisted discovery, Question 3.15, reducible monodromy setup, and Proposition 4.1; rendered Figure 4.1. | The paper openly separates computational evidence from theorem coverage. |
| 34 | §§4--5 | Lekili comparison, Theorem 4.3, proof reduction, and pre-Lagrangian splitting strategy. | The unfinished topology question is not a ProofNet-IR obligation. |
| 35 | §5 | Proposition 5.1, collars, 1-form constraints, and cohomological construction; rendered Figure 5.1. | Background only. |
| 36 | §5 | Mapping-torus contact form and extension across solid tori; rendered Figure 5.2. | Background only. |
| 37 | §5 | Cutting/gluing construction, Y(n,m), and Proposition 5.2; rendered Figure 5.3. | Compositional gluing is conceptual adjacency only. |
| 38 | §5 | Proof of Proposition 5.2 and contact-form extensions on both halves; rendered Figures 5.4--5.5. | Background only. |
| 39 | §§5--6 | Transition to bordered contact invariant, co-orientation reversal, parameterizations, and Stipsicz--Vertesi map. | Different invariant and module semantics from MLL. |
| 40 | §6 | Lemma 6.1 and LOSS/contact generators from Heegaard diagrams; rendered Figures 6.1--6.2. | Diagram verification is highly domain-specific. |
| 41 | §6 | Spin-c distinction, basepoint shift, and Lemma 6.2 setup; rendered Figures 6.3--6.5. | Background only. |
| 42 | §6 | Sutured caps, handleslides, destabilizations, and proof of Lemma 6.2; rendered Figures 6.5--6.8. | Local moves preserve specified invariants, but do not define proof-net equivalence. |
| 43 | §6 | Framing labels, link-surgery origin, and Type A graph models; rendered Figures 6.9--6.12. | A decorated graph is meaningful only with its module interpretation. |
| 44 | §6 | Type A graph action convention, boundedness, and periodic-domain setup; rendered Figures 6.11--6.12. | Reinforces the need for explicit graph semantics and boundedness contracts. |
| 45 | §6 | Periodic domains, admissibility, and simple domains; rendered Figures 6.13--6.16. | No MLL result. |
| 46 | §6 | Candidate higher products from complementary simple domains; rendered Figures 6.16--6.17. | Background only. |
| 47 | §6 | Definition 6.4, Proposition 6.5, contact-invariant candidates, and refined grading proof; rendered Figure 6.18. | Proof obligations rely on grading data absent from ProofNet-IR. |
| 48 | §6 | Grading groups, Reeb gradings, Table 6.1, and uniqueness argument. | Table is an algebraic calculation, not an MLL benchmark. |
| 49 | §6 | Completion of Proposition 6.5 and Corollary 6.6; rendered Figure 6.19. | Background only. |
| 50 | §§6--7 | Contact-invariant identification, alpha/beta warning, reparameterizing and gluing, and Type D graph models. | Explicitly warns that visually similar diagrams can change semantics. |
| 51 | §7 | Type D path interpretation, twisting-slice DD module, and Proposition 7.1; rendered Figures 7.1--7.2. | A different executable graph calculus with different correctness equations. |
| 52 | §7 | Contact generators, framing choices, and negative-Dehn-twist bimodules; rendered Figures 7.3--7.4. | Background only. |
| 53 | §7 | DA bimodule operations and Proposition 7.2 on spin-c preservation; rendered Figure 7.5. | Background only. |
| 54 | §7 | Handleslide proof, iterated framing, and setup of Theorem 4.3; rendered Figures 7.6--7.7. | Background only. |
| 55 | §7; Appendix A | Boundary computation proving vanishing, alternate generator remark, and torus-algebra basis. | The proof closes its own theorem; it does not supply checker soundness. |
| 56 | Appendix A | Torus algebra multiplication, Type A modules, strict unitality, and boundedness. | Algebraic module definitions are not current public API dependencies. |
| 57 | Appendix A | Type D, DD, and DA modules plus A/D box tensor product. | Compositional API inspiration only. |
| 58 | Appendix A; Appendix B | Remaining box tensor products and lower-genus bordered diagram construction; rendered Figure B.1. | Background only. |
| 59 | Appendix B | Bordered and genus-two diagrams, Sarkar--Wang setup, point labels, and algorithmic caution; rendered Figures B.2--B.3. | The author records an implementation caveat instead of silently assuming algorithm applicability. |
| 60 | Appendix B | Nice diagram and zoomed label regions; Proposition B.2; rendered Figures B.4--B.7. | A combinatorial computation after a proved domain-specific normalization. |
| 61 | Appendix B | Pure-differential cancellation rule and systematic simplification protocol. | Similar in spirit to graph reduction, but not a certified ProofNet-IR rewrite. |
| 62 | Appendix B | First component reductions; rendered Figures B.8--B.9. | Background only. |
| 63 | Appendix B | Further component reductions; rendered Figures B.10--B.11. | Background only. |
| 64 | Appendix B | Further component reductions; rendered Figures B.12--B.13. | Background only. |
| 65 | Appendix B | Component reductions; rendered Figures B.14--B.17. | Background only. |
| 66 | Appendix B | Component reductions; rendered Figures B.16--B.19. | Background only. |
| 67 | Appendix B | Component reductions; rendered Figures B.18--B.19. | Background only. |
| 68 | Appendix B | Component reductions; rendered Figures B.20--B.21. | Background only. |
| 69 | Appendix B | Final local component reductions; rendered Figures B.22--B.24. | Background only. |
| 70 | Appendix B | Reassembled decorated graph and Type D to Type A conversion; rendered Figure B.25. | The reduction result is parameterized by the source's torus algebra, not proof-net identity. |
| 71 | Appendices B--C | Corollaries B.4--B.5 and Python region-list generator for `hf-hat-obd-nice`; rendered Listing 1. | Concrete code supports the paper's computations only. |
| 72 | Appendix C | Region-label algorithm, near-nice caveat, benchmark filtering, and first rows of Table C.2. | The experiments are small contact-invariant calculations, not ProofNet-IR experiments. |
| 73 | Appendix C | Middle rows of Table C.2, including mixed vanishing/non-vanishing outcomes. | No transfer of empirical accuracy or performance claims is valid. |
| 74 | Appendix C; references | Final rows of Table C.2 and start of references. | Confirms the paper reports domain results but no checker, sequentializer, canonicalizer, or MLL performance theorem. |
| 75 | references | References from Honda--Kazez--Matic through Lipshitz--Ozsvath--Thurston. | Bibliographic accounting only. |
| 76 | references | Remaining references and author affiliation. | Bibliographic accounting only. |

## Strict claim boundary

This source proves contact-topology and bordered-Floer statements about open
books whose page is a four-punctured sphere. It does **not** state or prove the
Danos--Regnier criterion, MLL checker soundness/completeness,
desequentialization, sequentialization, proof-net canonicalization, graph
isomorphism, or a proof-search performance result. Its `hf-hat-obd` and
`hf-hat-obd-nice` computations are discovery/calculation evidence in a
different formal domain and are not part of the ProofNet-IR benchmark.

The legitimate project consequence is methodological: rich mathematical
diagrams require typed incidence data, explicit move semantics, invariant
tracking, and a clear boundary between machine-discovered examples and proved
claims. A later topology case study would require substantial new
formalization and cannot be advertised as a current library use case.
