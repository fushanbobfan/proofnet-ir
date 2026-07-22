# Page audit: *Geometry of Neuroscience*

Audit completed: 2026-07-21

## Source identity and method

- Local source: `geometry_of_neurosci.pdf`
- SHA-256: `e7730b0731bb9897e67961554bd2a00a96a0bcd47db342c6460d51c19e7a5602`
- Extent: 33 physical pages; printed pagination begins with page 1 on physical
  page 4 and ends with page 30 on physical page 33.
- Visible source status: the cover says "Generated May 12, 2026" and gives no
  author. The PDF metadata likewise gives no author. Its bibliography is
  primarily a map to M. Marcolli's 2026 course pages/slides plus standard
  secondary and primary sources.
- Text check: every page was extracted and read in order. `pypdf 6.10.0`
  produced 84,299 characters and 12,879 whitespace-delimited tokens. The
  repository's earlier `pdftotext`-based ledger reports 15,797 extracted words;
  these counts are extractor-dependent and are not page-coverage claims.
- Visual check: all 33 rendered pages were inspected, including every displayed
  formula and Figures 1--10. No page is blank. The only extraction problem was
  a console-encoding failure while printing physical page 4; re-extraction in
  UTF-8 and the rendered page confirmed that no source content was missing.

This is a complete page audit, not an endorsement of every result in the
notes. The document frequently labels results as a standard form, proof idea,
formal calculation, schematic theorem, or heuristic. Primary references must
be consulted before importing any such result into a formal proof.

## Page-by-page matrix

| Physical page | Printed page / section | Content checked | ProofNet-IR relevance and boundary |
|---:|---|---|---|
| 1 | cover | Title and generation date. | Establishes that this is generated expository material, not a primary proof-net source. |
| 2 | unnumbered / abstract | Four themes: fractals, probability, variational problems, and Gaussian free fields (GFFs); GFF is described as a natural neighbor rather than an advertised course topic. | Broad motivation only. It does not specify a proof system or correctness criterion. |
| 3 | unnumbered / contents | Complete section map through dynamics, fractals, neural codes, graphs, learning, geometry, segmentation, GFFs, tracking, language, and multiscale estimates. | Confirms scope and supports the page audit; no proof-net chapter is present. |
| 4 | 1 / orientation | Neural objects mapped to mathematical models; Figure 1; representation, state space, transformations, and graph Laplacians. | Weak conceptual support for explicit state spaces and transformations. This is an analogy, not a theorem about proof representations. |
| 5 | 2 / dynamics | Discrete and continuous dynamics; Hodgkin--Huxley and FitzHugh--Nagumo; Figure 2; linear stability proposition. | Mathematical training only; no direct certificate or logic claim. |
| 6 | 3 / dynamics | Linear-stability proof, coupled maps, fixed points, and the finite-state Lyapunov-function equivalence with absence of nontrivial cycles. | The local/global distinction is adjacent to checker design, but the theorem is not about switching graphs. |
| 7 | 4 / fractals | Logistic-map threshold; Hausdorff measure and critical-exponent definition of Hausdorff dimension. | No direct project dependency. |
| 8 | 5 / fractals | IFS attractor theorem, Moran formula under separation, Cantor/Sierpinski examples, Figures 3--4. | No direct project dependency. |
| 9 | 6 / symbolic dynamics | Symbolic itineraries, topological entropy, entropy/dimension example, and box dimension. | Sequence/tree encodings are adjacent language, not proof identity or sequentialization. |
| 10 | 7 / graph/fractal cautions | Graph-growth dimension; warning that Hausdorff dimension, power-law degree, and entropy dimension are inequivalent; multifractals; neural-code transition. | Useful warning against conflating graph statistics. It supplies no proof-net invariant. |
| 11 | 8 / neural codes | Binary codes, simplicial complexes, the nerve theorem, Helly-type convexity, neural rings. | Shows how combinatorial incidence can encode global structure; not linear-logic semantics. |
| 12 | 9 / neural codes and coding | Spectrum recovery of a simplicial code, neural ideals, linear codes, Singleton bound. | Local-to-global encoding analogy only. |
| 13 | 10 / coding and networks | Hamming-ball entropy, Hopfield energy descent, vertex expansion, and Tanner-code setup. | Energy descent and expansion are unrelated to MLL switching correctness. |
| 14 | 11 / expansion and Laplacians | Schematic expansion-to-distance statement; graph Laplacian, Dirichlet identity, and kernel characterization. | Graph connectivity vocabulary is relevant implementation background, but this page does not prove the checker theorem used by the library. |
| 15 | 12 / graph spectra and topology | Cheeger inequality, Erdős--Rényi thresholds, Ihara zeta/nonbacktracking walks, and directed-topology motivation. | Adjacent finite-graph mathematics. It does not define proof-net switchings. |
| 16 | 13 / directed topology and learning | Directed clique/flag complex, chain boundary with `∂² = 0`, Figure 5, expected and empirical risk. | Illustrates that missing edges and higher-dimensional cavities differ; not evidence for proof-net soundness. |
| 17 | 14 / learning and energy | Finite-class Hoeffding bound, Laplacian regularization and Euler equation, RBM energy/free energy. | No direct project dependency. |
| 18 | 15 / Gabor analysis | Short-time Fourier transform, Moyal identity, Gabor frames, density principle, Figure 6. | No direct project dependency. The density theorem is explicitly informal. |
| 19 | 16 / conformal and harmonic geometry | Harmonic-map energy, two-dimensional conformal invariance, Beltrami coefficient, Hopf differential holomorphicity. | No direct project dependency. Rendered notation, including conjugate derivatives, was checked visually. |
| 20 | 17 / contact geometry | Harmonic-sphere corollary; contact structures, Legendrian curves, Figure 7, Darboux theorem with proof idea. | No direct project dependency. |
| 21 | 18 / symplectization and segmentation | Symplectization; Mumford--Shah functional; Euler equation away from the edge set; contour variation. | Variational decomposition is an analogy only. |
| 22 | 19 / segmentation and GFF bridge | Formal curvature balance, Figure 8, schematic Ambrosio--Tortorelli convergence, and explicit introduction of GFFs as an adjacent bridge topic. | The page itself marks the GFF material as adjacent; it cannot serve as core proof-net evidence. |
| 23 | 20 / finite graph GFF | Pinned graph GFF, positive-definite pinned Laplacian, spatial Markov property, massive field, MAP setup. | Uses graph connectivity and Laplacians for probability, not proof correctness. |
| 24 | 21 / continuum GFF and Ising | Continuum GFF via Laplacian eigenfunctions, covariance as a Green function, segmentation relation, Ising-interface chain. | No direct project dependency. |
| 25 | 22 / tracking and language algebra | Plücker coordinates, Klein quadric, line incidence; free nonassociative magma; Hopf algebra of forests and admissible cuts. | Rooted composition/decomposition is conceptually relevant, but admissible forest cuts are not MLL par switchings and do not prove sequentialization. |
| 26 | 23 / Hopf structure and Frostman | Structural proof of the forest Hopf algebra; maximum-entropy Markov walk and free energy; Frostman lemma with proof idea. | Composition vocabulary only; no theorem transfers to the certificate representation. |
| 27 | 24 / energy, GFF spectra, renormalization | Riesz energy dimension bound; graph-GFF spectral expansion and path example; Sierpinski energy renormalization. | No direct project dependency. |
| 28 | 25 / renormalization and appendix | Energy-scaling calculation; harmonic extension minimizes graph energy; box-counting definitions and dimension inequality. | Harmonic minimization is not checker-guided proof repair. Dimension statements are unused and would need primary-source verification before formalization. |
| 29 | 26 / multiscale estimates | Figure 9; proof of Hausdorff/box-dimension inequality; mass-distribution principle; start of Bernoulli self-similar measure theorem. | No direct project dependency. |
| 30 | 27 / entropy and trees | Bernoulli measure dimension proof, biased Cantor example, regular-tree boundary dimension, Figure 10. | Tree representations are adjacent, but the boundary metric result says nothing about derivation/proof-net equivalence. |
| 31 | 28 / resistance and GFF | Tree resistance scaling; GFF increments equal effective resistance; explicitly heuristic Kolmogorov corollary. | No direct project dependency. The heuristic label prevents use as a formal authority. |
| 32 | 29 / fractal boundaries and synthesis | Minkowski sausage/content, smooth-curve asymptotic, fractal-boundary scaling, start of the four-theme synthesis. | No direct project dependency. |
| 33 | 30 / synthesis and references | GFF synthesis, Laplacian as unifying operator, and references 1--22. | Provides leads to primary sources only; it contains no proof-net reference or theorem. |

## Claim boundary for ProofNet-IR

This source may be cited only for broad motivation:

- physical page 4 motivates treating representation, state space, and
  transformations explicitly;
- physical pages 10--16 illustrate that local graph data and global
  combinatorial/topological properties are different;
- physical pages 25--26 illustrate rooted composition, forests, and explicit
  decomposition operations.

It cannot support any claim that:

- the Danos--Regnier switching criterion is sound or complete for unit-free
  cut-free MLL;
- every accepted certificate sequentializes;
- desequentialization preserves derivability;
- the current serialization is invariant under arbitrary vertex renaming;
- proof-net generation or repair improves search success, cost, or runtime;
- ProofNet-IR is ready for independent library use.

Those statements require direct proof-theory sources, Lean theorems, and/or
controlled experiments. None may be inferred from thematic similarity to
graphs, trees, energy, or local/global structure in this document.

## Rigor notes

- The notes openly omit full proofs when they would require a separate course
  and repeatedly use qualifiers such as "schematic", "formal", "proof idea",
  "informal standard form", and "heuristic".
- Physical pages 14, 18, 22, and 31 contain representative qualified results:
  schematic expansion/coding, an informal Gabor density principle, schematic
  Ambrosio--Tortorelli convergence, and a Kolmogorov heuristic.
- The formulas and figures are legible, but visual correctness is not a
  substitute for checking the cited primary literature.
- No definition, theorem, or proof from this source is currently imported into
  the trusted Lean core.
