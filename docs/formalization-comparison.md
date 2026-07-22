# Sequentialization formalization comparison

Review date: 2026-07-21

## Primary evidence added

The local generated exposition is not sufficient authority for a library-level
sequentialization theorem. The implementation plan is now cross-checked against:

- Danos and Regnier, *The Structure of Multiplicatives*, Archive for
  Mathematical Logic 28, 181-203 (1989), DOI
  <https://doi.org/10.1007/BF01622878>;
- Di Guardia and Laurent, *A Formalization of Multiplicative Proof-Nets in
  Rocq*, TLLA 2025,
  <https://remidig.github.io/papers/rocqtlla2025.pdf>;
- the corresponding Rocq development,
  <https://github.com/RemiDiG/proofnet_mll>, reviewed locally at commit
  `9b582a53c4c9c94013146d2c749597dada9edf96` under its LGPL license;
- Straßburger, *Proof Nets and the Identity of Proofs*, INRIA RR-6013 / arXiv
  `cs/0610123`, <https://arxiv.org/abs/cs/0610123>.

The upstream source is a proof reference, not code to copy into this MIT
repository. Any implementation here must be independently written and must
state the representation translation it proves.

## Representation mismatch

| Dimension | ProofNet-IR | Rocq `proofnet_mll` |
|---|---|---|
| Graph vertices | formula occurrences | rule and conclusion vertices |
| Graph edges | axiom/tensor/par incidence edges between occurrences | formula-labeled directed edges |
| Premise order | explicit link fields | edge-side labels and graph properties |
| Conclusions | occurrence indices | an order list containing every conclusion edge once |
| Cuts | absent | represented and sequentialized |
| Correctness implementation | explicitly enumerate each par switching and test its undirected tree | colored-path formulation on one multigraph |
| Sequentialization result | not yet general | a sequent proof whose desequentialization is graph-isomorphic to the input |

The two correctness presentations are mathematically related, but the Rocq
theorem cannot simply be restated for the Lean structure. In particular, the
target theorem must use an explicit occurrence-preserving isomorphism or
reindexing relation; literal certificate equality is too strong.

## Upstream proof architecture

The reviewed Rocq development separates the argument into:

1. graph/path and finite multigraph lemmas;
2. proof-structure and correctness definitions;
3. desequentialization and proof that every sequent derivation gives a net;
4. existence of a terminal splitting vertex, using a generalized Yeo theorem;
5. inverse cases for axiom, par, tensor, and cut vertices;
6. well-founded recursion on graph edge count;
7. a final dependent result containing a sequent proof and an isomorphism from
   its desequentialization to the original proof net.

Its final theorem has the essential shape "for every proof net `G`, there is a
linear-logic proof `p` whose proof structure is isomorphic to `G`". This
confirms that isomorphism is part of the correctness statement, not merely a
serialization convenience.

## Lean implementation obligations

Before general sequentialization can be claimed here, ProofNet-IR must:

1. define certificate reindexing and an equivalence/isomorphism relation that
   preserves formulas, ordered tensor/par premises, conclusions, and axiom
   pairing;
2. prove the checker and declarative correctness predicates invariant under
   that relation;
3. prove arbitrary inferred derivations desequentialize to accepted nets,
   rather than relying only on the post-checking safe API;
4. define terminal par and splitting tensor decomposition for the current
   occurrence graph;
5. prove each decomposition preserves proof-net correctness for its subnets;
6. prove a correct non-axiom net has an admissible terminal decomposition;
7. recurse on a strict size measure and return a `Derivation` together with an
   isomorphism to the original certificate.

These obligations replace the earlier informal plan of simply "finding a
splitting tensor". They also explain why v0.2.0 is a research prototype rather
than a completed proof-net library.

## Current implementation checkpoint

`ProofNetIR/Reindex.lean` now supplies the transport half of obligation 1: a
bounded bijection of natural-number vertices, consistent transport of formula
occurrences and ordered links, formula-lookup commutation, and a literal
inverse round trip. Local link typing and node ownership/count predicates are
also invariant. It deliberately does not yet mark obligation 1 complete. The
explicit certificate equivalence relation and whole-certificate structural,
switching, and checker invariance theorems remain open, after which
sequentialization can return a derivation together with that relation rather
than literal array equality.
