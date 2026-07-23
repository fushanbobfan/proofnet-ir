import ProofNetIR.Sequentialization

namespace ProofNetIR

/-- A vertex-number-free view of one incident link, retaining argument role
and all endpoint formula labels.  Link-list order is handled separately by
multiset comparison. -/
inductive LocalLinkView where
  | axiomLeft (left right : Option Formula)
  | axiomRight (left right : Option Formula)
  | tensorLeft (left right conclusion : Option Formula)
  | tensorRight (left right conclusion : Option Formula)
  | tensorConclusion (left right conclusion : Option Formula)
  | parLeft (left right conclusion : Option Formula)
  | parRight (left right conclusion : Option Formula)
  | parConclusion (left right conclusion : Option Formula)
  deriving Repr, DecidableEq

namespace Link

/-- Describe the role of `vertex` in a link without retaining submitted vertex
numbers.  Malformed self-incidences use the first matching role, consistently
before and after a bijective reindexing. -/
def localView? (certificate : Certificate) (vertex : Vertex) :
    Link → Option LocalLinkView
  | .axiom left right =>
      if left == vertex then
        some <| .axiomLeft (certificate.formula? left)
          (certificate.formula? right)
      else if right == vertex then
        some <| .axiomRight (certificate.formula? left)
          (certificate.formula? right)
      else
        none
  | .tensor left right conclusion =>
      if left == vertex then
        some <| .tensorLeft (certificate.formula? left)
          (certificate.formula? right) (certificate.formula? conclusion)
      else if right == vertex then
        some <| .tensorRight (certificate.formula? left)
          (certificate.formula? right) (certificate.formula? conclusion)
      else if conclusion == vertex then
        some <| .tensorConclusion (certificate.formula? left)
          (certificate.formula? right) (certificate.formula? conclusion)
      else
        none
  | .par left right conclusion =>
      if left == vertex then
        some <| .parLeft (certificate.formula? left)
          (certificate.formula? right) (certificate.formula? conclusion)
      else if right == vertex then
        some <| .parRight (certificate.formula? left)
          (certificate.formula? right) (certificate.formula? conclusion)
      else if conclusion == vertex then
        some <| .parConclusion (certificate.formula? left)
          (certificate.formula? right) (certificate.formula? conclusion)
      else
        none

@[simp] theorem localView?_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (link : Link)
    (vertex : Vertex) :
    (link.reindex r).localView? (certificate.reindex r) (r.forward vertex) =
      link.localView? certificate vertex := by
  cases link <;>
    simp [localView?, Link.reindex, certificate.reindex_formula?_forward,
      r.forward_beq]

end Link

namespace Certificate

/-- The multiset of numeric-free incident-link views at one vertex. -/
def localLinkViews (certificate : Certificate) (vertex : Vertex) :
    List LocalLinkView :=
  certificate.links.filterMap (Link.localView? certificate vertex)

@[simp] theorem localLinkViews_reindex (certificate : Certificate)
    (r : VertexRenaming certificate.formulas.size) (vertex : Vertex) :
    (certificate.reindex r).localLinkViews (r.forward vertex) =
      certificate.localLinkViews vertex := by
  unfold localLinkViews
  rw [Certificate.reindex_links, List.filterMap_map]
  have viewFunctions :
      Link.localView? (certificate.reindex r) (r.forward vertex) ∘
          Link.reindex r =
        Link.localView? certificate vertex := by
    funext link
    exact Link.localView?_reindex certificate r link vertex
  rw [viewFunctions]

theorem LinkPermutationEquivalent.localLinkViews_perm
    {left right : Certificate}
    (equivalent : left.LinkPermutationEquivalent right) (vertex : Vertex) :
    left.localLinkViews vertex |>.Perm (right.localLinkViews vertex) := by
  have viewFunctions : Link.localView? left vertex =
      Link.localView? right vertex := by
    funext link
    cases link <;>
      simp [Link.localView?, Certificate.formula?, equivalent.formulas]
  unfold localLinkViews
  rw [viewFunctions]
  exact equivalent.links.filterMap _

/-- Numeric-free one-hop incidence compatibility.  This is a necessary
condition for `ProofNetEquivalent`, so it can safely prune repeated-label
occurrence alignments before candidate vertex bijections are materialized. -/
def localIdentityCompatible (left right : Certificate)
    (targetVertex sourceVertex : Vertex) : Bool :=
  decide ((left.localLinkViews sourceVertex).Perm
    (right.localLinkViews targetVertex))

/-- Every direct proof-net equivalence witness satisfies the local structural
compatibility test at the inverse image of every target vertex. -/
theorem localIdentityCompatible_inverse {left right : Certificate}
    (vertexMap : VertexRenaming left.formulas.size)
    (relation : (left.reindex vertexMap).LinkPermutationEquivalent right)
    (target : Vertex) :
    localIdentityCompatible left right target (vertexMap.inverse target) =
      true := by
  have incidentPermutation := relation.localLinkViews_perm target
  have sourceViews :
      (left.reindex vertexMap).localLinkViews target =
        left.localLinkViews (vertexMap.inverse target) := by
    simpa only [vertexMap.forward_inverse] using
      left.localLinkViews_reindex vertexMap (vertexMap.inverse target)
  have desired : (left.localLinkViews (vertexMap.inverse target)).Perm
      (right.localLinkViews target) := by
    rw [← sourceViews]
    exact incidentPermutation
  simpa [localIdentityCompatible] using desired

end Certificate

end ProofNetIR
