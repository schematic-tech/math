import Schematic.Math.GraphTheory.PathsTrees.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Replace the forward `x`-to-`y` interval of a walk by another `x`-to-`y`
walk.  The main use is expanding a temporary separator edge along a path on
the opposite side of a separation. -/
def Walk.expandEdgeForward
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (q : G.Walk x y) :
    G.Walk u v :=
  ((p.takeUntil x hx).append q).append (p.dropUntil y hy)

theorem Walk.IsPath.expandEdgeForward
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    {q : G.Walk x y}
    (hq : q.IsPath)
    (hidx : p.support.idxOf x < p.support.idxOf y)
    (hclean :
      forall z : V, z ∈ q.support -> z ∈ p.support -> z = x ∨ z = y) :
    (Walk.expandEdgeForward p hx hy q).IsPath := by
  have hprefix : ((p.takeUntil x hx).append q).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (hp.takeUntil hx) hq ?_
    intro z hzprefix hzq
    have hzp : z ∈ p.support :=
      SimpleGraph.Walk.support_takeUntil_subset p hx hzprefix
    rcases hclean z hzq hzp with rfl | rfl
    · rfl
    · exact False.elim
        (Walk.not_mem_takeUntil_of_idxOf_lt hx hidx hzprefix)
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    hprefix (hp.dropUntil hy) ?_
  intro z hzleft hzsuffix
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
  rcases hzleft with hzprefix | hzq
  · exact False.elim
      (Set.disjoint_left.mp
        (Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
          hp hx hy hidx)
        hzprefix hzsuffix)
  · have hzp : z ∈ p.support :=
      SimpleGraph.Walk.support_dropUntil_subset p hy hzsuffix
    rcases hclean z hzq hzp with rfl | rfl
    · exact False.elim
        (Walk.IsPath.earlier_not_mem_dropUntil_of_idx_lt
          hp hy hidx hzsuffix)
    · rfl

theorem Walk.expandEdgeForward_support_subset
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (q : G.Walk x y) :
    {z : V | z ∈ (Walk.expandEdgeForward p hx hy q).support} ⊆
      {z : V | z ∈ p.support} ∪ {z : V | z ∈ q.support} := by
  intro z hz
  change z ∈ (Walk.expandEdgeForward p hx hy q).support at hz
  change z ∈ p.support ∨ z ∈ q.support
  rw [Walk.expandEdgeForward,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzleft | hzsuffix
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzleft
    rcases hzleft with hzprefix | hzq
    · exact Or.inl
        (SimpleGraph.Walk.support_takeUntil_subset p hx hzprefix)
    · exact Or.inr hzq
  · exact Or.inl
      (SimpleGraph.Walk.support_dropUntil_subset p hy hzsuffix)

theorem Walk.expandEdgeForward_internalVertices_subset
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (q : G.Walk x y) :
    Walk.InternalVertices (Walk.expandEdgeForward p hx hy q) ⊆
      Walk.InternalVertices p ∪ Walk.InternalVertices q := by
  intro z hz
  rcases Walk.expandEdgeForward_support_subset p hx hy q hz.1 with hzp | hzq
  · exact Or.inl ⟨hzp, hz.2.1, hz.2.2⟩
  · by_cases hzx : z = x
    · exact Or.inl ⟨by simpa [hzx] using hx, hz.2.1, hz.2.2⟩
    · by_cases hzy : z = y
      · exact Or.inl ⟨by simpa [hzy] using hy, hz.2.1, hz.2.2⟩
      · exact Or.inr ⟨hzq, hzx, hzy⟩

theorem Walk.expandEdgeForward_edges_subset
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (q : G.Walk x y) :
    forall e : Sym2 V,
      e ∈ (Walk.expandEdgeForward p hx hy q).edges ->
        e ∈ p.edges ∨ e ∈ q.edges := by
  intro e he
  rw [Walk.expandEdgeForward, SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  rcases he with heleft | hesuffix
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at heleft
    rcases heleft with heprefix | heq
    · exact Or.inl (SimpleGraph.Walk.edges_takeUntil_subset p hx heprefix)
    · exact Or.inr heq
  · exact Or.inl (SimpleGraph.Walk.edges_dropUntil_subset p hy hesuffix)

theorem Walk.expandEdgeForward_marker_not_mem_edges
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    {q : G.Walk x y}
    (hidx : p.support.idxOf x < p.support.idxOf y)
    (hq : s(x, y) ∉ q.edges) :
    s(x, y) ∉ (Walk.expandEdgeForward p hx hy q).edges := by
  intro he
  rw [Walk.expandEdgeForward, SimpleGraph.Walk.edges_append,
    List.mem_append] at he
  rcases he with heleft | hesuffix
  · rw [SimpleGraph.Walk.edges_append, List.mem_append] at heleft
    rcases heleft with heprefix | heq
    · have hy_prefix : y ∈ (p.takeUntil x hx).support :=
        (p.takeUntil x hx).snd_mem_support_of_mem_edges heprefix
      exact
        (Walk.not_mem_takeUntil_of_idxOf_lt hx hidx) hy_prefix
    · exact hq heq
  · have hx_suffix : x ∈ (p.dropUntil y hy).support :=
      (p.dropUntil y hy).fst_mem_support_of_mem_edges hesuffix
    exact
      (Walk.IsPath.earlier_not_mem_dropUntil_of_idx_lt
        hp hy hidx) hx_suffix

/-- Expand every occurrence of the undirected edge `s(x,y)` in a simple walk
along `q`, choosing the orientation in which the edge occurs. -/
def Walk.IsPath.expandEdge
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    (_hp : p.IsPath)
    (x y : V)
    (q : G.Walk x y) :
    G.Walk u v :=
  if he : s(x, y) ∈ p.edges then
    let hx := p.fst_mem_support_of_mem_edges he
    let hy := p.snd_mem_support_of_mem_edges he
    if _hforward : p.support.idxOf x < p.support.idxOf y then
      Walk.expandEdgeForward p hx hy q
    else
      Walk.expandEdgeForward p hy hx q.reverse
  else
    p

theorem Walk.IsPath.expandEdge_isPath
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    {q : G.Walk x y}
    (hq : q.IsPath)
    (hclean :
      forall z : V, z ∈ q.support -> z ∈ p.support -> z = x ∨ z = y) :
    (Walk.IsPath.expandEdge hp x y q).IsPath := by
  unfold Walk.IsPath.expandEdge
  split
  next he =>
    split
    next hforward =>
      exact Walk.IsPath.expandEdgeForward hp
        (p.fst_mem_support_of_mem_edges he)
        (p.snd_mem_support_of_mem_edges he)
        hq hforward hclean
    next hnot_forward =>
      have hxy_ne : x ≠ y := by
        have hxy_adj : G.Adj x y := by
          rw [← SimpleGraph.mem_edgeSet]
          exact p.edges_subset_edgeSet he
        exact hxy_adj.ne
      have hidx_ne : p.support.idxOf x ≠ p.support.idxOf y := by
        intro hidx
        exact hxy_ne
          ((List.idxOf_inj (p.fst_mem_support_of_mem_edges he)).mp hidx)
      have hreverse : p.support.idxOf y < p.support.idxOf x := by
        omega
      refine Walk.IsPath.expandEdgeForward hp
        (p.snd_mem_support_of_mem_edges he)
        (p.fst_mem_support_of_mem_edges he)
        hq.reverse hreverse ?_
      intro z hzq_reverse hzp
      have hzq : z ∈ q.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzq_reverse
      rcases hclean z hzq hzp with hzx | hzy
      · exact Or.inr hzx
      · exact Or.inl hzy
  next he =>
    exact hp

theorem Walk.IsPath.expandEdge_support_subset
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (q : G.Walk x y) :
    {z : V | z ∈ (Walk.IsPath.expandEdge hp x y q).support} ⊆
      {z : V | z ∈ p.support} ∪ {z : V | z ∈ q.support} := by
  unfold Walk.IsPath.expandEdge
  split
  next he =>
    split
    next hforward =>
      exact Walk.expandEdgeForward_support_subset p
        (p.fst_mem_support_of_mem_edges he)
        (p.snd_mem_support_of_mem_edges he) q
    next hnot_forward =>
      intro z hz
      rcases Walk.expandEdgeForward_support_subset p
          (p.snd_mem_support_of_mem_edges he)
          (p.fst_mem_support_of_mem_edges he) q.reverse hz with hzp | hzq
      · exact Or.inl hzp
      · exact Or.inr (by
          simpa [SimpleGraph.Walk.support_reverse] using hzq)
  next he =>
    intro z hz
    exact Or.inl hz

theorem Walk.IsPath.expandEdge_internalVertices_subset
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (q : G.Walk x y) :
    Walk.InternalVertices (Walk.IsPath.expandEdge hp x y q) ⊆
      Walk.InternalVertices p ∪ Walk.InternalVertices q := by
  unfold Walk.IsPath.expandEdge
  split
  next he =>
    split
    next hforward =>
      exact Walk.expandEdgeForward_internalVertices_subset p
        (p.fst_mem_support_of_mem_edges he)
        (p.snd_mem_support_of_mem_edges he) q
    next hnot_forward =>
      intro z hz
      rcases Walk.expandEdgeForward_internalVertices_subset p
          (p.snd_mem_support_of_mem_edges he)
          (p.fst_mem_support_of_mem_edges he) q.reverse hz with hzp | hzq
      · exact Or.inl hzp
      · exact Or.inr
          ((Walk.mem_internalVertices_reverse_iff q).mp hzq)
  next he =>
    intro z hz
    exact Or.inl hz

theorem Walk.IsPath.expandEdge_internalVertices_subset_with_marker
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (q : G.Walk x y) :
    forall z : V,
      z ∈ Walk.InternalVertices (Walk.IsPath.expandEdge hp x y q) ->
        z ∈ Walk.InternalVertices p ∨
          (s(x, y) ∈ p.edges ∧ z ∈ Walk.InternalVertices q) := by
  unfold Walk.IsPath.expandEdge
  split
  next he =>
    split
    next hforward =>
      intro z hz
      rcases Walk.expandEdgeForward_internalVertices_subset p
          (p.fst_mem_support_of_mem_edges he)
          (p.snd_mem_support_of_mem_edges he) q hz with hzp | hzq
      · exact Or.inl hzp
      · exact Or.inr ⟨he, hzq⟩
    next hnot_forward =>
      intro z hz
      rcases Walk.expandEdgeForward_internalVertices_subset p
          (p.snd_mem_support_of_mem_edges he)
          (p.fst_mem_support_of_mem_edges he) q.reverse hz with hzp | hzq
      · exact Or.inl hzp
      · exact Or.inr
          ⟨he, (Walk.mem_internalVertices_reverse_iff q).mp hzq⟩
  next he =>
    intro z hz
    exact Or.inl hz

theorem Walk.IsPath.expandEdge_edges_subset
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (q : G.Walk x y) :
    forall e : Sym2 V,
      e ∈ (Walk.IsPath.expandEdge hp x y q).edges ->
        e ∈ p.edges ∨ e ∈ q.edges := by
  unfold Walk.IsPath.expandEdge
  split
  next he =>
    split
    next hforward =>
      exact Walk.expandEdgeForward_edges_subset p
        (p.fst_mem_support_of_mem_edges he)
        (p.snd_mem_support_of_mem_edges he) q
    next hnot_forward =>
      intro e he_expanded
      rcases Walk.expandEdgeForward_edges_subset p
          (p.snd_mem_support_of_mem_edges he)
          (p.fst_mem_support_of_mem_edges he) q.reverse e he_expanded with hep | heq
      · exact Or.inl hep
      · exact Or.inr (by
          simpa [SimpleGraph.Walk.edges_reverse] using heq)
  next he =>
    intro e hep
    exact Or.inl hep

theorem Walk.IsPath.marker_not_mem_expandEdge_edges
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    {q : G.Walk x y}
    (hq : s(x, y) ∉ q.edges) :
    s(x, y) ∉ (Walk.IsPath.expandEdge hp x y q).edges := by
  unfold Walk.IsPath.expandEdge
  split
  next he =>
    split
    next hforward =>
      exact Walk.expandEdgeForward_marker_not_mem_edges hp
        (p.fst_mem_support_of_mem_edges he)
        (p.snd_mem_support_of_mem_edges he) hforward hq
    next hnot_forward =>
      have hxy_ne : x ≠ y := by
        have hxy_adj : G.Adj x y := by
          rw [← SimpleGraph.mem_edgeSet]
          exact p.edges_subset_edgeSet he
        exact hxy_adj.ne
      have hidx_ne : p.support.idxOf x ≠ p.support.idxOf y := by
        intro hidx
        exact hxy_ne
          ((List.idxOf_inj (p.fst_mem_support_of_mem_edges he)).mp hidx)
      have hreverse : p.support.idxOf y < p.support.idxOf x := by
        omega
      have hq_reverse : s(y, x) ∉ q.reverse.edges := by
        simpa [SimpleGraph.Walk.edges_reverse, Sym2.eq_swap] using hq
      simpa [Sym2.eq_swap] using
        (Walk.expandEdgeForward_marker_not_mem_edges hp
          (p.snd_mem_support_of_mem_edges he)
          (p.fst_mem_support_of_mem_edges he) hreverse hq_reverse)
  next he =>
    exact he

/-- If two walks have disjoint supports, then their edge lists are disjoint. -/
theorem Walk.edges_disjoint_of_support_disjoint
    {u v w x : V}
    {p : G.Walk u v}
    {q : G.Walk w x}
    (hdisjoint :
      Disjoint {z : V | z ∈ p.support} {z : V | z ∈ q.support}) :
    forall e : Sym2 V, e ∈ p.edges -> e ∈ q.edges -> False := by
  intro e
  refine Sym2.ind ?_ e
  intro a b heP heQ
  exact
    Set.disjoint_left.mp hdisjoint
      (p.fst_mem_support_of_mem_edges heP)
      (q.fst_mem_support_of_mem_edges heQ)

/-- If two walks meet in at most one support vertex, then their edge lists are
disjoint. -/
theorem Walk.edges_disjoint_of_support_inter_subset_singleton
    {u v w x c : V}
    {p : G.Walk u v}
    {q : G.Walk w x}
    (hinter :
      forall z : V, z ∈ p.support -> z ∈ q.support -> z = c) :
    forall e : Sym2 V, e ∈ p.edges -> e ∈ q.edges -> False := by
  intro e
  refine Sym2.ind ?_ e
  intro a b heP heQ
  have ha_eq : a = c :=
    hinter a
      (p.fst_mem_support_of_mem_edges heP)
      (q.fst_mem_support_of_mem_edges heQ)
  have hb_eq : b = c :=
    hinter b
      (p.snd_mem_support_of_mem_edges heP)
      (q.snd_mem_support_of_mem_edges heQ)
  have hdiag : Sym2.IsDiag s(a, b) := by
    rw [Sym2.mk_isDiag_iff]
    exact ha_eq.trans hb_eq.symm
  exact (G.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet heP)) hdiag

/-- Two edge-disjoint simple paths in opposite directions form a simple cycle
when their only common support vertices are the two endpoints. -/
theorem Walk.IsPath.append_isCycle_of_support_inter_subset_endpoints
    {u v : V}
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hedges :
      forall e : Sym2 V, e ∈ p.edges -> e ∈ q.edges -> False)
    (hinter :
      forall z : V, z ∈ p.support -> z ∈ q.support -> z = u ∨ z = v)
    (hp_not_nil : ¬ p.Nil) :
    (p.append q).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  constructor
  · rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_append]
    exact hp.edges_nodup.append hq.edges_nodup hedges
  constructor
  · intro hnil
    have hlen : (p.append q).length = 0 := by
      rw [hnil]
      rfl
    rw [SimpleGraph.Walk.length_append] at hlen
    have hp_len : 0 < p.length :=
      SimpleGraph.Walk.not_nil_iff_lt_length.mp hp_not_nil
    omega
  · rw [SimpleGraph.Walk.tail_support_append]
    refine List.Nodup.append hp.support_nodup.tail hq.support_nodup.tail ?_
    intro z hzp hzq
    have hzp_support : z ∈ p.support := List.mem_of_mem_tail hzp
    have hzq_support : z ∈ q.support := List.mem_of_mem_tail hzq
    rcases hinter z hzp_support hzq_support with hzu | hzv
    · exact Walk.IsPath.start_notMem_tail_support hp (by simpa [hzu] using hzp)
    · exact Walk.IsPath.start_notMem_tail_support hq (by simpa [hzv] using hzq)

theorem Walk.IsPath.takeUntil_append_of_clean
    [DecidableEq V]
    {u v x a : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    {q : G.Walk x a}
    (hq : q.IsPath)
    (hclean :
      forall z : V, z ∈ q.support -> z ∈ p.support -> z = x) :
    ((p.takeUntil x hx).append q).IsPath := by
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    (hp.takeUntil hx) hq ?_
  intro z hz_take hzq
  exact hclean z hzq
    (SimpleGraph.Walk.support_takeUntil_subset p hx hz_take)

theorem Walk.IsPath.reverse_append_dropUntil_of_clean
    [DecidableEq V]
    {u v x a : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    {q : G.Walk x a}
    (hq : q.IsPath)
    (hclean :
      forall z : V, z ∈ q.support -> z ∈ p.support -> z = x) :
    (q.reverse.append (p.dropUntil x hx)).IsPath := by
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    hq.reverse (hp.dropUntil hx) ?_
  intro z hzq_rev hz_drop
  have hzq : z ∈ q.support := by
    rw [SimpleGraph.Walk.support_reverse] at hzq_rev
    exact List.mem_reverse.mp hzq_rev
  have hzp : z ∈ p.support :=
    SimpleGraph.Walk.support_dropUntil_subset p hx hz_drop
  exact hclean z hzq hzp

theorem Walk.InternalVertices.takeUntil_append_boundary_clean
    [DecidableEq V]
    {u v x a : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    {q : G.Walk x a}
    {B : Set V}
    (hprefix_boundary :
      forall z : V,
        z ∈ (p.takeUntil x hx).support -> z ∈ B -> z = u ∨ z = x)
    (hq_boundary : Walk.InternalVertices q ∩ B = ∅)
    (hxB : x ∉ B) :
    Walk.InternalVertices ((p.takeUntil x hx).append q) ∩ B = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzInternal :
      z ∈ Walk.InternalVertices ((p.takeUntil x hx).append q) := hz.1
  have hzB : z ∈ B := hz.2
  have hzSupport := hzInternal.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzSupport
  rcases hzSupport with hz_prefix | hzq
  · rcases hprefix_boundary z hz_prefix hzB with hzu | hzx
    · exact hzInternal.2.1 hzu
    · exact hxB (by simpa [hzx] using hzB)
  · by_cases hzx : z = x
    · exact hxB (by simpa [hzx] using hzB)
    · by_cases hza : z = a
      · exact hzInternal.2.2 hza
      · have hzq_internal : z ∈ Walk.InternalVertices q :=
          ⟨hzq, hzx, hza⟩
        have hnot : z ∉ Walk.InternalVertices q ∩ B := by
          rw [hq_boundary]
          simp
        exact hnot ⟨hzq_internal, hzB⟩

theorem Walk.InternalVertices.reverse_append_dropUntil_boundary_clean
    [DecidableEq V]
    {u v x a : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    {q : G.Walk x a}
    {B : Set V}
    (hdrop_boundary :
      forall z : V,
        z ∈ (p.dropUntil x hx).support -> z ∈ B -> z = x ∨ z = v)
    (hq_boundary : Walk.InternalVertices q ∩ B = ∅)
    (hxB : x ∉ B) :
    Walk.InternalVertices (q.reverse.append (p.dropUntil x hx)) ∩ B =
      ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzInternal :
      z ∈ Walk.InternalVertices (q.reverse.append (p.dropUntil x hx)) :=
    hz.1
  have hzB : z ∈ B := hz.2
  have hzSupport := hzInternal.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzSupport
  rcases hzSupport with hzq_rev | hz_drop
  · have hzq : z ∈ q.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzq_rev
      exact List.mem_reverse.mp hzq_rev
    by_cases hzx : z = x
    · exact hxB (by simpa [hzx] using hzB)
    · by_cases hza : z = a
      · exact hzInternal.2.1 hza
      · have hzq_internal : z ∈ Walk.InternalVertices q :=
          ⟨hzq, hzx, hza⟩
        have hnot : z ∉ Walk.InternalVertices q ∩ B := by
          rw [hq_boundary]
          simp
        exact hnot ⟨hzq_internal, hzB⟩
  · rcases hdrop_boundary z hz_drop hzB with hzx | hzv
    · exact hxB (by simpa [hzx] using hzB)
    · exact hzInternal.2.2 hzv

theorem Walk.internalVertices_append_subset_support_union
    {u v w : V}
    (p : G.Walk u v)
    (q : G.Walk v w) :
    Walk.InternalVertices (p.append q) ⊆
      {x : V | x ∈ p.support} ∪ {x : V | x ∈ q.support} := by
  intro x hx
  have hx_support : x ∈ (p.append q).support := hx.1
  rw [SimpleGraph.Walk.mem_support_append_iff] at hx_support
  exact hx_support

theorem Walk.not_mem_internalVertices_append_of_not_mem_supports
    {u v w x : V}
    {p : G.Walk u v}
    {q : G.Walk v w}
    (hxp : x ∉ p.support)
    (hxq : x ∉ q.support) :
    x ∉ Walk.InternalVertices (p.append q) := by
  intro hx
  rcases Walk.internalVertices_append_subset_support_union p q hx with hx_p | hx_q
  · exact hxp hx_p
  · exact hxq hx_q

theorem Walk.end_not_mem_other_tail_of_support_disjoint
    {ι : Type*}
    {oldBoundary newBoundary : ι -> V}
    (tail : forall i : ι, G.Walk (oldBoundary i) (newBoundary i))
    (hdisjoint :
      forall i j : ι, i ≠ j ->
        Disjoint {v : V | v ∈ (tail i).support}
          {v : V | v ∈ (tail j).support}) :
    forall i j : ι, i ≠ j -> newBoundary i ∉ (tail j).support := by
  intro i j hij hmem
  exact Set.disjoint_left.mp (hdisjoint i j hij)
    (tail i).end_mem_support hmem

theorem connected_induce_exists_path_from_adjacent_support_subset_insert
    [DecidableEq V]
    {A : Set V}
    (hA : (G.induce A).Connected)
    {x y z : V}
    (hxA : x ∉ A)
    (hyA : y ∈ A)
    (hzA : z ∈ A)
    (hxy : G.Adj x y) :
    Exists fun p : G.Walk x z =>
      p.IsPath ∧ forall w : V, w ∈ p.support -> w = x ∨ w ∈ A := by
  obtain ⟨q, hq_path, hq_support⟩ :=
    connected_induce_exists_path_support_subset (G := G) hA hyA hzA
  let p : G.Walk x z := hxy.toWalk.append q
  have hp_path : p.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (SimpleGraph.Walk.IsPath.of_adj hxy) hq_path ?_
    intro w hw_edge hw_q
    have hwA : w ∈ A := hq_support w hw_q
    simp at hw_edge
    rcases hw_edge with rfl | rfl
    · exact False.elim (hxA hwA)
    · rfl
  refine ⟨p, hp_path, ?_⟩
  intro w hw
  change w ∈ (hxy.toWalk.append q).support at hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw_edge | hw_q
  · simp at hw_edge
    rcases hw_edge with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hyA
  · exact Or.inr (hq_support w hw_q)

theorem Subgraph.Connected.exists_path_from_adjacent_support_subset_insert
    {H : G.Subgraph}
    (hH : H.coe.Connected)
    {x y z : V}
    (hxH : x ∉ H.verts)
    (hyH : y ∈ H.verts)
    (hzH : z ∈ H.verts)
    (hxy : G.Adj x y) :
    Exists fun p : G.Walk x z =>
      p.IsPath ∧ forall w : V, w ∈ p.support -> w = x ∨ w ∈ H.verts := by
  obtain ⟨q, hq_path, hq_support⟩ :=
    Subgraph.Connected.exists_path_between_support_subset hH hyH hzH
  let p : G.Walk x z := hxy.toWalk.append q
  have hp_path : p.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (SimpleGraph.Walk.IsPath.of_adj hxy) hq_path ?_
    intro w hw_edge hw_q
    have hwH : w ∈ H.verts := hq_support w hw_q
    simp at hw_edge
    rcases hw_edge with rfl | rfl
    · exact False.elim (hxH hwH)
    · rfl
  refine ⟨p, hp_path, ?_⟩
  intro w hw
  change w ∈ (hxy.toWalk.append q).support at hw
  rw [SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hw_edge | hw_q
  · simp at hw_edge
    rcases hw_edge with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hyH
  · exact Or.inr (hq_support w hw_q)

theorem Walk.IsPath.end_notMem_dropLast_support
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath) :
    v ∉ p.support.dropLast := by
  have hnodup : (p.support.dropLast ++ [v]).Nodup := by
    have hnodup' :
        (p.support.dropLast ++ [p.support.getLast (by simp)]).Nodup := by
      rw [List.dropLast_append_getLast (SimpleGraph.Walk.support_ne_nil p)]
      exact hp.support_nodup
    simpa [SimpleGraph.Walk.getLast_support] using hnodup'
  rw [List.nodup_append] at hnodup
  intro hv
  exact hnodup.2.2 v hv v (by simp) rfl

theorem Walk.IsPath.dart_fst_ne_end_of_mem_darts
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    {d : G.Dart}
    (hd : d ∈ p.darts) :
    d.fst ≠ v := by
  intro hfst
  have hfst_drop : d.fst ∈ p.support.dropLast := by
    rw [← SimpleGraph.Walk.map_fst_darts]
    exact List.mem_map_of_mem hd
  exact Walk.IsPath.end_notMem_dropLast_support hp (by simpa [hfst] using hfst_drop)

theorem Separation.takeUntil_other_support_subset_left_of_separator_pair_of_path_avoids_one
    [DecidableEq V]
    (S : Separation G)
    {x y a b : V}
    (hseparator : S.separator = ({x, y} : Set V))
    (ha_left : a ∈ S.left)
    (hb_right_only : b ∈ S.right \ S.left)
    {p : G.Walk a b}
    (hp : p.IsPath)
    (hy_not_support : y ∉ p.support) :
    forall z : V,
      z ∈ (p.takeUntil x
        (S.walk_hits_other_of_separator_pair_of_avoids_one
          hseparator ha_left hb_right_only p hy_not_support)).support ->
        z ∈ S.left := by
  classical
  let hx : x ∈ p.support :=
    S.walk_hits_other_of_separator_pair_of_avoids_one
      hseparator ha_left hb_right_only p hy_not_support
  let q : G.Walk a x := p.takeUntil x hx
  have hq_path : q.IsPath := by
    simpa [q] using hp.takeUntil hx
  intro z hz
  have hzq : z ∈ q.support := by
    simpa [q, hx] using hz
  by_contra hz_not_left
  let r : G.Walk a z := q.takeUntil z hzq
  obtain ⟨d, hd_mem_r, hd_left, hd_not_left⟩ :=
    r.exists_boundary_dart S.left ha_left hz_not_left
  have hd_mem_q : d ∈ q.darts := by
    exact q.darts_takeUntil_subset hzq hd_mem_r
  have hd_snd_right : d.snd ∈ S.right :=
    S.mem_right_of_not_mem_left hd_not_left
  have hd_fst_right : d.fst ∈ S.right := by
    by_contra hd_fst_not_right
    exact S.no_cross hd_left hd_fst_not_right hd_snd_right hd_not_left d.2
  have hd_fst_sep : d.fst ∈ S.separator := ⟨hd_left, hd_fst_right⟩
  have hfst_pair : d.fst = x ∨ d.fst = y := by
    have : d.fst ∈ ({x, y} : Set V) := by
      simpa [hseparator] using hd_fst_sep
    simpa using this
  have hfst_ne_x : d.fst ≠ x :=
    Walk.IsPath.dart_fst_ne_end_of_mem_darts hq_path hd_mem_q
  have hfst_support_q : d.fst ∈ q.support :=
    q.dart_fst_mem_support_of_mem_darts hd_mem_q
  have hfst_support_p : d.fst ∈ p.support := by
    exact SimpleGraph.Walk.support_takeUntil_subset p hx hfst_support_q
  rcases hfst_pair with hfst_x | hfst_y
  · exact hfst_ne_x hfst_x
  · exact hy_not_support (by simpa [hfst_y] using hfst_support_p)

theorem Separation.exists_left_path_to_other_separator_of_two_connected_pair
    [Fintype V] [DecidableEq V]
    (S : Separation G)
    (h_two_connected : IsTwoConnected G)
    {x y a b : V}
    (hseparator : S.separator = ({x, y} : Set V))
    (ha_left : a ∈ S.left)
    (ha_ne_y : a ≠ y)
    (hb_right_only : b ∈ S.right \ S.left)
    (hb_ne_y : b ≠ y) :
    Exists fun q : G.Walk a x =>
      q.IsPath ∧
        (forall z : V, z ∈ q.support -> z ∈ S.left) ∧
          forall z : V, z ∈ q.support -> z ≠ y := by
  classical
  have hdelete_y_connected : (G.induce ({y} : Set V)ᶜ).Connected :=
    h_two_connected.2 ({y} : Set V) (by simp)
  have ha_compl : a ∈ ({y} : Set V)ᶜ := by
    simpa [Set.mem_singleton_iff] using ha_ne_y
  have hb_compl : b ∈ ({y} : Set V)ᶜ := by
    simpa [Set.mem_singleton_iff] using hb_ne_y
  obtain ⟨p, hp_path, hp_support⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) hdelete_y_connected ha_compl hb_compl
  have hy_not_support : y ∉ p.support := by
    intro hy
    exact (hp_support y hy) (by simp)
  let hx : x ∈ p.support :=
    S.walk_hits_other_of_separator_pair_of_avoids_one
      hseparator ha_left hb_right_only p hy_not_support
  let q : G.Walk a x := p.takeUntil x hx
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q] using hp_path.takeUntil hx
  · intro z hz
    exact
      S.takeUntil_other_support_subset_left_of_separator_pair_of_path_avoids_one
        hseparator ha_left hb_right_only hp_path hy_not_support z (by
          simpa [q, hx] using hz)
  · intro z hz hzy
    have hz_p : z ∈ p.support :=
      SimpleGraph.Walk.support_takeUntil_subset p hx (by simpa [q] using hz)
    exact hy_not_support (by simpa [hzy] using hz_p)

theorem exists_connected_subgraph_avoiding_endpoint_adjacent_to_endpoint
    [DecidableEq V]
    {A : Set V}
    {v1 v2 x y : V}
    (edge : G.Adj v1 v2)
    (hv1_ne_y : v1 ≠ y)
    (qx : G.Walk v1 x)
    (hqx_subset : forall z : V, z ∈ qx.support -> z ∈ A)
    (hqx_avoid_y : forall z : V, z ∈ qx.support -> z ≠ y)
    (qy : G.Walk v2 y)
    (hqy_path : qy.IsPath)
    (hqy_subset : forall z : V, z ∈ qy.support -> z ∈ A) :
    Exists fun H : G.Subgraph =>
      H.coe.Connected ∧
        v1 ∈ H.verts ∧
          x ∈ H.verts ∧
            (v2 = y ∨ v2 ∈ H.verts) ∧
              y ∉ H.verts ∧
                H.verts ⊆ A ∧
                  Exists fun z : V => z ∈ H.verts ∧ G.Adj z y := by
  classical
  by_cases hv2_y : v2 = y
  · refine ⟨qx.toSubgraph, qx.toSubgraph_connected.coe, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact qx.start_mem_verts_toSubgraph
    · exact qx.end_mem_verts_toSubgraph
    · exact Or.inl hv2_y
    · intro hy
      exact hqx_avoid_y y (by
        rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hy) rfl
    · intro z hz
      exact hqx_subset z (by
        rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hz)
    · exact ⟨v1, qx.start_mem_verts_toSubgraph, by simpa [hv2_y] using edge⟩
  · have hqy_not_nil : Not qy.Nil :=
      SimpleGraph.Walk.not_nil_of_ne (p := qy) hv2_y
    have hpen_support : qy.penultimate ∈ qy.support :=
      List.mem_of_mem_dropLast
        (SimpleGraph.Walk.penultimate_mem_dropLast_support hqy_not_nil)
    let qyprefix : G.Walk v2 qy.penultimate :=
      qy.takeUntil qy.penultimate hpen_support
    have hqyprefix_avoid_y :
        forall z : V, z ∈ qyprefix.support -> z ≠ y := by
      intro z hz hzy
      have hy_not :
          y ∉ qyprefix.support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          hqy_path hpen_support
          (by exact (qy.adj_penultimate hqy_not_nil).ne')
      exact hy_not (by simpa [hzy] using hz)
    let ry : G.Walk v1 qy.penultimate :=
      edge.toWalk.append qyprefix
    have hry_avoid_y : forall z : V, z ∈ ry.support -> z ≠ y := by
      intro z hz hzy
      have hz' : z = v1 ∨ z ∈ qyprefix.support := by
        simpa [ry, SimpleGraph.Walk.mem_support_append_iff] using hz
      rcases hz' with hz_edge | hz_prefix
      · exact hv1_ne_y (hz_edge.symm.trans hzy)
      · exact hqyprefix_avoid_y z hz_prefix hzy
    have hqyprefix_subset : forall z : V, z ∈ qyprefix.support -> z ∈ A := by
      intro z hz
      exact hqy_subset z
        (SimpleGraph.Walk.support_takeUntil_subset qy hpen_support
          (by simpa [qyprefix] using hz))
    have hry_subset : forall z : V, z ∈ ry.support -> z ∈ A := by
      intro z hz
      have hz' : z = v1 ∨ z ∈ qyprefix.support := by
        simpa [ry, SimpleGraph.Walk.mem_support_append_iff] using hz
      rcases hz' with hz_v1 | hz_prefix
      · exact hqx_subset z (by simp [hz_v1])
      · exact hqyprefix_subset z hz_prefix
    let H : G.Subgraph := qx.toSubgraph ⊔ ry.toSubgraph
    have hinter : (qx.toSubgraph ⊓ ry.toSubgraph).verts.Nonempty := by
      refine ⟨v1, ?_⟩
      simp [ry]
    have hH_connected_subgraph : H.Connected := by
      exact SimpleGraph.Subgraph.connected_sup
        qx.toSubgraph_connected.preconnected
        ry.toSubgraph_connected.preconnected hinter
    refine ⟨H, hH_connected_subgraph.coe, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [H]
    · simp [H]
    · exact Or.inr (by simp [H, ry, qyprefix])
    · intro hyH
      have hy_cases :
          y ∈ qx.toSubgraph.verts ∨ y ∈ ry.toSubgraph.verts := by
        simpa [H, SimpleGraph.Subgraph.verts_sup] using hyH
      rcases hy_cases with hy_qx | hy_ry
      · exact hqx_avoid_y y
          (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hy_qx) rfl
      · exact hry_avoid_y y
          (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hy_ry) rfl
    · intro z hzH
      have hz_cases :
          z ∈ qx.toSubgraph.verts ∨ z ∈ ry.toSubgraph.verts := by
        simpa [H, SimpleGraph.Subgraph.verts_sup] using hzH
      rcases hz_cases with hz_qx | hz_ry
      · exact hqx_subset z
          (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hz_qx)
      · exact hry_subset z
          (by rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hz_ry)
    · refine ⟨qy.penultimate, ?_, qy.adj_penultimate hqy_not_nil⟩
      simp [H, ry]

theorem Walk.IsPath.end_notMem_walk_dropLast_support
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hnil : Not p.Nil) :
    v ∉ p.dropLast.support := by
  simpa [SimpleGraph.Walk.support_dropLast hnil] using
    (Walk.IsPath.end_notMem_dropLast_support hp)

theorem Walk.mem_dropLast_support_of_mem_support_ne_end
    {u v z : V}
    {p : G.Walk u v}
    (hz : z ∈ p.support)
    (hz_ne_end : z ≠ v) :
    z ∈ p.dropLast.support := by
  have hnot_nil : ¬ p.Nil := by
    intro hnil
    cases hnil
    simp at hz
    exact hz_ne_end hz
  rw [SimpleGraph.Walk.support_dropLast hnot_nil]
  exact List.mem_dropLast_of_mem_of_ne_getLast hz (by
    intro hzlast
    exact hz_ne_end (by
      simpa [SimpleGraph.Walk.getLast_support] using hzlast))

theorem Walk.cycle_middle_subwalk
    {u : V}
    (c : G.Walk u u) :
    c.tail.tail.dropLast.IsSubwalk c := by
  have htail : c.tail.IsSubwalk c := by
    change (c.drop 1).IsSubwalk c
    exact c.isSubwalk_drop 1
  have htailtail : c.tail.tail.IsSubwalk c.tail := by
    change (c.tail.drop 1).IsSubwalk c.tail
    exact c.tail.isSubwalk_drop 1
  have hmiddle : c.tail.tail.dropLast.IsSubwalk c.tail.tail :=
    (SimpleGraph.Walk.isSubwalk_rfl c.tail.tail).dropLast
  exact hmiddle.trans (htailtail.trans htail)


end Schematic.Math.GraphTheory
