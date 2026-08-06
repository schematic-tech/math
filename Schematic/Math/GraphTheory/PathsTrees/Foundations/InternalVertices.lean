import Schematic.Math.GraphTheory.PathsTrees.Foundations.SpanningWalks

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
def Walk.InternalVertices {u v : V} (p : G.Walk u v) : Set V :=
  {x : V | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

theorem Subgraph.neighborSet_eq_empty_of_not_mem_verts
    (H : G.Subgraph) {v : V} (hv : v ∉ H.verts) :
    H.neighborSet v = ∅ := by
  ext y
  constructor
  · intro hy
    exact False.elim (hv (H.edge_vert hy))
  · intro hy
    simp at hy

theorem Subgraph.neighborSet_sup_eq_union
    (H K : G.Subgraph) (v : V) :
    (H ⊔ K).neighborSet v = H.neighborSet v ∪ K.neighborSet v := by
  ext y
  simp [SimpleGraph.Subgraph.neighborSet]

theorem Walk.toWalk_neighborSet_start {a b : V} (h : G.Adj a b) :
    h.toWalk.toSubgraph.neighborSet a = {b} := by
  ext y
  simp [SimpleGraph.Subgraph.neighborSet, SimpleGraph.Walk.toSubgraph, Sym2.eq,
    h.ne.symm]

theorem Walk.toWalk_neighborSet_end {a b : V} (h : G.Adj a b) :
    h.toWalk.toSubgraph.neighborSet b = {a} := by
  ext y
  simp [SimpleGraph.Subgraph.neighborSet, SimpleGraph.Walk.toSubgraph, Sym2.eq,
    h.ne]

theorem Walk.Nil.toSubgraph_neighborSet_eq_empty
    {u v x : V}
    {p : G.Walk u v}
    (h : p.Nil) :
    p.toSubgraph.neighborSet x = ∅ := by
  cases h
  simp [SimpleGraph.Walk.toSubgraph]

theorem Walk.IsPath.start_ne_end_of_not_nil
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hnil : ¬ p.Nil) :
    u ≠ v := by
  intro huv
  subst v
  have hp_eq : p = SimpleGraph.Walk.nil :=
    (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp
  exact hnil (hp_eq.symm ▸ SimpleGraph.Walk.Nil.nil)

theorem Walk.internalVertices_subset_support
    {u v : V}
    (p : G.Walk u v) :
    Walk.InternalVertices p ⊆ {x : V | x ∈ p.support} := by
  intro x hx
  exact hx.1

theorem Walk.not_mem_of_internalVertices_disjoint_of_mem_support_ne_endpoints
    {u v x : V}
    {p : G.Walk u v}
    {B : Set V}
    (hclean : Walk.InternalVertices p ∩ B = ∅)
    (hx : x ∈ p.support)
    (hxu : x ≠ u)
    (hxv : x ≠ v) :
    x ∉ B := by
  intro hxB
  have hxInternal : x ∈ Walk.InternalVertices p := ⟨hx, hxu, hxv⟩
  have hnot : x ∉ Walk.InternalVertices p ∩ B := by
    rw [hclean]
    simp
  exact hnot ⟨hxInternal, hxB⟩

theorem Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
    {u v x : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support) :
    x ∈ Walk.InternalVertices p ∨ x = u ∨ x = v := by
  by_cases hxu : x = u
  · exact Or.inr (Or.inl hxu)
  · by_cases hxv : x = v
    · exact Or.inr (Or.inr hxv)
    · exact Or.inl ⟨hx, hxu, hxv⟩

theorem Walk.mem_internalVertices_or_endpoint_of_mem_support
    {u v x : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support) :
    x ∈ Walk.InternalVertices p ∨ x ∈ ({u, v} : Set V) := by
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := p) hx with
    hxint | hxend
  · exact Or.inl hxint
  · rcases hxend with rfl | rfl <;> simp

theorem Walk.not_mem_internalVertices_of_not_mem_support
    {u v x : V}
    {p : G.Walk u v}
    (hx : x ∉ p.support) :
    x ∉ Walk.InternalVertices p := by
  intro hxint
  exact hx hxint.1

theorem Walk.internalVertices_disjoint_of_support_disjoint
    {u v x y : V}
    {p : G.Walk u v}
    {q : G.Walk x y}
    (hdis :
      Disjoint {z : V | z ∈ p.support} {z : V | z ∈ q.support}) :
    Disjoint (Walk.InternalVertices p) (Walk.InternalVertices q) := by
  rw [Set.disjoint_left]
  intro z hz_p hz_q
  exact Set.disjoint_left.mp hdis hz_p.1 hz_q.1

theorem Walk.reachable_induce_of_support_subset
    {A : Set V}
    {u v : V}
    (p : G.Walk u v)
    (hp : forall z : V, z ∈ p.support -> z ∈ A) :
    (G.induce A).Reachable
      ⟨u, hp u p.start_mem_support⟩
      ⟨v, hp v p.end_mem_support⟩ := by
  exact ⟨p.induce A hp⟩

/-- Component supports are closed under walks whose support stays in the
ambient inducing set. -/
theorem induceComponentSupport_mem_of_walk
    {A : Set V}
    (C : (G.induce A).ConnectedComponent)
    {x y : V}
    (hx : x ∈ induceComponentSupport (G := G) C)
    (hyA : y ∈ A)
    (p : G.Walk x y)
    (hpA : forall z : V, z ∈ p.support -> z ∈ A) :
    y ∈ induceComponentSupport (G := G) C := by
  rcases hx with ⟨hxA, hxC⟩
  have hreach :
      (G.induce A).Reachable
        (⟨x, hxA⟩ : A) (⟨y, hyA⟩ : A) :=
    Walk.reachable_induce_of_support_subset p hpA
  have hyC : (⟨y, hyA⟩ : A) ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [← (SimpleGraph.ConnectedComponent.mem_supp_iff
      C (⟨x, hxA⟩ : A)).mp hxC]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  exact ⟨hyA, hyC⟩

theorem Walk.reachable_induce_compl_singleton_of_support_avoids
    {u v x : V}
    (p : G.Walk u v)
    (hp : forall z : V, z ∈ p.support -> z ≠ x) :
    (G.induce ({x} : Set V)ᶜ).Reachable
      ⟨u, by exact hp u p.start_mem_support⟩
      ⟨v, by exact hp v p.end_mem_support⟩ :=
  Walk.reachable_induce_of_support_subset p hp

theorem Walk.mem_internalVertices_reverse_iff
    {u v z : V}
    (p : G.Walk u v) :
    z ∈ Walk.InternalVertices p.reverse ↔ z ∈ Walk.InternalVertices p := by
  constructor
  · rintro ⟨hz_support, hz_ne_v, hz_ne_u⟩
    rw [SimpleGraph.Walk.support_reverse] at hz_support
    exact ⟨List.mem_reverse.mp hz_support, hz_ne_u, hz_ne_v⟩
  · rintro ⟨hz_support, hz_ne_u, hz_ne_v⟩
    exact ⟨by
      rw [SimpleGraph.Walk.support_reverse]
      exact List.mem_reverse.mpr hz_support, hz_ne_v, hz_ne_u⟩

theorem Walk.internalVertices_reverse
    {u v : V}
    (p : G.Walk u v) :
    Walk.InternalVertices p.reverse = Walk.InternalVertices p := by
  ext z
  exact Walk.mem_internalVertices_reverse_iff p

theorem Walk.mem_internalVertices_copy_iff
    {u v u' v' z : V}
    (p : G.Walk u v)
    (hu : u = u')
    (hv : v = v') :
    z ∈ Walk.InternalVertices (p.copy hu hv) ↔
      z ∈ Walk.InternalVertices p := by
  subst u'
  subst v'
  rfl

theorem Walk.internalVertices_copy
    {u v u' v' : V}
    (p : G.Walk u v)
    (hu : u = u')
    (hv : v = v') :
    Walk.InternalVertices (p.copy hu hv) = Walk.InternalVertices p := by
  ext z
  exact Walk.mem_internalVertices_copy_iff p hu hv

theorem Walk.out_mem_support_of_mem_edges
    {u v : V}
    {p : G.Walk u v}
    {e : Sym2 V}
    (he : e ∈ p.edges) :
    e.out.1 ∈ p.support ∧ e.out.2 ∈ p.support := by
  constructor
  · exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
      (Or.inr ⟨e, he, Sym2.out_fst_mem e⟩)
  · exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
      (Or.inr ⟨e, he, Sym2.out_snd_mem e⟩)

theorem Walk.not_mem_internalVertices_toWalk
    {u v z : V}
    (huv : G.Adj u v) :
    z ∉ Walk.InternalVertices huv.toWalk := by
  intro hz
  simp [Walk.InternalVertices] at hz
  rcases hz.1 with hzu | hzv
  · exact hz.2.1 hzu
  · exact hz.2.2 hzv

theorem Walk.mem_internalVertices_two_edge_toWalk_iff
    {u v w z : V}
    (huv : G.Adj u v)
    (hvw : G.Adj v w) :
    z ∈ Walk.InternalVertices (huv.toWalk.append hvw.toWalk) ↔ z = v := by
  constructor
  · intro hz
    simp [Walk.InternalVertices] at hz
    rcases hz.1 with hzu | hzv | hzw
    · exact False.elim (hz.2.1 hzu)
    · exact hzv
    · exact False.elim (hz.2.2 hzw)
  · intro hz
    subst hz
    refine ⟨?_, huv.ne.symm, hvw.ne⟩
    simp

theorem Walk.not_mem_internalVertices_of_length_eq_one
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.length = 1) :
    z ∉ Walk.InternalVertices p := by
  intro hz
  induction p with
  | nil =>
      simp at hp
  | cons huv p ih =>
      cases p with
      | nil =>
          exact Walk.not_mem_internalVertices_toWalk huv hz
      | cons hvw q =>
          simp at hp

theorem Walk.IsPath.support_eq_singleton_of_closed
    {u : V}
    {p : G.Walk u u}
    (hp : p.IsPath) :
    p.support = [u] := by
  have hp_nil : p = SimpleGraph.Walk.nil :=
    (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp
  simp [hp_nil]

theorem Walk.IsPath.mem_support_eq_of_closed
    {u z : V}
    {p : G.Walk u u}
    (hp : p.IsPath)
    (hz : z ∈ p.support) :
    z = u := by
  have hsupport := Walk.IsPath.support_eq_singleton_of_closed hp
  simpa [hsupport] using hz

theorem Walk.IsPath.not_mem_punctured_support_of_closed
    {u z : V}
    {p : G.Walk u u}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzu : z ≠ u) :
    False := by
  exact hzu (Walk.IsPath.mem_support_eq_of_closed hp hz)

theorem Walk.IsPath.end_ne_start_of_mem_support_ne_start
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzu : z ≠ u) :
    v ≠ u := by
  intro hvu
  let q : G.Walk u u := p.copy rfl hvu
  have hq : q.IsPath := by
    simpa [q] using (SimpleGraph.Walk.isPath_copy p rfl hvu).mpr hp
  have hzq : z ∈ q.support := by
    simpa [q] using hz
  exact hzu (Walk.IsPath.mem_support_eq_of_closed hq hzq)

theorem Walk.IsPath.start_ne_end_of_mem_support_ne_start
    {u v z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hz : z ∈ p.support)
    (hzu : z ≠ u) :
    u ≠ v := by
  exact (Walk.IsPath.end_ne_start_of_mem_support_ne_start hp hz hzu).symm

theorem Walk.mem_support_of_mem_internalVertices_concat
    {u v w z : V}
    (p : G.Walk u v)
    (hvw : G.Adj v w)
    (hz : z ∈ Walk.InternalVertices (p.concat hvw)) :
    z ∈ p.support := by
  rcases hz with ⟨hz_support, _hz_ne_u, hz_ne_w⟩
  rw [SimpleGraph.Walk.support_concat] at hz_support
  simp only [List.mem_append, List.mem_singleton] at hz_support
  rcases hz_support with hz_support | hz_eq_w
  · exact hz_support
  · exact False.elim (hz_ne_w hz_eq_w)

theorem Walk.mem_support_and_ne_start_of_mem_internalVertices_concat
    {u v w z : V}
    (p : G.Walk u v)
    (hvw : G.Adj v w)
    (hz : z ∈ Walk.InternalVertices (p.concat hvw)) :
    z ∈ p.support ∧ z ≠ u := by
  exact ⟨Walk.mem_support_of_mem_internalVertices_concat p hvw hz, hz.2.1⟩

theorem Walk.mem_internalVertices_or_eq_end_of_mem_internalVertices_concat
    {u v w z : V}
    (p : G.Walk u v)
    (hvw : G.Adj v w)
    (hz : z ∈ Walk.InternalVertices (p.concat hvw)) :
    z ∈ Walk.InternalVertices p ∨ z = v := by
  have hz_support : z ∈ p.support :=
    Walk.mem_support_of_mem_internalVertices_concat p hvw hz
  by_cases hzv : z = v
  · exact Or.inr hzv
  · exact Or.inl ⟨hz_support, hz.2.1, hzv⟩

theorem Walk.mem_internalVertices_concat_of_mem_internalVertices
    {u v w z : V}
    (p : G.Walk u v)
    (hvw : G.Adj v w)
    (hz : z ∈ Walk.InternalVertices p)
    (hzw : z ≠ w) :
    z ∈ Walk.InternalVertices (p.concat hvw) := by
  rcases hz with ⟨hz_support, hz_ne_u, hz_ne_v⟩
  refine ⟨?_, hz_ne_u, hzw⟩
  rw [SimpleGraph.Walk.support_concat]
  simp [hz_support]

theorem Walk.edge_append_isPath
    {u v w : V}
    {q : G.Walk v w}
    (h : G.Adj u v)
    (hq : q.IsPath)
    (hu : u ∉ q.support) :
    (h.toWalk.append q).IsPath := by
  simpa using (hq.cons hu (h := h))

theorem Walk.edge_append_support_subset_insert
    {u v w : V}
    {q : G.Walk v w}
    (h : G.Adj u v) :
    {z : V | z ∈ (h.toWalk.append q).support} ⊆
      insert u {z : V | z ∈ q.support} := by
  intro z hz
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz_edge | hzq
  · simp at hz_edge
    rcases hz_edge with rfl | rfl
    · simp
    · exact Set.mem_insert_of_mem u q.start_mem_support
  · exact Set.mem_insert_of_mem u hzq

theorem Walk.two_edge_append_isPath
    {u v w x : V}
    (huv : G.Adj u v)
    (hvw : G.Adj v w)
    {q : G.Walk w x}
    (hq : q.IsPath)
    (hu_not : u ∉ q.support)
    (hv_not : v ∉ q.support) :
    ((huv.toWalk.append hvw.toWalk).append q).IsPath := by
  have hinner : (hvw.toWalk.append q).IsPath :=
    Walk.edge_append_isPath hvw hq hv_not
  have hu_not_inner : u ∉ (hvw.toWalk.append q).support := by
    intro hu_mem
    rw [SimpleGraph.Walk.mem_support_append_iff] at hu_mem
    rcases hu_mem with hu_edge | hu_q
    · simp at hu_edge
      rcases hu_edge with h | h
      · exact huv.ne h
      · exact hu_not (by simp [h])
    · exact hu_not hu_q
  have hpath : (huv.toWalk.append (hvw.toWalk.append q)).IsPath :=
    Walk.edge_append_isPath huv hinner hu_not_inner
  simpa [SimpleGraph.Walk.append_assoc] using hpath

theorem Walk.two_edge_append_support_subset_insert
    {u v w x : V}
    (huv : G.Adj u v)
    (hvw : G.Adj v w)
    {q : G.Walk w x} :
    {z : V | z ∈ ((huv.toWalk.append hvw.toWalk).append q).support} ⊆
      insert u (insert v {z : V | z ∈ q.support}) := by
  intro z hz
  rw [← SimpleGraph.Walk.append_assoc] at hz
  have hz' :=
    Walk.edge_append_support_subset_insert (q := hvw.toWalk.append q) huv hz
  rcases hz' with rfl | hz_inner
  · simp
  · have hz'' := Walk.edge_append_support_subset_insert (q := q) hvw hz_inner
    rcases hz'' with rfl | hzq
    · simp
    · exact Set.mem_insert_of_mem u (Set.mem_insert_of_mem v hzq)

/-- Attach a clean tail `q` to a chosen branch endpoint `root`.  If the
attachment vertex is adjacent to `root`, prepend that edge; otherwise use the
edge from `root` to `other` and then the edge from `other` to the attachment.
-/
noncomputable def Walk.branchAttachmentPath
    {root other v endv : V}
    (hroot_other : G.Adj root other)
    (hside : G.Adj root v ∨ G.Adj other v)
    (q : G.Walk v endv) : G.Walk root endv := by
  classical
  by_cases hrootv : G.Adj root v
  · exact hrootv.toWalk.append q
  · exact (hroot_other.toWalk.append (hside.resolve_left hrootv).toWalk).append q

theorem Walk.branchAttachmentPath_isPath
    {root other v endv : V}
    (hroot_other : G.Adj root other)
    (hside : G.Adj root v ∨ G.Adj other v)
    {q : G.Walk v endv}
    (hq : q.IsPath)
    (hroot_not : root ∉ q.support)
    (hother_not : other ∉ q.support) :
    (Walk.branchAttachmentPath hroot_other hside q).IsPath := by
  classical
  by_cases hrootv : G.Adj root v
  · simpa [Walk.branchAttachmentPath, hrootv] using
      Walk.edge_append_isPath hrootv hq hroot_not
  · have hotherv : G.Adj other v := hside.resolve_left hrootv
    simpa [Walk.branchAttachmentPath, hrootv] using
      Walk.two_edge_append_isPath hroot_other hotherv hq hroot_not hother_not

theorem Walk.branchAttachmentPath_support_subset
    {root other v endv : V}
    (hroot_other : G.Adj root other)
    (hside : G.Adj root v ∨ G.Adj other v)
    {q : G.Walk v endv} :
    {z : V | z ∈ (Walk.branchAttachmentPath hroot_other hside q).support} ⊆
      insert root (insert other {z : V | z ∈ q.support}) := by
  classical
  intro z hz
  by_cases hrootv : G.Adj root v
  · have hz' :=
      Walk.edge_append_support_subset_insert (q := q) hrootv
        (by simpa [Walk.branchAttachmentPath, hrootv] using hz)
    rcases hz' with rfl | hzq
    · simp
    · exact Set.mem_insert_of_mem root (Set.mem_insert_of_mem other hzq)
  · have hotherv : G.Adj other v := hside.resolve_left hrootv
    exact
      Walk.two_edge_append_support_subset_insert hroot_other hotherv
        (by simpa [Walk.branchAttachmentPath, hrootv] using hz)

theorem Walk.branchAttachmentPath_direct_support_subset
    {root other v endv : V}
    (hroot_other : G.Adj root other)
    (hrootv : G.Adj root v)
    {q : G.Walk v endv} :
    {z : V |
      z ∈ (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q).support} ⊆
      insert root {z : V | z ∈ q.support} := by
  classical
  intro z hz
  have hz' : z ∈ (hrootv.toWalk.append q).support := by
    simpa [Walk.branchAttachmentPath, hrootv] using hz
  exact Walk.edge_append_support_subset_insert (q := q) hrootv hz'

theorem Walk.branchAttachmentPath_direct_other_not_mem_internal
    {root other v endv : V}
    (hroot_other : G.Adj root other)
    (hrootv : G.Adj root v)
    {q : G.Walk v endv}
    (hother_not : other ∉ q.support) :
    other ∉
      Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q) := by
  intro hother
  have hcases :
      other = root ∨ other ∈ q.support := by
    have hsupp :=
      Walk.branchAttachmentPath_direct_support_subset
        hroot_other hrootv hother.1
    simpa using hsupp
  rcases hcases with h | h
  · exact hroot_other.ne h.symm
  · exact hother_not h

theorem Walk.branchAttachmentPath_direct_internalVertices_subset_tail
    {root other v endv : V}
    (hroot_other : G.Adj root other)
    (hrootv : G.Adj root v)
    {q : G.Walk v endv} :
    Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv) q) ⊆
      {z : V | z ∈ q.support} := by
  intro z hz
  have hz_cases : z = root ∨ z ∈ q.support := by
    have hsupp :=
      Walk.branchAttachmentPath_direct_support_subset
        hroot_other hrootv hz.1
    simpa using hsupp
  rcases hz_cases with hroot | hzq
  · exact False.elim (hz.2.1 hroot)
  · exact hzq

theorem Walk.branchAttachmentPath_direct_direct_internally_disjoint
    {root₁ other₁ root₂ other₂ v₁ v₂ end₁ end₂ : V}
    (hroot_other₁ : G.Adj root₁ other₁)
    (hrootv₁ : G.Adj root₁ v₁)
    (hroot_other₂ : G.Adj root₂ other₂)
    (hrootv₂ : G.Adj root₂ v₂)
    {q₁ : G.Walk v₁ end₁}
    {q₂ : G.Walk v₂ end₂}
    (hdisj :
      Disjoint {z : V | z ∈ q₁.support} {z : V | z ∈ q₂.support}) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other₁ (Or.inl hrootv₁) q₁))
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other₂ (Or.inl hrootv₂) q₂)) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  exact Set.disjoint_left.mp hdisj
    (Walk.branchAttachmentPath_direct_internalVertices_subset_tail
      hroot_other₁ hrootv₁ hz₁)
    (Walk.branchAttachmentPath_direct_internalVertices_subset_tail
      hroot_other₂ hrootv₂ hz₂)

theorem Walk.branchAttachmentPath_internal_disjoint_of_left_direct
    {root other v₁ v₂ end₁ end₂ : V}
    (hroot_other : G.Adj root other)
    (hrootv₁ : G.Adj root v₁)
    (hside₂ : G.Adj root v₂ ∨ G.Adj other v₂)
    {q₁ : G.Walk v₁ end₁}
    {q₂ : G.Walk v₂ end₂}
    (hq₁_outside :
      forall z : V, z ∈ q₁.support -> z ∉ ({root, other} : Set V))
    (hdisj :
      Disjoint {z : V | z ∈ q₁.support} {z : V | z ∈ q₂.support}) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv₁) q₁))
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other hside₂ q₂)) := by
  classical
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have hz₁_cases : z = root ∨ z ∈ q₁.support := by
    have hz_support :=
      Walk.edge_append_support_subset_insert (q := q₁) hrootv₁
        (by simpa [Walk.branchAttachmentPath, hrootv₁] using hz₁.1)
    simpa using hz_support
  rcases hz₁_cases with rfl | hzq₁
  · exact hz₁.2.1 rfl
  · have hz₂_cases :
        z = root ∨ z = other ∨ z ∈ q₂.support := by
      have hz_support :=
        Walk.branchAttachmentPath_support_subset hroot_other hside₂ hz₂.1
      simpa using hz_support
    have hz_mem_root : z = root -> z ∈ ({root, other} : Set V) := by
      intro h
      simp [h]
    have hz_mem_other : z = other -> z ∈ ({root, other} : Set V) := by
      intro h
      simp [h]
    rcases hz₂_cases with hzroot | hzother | hzq₂
    · exact hq₁_outside z hzq₁ (hz_mem_root hzroot)
    · exact hq₁_outside z hzq₁ (hz_mem_other hzother)
    · exact Set.disjoint_left.mp hdisj hzq₁ hzq₂

theorem Walk.branchAttachmentPath_internal_disjoint_of_right_direct
    {root other v₁ v₂ end₁ end₂ : V}
    (hroot_other : G.Adj root other)
    (hside₁ : G.Adj root v₁ ∨ G.Adj other v₁)
    (hrootv₂ : G.Adj root v₂)
    {q₁ : G.Walk v₁ end₁}
    {q₂ : G.Walk v₂ end₂}
    (hq₂_outside :
      forall z : V, z ∈ q₂.support -> z ∉ ({root, other} : Set V))
    (hdisj :
      Disjoint {z : V | z ∈ q₁.support} {z : V | z ∈ q₂.support}) :
    Disjoint
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other hside₁ q₁))
      (Walk.InternalVertices
        (Walk.branchAttachmentPath hroot_other (Or.inl hrootv₂) q₂)) := by
  exact
    (Walk.branchAttachmentPath_internal_disjoint_of_left_direct
      hroot_other hrootv₂ hside₁ hq₂_outside hdisj.symm).symm

/-- The short source walk replacing an internal occurrence of a contracted
edge.  It connects the two source-side attachment vertices through `a`,
through `b`, or through the edge `ab`, depending on the decoded sides. -/
noncomputable def Walk.pairAttachmentBridge
    {a b vL vR : V}
    (hab : G.Adj a b)
    (hsideL : G.Adj a vL ∨ G.Adj b vL)
    (hsideR : G.Adj a vR ∨ G.Adj b vR) :
    G.Walk vL vR := by
  classical
  by_cases haL : G.Adj a vL
  · by_cases haR : G.Adj a vR
    · exact haL.symm.toWalk.append haR.toWalk
    · exact (haL.symm.toWalk.append hab.toWalk).append
        (hsideR.resolve_left haR).toWalk
  · have hbL : G.Adj b vL := hsideL.resolve_left haL
    by_cases haR : G.Adj a vR
    · exact (hbL.symm.toWalk.append hab.symm.toWalk).append haR.toWalk
    · exact hbL.symm.toWalk.append (hsideR.resolve_left haR).toWalk

theorem Walk.pairAttachmentBridge_support_subset
    {a b vL vR : V}
    (hab : G.Adj a b)
    (hsideL : G.Adj a vL ∨ G.Adj b vL)
    (hsideR : G.Adj a vR ∨ G.Adj b vR) :
    {z : V | z ∈ (Walk.pairAttachmentBridge hab hsideL hsideR).support} ⊆
      ({a, b, vL, vR} : Set V) := by
  classical
  intro z hz
  by_cases haL : G.Adj a vL
  · by_cases haR : G.Adj a vR
    · simp [Walk.pairAttachmentBridge, haL, haR] at hz ⊢
      tauto
    · simp [Walk.pairAttachmentBridge, haL, haR] at hz ⊢
      tauto
  · have hbL : G.Adj b vL := hsideL.resolve_left haL
    by_cases haR : G.Adj a vR
    · simp [Walk.pairAttachmentBridge, haL, haR] at hz ⊢
      tauto
    · simp [Walk.pairAttachmentBridge, haL, haR] at hz ⊢
      tauto

theorem Walk.pairAttachmentBridge_isPath
    {a b vL vR : V}
    (hab : G.Adj a b)
    (hsideL : G.Adj a vL ∨ G.Adj b vL)
    (hsideR : G.Adj a vR ∨ G.Adj b vR)
    (hvL : vL ∉ ({a, b} : Set V))
    (hvR : vR ∉ ({a, b} : Set V))
    (hne : vL ≠ vR) :
    (Walk.pairAttachmentBridge hab hsideL hsideR).IsPath := by
  classical
  by_cases haL : G.Adj a vL
  · by_cases haR : G.Adj a vR
    · have hvL_not :
          vL ∉ (SimpleGraph.Walk.nil : G.Walk vR vR).support := by
        simp [hne]
      have ha_not :
          a ∉ (SimpleGraph.Walk.nil : G.Walk vR vR).support := by
        simp
        intro haeq
        exact hvR (by simp [haeq])
      simpa [Walk.pairAttachmentBridge, haL, haR] using
        Walk.two_edge_append_isPath haL.symm haR
          (q := (SimpleGraph.Walk.nil : G.Walk vR vR)) (by simp)
          hvL_not ha_not
    · have hbR : G.Adj b vR := hsideR.resolve_left haR
      have hvL_not : vL ∉ hbR.toWalk.support := by
        intro hmem
        simp at hmem
        rcases hmem with h | h
        · exact hvL (by simp [h])
        · exact hne h
      have ha_not : a ∉ hbR.toWalk.support := by
        intro hmem
        simp at hmem
        rcases hmem with h | h
        · exact hab.ne h
        · exact hvR (by simp [h])
      simpa [Walk.pairAttachmentBridge, haL, haR] using
        Walk.two_edge_append_isPath haL.symm hab (q := hbR.toWalk)
          (SimpleGraph.Walk.IsPath.of_adj hbR) hvL_not ha_not
  · have hbL : G.Adj b vL := hsideL.resolve_left haL
    by_cases haR : G.Adj a vR
    · have hvL_not : vL ∉ haR.toWalk.support := by
        intro hmem
        simp at hmem
        rcases hmem with h | h
        · exact hvL (by simp [h])
        · exact hne h
      have hb_not : b ∉ haR.toWalk.support := by
        intro hmem
        simp at hmem
        rcases hmem with h | h
        · exact hab.ne h.symm
        · exact hvR (by simp [h])
      simpa [Walk.pairAttachmentBridge, haL, haR] using
        Walk.two_edge_append_isPath hbL.symm hab.symm (q := haR.toWalk)
          (SimpleGraph.Walk.IsPath.of_adj haR) hvL_not hb_not
    · have hbR : G.Adj b vR := hsideR.resolve_left haR
      have hvL_not :
          vL ∉ (SimpleGraph.Walk.nil : G.Walk vR vR).support := by
        simp [hne]
      have hb_not :
          b ∉ (SimpleGraph.Walk.nil : G.Walk vR vR).support := by
        simp
        intro hbeq
        exact hvR (by simp [hbeq])
      simpa [Walk.pairAttachmentBridge, haL, haR] using
        Walk.two_edge_append_isPath hbL.symm hbR
          (q := (SimpleGraph.Walk.nil : G.Walk vR vR)) (by simp)
          hvL_not hb_not

theorem Walk.edge_append_dropUntil_isPath
    [DecidableEq V]
    {a b u x : V}
    {p : G.Walk a b}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hux : G.Adj u x)
    (hu : u ∉ p.support) :
    (hux.toWalk.append (p.dropUntil x hx)).IsPath := by
  have hdrop : (p.dropUntil x hx).IsPath := by
    exact SimpleGraph.Walk.isPath_of_isSubwalk
      (SimpleGraph.Walk.isSubwalk_dropUntil p hx) hp
  have hu_drop : u ∉ (p.dropUntil x hx).support := by
    intro h
    exact hu (SimpleGraph.Walk.support_dropUntil_subset p hx h)
  exact Walk.edge_append_isPath hux hdrop hu_drop

theorem Walk.edge_append_dropUntil_support_subset_insert
    [DecidableEq V]
    {a b u x : V}
    {p : G.Walk a b}
    (hx : x ∈ p.support)
    (hux : G.Adj u x) :
    {z : V | z ∈ (hux.toWalk.append (p.dropUntil x hx)).support} ⊆
      insert u {z : V | z ∈ p.support} := by
  intro z hz
  have hz' :=
    Walk.edge_append_support_subset_insert (q := p.dropUntil x hx) hux hz
  rcases hz' with rfl | hz_drop
  · simp
  · exact Set.mem_insert_of_mem u
      (SimpleGraph.Walk.support_dropUntil_subset p hx hz_drop)


end Schematic.Math.GraphTheory
