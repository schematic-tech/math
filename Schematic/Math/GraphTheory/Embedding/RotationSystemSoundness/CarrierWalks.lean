import Schematic.Math.GraphTheory.Subdivisions

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness

/-- Choose one of the two orientations of every source edge uniformly.  The
raw `StrictSubdivisionModel` interface deliberately does not identify the
walks supplied for `hxy` and `hxy.symm`; this normalization makes the reverse
orientation definitionally the reverse of the chosen walk. -/
noncomputable def orderedStrictSubdivisionModel
    {W : Type u} {V : Type v}
    [LinearOrder W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) :
    StrictSubdivisionModel H G where
  toSubdivisionModel.branchVertex := M.branchVertex
  toSubdivisionModel.branchVertex_injective := M.branchVertex_injective
  toSubdivisionModel.edgePath {x y} hxy :=
    if x < y then M.edgePath hxy else (M.edgePath hxy.symm).reverse
  toSubdivisionModel.edgePath_isPath {x y} hxy := by
    split
    · exact M.edgePath_isPath hxy
    · exact (M.edgePath_isPath hxy.symm).reverse
  toSubdivisionModel.no_internal_branch_vertices :=
    M.no_internal_branch_vertices
  toSubdivisionModel.internally_disjoint_edge_paths :=
    M.internally_disjoint_edge_paths
  no_internal_branch_vertices' := by
    intro x y hxy z hz w hzw
    change z ∈ Walk.InternalVertices
      (if x < y then M.edgePath hxy else (M.edgePath hxy.symm).reverse) at hz
    change z = M.branchVertex w at hzw
    split at hz
    · exact M.no_internal_branch_vertices' hxy hz w hzw
    · exact M.no_internal_branch_vertices' hxy.symm
        ((Walk.mem_internalVertices_reverse_iff _).mp hz) w hzw
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    change Disjoint
      (Walk.InternalVertices
        (if x < y then M.edgePath hxy else (M.edgePath hxy.symm).reverse))
      (Walk.InternalVertices
        (if x' < y' then M.edgePath hx'y'
          else (M.edgePath hx'y'.symm).reverse))
    split <;> split
    · exact M.internally_disjoint_edge_paths' hxy hx'y' hne
    · simpa only [Walk.internalVertices_reverse] using
        M.internally_disjoint_edge_paths' hxy hx'y'.symm (by aesop)
    · simpa only [Walk.internalVertices_reverse] using
        M.internally_disjoint_edge_paths' hxy.symm hx'y' (by aesop)
    · simpa only [Walk.internalVertices_reverse] using
        M.internally_disjoint_edge_paths' hxy.symm hx'y'.symm (by aesop)

theorem orderedStrictSubdivisionModel_edgePath_symm
    {W : Type u} {V : Type v}
    [LinearOrder W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W} (hxy : H.Adj x y) :
    (orderedStrictSubdivisionModel M).edgePath hxy.symm =
      ((orderedStrictSubdivisionModel M).edgePath hxy).reverse := by
  by_cases hlt : x < y
  · have hnlt : ¬ y < x := not_lt_of_ge (le_of_lt hlt)
    simp [orderedStrictSubdivisionModel, hlt, hnlt]
  · have hyx : y < x :=
      lt_of_le_of_ne (le_of_not_gt hlt) hxy.ne.symm
    simp [orderedStrictSubdivisionModel, hlt, hyx]

/-- The same-vertex graph consisting exactly of the selected subdivision
paths.  Isolated ambient vertices remain in the type but not in its support. -/
def strictSubdivisionCarrierGraph
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) : SimpleGraph V :=
  ⨆ x : W, ⨆ y : W, ⨆ hxy : H.Adj x y,
    (M.edgePath hxy).toSubgraph.spanningCoe

theorem strictSubdivisionCarrierGraph_adj_iff
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) {a b : V} :
    (strictSubdivisionCarrierGraph M).Adj a b ↔
      Exists fun x : W => Exists fun y : W =>
        Exists fun hxy : H.Adj x y =>
          (M.edgePath hxy).toSubgraph.Adj a b := by
  simp [strictSubdivisionCarrierGraph]

theorem strictSubdivisionCarrierGraph_le
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) :
    strictSubdivisionCarrierGraph M ≤ G := by
  apply iSup_le
  intro x
  apply iSup_le
  intro y
  apply iSup_le
  intro hxy
  exact (M.edgePath hxy).toSubgraph.spanningCoe_le

theorem edgePath_edges_mem_strictSubdivisionCarrierGraph
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W} (hxy : H.Adj x y) (e : Sym2 V)
    (he : e ∈ (M.edgePath hxy).edges) :
    e ∈ (strictSubdivisionCarrierGraph M).edgeSet := by
  revert he
  refine Sym2.ind ?_ e
  intro a b hab
  rw [SimpleGraph.mem_edgeSet]
  refine (strictSubdivisionCarrierGraph_adj_iff M).mpr ⟨x, y, hxy, ?_⟩
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact hab

theorem edgePath_toSubgraph_spanningCoe_le_carrier
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W} (hxy : H.Adj x y) :
    (M.edgePath hxy).toSubgraph.spanningCoe ≤
      strictSubdivisionCarrierGraph M := by
  intro a b hab
  exact (strictSubdivisionCarrierGraph_adj_iff M).mpr
    ⟨x, y, hxy, hab⟩

theorem edgePath_support_subset_carrier_support
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W} (hxy : H.Adj x y) :
    {z : V | z ∈ (M.edgePath hxy).support} ⊆
      (strictSubdivisionCarrierGraph M).support := by
  intro z hz
  have hnotNil : ¬ (M.edgePath hxy).Nil := by
    intro hnil
    have hends : M.branchVertex x = M.branchVertex y := hnil.eq
    exact hxy.ne (M.branchVertex_injective hends)
  rcases
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil
        hnotNil).mp hz with
    ⟨e, he, hze⟩
  have heCarrier : e ∈ (strictSubdivisionCarrierGraph M).edgeSet :=
    edgePath_edges_mem_strictSubdivisionCarrierGraph M hxy e he
  revert hze heCarrier
  refine Sym2.ind ?_ e
  intro a b hz hab
  rw [Sym2.mem_iff] at hz
  rw [SimpleGraph.mem_edgeSet] at hab
  rw [SimpleGraph.mem_support]
  rcases hz with rfl | rfl
  · exact ⟨b, hab⟩
  · exact ⟨a, hab.symm⟩

noncomputable def edgeRestrictStrictSubdivisionCarrier
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) :
    StrictSubdivisionModel H (strictSubdivisionCarrierGraph M) :=
  M.edgeRestrict (edgePath_edges_mem_strictSubdivisionCarrierGraph M)

/-- Replace every edge of a source walk by its selected subdivision path. -/
noncomputable def strictSubdivisionLiftWalk
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G) :
    forall {a b : W}, H.Walk a b ->
      G.Walk (M.branchVertex a) (M.branchVertex b)
  | _, _, .nil => .nil
  | _, _, .cons hab p =>
      (M.edgePath hab).append (strictSubdivisionLiftWalk M p)

theorem branchVertex_mem_strictSubdivisionLiftWalk_support_iff
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {a b c : W} (p : H.Walk a b) :
    M.branchVertex c ∈ (strictSubdivisionLiftWalk M p).support ↔
      c ∈ p.support := by
  induction p with
  | nil =>
      simp only [strictSubdivisionLiftWalk,
        SimpleGraph.Walk.support_nil, List.mem_singleton]
      exact M.branchVertex_injective.eq_iff
  | cons hab p ih =>
      rw [strictSubdivisionLiftWalk,
        SimpleGraph.Walk.mem_support_append_iff,
        M.branchVertex_mem_edgePath_support_iff hab, ih]
      rw [SimpleGraph.Walk.support_cons, List.mem_cons]
      constructor
      · rintro ((rfl | rfl) | hc)
        · exact Or.inl rfl
        · exact Or.inr p.start_mem_support
        · exact Or.inr hc
      · rintro (rfl | hc)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hc

/-- An internal vertex of one selected path can lie on another selected path
only when both paths represent the same unoriented source edge. -/
theorem source_edge_eq_of_internal_mem_edgePath_support
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a b : W}
    (hxy : H.Adj x y) (hab : H.Adj a b)
    {z : V}
    (hz : z ∈ Walk.InternalVertices (M.edgePath hxy))
    (hz' : z ∈ (M.edgePath hab).support) :
    s(x, y) = s(a, b) := by
  by_contra hneEdge
  have hne :
      Not ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
    simpa [Sym2.eq_iff] using hneEdge
  rcases
      M.edgePath_support_inter_subset_common_branch_vertices
        hxy hab hne hz.1 hz' with
    ⟨w, _hwxy, _hwab, hzw⟩
  exact M.no_internal_branch_vertices' hxy hz w hzw

/-- Internal subdivision vertices in a lifted walk come precisely from source
edges used by that walk.  Only the forward implication is needed below. -/
theorem source_edge_mem_of_internal_mem_strictSubdivisionLiftWalk_support
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y a b : W}
    (hxy : H.Adj x y)
    {z : V}
    (hz : z ∈ Walk.InternalVertices (M.edgePath hxy))
    (p : H.Walk a b)
    (hzp : z ∈ (strictSubdivisionLiftWalk M p).support) :
    s(x, y) ∈ p.edges := by
  induction p with
  | nil =>
      simp only [strictSubdivisionLiftWalk,
        SimpleGraph.Walk.support_nil, List.mem_singleton] at hzp
      exact False.elim
        (M.no_internal_branch_vertices' hxy hz _ hzp)
  | cons hab p ih =>
      rw [strictSubdivisionLiftWalk,
        SimpleGraph.Walk.mem_support_append_iff] at hzp
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons]
      rcases hzp with hzhead | hztail
      · exact Or.inl
          (source_edge_eq_of_internal_mem_edgePath_support
            M hxy hab hz hzhead)
      · exact Or.inr (ih hztail)

end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
