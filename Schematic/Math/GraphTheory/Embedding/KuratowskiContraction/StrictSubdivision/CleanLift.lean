import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.TwoTwo

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- A quotient edge path whose endpoints and support avoid the collapsed
vertex lifts to an original source path between the uncollapsed branch
vertices.  This is the ordinary, non-spliced edge case for reconstructing a
strict subdivision after uncontraction. -/
theorem strictSubdivisionModel_collapseEdge_clean_edgePath_lift
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y : W}
    (hxy : K.Adj x y)
    (hx :
      M.branchVertex x ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid : forall t, t ∈ (M.edgePath hxy).support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun q : G.Walk
      (GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex x) hx)
      (GraphContraction.collapseEdgeUncollapse G hab (M.branchVertex y) hy) =>
        q.IsPath ∧
          forall t : V, t ∈ q.support -> t ∉ ({a, b} : Set V) := by
  classical
  let q :=
    GraphContraction.collapseEdgeWalkOutside G hab hx hy
      (M.edgePath hxy) havoid
  have hq : q.IsPath :=
    GraphContraction.collapseEdgeWalkOutside_isPath G hab hx hy
      (M.edgePath hxy) havoid (M.edgePath_isPath hxy)
  have hqout :
      forall t : V, t ∈ q.support -> t ∉ ({a, b} : Set V) := by
    intro t ht
    exact
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab hx hy
        (M.edgePath hxy) havoid ht
  exact ⟨q, hq, hqout⟩

theorem strictSubdivisionModel_collapseEdge_clean_lifts_support_disjoint_of_no_common_endpoint
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {x y x' y' : W}
    (hxy : K.Adj x y)
    (hx'y' : K.Adj x' y')
    (hx :
      M.branchVertex x ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hy :
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hx' :
      M.branchVertex x' ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hy' :
      M.branchVertex y' ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid : forall t, t ∈ (M.edgePath hxy).support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid' : forall t, t ∈ (M.edgePath hx'y').support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hxx' : x ≠ x')
    (hxy' : x ≠ y')
    (hyx' : y ≠ x')
    (hyy' : y ≠ y') :
    Disjoint
      {t : V | t ∈
        (GraphContraction.collapseEdgeWalkOutside G hab hx hy
          (M.edgePath hxy) havoid).support}
      {t : V | t ∈
        (GraphContraction.collapseEdgeWalkOutside G hab hx' hy'
          (M.edgePath hx'y') havoid').support} := by
  classical
  rw [Set.disjoint_left]
  intro t ht ht'
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab hx hy (M.edgePath hxy) havoid ht with
    ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab hx' hy' (M.edgePath hx'y') havoid' ht' with
    ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
  have hqv_rv : qv = rv :=
    GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
      (hqv_eq.trans hrv_eq.symm)
  have hdisj :=
    M.edgePath_support_disjoint_of_no_common_endpoint hxy hx'y'
      hxx' hxy' hyx' hyy'
  exact Set.disjoint_left.mp hdisj hqv_mem
    (by simpa [hqv_rv] using hrv_mem)

theorem strictSubdivisionModel_collapseEdge_clean_lift_no_internal_branch_vertices
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {s t : W}
    (hst : K.Adj s t)
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {z : V}
    (hz : z ∈ Walk.InternalVertices
      (GraphContraction.collapseEdgeWalkOutside G hab
        (hbranch s) (hbranch t) (M.edgePath hst) havoid))
    (w : W) :
    z ≠
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w) (hbranch w) := by
  intro hzw
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab (hbranch s) (hbranch t) (M.edgePath hst) havoid hz.1 with
    ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  have hqv_branch : qv = M.branchVertex w :=
    GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne
      (hbranch w) (hqv_eq.trans hzw)
  have hw_endpoint : w = s ∨ w = t := by
    have hmem : M.branchVertex w ∈ (M.edgePath hst).support := by
      simpa [hqv_branch] using hqv_mem
    exact (M.branchVertex_mem_edgePath_support_iff hst).mp hmem
  rcases hw_endpoint with rfl | rfl
  · exact hz.2.1 hzw
  · exact hz.2.2 hzw

theorem strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    (hbranch :
      forall w : W,
        M.branchVertex w ≠
          (none : (GraphContraction.collapseEdge G hab).Target))
    {s t s' t' : W}
    (hst : K.Adj s t)
    (hs't' : K.Adj s' t')
    (hne : Not ((s = s' ∧ t = t') ∨ (s = t' ∧ t = s')))
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid' : forall qv, qv ∈ (M.edgePath hs't').support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Disjoint
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          (hbranch s) (hbranch t) (M.edgePath hst) havoid))
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          (hbranch s') (hbranch t') (M.edgePath hs't') havoid')) := by
  classical
  rw [Set.disjoint_left]
  intro z hz hz'
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab (hbranch s) (hbranch t) (M.edgePath hst) havoid hz.1 with
    ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab (hbranch s') (hbranch t') (M.edgePath hs't') havoid' hz'.1 with
    ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
  have hqv_rv : qv = rv :=
    GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
      (hqv_eq.trans hrv_eq.symm)
  have hqv_internal : qv ∈ Walk.InternalVertices (M.edgePath hst) := by
    refine ⟨hqv_mem, ?_, ?_⟩
    · intro hqs
      have hz_start :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex s) (hbranch s) := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
            hqv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s) (hbranch s) :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
              (hbranch s) hqs
      exact hz.2.1 hz_start
    · intro hqt
      have hz_end :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t) (hbranch t) := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
            hqv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex t) (hbranch t) :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
              (hbranch t) hqt
      exact hz.2.2 hz_end
  have hrv_internal : rv ∈ Walk.InternalVertices (M.edgePath hs't') := by
    refine ⟨hrv_mem, ?_, ?_⟩
    · intro hrs
      have hz_start :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex s') (hbranch s') := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
            hrv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s') (hbranch s') :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
              (hbranch s') hrs
      exact hz'.2.1 hz_start
    · intro hrt
      have hz_end :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t') (hbranch t') := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
            hrv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex t') (hbranch t') :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
              (hbranch t') hrt
      exact hz'.2.2 hz_end
  exact Set.disjoint_left.mp
    (M.internally_disjoint_edge_paths' hst hs't' hne)
    hqv_internal (by simpa [hqv_rv] using hrv_internal)
end FourColor

end Schematic.Math.GraphTheory
