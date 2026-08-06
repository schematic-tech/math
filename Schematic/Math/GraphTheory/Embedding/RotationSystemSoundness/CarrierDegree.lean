import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.SupportInducedRotation

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness
theorem orderedStrictSubdivisionCarrier_neighbor_mem_edgePath
    {W : Type u} {V : Type v}
    [LinearOrder W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    {x y : W} (hxy : H.Adj x y)
    {v z : V}
    (hv : v ∈ Walk.InternalVertices
      ((orderedStrictSubdivisionModel M).edgePath hxy))
    (hvz : (strictSubdivisionCarrierGraph
      (orderedStrictSubdivisionModel M)).Adj v z) :
    ((orderedStrictSubdivisionModel M).edgePath hxy).toSubgraph.Adj v z := by
  let N := orderedStrictSubdivisionModel M
  rcases (strictSubdivisionCarrierGraph_adj_iff N).mp hvz with
    ⟨x', y', hx'y', hvz'⟩
  have hv' : v ∈ (N.edgePath hx'y').support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (N.edgePath hx'y').toSubgraph.edge_vert hvz'
  by_cases hsame :
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')
  · rcases hsame with ⟨rfl, rfl⟩ | ⟨hxy', hyx'⟩
    · simpa only [N, Subsingleton.elim hx'y' hxy] using hvz'
    · subst y'
      subst x'
      have hpath : N.edgePath hx'y' = (N.edgePath hxy).reverse := by
        simpa only [N, Subsingleton.elim hx'y' hxy.symm] using
          orderedStrictSubdivisionModel_edgePath_symm M hxy
      simpa only [hpath, SimpleGraph.Walk.toSubgraph_reverse] using hvz'
  · rcases
        N.edgePath_support_inter_subset_common_branch_vertices
          hxy hx'y' hsame hv.1 hv' with
      ⟨w, _hw, _hw', hvw⟩
    exact False.elim
      (N.no_internal_branch_vertices' hxy hv w hvw)

theorem orderedStrictSubdivisionCarrier_internal_degree_eq_two
    {W : Type u} {V : Type v}
    [LinearOrder W]
    [Fintype V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    [DecidableRel (strictSubdivisionCarrierGraph
      (orderedStrictSubdivisionModel M)).Adj]
    {x y : W} (hxy : H.Adj x y)
    {v : V}
    (hv : v ∈ Walk.InternalVertices
      ((orderedStrictSubdivisionModel M).edgePath hxy)) :
    (strictSubdivisionCarrierGraph
      (orderedStrictSubdivisionModel M)).degree v = 2 := by
  classical
  let N := orderedStrictSubdivisionModel M
  let C := strictSubdivisionCarrierGraph N
  have hneighbors :
      C.neighborSet v = (N.edgePath hxy).toSubgraph.neighborSet v := by
    ext z
    simp only [SimpleGraph.mem_neighborSet]
    constructor
    · exact orderedStrictSubdivisionCarrier_neighbor_mem_edgePath M hxy hv
    · intro hvz
      exact (strictSubdivisionCarrierGraph_adj_iff N).mpr
        ⟨x, y, hxy, hvz⟩
  have hpathNeighbors :
      ((N.edgePath hxy).toSubgraph.neighborSet v).ncard = 2 :=
    Schematic.Math.GraphTheory.Walk.IsPath.ncard_neighborSet_toSubgraph_eq_two_of_mem_internalVertices
      (N.edgePath_isPath hxy) hv
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard, hneighbors]
  exact hpathNeighbors


end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
