import Schematic.Math.GraphTheory.Subdivisions.K5TrianglePaths

/-! Degree consequences of K5 and K3,3 subdivision models. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem K33Graph_exists_adj (x : K33Vertex) :
    Exists fun y : K33Vertex => K33Graph.Adj x y := by
  cases x with
  | inl i =>
      exact ⟨Sum.inr 0, by simp [K33Graph]⟩
  | inr i =>
      exact ⟨Sum.inl 0, by simp [K33Graph]⟩

theorem K5Graph_degree (x : Fin 5) :
    K5Graph.degree x = 4 := by
  simp [Fintype.card_fin]

theorem K33Graph_degree (x : K33Vertex)
    [Fintype (K33Graph.neighborSet x)] :
    K33Graph.degree x = 3 := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  cases x with
  | inl i =>
      let e : K33Graph.neighborSet (Sum.inl i) ≃ Fin 3 := {
        toFun := fun v => by
          rcases v with ⟨v, hv⟩
          cases v with
          | inl j => cases hv
          | inr j => exact j
        invFun := fun j => ⟨Sum.inr j, by simp [SimpleGraph.neighborSet, K33Graph]⟩
        left_inv := by
          intro v
          rcases v with ⟨v, hv⟩
          cases v with
          | inl j => cases hv
          | inr j => rfl
        right_inv := fun j => rfl }
      simpa using Fintype.card_congr e
  | inr i =>
      let e : K33Graph.neighborSet (Sum.inr i) ≃ Fin 3 := {
        toFun := fun v => by
          rcases v with ⟨v, hv⟩
          cases v with
          | inl j => exact j
          | inr j => cases hv
        invFun := fun j => ⟨Sum.inl j, by simp [SimpleGraph.neighborSet, K33Graph]⟩
        left_inv := by
          intro v
          rcases v with ⟨v, hv⟩
          cases v with
          | inl j => rfl
          | inr j => cases hv
        right_inv := fun j => rfl }
      simpa using Fintype.card_congr e

theorem StrictSubdivisionModel.K5_branchVertex_ne_of_degree_le_three
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v : V}
    (hdegree : G.degree v <= 3)
    (x : Fin 5) :
    M.branchVertex x ≠ v := by
  classical
  refine M.branchVertex_ne_of_host_degree_lt_source_degree x ?_
  rw [K5Graph_degree x]
  omega

theorem StrictSubdivisionModel.K33_branchVertex_ne_of_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v : V}
    (hdegree : G.degree v <= 2)
    (x : K33Vertex) :
    M.branchVertex x ≠ v := by
  classical
  refine M.branchVertex_ne_of_host_degree_lt_source_degree x ?_
  rw [K33Graph_degree x]
  omega

theorem StrictSubdivisionModel.K5_internal_of_edgePath_support_of_degree_le_three
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v : V}
    (hdegree : G.degree v <= 3)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support) :
    v ∈ Walk.InternalVertices (M.edgePath hxy) := by
  classical
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := M.edgePath hxy) hv with
    hv_internal | hv_endpoint
  · exact hv_internal
  · rcases hv_endpoint with hv_start | hv_end
    · exact False.elim
        ((M.K5_branchVertex_ne_of_degree_le_three hdegree x) hv_start.symm)
    · exact False.elim
        ((M.K5_branchVertex_ne_of_degree_le_three hdegree y) hv_end.symm)

theorem StrictSubdivisionModel.K33_internal_of_edgePath_support_of_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v : V}
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support) :
    v ∈ Walk.InternalVertices (M.edgePath hxy) := by
  classical
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := M.edgePath hxy) hv with
    hv_internal | hv_endpoint
  · exact hv_internal
  · rcases hv_endpoint with hv_start | hv_end
    · exact False.elim
        ((M.K33_branchVertex_ne_of_degree_le_two hdegree x) hv_start.symm)
    · exact False.elim
        ((M.K33_branchVertex_ne_of_degree_le_two hdegree y) hv_end.symm)

theorem StrictSubdivisionModel.K5_neighbor_mem_edgePath_toSubgraph_of_support_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hvw : G.Adj v w) :
    w ∈ (M.edgePath hxy).toSubgraph.neighborSet v := by
  classical
  have hv_internal :
      v ∈ Walk.InternalVertices (M.edgePath hxy) :=
    M.K5_internal_of_edgePath_support_of_degree_le_three
      (by omega) hxy hv
  exact
    M.neighbor_mem_edgePath_toSubgraph_of_internal_degree_le_two
      hxy hv_internal hdegree hvw

theorem StrictSubdivisionModel.K5_incident_edge_mem_edgePath_edges_of_support_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hvw : G.Adj v w) :
    s(v, w) ∈ (M.edgePath hxy).edges := by
  have hw_path :
      w ∈ (M.edgePath hxy).toSubgraph.neighborSet v :=
    M.K5_neighbor_mem_edgePath_toSubgraph_of_support_degree_le_two
      hdegree hxy hv hvw
  simpa using
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges
      (p := M.edgePath hxy)).mp hw_path

theorem StrictSubdivisionModel.K5_idxOf_incident_edge_eq_succ_or_of_support_degree_le_two
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hvw : G.Adj v w) :
    (M.edgePath hxy).support.idxOf w =
        (M.edgePath hxy).support.idxOf v + 1 ∨
      (M.edgePath hxy).support.idxOf v =
        (M.edgePath hxy).support.idxOf w + 1 := by
  have hedge :
      s(v, w) ∈ (M.edgePath hxy).edges :=
    M.K5_incident_edge_mem_edgePath_edges_of_support_degree_le_two
      hdegree hxy hv hvw
  have hw : w ∈ (M.edgePath hxy).support := by
    exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
      (Or.inr ⟨s(v, w), hedge, by simp⟩)
  exact
    Walk.IsPath.idxOf_eq_succ_or_of_mem_edges
      (M.edgePath_isPath hxy) hedge

theorem StrictSubdivisionModel.K5_edgePath_same_or_reverse_of_degree_le_two_mem_support
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v : V}
    (hdegree : G.degree v <= 2)
    {x y x' y' : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hx'y' : K5Graph.Adj x' y')
    (hv : v ∈ (M.edgePath hxy).support)
    (hv' : v ∈ (M.edgePath hx'y').support) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  classical
  by_contra hne
  have hv_internal :
      v ∈ Walk.InternalVertices (M.edgePath hxy) :=
    M.K5_internal_of_edgePath_support_of_degree_le_three
      (by omega) hxy hv
  have hv'_internal :
      v ∈ Walk.InternalVertices (M.edgePath hx'y') :=
    M.K5_internal_of_edgePath_support_of_degree_le_three
      (by omega) hx'y' hv'
  exact
    Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hxy hx'y' hne)
      hv_internal hv'_internal

theorem StrictSubdivisionModel.K5_not_mem_other_edgePath_support_of_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v : V}
    (hdegree : G.degree v <= 2)
    {x y x' y' : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hx'y' : K5Graph.Adj x' y')
    (hv : v ∈ (M.edgePath hxy).support)
    (hother : Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) :
    v ∉ (M.edgePath hx'y').support := by
  intro hv'
  exact hother
    (M.K5_edgePath_same_or_reverse_of_degree_le_two_mem_support
      hdegree hxy hx'y' hv hv')

theorem StrictSubdivisionModel.K33_neighbor_mem_edgePath_toSubgraph_of_support_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hvw : G.Adj v w) :
    w ∈ (M.edgePath hxy).toSubgraph.neighborSet v := by
  classical
  have hv_internal :
      v ∈ Walk.InternalVertices (M.edgePath hxy) :=
    M.K33_internal_of_edgePath_support_of_degree_le_two
      hdegree hxy hv
  exact
    M.neighbor_mem_edgePath_toSubgraph_of_internal_degree_le_two
      hxy hv_internal hdegree hvw

theorem StrictSubdivisionModel.K33_incident_edge_mem_edgePath_edges_of_support_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hvw : G.Adj v w) :
    s(v, w) ∈ (M.edgePath hxy).edges := by
  have hw_path :
      w ∈ (M.edgePath hxy).toSubgraph.neighborSet v :=
    M.K33_neighbor_mem_edgePath_toSubgraph_of_support_degree_le_two
      hdegree hxy hv hvw
  simpa using
    (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges
      (p := M.edgePath hxy)).mp hw_path

theorem StrictSubdivisionModel.K33_idxOf_incident_edge_eq_succ_or_of_support_degree_le_two
    {V : Type v} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hvw : G.Adj v w) :
    (M.edgePath hxy).support.idxOf w =
        (M.edgePath hxy).support.idxOf v + 1 ∨
      (M.edgePath hxy).support.idxOf v =
        (M.edgePath hxy).support.idxOf w + 1 := by
  have hedge :
      s(v, w) ∈ (M.edgePath hxy).edges :=
    M.K33_incident_edge_mem_edgePath_edges_of_support_degree_le_two
      hdegree hxy hv hvw
  have hw : w ∈ (M.edgePath hxy).support := by
    exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
      (Or.inr ⟨s(v, w), hedge, by simp⟩)
  exact
    Walk.IsPath.idxOf_eq_succ_or_of_mem_edges
      (M.edgePath_isPath hxy) hedge

theorem StrictSubdivisionModel.K33_edgePath_same_or_reverse_of_degree_le_two_mem_support
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v : V}
    (hdegree : G.degree v <= 2)
    {x y x' y' : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hx'y' : K33Graph.Adj x' y')
    (hv : v ∈ (M.edgePath hxy).support)
    (hv' : v ∈ (M.edgePath hx'y').support) :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  classical
  by_contra hne
  have hv_internal :
      v ∈ Walk.InternalVertices (M.edgePath hxy) :=
    M.K33_internal_of_edgePath_support_of_degree_le_two
      hdegree hxy hv
  have hv'_internal :
      v ∈ Walk.InternalVertices (M.edgePath hx'y') :=
    M.K33_internal_of_edgePath_support_of_degree_le_two
      hdegree hx'y' hv'
  exact
    Set.disjoint_left.mp
      (M.internally_disjoint_edge_paths' hxy hx'y' hne)
      hv_internal hv'_internal

theorem StrictSubdivisionModel.K33_not_mem_other_edgePath_support_of_degree_le_two
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v : V}
    (hdegree : G.degree v <= 2)
    {x y x' y' : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hx'y' : K33Graph.Adj x' y')
    (hv : v ∈ (M.edgePath hxy).support)
    (hother : Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) :
    v ∉ (M.edgePath hx'y').support := by
  intro hv'
  exact hother
    (M.K33_edgePath_same_or_reverse_of_degree_le_two_mem_support
      hdegree hxy hx'y' hv hv')

theorem StrictSubdivisionModel.K5_branchVertex_ne_of_degree_le_one
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v : V}
    (hdegree : G.degree v <= 1)
    (x : Fin 5) :
    M.branchVertex x ≠ v := by
  classical
  intro hx
  subst v
  letI : Fintype (K5Graph.neighborSet x) := inferInstance
  letI : Fintype (G.neighborSet (M.branchVertex x)) := inferInstance
  have hsource :
      K5Graph.degree x <= G.degree (M.branchVertex x) :=
    M.source_degree_le_branchVertex_degree x
  rw [K5Graph_degree x] at hsource
  omega

theorem StrictSubdivisionModel.K33_branchVertex_ne_of_degree_le_one
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v : V}
    (hdegree : G.degree v <= 1)
    (x : K33Vertex) :
    M.branchVertex x ≠ v := by
  classical
  intro hx
  subst v
  letI : Fintype (K33Graph.neighborSet x) := inferInstance
  letI : Fintype (G.neighborSet (M.branchVertex x)) := inferInstance
  have hsource :
      K33Graph.degree x <= G.degree (M.branchVertex x) :=
    M.source_degree_le_branchVertex_degree x
  rw [K33Graph_degree x] at hsource
  omega

theorem StrictSubdivisionModel.K5_edgePath_support_ne_of_degree_le_one
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v : V}
    (hdegree : G.degree v <= 1)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    {z : V}
    (hz : z ∈ (M.edgePath hxy).support) :
    z ≠ v := by
  classical
  intro hzv
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := M.edgePath hxy) hz with
    hz_internal | hz_endpoint
  · exact
      (Walk.IsPath.not_mem_internalVertices_of_degree_le_one
        (G := G) (x := v) (M.edgePath_isPath hxy) hdegree)
        (by simpa [hzv] using hz_internal)
  · rcases hz_endpoint with hz_start | hz_end
    · exact
        (M.K5_branchVertex_ne_of_degree_le_one hdegree x)
          (hz_start.symm.trans hzv)
    · exact
        (M.K5_branchVertex_ne_of_degree_le_one hdegree y)
          (hz_end.symm.trans hzv)

theorem StrictSubdivisionModel.K33_edgePath_support_ne_of_degree_le_one
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v : V}
    (hdegree : G.degree v <= 1)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    {z : V}
    (hz : z ∈ (M.edgePath hxy).support) :
    z ≠ v := by
  classical
  intro hzv
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := M.edgePath hxy) hz with
    hz_internal | hz_endpoint
  · exact
      (Walk.IsPath.not_mem_internalVertices_of_degree_le_one
        (G := G) (x := v) (M.edgePath_isPath hxy) hdegree)
        (by simpa [hzv] using hz_internal)
  · rcases hz_endpoint with hz_start | hz_end
    · exact
        (M.K33_branchVertex_ne_of_degree_le_one hdegree x)
          (hz_start.symm.trans hzv)
    · exact
        (M.K33_branchVertex_ne_of_degree_le_one hdegree y)
          (hz_end.symm.trans hzv)

theorem ContainsStrictSubdivision.K5_induce_compl_singleton_of_degree_le_one
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V}
    (h : ContainsStrictSubdivision K5Graph G)
    (hdegree : G.degree v <= 1) :
    ContainsStrictSubdivision K5Graph (G.induce {z : V | z ≠ v}) := by
  classical
  rcases h with ⟨M⟩
  exact ⟨M.targetRestrict {z : V | z ≠ v}
    (fun x => M.K5_branchVertex_ne_of_degree_le_one hdegree x)
    (by
      intro x y hxy z hz
      exact M.K5_edgePath_support_ne_of_degree_le_one hdegree hxy hz)⟩

theorem ContainsStrictSubdivision.K33_induce_compl_singleton_of_degree_le_one
    {V : Type v} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V}
    (h : ContainsStrictSubdivision K33Graph G)
    (hdegree : G.degree v <= 1) :
    ContainsStrictSubdivision K33Graph (G.induce {z : V | z ≠ v}) := by
  classical
  rcases h with ⟨M⟩
  exact ⟨M.targetRestrict {z : V | z ≠ v}
    (fun x => M.K33_branchVertex_ne_of_degree_le_one hdegree x)
    (by
      intro x y hxy z hz
      exact M.K33_edgePath_support_ne_of_degree_le_one hdegree hxy hz)⟩

end Schematic.Math.GraphTheory
