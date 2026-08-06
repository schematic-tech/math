import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Foundations
import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Paths.Splice

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem strictSubdivisionModel_exists_isPath_collapseEdge_edgePath
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y : W}
    (hxy : K.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    (hw : w ∈ (M.edgePath hxy).support)
    (hconsecutive :
      (M.edgePath hxy).support.idxOf w =
          (M.edgePath hxy).support.idxOf v + 1 ∨
        (M.edgePath hxy).support.idxOf v =
          (M.edgePath hxy).support.idxOf w + 1) :
    Exists fun q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)) =>
      q.IsPath ∧
        ∀ z, z ∈ q.support →
          ∃ t, t ∈ (M.edgePath hxy).support ∧
            (GraphContraction.collapseEdge G hvw).map t = z := by
  rcases hconsecutive with hforward | hreverse
  · exact exists_isPath_collapseEdge_splice_forward
      hvw (M.edgePath_isPath hxy) hv hw hforward
  · exact exists_isPath_collapseEdge_splice_reverse
      hvw (M.edgePath_isPath hxy) hv hw hreverse

theorem strictSubdivisionModel_exists_isPath_collapseEdge_clean_edgePath
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y : W}
    (hxy : K.Adj x y)
    (havoid : v ∉ (M.edgePath hxy).support) :
    Exists fun q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)) =>
      q.IsPath ∧
        ∀ z, z ∈ q.support →
          ∃ t, t ∈ (M.edgePath hxy).support ∧
            (GraphContraction.collapseEdge G hvw).map t = z := by
  classical
  let p := M.edgePath hxy
  have hnot_both : ¬ (v ∈ p.support ∧ w ∈ p.support) :=
    fun h => havoid (by simpa [p] using h.1)
  let q := GraphContraction.collapseEdgeWalkOfNotPairBoth hvw p hnot_both
  have hq : q.IsPath := by
    simpa [q, p] using
      GraphContraction.isPath_collapseEdgeWalkOfNotPairBoth
        hvw p (M.edgePath_isPath hxy) hnot_both
  refine ⟨q, hq, ?_⟩
  intro z hz
  have hz_map :
      z ∈ p.support.map (GraphContraction.collapseEdge G hvw).map := by
    simpa [q, GraphContraction.support_collapseEdgeWalkOfNotPairBoth] using hz
  rcases List.mem_map.mp hz_map with ⟨t, ht, rfl⟩
  exact ⟨t, by simpa [p] using ht, rfl⟩

theorem StrictSubdivisionModel.K5_neighbor_mem_edgePath_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v ≤ 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support) :
    w ∈ (M.edgePath hxy).support := by
  have hedge := M.K5_incident_edge_mem_edgePath_edges_of_support_degree_le_two
    hdegree hxy hv hvw
  exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨s(v, w), hedge, by simp⟩)

theorem StrictSubdivisionModel.K33_neighbor_mem_edgePath_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v ≤ 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support) :
    w ∈ (M.edgePath hxy).support := by
  have hedge := M.K33_incident_edge_mem_edgePath_edges_of_support_degree_le_two
    hdegree hxy hv hvw
  exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨s(v, w), hedge, by simp⟩)

/-- Degree-two affected-path contraction for a strict `K_5` model.  If the
low-degree endpoint `v` lies on a model path, then its incident edge `vw` lies
on that same path and the split-path contraction primitive gives a simple
quotient replacement for that source edge. -/
theorem StrictSubdivisionModel.K5_exists_isPath_collapseEdge_edgePath_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support) :
    Exists fun q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)) =>
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun t : V =>
              t ∈ (M.edgePath hxy).support ∧
                (GraphContraction.collapseEdge G hvw).map t = z := by
  apply strictSubdivisionModel_exists_isPath_collapseEdge_edgePath M hvw hxy hv
  exact StrictSubdivisionModel.K5_neighbor_mem_edgePath_of_degree_le_two
    M hvw hdegree hxy hv
  exact M.K5_idxOf_incident_edge_eq_succ_or_of_support_degree_le_two
    hdegree hxy hv hvw

/-- Degree-two affected-path contraction for a strict `K_{3,3}` model. -/
theorem StrictSubdivisionModel.K33_exists_isPath_collapseEdge_edgePath_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support) :
    Exists fun q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)) =>
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun t : V =>
              t ∈ (M.edgePath hxy).support ∧
                (GraphContraction.collapseEdge G hvw).map t = z := by
  apply strictSubdivisionModel_exists_isPath_collapseEdge_edgePath M hvw hxy hv
  exact StrictSubdivisionModel.K33_neighbor_mem_edgePath_of_degree_le_two
    M hvw hdegree hxy hv
  exact M.K33_idxOf_incident_edge_eq_succ_or_of_support_degree_le_two
    hdegree hxy hv hvw

/-- Clean-path quotient lift for `K_5` model paths that avoid the degree-two
endpoint being contracted. -/
theorem StrictSubdivisionModel.K5_exists_isPath_collapseEdge_clean_edgePath_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (havoid : v ∉ (M.edgePath hxy).support) :
    Exists fun q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)) =>
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun t : V =>
              t ∈ (M.edgePath hxy).support ∧
                (GraphContraction.collapseEdge G hvw).map t = z :=
  strictSubdivisionModel_exists_isPath_collapseEdge_clean_edgePath M hvw hxy havoid

/-- Clean-path quotient lift for `K_{3,3}` model paths. -/
theorem StrictSubdivisionModel.K33_exists_isPath_collapseEdge_clean_edgePath_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (havoid : v ∉ (M.edgePath hxy).support) :
    Exists fun q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)) =>
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun t : V =>
              t ∈ (M.edgePath hxy).support ∧
                (GraphContraction.collapseEdge G hvw).map t = z :=
  strictSubdivisionModel_exists_isPath_collapseEdge_clean_edgePath M hvw hxy havoid

/-- Branch vertices remain injective after contracting an edge incident with a
degree-two endpoint not used as a `K_5` branch vertex. -/
theorem StrictSubdivisionModel.K5_collapseEdge_branchVertex_injective_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2) :
    Function.Injective
      (fun x : Fin 5 =>
        (GraphContraction.collapseEdge G hvw).map (M.branchVertex x)) :=
  strictSubdivisionModel_collapseEdge_branchVertex_injective_of_avoids_left
    M hvw fun x => M.K5_branchVertex_ne_of_degree_le_three (by omega) x

/-- Branch-map injectivity under the same degree-two contraction for
`K_{3,3}` models. -/
theorem StrictSubdivisionModel.K33_collapseEdge_branchVertex_injective_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2) :
    Function.Injective
      (fun x : K33Vertex =>
        (GraphContraction.collapseEdge G hvw).map (M.branchVertex x)) :=
  strictSubdivisionModel_collapseEdge_branchVertex_injective_of_avoids_left
    M hvw fun x => M.K33_branchVertex_ne_of_degree_le_two hdegree x

theorem strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y : W}
    (hxy : K.Adj x y)
    (hbranch_ne : ∀ r, M.branchVertex r ≠ v)
    (hsurvivor :
      w ∈ (M.edgePath hxy).support ∨
        v ∉ (M.edgePath hxy).support)
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    (hreflect :
      ∀ z, z ∈ q.support →
        ∃ t, t ∈ (M.edgePath hxy).support ∧
          (GraphContraction.collapseEdge G hvw).map t = z) :
    ∀ {z}, z ∈ Walk.InternalVertices q → ∀ r,
      z ≠ (GraphContraction.collapseEdge G hvw).map
        (M.branchVertex r) := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  intro z hz r hz_branch
  rcases hreflect z hz.1 with ⟨t, ht_support, ht_map⟩
  have hmap_eq : C.map t = C.map (M.branchVertex r) :=
    ht_map.trans hz_branch
  have hr_ne_x : r ≠ x := by
    intro hrx
    exact hz.2.1 (by simpa [C, hrx] using hz_branch)
  have hr_ne_y : r ≠ y := by
    intro hry
    exact hz.2.2 (by simpa [C, hry] using hz_branch)
  have hbranch_support :
      M.branchVertex r ∈ (M.edgePath hxy).support := by
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hvw (v := t) (w := M.branchVertex r)).mp hmap_eq with
      hpair | houtside
    · have ht_pair : t = v ∨ t = w := by
        simpa using hpair.1
      have hr_pair : M.branchVertex r = v ∨ M.branchVertex r = w := by
        simpa using hpair.2
      have hrw : M.branchVertex r = w :=
        hr_pair.resolve_left (hbranch_ne r)
      rcases hsurvivor with hw_support | havoid
      · simpa [hrw] using hw_support
      · have htw : t = w := by
          rcases ht_pair with htv | htw
          · exact False.elim (havoid (by simpa [htv] using ht_support))
          · exact htw
        simpa [hrw, htw] using ht_support
    · simpa [houtside.1] using ht_support
  have hbranch_internal :
      M.branchVertex r ∈ Walk.InternalVertices (M.edgePath hxy) := by
    rcases
        Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
          (p := M.edgePath hxy) hbranch_support with
      hinternal | hendpoint
    · exact hinternal
    · rcases hendpoint with hstart | hend
      · exact False.elim (hr_ne_x (M.branchVertex_injective hstart))
      · exact False.elim (hr_ne_y (M.branchVertex_injective hend))
  exact M.no_internal_branch_vertices' hxy hbranch_internal r rfl

/-- The affected quotient replacement path for a degree-two contraction has
no internal branch vertex images in the `K_5` case.  The only new possible
collision is the contracted image of `v` with `w`; if `w` is a branch vertex,
then either it is an endpoint of the affected source edge, making the quotient
occurrence an endpoint, or it would already be an internal branch vertex of
the original strict model. -/
theorem StrictSubdivisionModel.K5_collapseEdge_affected_path_no_internal_branch_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    (hreflect :
      forall z,
        z ∈ q.support ->
          Exists fun t : V =>
            t ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map t = z) :
    forall {z},
      z ∈ Walk.InternalVertices q ->
        forall r : Fin 5,
          z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r) := by
  refine strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
    M hvw hxy
      (fun r => M.K5_branchVertex_ne_of_degree_le_three (by omega) r)
      (Or.inl ?_) hreflect
  have hedge : s(v, w) ∈ (M.edgePath hxy).edges :=
    M.K5_incident_edge_mem_edgePath_edges_of_support_degree_le_two
      hdegree hxy hv hvw
  exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨s(v, w), hedge, by simp⟩)

/-- `K_{3,3}` analogue of
`K5_collapseEdge_affected_path_no_internal_branch_vertices`. -/
theorem StrictSubdivisionModel.K33_collapseEdge_affected_path_no_internal_branch_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    (hreflect :
      forall z,
        z ∈ q.support ->
          Exists fun t : V =>
            t ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map t = z) :
    forall {z},
      z ∈ Walk.InternalVertices q ->
        forall r : K33Vertex,
          z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r) := by
  refine strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
    M hvw hxy
      (fun r => M.K33_branchVertex_ne_of_degree_le_two hdegree r)
      (Or.inl ?_) hreflect
  have hedge : s(v, w) ∈ (M.edgePath hxy).edges :=
    M.K33_incident_edge_mem_edgePath_edges_of_support_degree_le_two
      hdegree hxy hv hvw
  exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨s(v, w), hedge, by simp⟩)

/-- Clean quotient lifts also have no internal branch vertex images in the
`K_5` case. -/
theorem StrictSubdivisionModel.K5_collapseEdge_clean_path_no_internal_branch_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (havoid : v ∉ (M.edgePath hxy).support)
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    (hreflect :
      forall z,
        z ∈ q.support ->
          Exists fun t : V =>
            t ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map t = z) :
    forall {z},
      z ∈ Walk.InternalVertices q ->
        forall r : Fin 5,
          z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r) :=
  strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
    M hvw hxy
      (fun r => M.K5_branchVertex_ne_of_degree_le_three (by omega) r)
      (Or.inr havoid) hreflect

/-- Clean quotient lifts are branch-clean for `K_{3,3}` models. -/
theorem StrictSubdivisionModel.K33_collapseEdge_clean_path_no_internal_branch_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (havoid : v ∉ (M.edgePath hxy).support)
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    (hreflect :
      forall z,
        z ∈ q.support ->
          Exists fun t : V =>
            t ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map t = z) :
    forall {z},
      z ∈ Walk.InternalVertices q ->
        forall r : K33Vertex,
          z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r) :=
  strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
    M hvw hxy
      (fun r => M.K33_branchVertex_ne_of_degree_le_two hdegree r)
      (Or.inr havoid) hreflect

theorem collapseEdge_internal_of_reflected_internal
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w x y : V}
    (hvw : G.Adj v w)
    {p : G.Walk x y}
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map x)
        ((GraphContraction.collapseEdge G hvw).map y)}
    {z : (GraphContraction.collapseEdge G hvw).Target}
    {a : V}
    (hz : z ∈ Walk.InternalVertices q)
    (ha : a ∈ p.support)
    (hmap : (GraphContraction.collapseEdge G hvw).map a = z) :
    a ∈ Walk.InternalVertices p := by
  rcases Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support ha with
    hint | hendpoint
  · exact hint
  · rcases hendpoint with hstart | hend
    · exact False.elim (hz.2.1 (by simpa [hstart] using hmap.symm))
    · exact False.elim (hz.2.2 (by simpa [hend] using hmap.symm))

theorem strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y s t : W}
    (hxy : K.Adj x y)
    (hst : K.Adj s t)
    (hne : ¬ ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
    (hsurvivor_xy :
      w ∈ (M.edgePath hxy).support ∨
        v ∉ (M.edgePath hxy).support)
    (havoid_st : v ∉ (M.edgePath hst).support)
    {qxy :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    {qst :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t))}
    (hreflect_xy :
      ∀ z, z ∈ qxy.support →
        ∃ a, a ∈ (M.edgePath hxy).support ∧
          (GraphContraction.collapseEdge G hvw).map a = z)
    (hreflect_st :
      ∀ z, z ∈ qst.support →
        ∃ a, a ∈ (M.edgePath hst).support ∧
          (GraphContraction.collapseEdge G hvw).map a = z) :
    Disjoint (Walk.InternalVertices qxy) (Walk.InternalVertices qst) := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  rw [Set.disjoint_left]
  intro z hzxy hzst
  rcases hreflect_xy z hzxy.1 with ⟨a, ha_support, ha_map⟩
  rcases hreflect_st z hzst.1 with ⟨b, hb_support, hb_map⟩
  have hab_map : C.map a = C.map b := ha_map.trans hb_map.symm
  have disjoint_original
      {a b : V}
      (ha_internal : a ∈ Walk.InternalVertices (M.edgePath hxy))
      (hb_internal : b ∈ Walk.InternalVertices (M.edgePath hst))
      (hab : a = b) : False :=
    Set.disjoint_left.mp (M.internally_disjoint_edge_paths' hxy hst hne)
      ha_internal (by simpa [hab] using hb_internal)
  rcases
      (GraphContraction.collapseEdge_map_eq_iff
        (G := G) hvw (v := a) (w := b)).mp hab_map with
    hpair | houtside
  · have ha_pair : a = v ∨ a = w := by simpa using hpair.1
    have hb_pair : b = v ∨ b = w := by simpa using hpair.2
    have hbw : b = w := by
      rcases hb_pair with hbv | hbw
      · exact False.elim (havoid_st (by simpa [hbv] using hb_support))
      · exact hbw
    rcases hsurvivor_xy with hw_support | havoid_xy
    · have hw_map : C.map w = z := by simpa [hbw] using hb_map
      have hw_internal :=
        collapseEdge_internal_of_reflected_internal hvw hzxy hw_support hw_map
      have hb_internal :=
        collapseEdge_internal_of_reflected_internal hvw hzst hb_support hb_map
      exact disjoint_original hw_internal hb_internal hbw.symm
    · have haw : a = w := by
        rcases ha_pair with hav | haw
        · exact False.elim (havoid_xy (by simpa [hav] using ha_support))
        · exact haw
      have ha_internal :=
        collapseEdge_internal_of_reflected_internal hvw hzxy ha_support ha_map
      have hb_internal :=
        collapseEdge_internal_of_reflected_internal hvw hzst hb_support hb_map
      exact disjoint_original ha_internal hb_internal (haw.trans hbw.symm)
  · have ha_internal :=
      collapseEdge_internal_of_reflected_internal hvw hzxy ha_support ha_map
    have hb_internal :=
      collapseEdge_internal_of_reflected_internal hvw hzst hb_support hb_map
    exact disjoint_original ha_internal hb_internal houtside.1

/-- Two clean quotient lifts of distinct `K_5` model paths remain internally
disjoint after contracting a degree-two endpoint avoided by both original
paths. -/
theorem StrictSubdivisionModel.K5_collapseEdge_clean_paths_internally_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y s t : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hst : K5Graph.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
    (havoid_xy : v ∉ (M.edgePath hxy).support)
    (havoid_st : v ∉ (M.edgePath hst).support)
    {qxy :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    {qst :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t))}
    (hreflect_xy :
      forall z,
        z ∈ qxy.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z)
    (hreflect_st :
      forall z,
        z ∈ qst.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hst).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z) :
    Disjoint (Walk.InternalVertices qxy) (Walk.InternalVertices qst) :=
  strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
    M hvw hxy hst hne (Or.inr havoid_xy) havoid_st hreflect_xy hreflect_st

/-- Clean-clean internal disjointness after degree-two contraction for
`K_{3,3}` model paths. -/
theorem StrictSubdivisionModel.K33_collapseEdge_clean_paths_internally_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    {x y s t : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hst : K33Graph.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
    (havoid_xy : v ∉ (M.edgePath hxy).support)
    (havoid_st : v ∉ (M.edgePath hst).support)
    {qxy :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    {qst :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t))}
    (hreflect_xy :
      forall z,
        z ∈ qxy.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z)
    (hreflect_st :
      forall z,
        z ∈ qst.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hst).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z) :
    Disjoint (Walk.InternalVertices qxy) (Walk.InternalVertices qst) :=
  strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
    M hvw hxy hst hne (Or.inr havoid_xy) havoid_st hreflect_xy hreflect_st

/-- Mixed affected-clean internal disjointness for quotient `K_5` model
paths after contracting a degree-two endpoint. -/
theorem StrictSubdivisionModel.K5_collapseEdge_affected_clean_paths_internally_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y s t : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hst : K5Graph.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
    (hv : v ∈ (M.edgePath hxy).support)
    (havoid_st : v ∉ (M.edgePath hst).support)
    {qxy :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    {qst :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t))}
    (hreflect_xy :
      forall z,
        z ∈ qxy.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z)
    (hreflect_st :
      forall z,
        z ∈ qst.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hst).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z) :
    Disjoint (Walk.InternalVertices qxy) (Walk.InternalVertices qst) := by
  refine strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
    M hvw hxy hst hne (Or.inl ?_) havoid_st hreflect_xy hreflect_st
  have hedge : s(v, w) ∈ (M.edgePath hxy).edges :=
    M.K5_incident_edge_mem_edgePath_edges_of_support_degree_le_two
      hdegree hxy hv hvw
  exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨s(v, w), hedge, by simp⟩)

/-- Mixed affected-clean internal disjointness for quotient `K_{3,3}` model
paths after contracting a degree-two endpoint. -/
theorem StrictSubdivisionModel.K33_collapseEdge_affected_clean_paths_internally_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y s t : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hst : K33Graph.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
    (hv : v ∈ (M.edgePath hxy).support)
    (havoid_st : v ∉ (M.edgePath hst).support)
    {qxy :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y))}
    {qst :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t))}
    (hreflect_xy :
      forall z,
        z ∈ qxy.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hxy).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z)
    (hreflect_st :
      forall z,
        z ∈ qst.support ->
          Exists fun a : V =>
            a ∈ (M.edgePath hst).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z) :
    Disjoint (Walk.InternalVertices qxy) (Walk.InternalVertices qst) := by
  refine strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
    M hvw hxy hst hne (Or.inl ?_) havoid_st hreflect_xy hreflect_st
  have hedge : s(v, w) ∈ (M.edgePath hxy).edges :=
    M.K33_incident_edge_mem_edgePath_edges_of_support_degree_le_two
      hdegree hxy hv hvw
  exact (SimpleGraph.Walk.mem_support_iff_exists_mem_edges).mpr
    (Or.inr ⟨s(v, w), hedge, by simp⟩)


end FourColor

end Schematic.Math.GraphTheory
