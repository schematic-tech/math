import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Paths.LowDegree

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

noncomputable def strictSubdivisionModel_collapseEdge_edgePathData
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    {s t : W}
    (hst : K.Adj s t)
    (haffected :
      v ∈ (M.edgePath hst).support →
        ∃ q : (GraphContraction.collapseEdge G hvw).graph.Walk
            ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
            ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)),
          q.IsPath ∧ ∀ z, z ∈ q.support →
            ∃ a, a ∈ (M.edgePath hst).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z)
    (hclean :
      v ∉ (M.edgePath hst).support →
        ∃ q : (GraphContraction.collapseEdge G hvw).graph.Walk
            ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
            ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)),
          q.IsPath ∧ ∀ z, z ∈ q.support →
            ∃ a, a ∈ (M.edgePath hst).support ∧
              (GraphContraction.collapseEdge G hvw).map a = z) :
    {q : (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)) //
      q.IsPath ∧ ∀ z, z ∈ q.support →
        ∃ a, a ∈ (M.edgePath hst).support ∧
          (GraphContraction.collapseEdge G hvw).map a = z} := by
  classical
  by_cases hvst : v ∈ (M.edgePath hst).support
  · exact ⟨Classical.choose (haffected hvst), Classical.choose_spec (haffected hvst)⟩
  · exact ⟨Classical.choose (hclean hvst), Classical.choose_spec (hclean hvst)⟩

/-- Edge-path selector data for the `K_5` degree-two reverse-contraction
model.  For each source edge we use the affected split-splice lift exactly
when the low-degree endpoint lies on that same source path; otherwise we use
the clean quotient lift.  The subtype packages the selected quotient path
together with the two facts used by the strict-model fields: pathness and
support reflection back to the original source path. -/
noncomputable def StrictSubdivisionModel.K5_collapseEdge_edgePathData_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (_hv : v ∈ (M.edgePath hxy).support)
    {s t : Fin 5}
    (hst : K5Graph.Adj s t) :
    { q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)) //
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun a : V =>
              a ∈ (M.edgePath hst).support ∧
                (GraphContraction.collapseEdge G hvw).map a = z } :=
  strictSubdivisionModel_collapseEdge_edgePathData M hvw hst
    (fun hvst =>
      StrictSubdivisionModel.K5_exists_isPath_collapseEdge_edgePath_of_degree_le_two
        M hvw hdegree hst hvst)
    (fun hvst =>
      StrictSubdivisionModel.K5_exists_isPath_collapseEdge_clean_edgePath_of_degree_le_two
        M hvw hst hvst)

/-- Edge-path selector for the `K_5` degree-two reverse-contraction model.
It uses the split-spliced affected quotient path for every old source path
that contains `v`, and clean quotient lifts for the remaining source paths. -/
noncomputable def StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {s t : Fin 5}
    (hst : K5Graph.Adj s t) :
    (GraphContraction.collapseEdge G hvw).graph.Walk
      ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
      ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)) :=
  (StrictSubdivisionModel.K5_collapseEdge_edgePathData_of_degree_le_two M
    hvw hdegree hxy hv hst).1
theorem StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_isPath
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {s t : Fin 5}
    (hst : K5Graph.Adj s t) :
    (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two M
      hvw hdegree hxy hv hst).IsPath :=
  (StrictSubdivisionModel.K5_collapseEdge_edgePathData_of_degree_le_two M
    hvw hdegree hxy hv hst).2.1

theorem StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_reflect
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {s t : Fin 5}
    (hst : K5Graph.Adj s t) :
    forall z,
      z ∈ (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two M
        hvw hdegree hxy hv hst).support ->
        Exists fun a : V =>
          a ∈ (M.edgePath hst).support ∧
            (GraphContraction.collapseEdge G hvw).map a = z :=
  (StrictSubdivisionModel.K5_collapseEdge_edgePathData_of_degree_le_two M
    hvw hdegree hxy hv hst).2.2

/-- Edge-path selector data for the `K_{3,3}` degree-two reverse-contraction
model.  This is the bipartite analogue of the `K_5` selector data above:
affected source paths are split-spliced through the contracted edge, and
source paths avoiding the low-degree endpoint are cleanly lifted. -/
noncomputable def StrictSubdivisionModel.K33_collapseEdge_edgePathData_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (_hv : v ∈ (M.edgePath hxy).support)
    {s t : K33Vertex}
    (hst : K33Graph.Adj s t) :
    { q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)) //
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun a : V =>
              a ∈ (M.edgePath hst).support ∧
                (GraphContraction.collapseEdge G hvw).map a = z } :=
  strictSubdivisionModel_collapseEdge_edgePathData M hvw hst
    (fun hvst =>
      StrictSubdivisionModel.K33_exists_isPath_collapseEdge_edgePath_of_degree_le_two
        M hvw hdegree hst hvst)
    (fun hvst =>
      StrictSubdivisionModel.K33_exists_isPath_collapseEdge_clean_edgePath_of_degree_le_two
        M hvw hst hvst)

/-- Edge-path selector for the `K_{3,3}` degree-two reverse-contraction model. -/
noncomputable def StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {s t : K33Vertex}
    (hst : K33Graph.Adj s t) :
    (GraphContraction.collapseEdge G hvw).graph.Walk
      ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
      ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t)) :=
  (StrictSubdivisionModel.K33_collapseEdge_edgePathData_of_degree_le_two M
    hvw hdegree hxy hv hst).1

theorem StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_isPath
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {s t : K33Vertex}
    (hst : K33Graph.Adj s t) :
    (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two M
      hvw hdegree hxy hv hst).IsPath :=
  (StrictSubdivisionModel.K33_collapseEdge_edgePathData_of_degree_le_two M
    hvw hdegree hxy hv hst).2.1

theorem StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_reflect
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hv : v ∈ (M.edgePath hxy).support)
    {s t : K33Vertex}
    (hst : K33Graph.Adj s t) :
    forall z,
      z ∈ (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two M
        hvw hdegree hxy hv hst).support ->
        Exists fun a : V =>
          a ∈ (M.edgePath hst).support ∧
            (GraphContraction.collapseEdge G hvw).map a = z :=
  (StrictSubdivisionModel.K33_collapseEdge_edgePathData_of_degree_le_two M
    hvw hdegree hxy hv hst).2.2

theorem not_same_or_reverse_swap
    {α : Type*} {x y s t : α}
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s))) :
    Not ((s = x ∧ t = y) ∨ (s = y ∧ t = x)) := by
  intro h
  exact hne
    (by
      rcases h with h | h
      · exact Or.inl ⟨h.1.symm, h.2.symm⟩
      · exact Or.inr ⟨h.2.symm, h.1.symm⟩)

theorem strictSubdivisionModel_collapseEdge_selected_path_no_internal_branch_vertices
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    (hbranch_ne : ∀ r, M.branchVertex r ≠ v)
    (hneighbor :
      ∀ {s t : W} (hst : K.Adj s t),
        v ∈ (M.edgePath hst).support →
          w ∈ (M.edgePath hst).support)
    {s t : W}
    (hst : K.Adj s t)
    {q :
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex s))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex t))}
    (hreflect :
      ∀ z, z ∈ q.support →
        ∃ a, a ∈ (M.edgePath hst).support ∧
          (GraphContraction.collapseEdge G hvw).map a = z) :
    ∀ {z}, z ∈ Walk.InternalVertices q → ∀ r,
      z ≠ (GraphContraction.collapseEdge G hvw).map
        (M.branchVertex r) := by
  by_cases hvst : v ∈ (M.edgePath hst).support
  · exact strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
      M hvw hst hbranch_ne (Or.inl (hneighbor hst hvst)) hreflect
  · exact strictSubdivisionModel_collapseEdge_reflected_path_no_internal_branch_vertices
      M hvw hst hbranch_ne (Or.inr hvst) hreflect

theorem strictSubdivisionModel_collapseEdge_selected_paths_internally_disjoint
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    (hneighbor :
      ∀ {a b : W} (hab : K.Adj a b),
        v ∈ (M.edgePath hab).support →
          w ∈ (M.edgePath hab).support)
    (hsame :
      ∀ {x y s t : W} (hxy : K.Adj x y) (hst : K.Adj s t),
        v ∈ (M.edgePath hxy).support →
        v ∈ (M.edgePath hst).support →
          (x = s ∧ y = t) ∨ (x = t ∧ y = s))
    {x y s t : W}
    (hxy : K.Adj x y)
    (hst : K.Adj s t)
    (hne : ¬ ((x = s ∧ y = t) ∨ (x = t ∧ y = s)))
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
  by_cases hvxy : v ∈ (M.edgePath hxy).support
  · by_cases hvst : v ∈ (M.edgePath hst).support
    · exact False.elim (hne (hsame hxy hst hvxy hvst))
    · exact strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
        M hvw hxy hst hne (Or.inl (hneighbor hxy hvxy)) hvst
          hreflect_xy hreflect_st
  · by_cases hvst : v ∈ (M.edgePath hst).support
    · exact Disjoint.symm
        (strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
          M hvw hst hxy (not_same_or_reverse_swap hne)
            (Or.inl (hneighbor hst hvst)) hvxy hreflect_st hreflect_xy)
    · exact strictSubdivisionModel_collapseEdge_reflected_paths_internally_disjoint
        M hvw hxy hst hne (Or.inr hvxy) hvst hreflect_xy hreflect_st

/-- Branch-clean field for the selected `K_5` quotient edge paths in the
degree-two reverse-contraction model. -/
theorem StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_no_internal_branch_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {a b : Fin 5}
    (hab : K5Graph.Adj a b)
    (hvab : v ∈ (M.edgePath hab).support)
    {s t : Fin 5}
    (hst : K5Graph.Adj s t) :
    forall {z},
      z ∈ Walk.InternalVertices
        (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two M
          hvw hdegree hab hvab hst) ->
        forall r : Fin 5,
          z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r) :=
  strictSubdivisionModel_collapseEdge_selected_path_no_internal_branch_vertices
    M hvw
      (fun r => M.K5_branchVertex_ne_of_degree_le_three (by omega) r)
      (fun hst hvst =>
        StrictSubdivisionModel.K5_neighbor_mem_edgePath_of_degree_le_two
          M hvw hdegree hst hvst)
      hst
      (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_reflect
        M hvw hdegree hab hvab hst)

/-- Internal-disjointness field for the selected `K_5` quotient edge paths in
the degree-two reverse-contraction model. -/
theorem StrictSubdivisionModel.K5_collapseEdge_edgePaths_of_degree_le_two_internally_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {a b : Fin 5}
    (hab : K5Graph.Adj a b)
    (hvab : v ∈ (M.edgePath hab).support)
    {x y s t : Fin 5}
    (hxy : K5Graph.Adj x y)
    (hst : K5Graph.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s))) :
    Disjoint
      (Walk.InternalVertices
        (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two M
          hvw hdegree hab hvab hxy))
      (Walk.InternalVertices
        (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two M
          hvw hdegree hab hvab hst)) :=
  strictSubdivisionModel_collapseEdge_selected_paths_internally_disjoint
    M hvw
      (fun h hv =>
        StrictSubdivisionModel.K5_neighbor_mem_edgePath_of_degree_le_two
          M hvw hdegree h hv)
      (fun hxy hst hvxy hvst =>
        M.K5_edgePath_same_or_reverse_of_degree_le_two_mem_support
          hdegree hxy hst hvxy hvst)
      hxy hst hne
      (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_reflect
        M hvw hdegree hab hvab hxy)
      (StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_reflect
        M hvw hdegree hab hvab hst)

/-- Branch-clean field for the selected `K_{3,3}` quotient edge paths in the
degree-two reverse-contraction model. -/
theorem StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_no_internal_branch_vertices
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {a b : K33Vertex}
    (hab : K33Graph.Adj a b)
    (hvab : v ∈ (M.edgePath hab).support)
    {s t : K33Vertex}
    (hst : K33Graph.Adj s t) :
    forall {z},
      z ∈ Walk.InternalVertices
        (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two M
          hvw hdegree hab hvab hst) ->
        forall r : K33Vertex,
          z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r) :=
  strictSubdivisionModel_collapseEdge_selected_path_no_internal_branch_vertices
    M hvw
      (fun r => M.K33_branchVertex_ne_of_degree_le_two hdegree r)
      (fun hst hvst =>
        StrictSubdivisionModel.K33_neighbor_mem_edgePath_of_degree_le_two
          M hvw hdegree hst hvst)
      hst
      (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_reflect
        M hvw hdegree hab hvab hst)

/-- Internal-disjointness field for the selected `K_{3,3}` quotient edge paths
in the degree-two reverse-contraction model. -/
theorem StrictSubdivisionModel.K33_collapseEdge_edgePaths_of_degree_le_two_internally_disjoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {a b : K33Vertex}
    (hab : K33Graph.Adj a b)
    (hvab : v ∈ (M.edgePath hab).support)
    {x y s t : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hst : K33Graph.Adj s t)
    (hne : Not ((x = s ∧ y = t) ∨ (x = t ∧ y = s))) :
    Disjoint
      (Walk.InternalVertices
        (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two M
          hvw hdegree hab hvab hxy))
      (Walk.InternalVertices
        (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two M
          hvw hdegree hab hvab hst)) :=
  strictSubdivisionModel_collapseEdge_selected_paths_internally_disjoint
    M hvw
      (fun h hv =>
        StrictSubdivisionModel.K33_neighbor_mem_edgePath_of_degree_le_two
          M hvw hdegree h hv)
      (fun hxy hst hvxy hvst =>
        M.K33_edgePath_same_or_reverse_of_degree_le_two_mem_support
          hdegree hxy hst hvxy hvst)
      hxy hst hne
      (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_reflect
        M hvw hdegree hab hvab hxy)
      (StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_reflect
        M hvw hdegree hab hvab hst)

noncomputable def strictSubdivisionModel_collapseEdge_of_pathFamily
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {v w : V}
    (hvw : G.Adj v w)
    (hbranch : Function.Injective fun r =>
      (GraphContraction.collapseEdge G hvw).map (M.branchVertex r))
    (path : ∀ {x y : W}, K.Adj x y →
      (GraphContraction.collapseEdge G hvw).graph.Walk
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex x))
        ((GraphContraction.collapseEdge G hvw).map (M.branchVertex y)))
    (hpath : ∀ {x y : W} (hxy : K.Adj x y), (path hxy).IsPath)
    (hbranch_clean :
      ∀ {x y : W} (hxy : K.Adj x y)
        {z : (GraphContraction.collapseEdge G hvw).Target},
        z ∈ Walk.InternalVertices (path hxy) →
          ∀ r, z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r))
    (hdisjoint :
      ∀ {x y s t : W} (hxy : K.Adj x y) (hst : K.Adj s t),
        ¬ ((x = s ∧ y = t) ∨ (x = t ∧ y = s)) →
          Disjoint (Walk.InternalVertices (path hxy))
            (Walk.InternalVertices (path hst))) :
    StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hvw).graph where
  toSubdivisionModel := {
    branchVertex := fun r =>
      (GraphContraction.collapseEdge G hvw).map (M.branchVertex r)
    branchVertex_injective := hbranch
    edgePath := path
    edgePath_isPath := hpath
    no_internal_branch_vertices :=
      ∀ {x y : W} (hxy : K.Adj x y)
        {z : (GraphContraction.collapseEdge G hvw).Target},
        z ∈ Walk.InternalVertices (path hxy) →
          ∀ r, z ≠ (GraphContraction.collapseEdge G hvw).map
            (M.branchVertex r)
    internally_disjoint_edge_paths :=
      ∀ {x y s t : W} (hxy : K.Adj x y) (hst : K.Adj s t),
        ¬ ((x = s ∧ y = t) ∨ (x = t ∧ y = s)) →
          Disjoint (Walk.InternalVertices (path hxy))
            (Walk.InternalVertices (path hst)) }
  no_internal_branch_vertices' := hbranch_clean
  internally_disjoint_edge_paths' := hdisjoint

/-- Full `K_5` strict-subdivision model after contracting an incident edge at a
degree-two endpoint that is used by at least one source path. -/
noncomputable def StrictSubdivisionModel.K5_collapseEdge_of_degree_le_two_mem_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {a b : Fin 5}
    (hab : K5Graph.Adj a b)
    (hvab : v ∈ (M.edgePath hab).support) :
    StrictSubdivisionModel K5Graph
      (GraphContraction.collapseEdge G hvw).graph :=
  strictSubdivisionModel_collapseEdge_of_pathFamily M hvw
    (StrictSubdivisionModel.K5_collapseEdge_branchVertex_injective_of_degree_le_two M hvw hdegree)
    (fun {_ _} hst => StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two M hvw hdegree hab hvab hst)
    (fun {_ _} hst => StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_isPath M hvw hdegree hab hvab hst)
    (fun {_ _} hst {z} hz r => StrictSubdivisionModel.K5_collapseEdge_edgePath_of_degree_le_two_no_internal_branch_vertices M hvw hdegree hab hvab hst (z := z) hz r)
    (fun {_ _ _ _} hxy hst hne => StrictSubdivisionModel.K5_collapseEdge_edgePaths_of_degree_le_two_internally_disjoint M hvw hdegree hab hvab hxy hst hne)

/-- Full `K_{3,3}` strict-subdivision model after contracting an incident edge
at a degree-two endpoint that is used by at least one source path. -/
noncomputable def StrictSubdivisionModel.K33_collapseEdge_of_degree_le_two_mem_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    {a b : K33Vertex}
    (hab : K33Graph.Adj a b)
    (hvab : v ∈ (M.edgePath hab).support) :
    StrictSubdivisionModel K33Graph
      (GraphContraction.collapseEdge G hvw).graph :=
  strictSubdivisionModel_collapseEdge_of_pathFamily M hvw
    (StrictSubdivisionModel.K33_collapseEdge_branchVertex_injective_of_degree_le_two M hvw hdegree)
    (fun {_ _} hst => StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two M hvw hdegree hab hvab hst)
    (fun {_ _} hst => StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_isPath M hvw hdegree hab hvab hst)
    (fun {_ _} hst {z} hz r => StrictSubdivisionModel.K33_collapseEdge_edgePath_of_degree_le_two_no_internal_branch_vertices M hvw hdegree hab hvab hst (z := z) hz r)
    (fun {_ _ _ _} hxy hst hne => StrictSubdivisionModel.K33_collapseEdge_edgePaths_of_degree_le_two_internally_disjoint M hvw hdegree hab hvab hxy hst hne)

theorem ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two_mem_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (h : ContainsStrictSubdivision K5Graph G)
    {a b : Fin 5}
    (hab : K5Graph.Adj a b)
    (hvab : v ∈ ((Classical.choice h).edgePath hab).support) :
    ContainsStrictSubdivision K5Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  exact ⟨
    StrictSubdivisionModel.K5_collapseEdge_of_degree_le_two_mem_path
      (Classical.choice h) hvw hdegree hab hvab⟩

theorem ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two_mem_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (h : ContainsStrictSubdivision K33Graph G)
    {a b : K33Vertex}
    (hab : K33Graph.Adj a b)
    (hvab : v ∈ ((Classical.choice h).edgePath hab).support) :
    ContainsStrictSubdivision K33Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  exact ⟨
    StrictSubdivisionModel.K33_collapseEdge_of_degree_le_two_mem_path
      (Classical.choice h) hvw hdegree hab hvab⟩

/-- Degree-two reverse-contraction branch for strict `K_5` obstructions.  If
`G` contains a strict `K_5` subdivision, then contracting any edge incident with
a degree-at-most-two endpoint leaves a strict `K_5` subdivision in the
contracted graph. -/
theorem ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (h : ContainsStrictSubdivision K5Graph G) :
    ContainsStrictSubdivision K5Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  by_cases huse :
      Exists fun x : Fin 5 =>
        Exists fun y : Fin 5 =>
          Exists fun hxy : K5Graph.Adj x y =>
            v ∈ ((Classical.choice h).edgePath hxy).support
  · rcases huse with ⟨x, y, hxy, hv⟩
    exact
      ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two_mem_path
        hvw hdegree h hxy hv
  · refine
      ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two_avoids_left
        hvw hdegree h ?_
    intro x y hxy hv
    exact huse ⟨x, y, hxy, hv⟩

/-- Degree-two reverse-contraction branch for strict `K_{3,3}` obstructions. -/
theorem ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (h : ContainsStrictSubdivision K33Graph G) :
    ContainsStrictSubdivision K33Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  by_cases huse :
      Exists fun x : K33Vertex =>
        Exists fun y : K33Vertex =>
          Exists fun hxy : K33Graph.Adj x y =>
            v ∈ ((Classical.choice h).edgePath hxy).support
  · rcases huse with ⟨x, y, hxy, hv⟩
    exact
      ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two_mem_path
        hvw hdegree h hxy hv
  · refine
      ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two_avoids_left
        hvw hdegree h ?_
    intro x y hxy hv
    exact huse ⟨x, y, hxy, hv⟩
end FourColor

end Schematic.Math.GraphTheory
