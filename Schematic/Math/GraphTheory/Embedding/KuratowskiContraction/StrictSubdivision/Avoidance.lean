import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.Planarity

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem IsPlanar.collapseEdge
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b) :
    IsPlanar (GraphContraction.collapseEdge G hab).graph where
  no_K5_subdivision :=
    not_containsStrictSubdivision_K5_collapseEdge_of_planar h_planar hab
  no_K33_subdivision :=
    not_containsStrictSubdivision_K33_collapseEdge_of_planar h_planar hab

theorem strictSubdivisionModel_collapseEdge_branchVertex_injective_of_pair_mem_eq
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {a b common : V}
    (hab : G.Adj a b)
    (hcommon : ∀ x, M.branchVertex x ∈ ({a, b} : Set V) →
      M.branchVertex x = common) :
    Function.Injective fun x =>
      (GraphContraction.collapseEdge G hab).map (M.branchVertex x) := by
  classical
  intro x y hxy
  rcases
      (GraphContraction.collapseEdge_map_eq_iff
        (G := G) hab (v := M.branchVertex x) (w := M.branchVertex y)).mp hxy with
    hpair | houtside
  · apply M.branchVertex_injective
    exact (hcommon x hpair.1).trans (hcommon y hpair.2).symm
  · exact M.branchVertex_injective houtside.1

theorem strictSubdivisionModel_collapseEdge_branchVertex_injective_of_avoids_left
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {a b : V}
    (hab : G.Adj a b)
    (havoid_branch : forall x : W, M.branchVertex x ≠ a) :
    Function.Injective
      (fun x : W =>
        (GraphContraction.collapseEdge G hab).map (M.branchVertex x)) :=
  strictSubdivisionModel_collapseEdge_branchVertex_injective_of_pair_mem_eq
    M hab fun x hx => by
      rcases hx with hx | hx
      · exact False.elim (havoid_branch x hx)
      · exact hx

theorem strictSubdivisionModel_collapseEdge_branchVertex_injective_of_avoids_right
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {a b : V}
    (hab : G.Adj a b)
    (havoid_branch : forall x : W, M.branchVertex x ≠ b) :
    Function.Injective
      (fun x : W =>
        (GraphContraction.collapseEdge G hab).map (M.branchVertex x)) :=
  strictSubdivisionModel_collapseEdge_branchVertex_injective_of_pair_mem_eq
    M hab fun x hx => by
      rcases hx with hx | hx
      · exact hx
      · exact False.elim (havoid_branch x hx)

noncomputable def strictSubdivisionModel_collapseEdge_of_avoids_left
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {a b : V}
    (hab : G.Adj a b)
    (havoid_branch : forall x : W, M.branchVertex x ≠ a)
    (havoid_path :
      forall {x y : W} (hxy : K.Adj x y) {z : V},
        z ∈ (M.edgePath hxy).support -> z ≠ a) :
    StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph :=
  (M.targetRestrict {z : V | z ≠ a}
      (fun x => havoid_branch x)
      (by
        intro x y hxy z hz
        exact havoid_path hxy hz)).map
    (GraphContraction.collapseEdgeDeleteLeftHom G hab)
    (GraphContraction.collapseEdgeDeleteLeftHom_injective G hab)

noncomputable def strictSubdivisionModel_collapseEdge_of_avoids_right
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel K G)
    {a b : V}
    (hab : G.Adj a b)
    (havoid_branch : forall x : W, M.branchVertex x ≠ b)
    (havoid_path :
      forall {x y : W} (hxy : K.Adj x y) {z : V},
        z ∈ (M.edgePath hxy).support -> z ≠ b) :
    StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph :=
  (M.targetRestrict {z : V | z ≠ b}
      (fun x => havoid_branch x)
      (by
        intro x y hxy z hz
        exact havoid_path hxy hz)).map
    (GraphContraction.collapseEdgeDeleteRightHom G hab)
    (GraphContraction.collapseEdgeDeleteRightHom_injective G hab)

theorem ContainsStrictSubdivision.collapseEdge_of_avoids_left
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (h : ContainsStrictSubdivision K G)
    (havoid_branch :
      forall x : W, (Classical.choice h).branchVertex x ≠ a)
    (havoid_path :
      forall {x y : W} (hxy : K.Adj x y) {z : V},
        z ∈ ((Classical.choice h).edgePath hxy).support -> z ≠ a) :
    ContainsStrictSubdivision K
      (GraphContraction.collapseEdge G hab).graph := by
  classical
  exact ⟨strictSubdivisionModel_collapseEdge_of_avoids_left
    (Classical.choice h) hab havoid_branch havoid_path⟩

theorem ContainsStrictSubdivision.collapseEdge_of_avoids_right
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (h : ContainsStrictSubdivision K G)
    (havoid_branch :
      forall x : W, (Classical.choice h).branchVertex x ≠ b)
    (havoid_path :
      forall {x y : W} (hxy : K.Adj x y) {z : V},
        z ∈ ((Classical.choice h).edgePath hxy).support -> z ≠ b) :
    ContainsStrictSubdivision K
      (GraphContraction.collapseEdge G hab).graph := by
  classical
  exact ⟨strictSubdivisionModel_collapseEdge_of_avoids_right
    (Classical.choice h) hab havoid_branch havoid_path⟩

noncomputable def strictSubdivisionModel_K5_collapseEdge_of_degree_le_two_avoids_left
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K5Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (havoid_path :
      forall {x y : Fin 5} (hxy : K5Graph.Adj x y),
        v ∉ (M.edgePath hxy).support) :
    StrictSubdivisionModel K5Graph
      (GraphContraction.collapseEdge G hvw).graph :=
  strictSubdivisionModel_collapseEdge_of_avoids_left M hvw
    (fun x => M.K5_branchVertex_ne_of_degree_le_three (by omega) x)
    (by
      intro x y hxy z hz hzv
      exact havoid_path hxy (by simpa [hzv] using hz))

noncomputable def strictSubdivisionModel_K33_collapseEdge_of_degree_le_two_avoids_left
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : StrictSubdivisionModel K33Graph G)
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (havoid_path :
      forall {x y : K33Vertex} (hxy : K33Graph.Adj x y),
        v ∉ (M.edgePath hxy).support) :
    StrictSubdivisionModel K33Graph
      (GraphContraction.collapseEdge G hvw).graph :=
  strictSubdivisionModel_collapseEdge_of_avoids_left M hvw
    (fun x => M.K33_branchVertex_ne_of_degree_le_two hdegree x)
    (by
      intro x y hxy z hz hzv
      exact havoid_path hxy (by simpa [hzv] using hz))

theorem ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two_avoids_left
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (h : ContainsStrictSubdivision K5Graph G)
    (havoid_path :
      forall {x y : Fin 5} (hxy : K5Graph.Adj x y),
        v ∉ ((Classical.choice h).edgePath hxy).support) :
    ContainsStrictSubdivision K5Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  exact ⟨strictSubdivisionModel_K5_collapseEdge_of_degree_le_two_avoids_left
    (Classical.choice h) hvw hdegree havoid_path⟩

theorem ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two_avoids_left
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 2)
    (h : ContainsStrictSubdivision K33Graph G)
    (havoid_path :
      forall {x y : K33Vertex} (hxy : K33Graph.Adj x y),
        v ∉ ((Classical.choice h).edgePath hxy).support) :
    ContainsStrictSubdivision K33Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  exact ⟨strictSubdivisionModel_K33_collapseEdge_of_degree_le_two_avoids_left
    (Classical.choice h) hvw hdegree havoid_path⟩

/-- Degree-one vertices cannot participate in a strict `K_5` subdivision, so
any strict `K_5` obstruction in `G` survives contraction of an incident edge at
that vertex.  This is the first reverse-contraction branch in the
Makarychev/Skopenkov induction. -/
theorem ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_one
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (h : ContainsStrictSubdivision K5Graph G) :
    ContainsStrictSubdivision K5Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  refine ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two_avoids_left
    hvw (by omega) h ?_
  intro x y hxy hv
  exact (Classical.choice h).K5_edgePath_support_ne_of_degree_le_one
    hdegree hxy hv rfl

/-- The analogous degree-one reverse-contraction branch for `K_{3,3}`. -/
theorem ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_one
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (h : ContainsStrictSubdivision K33Graph G) :
    ContainsStrictSubdivision K33Graph
      (GraphContraction.collapseEdge G hvw).graph := by
  classical
  refine ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two_avoids_left
    hvw (by omega) h ?_
  intro x y hxy hv
  exact (Classical.choice h).K33_edgePath_support_ne_of_degree_le_one
    hdegree hxy hv rfl

/-- Source-facing contraction extension for a degree-one endpoint.  If
contracting an incident edge at such a vertex is planar in the
strict-subdivision sense, then the original graph is planar. -/
theorem IsPlanar.of_collapseEdge_of_degree_le_one
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (h_planar :
      IsPlanar (GraphContraction.collapseEdge G hvw).graph)
    (hdegree : G.degree v <= 1) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact h_planar.no_K5_subdivision
      (ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_one
        hvw hdegree hK5)
  · intro hK33
    exact h_planar.no_K33_subdivision
      (ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_one
        hvw hdegree hK33)
end FourColor

end Schematic.Math.GraphTheory
