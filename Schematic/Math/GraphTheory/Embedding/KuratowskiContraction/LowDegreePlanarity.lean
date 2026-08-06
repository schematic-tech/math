import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Paths.Reflection

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Source-facing contraction extension for a degree-two endpoint.  This is the
formal version of the Makarychev/Skopenkov induction line: when a vertex of
degree at most two is incident with an edge whose contraction is planar, the
original graph is planar. -/
theorem IsPlanar.of_collapseEdge_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (h_planar :
      IsPlanar (GraphContraction.collapseEdge G hvw).graph)
    (hdegree : G.degree v <= 2) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact h_planar.no_K5_subdivision
      (ContainsStrictSubdivision.K5_collapseEdge_of_degree_le_two
        hvw hdegree hK5)
  · intro hK33
    exact h_planar.no_K33_subdivision
      (ContainsStrictSubdivision.K33_collapseEdge_of_degree_le_two
        hvw hdegree hK33)

/-- Source-proof low-degree branch packaged in the exact form used by
Makarychev/Skopenkov: if a degree-at-most-two vertex has an incident edge whose
contraction is planar, then the original graph is planar. -/
theorem IsPlanar.of_incident_collapseEdge_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V}
    (hdegree : G.degree v <= 2)
    (hincident : Exists fun w : V => G.Adj v w)
    (hcontract :
      forall {w : V} (hvw : G.Adj v w),
        IsPlanar (GraphContraction.collapseEdge G hvw).graph) :
    IsPlanar G := by
  rcases hincident with ⟨w, hvw⟩
  exact IsPlanar.of_collapseEdge_of_degree_le_two
    hvw (hcontract hvw) hdegree

/-- First reduction in the Makarychev/Skopenkov proposition.  In a connected
graph, if every edge contraction is already planar, then the existence of a
vertex of degree at most two makes the original graph planar.  The isolated
vertex subcase collapses the connected graph to a one-vertex graph; the
non-isolated subcase is the checked degree-two uncontraction branch above. -/
theorem IsPlanar.of_preconnected_forall_collapseEdge_of_exists_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hdegree : Exists fun v : V => G.degree v <= 2)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        IsPlanar (GraphContraction.collapseEdge G hab).graph) :
    IsPlanar G := by
  classical
  rcases hdegree with ⟨v, hvdeg⟩
  by_cases hincident : Exists fun w : V => G.Adj v w
  · exact IsPlanar.of_incident_collapseEdge_of_degree_le_two
      (G := G) hvdeg hincident (by
        intro w hvw
        exact hcontract hvw)
  · have hvzero : G.degree v = 0 := by
      exact Nat.eq_zero_of_not_pos (by
        intro hpos
        exact hincident ((G.degree_pos_iff_exists_adj v).mp hpos))
    haveI : Subsingleton V := ⟨by
      intro x y
      have hxv : x = v := by
        by_contra hxv
        exact
          (SimpleGraph.not_reachable_of_right_degree_zero
            (G := G) hxv hvzero) (hG x v)
      have hyv : y = v := by
        by_contra hyv
        exact
          (SimpleGraph.not_reachable_of_right_degree_zero
            (G := G) hyv hvzero) (hG y v)
      exact hxv.trans hyv.symm⟩
    exact IsPlanar.of_max_degree_le_two (G := G) (by
      intro x
      have hno : forall y : V, ¬ G.Adj x y := by
        intro y hxy
        exact hxy.ne (Subsingleton.elim x y)
      have hxzero : G.degree x = 0 := by
        exact Nat.eq_zero_of_not_pos (by
          intro hpos
          rcases (G.degree_pos_iff_exists_adj x).mp hpos with ⟨y, hxy⟩
          exact hno y hxy)
      omega)

/-- Contrapositive form of the same source reduction.  A connected non-planar
minimal counterexample whose edge contractions are planar has minimum degree
at least three. -/
theorem min_degree_three_of_not_planar_preconnected_forall_collapseEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.Preconnected)
    (hcontract :
      forall {a b : V} (hab : G.Adj a b),
        IsPlanar (GraphContraction.collapseEdge G hab).graph)
    (hnot_planar : ¬ IsPlanar G) :
    forall v : V, 3 <= G.degree v := by
  intro v
  by_contra hlt
  have hvdeg : G.degree v <= 2 := by omega
  exact hnot_planar
    (IsPlanar.of_preconnected_forall_collapseEdge_of_exists_degree_le_two
      (G := G) hG ⟨v, hvdeg⟩ hcontract)

theorem collapsedVertex_mem_support_of_containsStrictSubdivision_K5_collapseSubgraph
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hK5 :
      ContainsStrictSubdivision K5Graph
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    none ∈ (GraphContraction.collapseSubgraph G H hH_connected).graph.support := by
  classical
  by_contra hnone
  exact
    (not_containsStrictSubdivision_K5_collapseSubgraph_of_support_avoids
      h_planar H hH_connected
      (by
        intro y hy hy_none
        exact hnone (by simpa [hy_none] using hy))) hK5

theorem collapsedVertex_mem_support_of_containsStrictSubdivision_K33_collapseSubgraph
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hK33 :
      ContainsStrictSubdivision K33Graph
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    none ∈ (GraphContraction.collapseSubgraph G H hH_connected).graph.support := by
  classical
  by_contra hnone
  exact
    (not_containsStrictSubdivision_K33_collapseSubgraph_of_support_avoids
      h_planar H hH_connected
      (by
        intro y hy hy_none
        exact hnone (by simpa [hy_none] using hy))) hK33

theorem exists_attachment_of_containsStrictSubdivision_K5_collapseSubgraph
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hK5 :
      ContainsStrictSubdivision K5Graph
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    Exists fun u : V =>
      Exists fun v : V => u ∈ H.verts ∧ v ∉ H.verts ∧ G.Adj u v := by
  exact
    (GraphContraction.collapseSubgraph_none_mem_support_iff G H hH_connected).mp
      (collapsedVertex_mem_support_of_containsStrictSubdivision_K5_collapseSubgraph
        h_planar H hH_connected hK5)

theorem exists_attachment_of_containsStrictSubdivision_K33_collapseSubgraph
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    (hK33 :
      ContainsStrictSubdivision K33Graph
        (GraphContraction.collapseSubgraph G H hH_connected).graph) :
    Exists fun u : V =>
      Exists fun v : V => u ∈ H.verts ∧ v ∉ H.verts ∧ G.Adj u v := by
  exact
    (GraphContraction.collapseSubgraph_none_mem_support_iff G H hH_connected).mp
      (collapsedVertex_mem_support_of_containsStrictSubdivision_K33_collapseSubgraph
        h_planar H hH_connected hK33)

theorem exists_endpoint_attachment_of_containsStrictSubdivision_K5_collapseEdge
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (hK5 :
      ContainsStrictSubdivision K5Graph
        (GraphContraction.collapseEdge G hab).graph) :
    Exists fun v : V =>
      v ∉ ({a, b} : Set V) ∧ (G.Adj a v ∨ G.Adj b v) := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected := GraphContraction.connected_top_induce_pair_of_adj
    (G := G) hab
  have hK5' :
      ContainsStrictSubdivision K5Graph
        (GraphContraction.collapseSubgraph G H hH).graph := by
    simpa [GraphContraction.collapseEdge, H, hH] using hK5
  rcases exists_attachment_of_containsStrictSubdivision_K5_collapseSubgraph
      h_planar H hH hK5' with ⟨u, v, huH, hvH, huv⟩
  have hu_pair : u = a ∨ u = b := by
    change u ∈ ({a, b} : Set V) at huH
    simpa using huH
  have hv_pair : v ∉ ({a, b} : Set V) := by
    change v ∉ ({a, b} : Set V) at hvH
    exact hvH
  rcases hu_pair with rfl | rfl
  · exact ⟨v, hv_pair, Or.inl huv⟩
  · exact ⟨v, hv_pair, Or.inr huv⟩

theorem exists_endpoint_attachment_of_containsStrictSubdivision_K33_collapseEdge
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (hK33 :
      ContainsStrictSubdivision K33Graph
        (GraphContraction.collapseEdge G hab).graph) :
    Exists fun v : V =>
      v ∉ ({a, b} : Set V) ∧ (G.Adj a v ∨ G.Adj b v) := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected := GraphContraction.connected_top_induce_pair_of_adj
    (G := G) hab
  have hK33' :
      ContainsStrictSubdivision K33Graph
        (GraphContraction.collapseSubgraph G H hH).graph := by
    simpa [GraphContraction.collapseEdge, H, hH] using hK33
  rcases exists_attachment_of_containsStrictSubdivision_K33_collapseSubgraph
      h_planar H hH hK33' with ⟨u, v, huH, hvH, huv⟩
  have hu_pair : u = a ∨ u = b := by
    change u ∈ ({a, b} : Set V) at huH
    simpa using huH
  have hv_pair : v ∉ ({a, b} : Set V) := by
    change v ∉ ({a, b} : Set V) at hvH
    exact hvH
  rcases hu_pair with rfl | rfl
  · exact ⟨v, hv_pair, Or.inl huv⟩
  · exact ⟨v, hv_pair, Or.inr huv⟩
end FourColor

end Schematic.Math.GraphTheory
