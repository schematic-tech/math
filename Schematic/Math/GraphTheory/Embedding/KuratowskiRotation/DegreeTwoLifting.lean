import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.DegreeTwoSubdivision

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

/-- Non-adjacent degree-two contraction induction branch: if contracting one
incident edge at `v` gives an Euler-planar rotation system, and the two
neighbours of `v` are not adjacent, then the original graph is obtained by a
checked pure edge subdivision. -/
theorem HasEulerRotationSystem.of_collapseEdge_of_degree_two_nonadjacent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (hcontract :
      HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem G := by
  rcases hcontract with ⟨R, hR⟩
  exact
    ⟨DegreeTwoSubdivision.nonAdjacentSubdivisionRotationSystem
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hnonadj R,
      DegreeTwoSubdivision.nonAdjacentSubdivisionRotationSystem_dual_eulerPlanar
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj R hR⟩

/-- Adjacent degree-two contraction induction branch: if the two neighbours of
the degree-two vertex are already adjacent, then uncontraction is the checked
triangle/local-face expansion of the contracted graph rotation system. -/
theorem HasEulerRotationSystem.of_collapseEdge_of_degree_two_adjacent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (hcontract :
      HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem G := by
  rcases hcontract with ⟨R, hR⟩
  exact
    ⟨DegreeTwoSubdivision.adjacentTriangleRotationSystem
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hadj R,
      DegreeTwoSubdivision.adjacentTriangleRotationSystem_dual_eulerPlanar
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R hR⟩

/-- Degree-two contraction branch with exact local neighbour data.  The two
neighbours of the restored vertex either are adjacent, giving the triangle
lift, or are non-adjacent, giving the subdivision lift. -/
theorem HasEulerRotationSystem.of_collapseEdge_of_degree_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hcontract :
      HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem G := by
  classical
  by_cases hadj : G.Adj w u
  · exact
      HasEulerRotationSystem.of_collapseEdge_of_degree_two_adjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj hcontract
  · exact
      HasEulerRotationSystem.of_collapseEdge_of_degree_two_nonadjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj hcontract

/-- Incident-edge form of the degree-two contraction branch. -/
theorem HasEulerRotationSystem.of_incident_collapseEdge_of_degree_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V}
    (hupper : G.degree v <= 2)
    (hlower : ¬ G.degree v <= 1)
    (hincident : Exists fun w : V => G.Adj v w)
    (hcontract :
      forall {w : V} (hvw : G.Adj v w),
        letI : DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj :=
          Classical.decRel _
        HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    HasEulerRotationSystem G := by
  classical
  rcases hincident with ⟨w, hvw⟩
  rcases exists_second_neighbor_and_neighbor_eq_of_degree_le_two
      (G := G) (v := v) (w := w) hupper hlower hvw with
    ⟨u, hvu, huw, hneigh⟩
  have hu : u ∉ ({v, w} : Set V) := by
    have huv : u ≠ v := hvu.ne'
    simp [huv, huw]
  letI : DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj :=
    Classical.decRel _
  exact
    HasEulerRotationSystem.of_collapseEdge_of_degree_two
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh (hcontract hvw)


end FourColor

end Schematic.Math.GraphTheory
