import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.SuppressionGraph
import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph
open RotationSystemVertexDeletion

namespace RotationSoundness
theorem deletedGraph_suppressionGraph_eq_induce
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (huv : u ≠ v)
    (hnonadj : ¬ G.Adj w u) :
    EdgeDeletion.deletedGraph
        (suppressionGraph G v ⟨w, hvw.ne'⟩ ⟨u, huv⟩)
        ⟨w, hvw.ne'⟩ ⟨u, huv⟩ =
      G.induce {z : V | z ≠ v} := by
  ext x y
  simp only [EdgeDeletion.deletedGraph, SimpleGraph.deleteEdges_adj,
    suppressionGraph, SimpleGraph.sup_adj, SimpleGraph.induce_adj,
    SimpleGraph.edge_adj, Set.mem_singleton_iff, Sym2.eq_iff,
    ne_eq, not_or, not_and_or]
  constructor
  · rintro ⟨hG | hedge, hnot⟩
    · exact hG
    · rcases hedge.1 with hforward | hbackward
      · exact False.elim (hnot.1.elim
          (fun hx => hx hforward.1) (fun hy => hy hforward.2))
      · exact False.elim (hnot.2.elim
          (fun hx => hx hbackward.1) (fun hy => hy hbackward.2))
  · intro hG
    refine ⟨Or.inl hG, ?_, ?_⟩
    · by_contra h
      push Not at h
      exact hnonadj (by simpa [h.1, h.2] using hG)
    · by_contra h
      push Not at h
      exact hnonadj (by simpa [h.1, h.2] using hG.symm)

/-- Insert an edge into an Euler-planar rotation indexed by a propositionally
equal deleted graph, using explicit cofacial endpoint darts. -/
theorem HasEulerRotationSystem.of_deletedGraph_eq_cofacial_pivots
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {a b : V}
    (hab : H.Adj a b)
    (hdel : EdgeDeletion.deletedGraph H a b = G)
    (R : RotationSystem G)
    (hR : R.toHypermap.dual.EulerPlanar)
    {p q : OrientedEdge G}
    (hp : p.tail = a)
    (hq : q.tail = b)
    (hreach : PermReachable R.toHypermap.face p q) :
    HasEulerRotationSystem H := by
  classical
  let D := EdgeDeletion.deletedGraph H a b
  letI : DecidableRel D.Adj := inferInstance
  let φ : D ≃g G := {
    toEquiv := Equiv.refl V
    map_rel_iff' := by
      intro x y
      change G.Adj x y ↔ (EdgeDeletion.deletedGraph H a b).Adj x y
      rw [hdel]
  }
  let RD : RotationSystem D := RotationSystem.ofIso φ R
  let ψ : Hypermap.Iso RD.toHypermap R.toHypermap :=
    RotationSystem.ofIso_toHypermapIso φ R
  have hRD : RD.toHypermap.dual.EulerPlanar := by
    have hprimal : R.toHypermap.EulerPlanar :=
      R.toHypermap.dual_eulerPlanar_iff.mp hR
    have hsource : RD.toHypermap.EulerPlanar :=
      (ψ.eulerPlanar_iff).mpr hprimal
    exact RD.toHypermap.dual_eulerPlanar_iff.mpr hsource
  let E := orientedEdgeEquivOfGraphIso φ
  let pD : OrientedEdge D := E.symm p
  let qD : OrientedEdge D := E.symm q
  have hpD : pD.tail = a := by
    simpa [pD, E, φ, orientedEdgeEquivOfGraphIso, OrientedEdge.tail] using hp
  have hqD : qD.tail = b := by
    simpa [qD, E, φ, orientedEdgeEquivOfGraphIso, OrientedEdge.tail] using hq
  have hreachD : PermReachable RD.toHypermap.face pD qD := by
    apply (ψ.faceReachable_iff).mpr
    simpa [pD, qD, E, ψ, φ] using hreach
  exact HasEulerRotationSystem.of_deleteEdge_of_cofacial_pivots
    hab RD hRD hpD hqD
      ((EdgeDeletion.addEdgeCofacial_some_some RD.toHypermap pD qD).mpr
        hreachD)

/-- Contracting an edge at a degree-two vertex preserves an Euler-planar
rotation whenever the source graph is two-connected. -/
theorem HasEulerRotationSystem.collapseEdge_of_degree_two_of_isTwoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h2 : IsTwoConnected G)
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hneigh : forall z : V, G.Adj v z -> z = w ∨ z = u)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hG : HasEulerRotationSystem G) :
    HasEulerRotationSystem (GraphContraction.collapseEdge G hvw).graph := by
  classical
  rcases hG with ⟨R, hR⟩
  let D : SimpleGraph {z : V // z ≠ v} := G.induce {z : V | z ≠ v}
  let wD : {z : V // z ≠ v} := ⟨w, hvw.ne'⟩
  let uD : {z : V // z ≠ v} := ⟨u, huv⟩
  let J : SimpleGraph {z : V // z ≠ v} := suppressionGraph G v wD uD
  letI : DecidableRel J.Adj := Classical.decRel _
  let RD : RotationSystem D := vertexDeletedRotationSystem R v
  have hRD : RD.toHypermap.dual.EulerPlanar :=
    vertexDeletedRotationSystem_dual_eulerPlanar R v hR
  have hJ : HasEulerRotationSystem J := by
    by_cases hadj : G.Adj w u
    · have hadjD : D.Adj wD uD := by
        exact hadj
      have hJD : J = D := by
        exact SimpleGraph.sup_edge_of_adj D hadjD
      let φ : J ≃g D := {
        toEquiv := Equiv.refl _
        map_rel_iff' := by
          intro x y
          change D.Adj x y ↔ J.Adj x y
          rw [hJD]
      }
      exact HasEulerRotationSystem.of_iso φ ⟨RD, hRD⟩
    · have hJU : J.Adj wD uD := by
        exact (SimpleGraph.sup_adj _ _ _ _).mpr
          (Or.inr ((SimpleGraph.edge_adj wD uD wD uD).mpr
            ⟨Or.inl ⟨rfl, rfl⟩, by simpa [wD, uD] using huw.symm⟩))
      have hdel : EdgeDeletion.deletedGraph J wD uD = D := by
        simpa [J, D, wD, uD] using
          deletedGraph_suppressionGraph_eq_induce
            (G := G) hvw huv hadj
      have hnode : forall d : OrientedEdge G, R.node d ≠ d :=
        node_ne_self_of_isTwoConnected R h2
      let dw : OrientedEdge G := ⟨(v, w), hvw⟩
      let du : OrientedEdge G := ⟨(v, u), hvu⟩
      let p : OrientedEdge D := vertexDeletedFacePort R v hnode dw rfl
      let q : OrientedEdge D := vertexDeletedFacePort R v hnode du rfl
      have hp : p.tail = wD := by
        apply Subtype.ext
        exact vertexDeletedFacePort_tail_val R v hnode dw rfl
      have hq : q.tail = uD := by
        apply Subtype.ext
        exact vertexDeletedFacePort_tail_val R v hnode du rfl
      have hreach : PermReachable RD.toHypermap.face p q := by
        exact vertexDeletedFacePort_faceReachable_of_isTwoConnected_dualEulerPlanar
          R h2 hR v dw du rfl rfl
      exact HasEulerRotationSystem.of_deletedGraph_eq_cofacial_pivots
        hJU hdel RD hRD hp hq hreach
  exact HasEulerRotationSystem.of_iso
    (suppressionGraphIsoCollapse hvw hvu huv huw hneigh).symm hJ




end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
