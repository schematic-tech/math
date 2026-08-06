import Schematic.Math.GraphTheory.Embedding.Kuratowski.InductionPreliminaries
import Schematic.Math.GraphTheory.Embedding.Kuratowski.ObstructionReductions

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Deletion-contraction induction for the contraction-aware source theorem.
The outer induction is on vertex count and the inner induction is on edge
count.  Every edge contraction has therefore been embedded when the source
theorem is invoked. -/
theorem hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSourceWithContraction
    (hsource : CofacialDeletionSourceWithContractionTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      Fintype.card V = n →
        ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
          IsPlanar G → HasEulerRotationSystem G
  have hP : forall n : Nat, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IHv =>
        intro V _ _ hV G _ h_planar
        let Q : Nat → Prop := fun m =>
          ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
            G.edgeFinset.card = m →
              IsPlanar G → HasEulerRotationSystem G
        have hQ : forall m : Nat, Q m := by
          intro m
          induction m using Nat.strong_induction_on with
          | h m IHe =>
              intro G _ hE h_planar
              by_cases hG : G.Preconnected
              · exact
                  HasEulerRotationSystem.of_isPlanar_preconnected_forall_collapseEdge_of_deleteEdge_cofacial_large
                    (G := G) h_planar hG
                    (by
                      intro a b hab
                      letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
                        GraphContraction.collapseEdgeTargetFintype G hab
                      letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
                        GraphContraction.collapseEdgeTargetDecidableEq G hab
                      letI :
                          DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
                        Classical.decRel _
                      intro hcontract_planar
                      have hlt :
                          Fintype.card (GraphContraction.collapseEdge G hab).Target < n := by
                        have hraw :
                            Fintype.card (GraphContraction.collapseEdge G hab).Target <
                              Fintype.card V :=
                          GraphContraction.collapseEdge_target_card_lt G hab
                        omega
                      have hIH :
                          P (Fintype.card (GraphContraction.collapseEdge G hab).Target) :=
                        IHv (Fintype.card (GraphContraction.collapseEdge G hab).Target)
                          hlt
                      exact
                        hIH
                          (V := (GraphContraction.collapseEdge G hab).Target) rfl
                          (G := (GraphContraction.collapseEdge G hab).graph)
                          hcontract_planar)
                    (by
                      intro hlarge hmin
                      have hcontract_embedded :
                          ∀ {a b : V} (hab : G.Adj a b),
                            letI : DecidableRel
                                (GraphContraction.collapseEdge G hab).graph.Adj :=
                              Classical.decRel _
                            HasEulerRotationSystem
                              (GraphContraction.collapseEdge G hab).graph := by
                        intro a b hab
                        letI : Fintype (GraphContraction.collapseEdge G hab).Target :=
                          GraphContraction.collapseEdgeTargetFintype G hab
                        letI : DecidableEq (GraphContraction.collapseEdge G hab).Target :=
                          GraphContraction.collapseEdgeTargetDecidableEq G hab
                        letI :
                            DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj :=
                          Classical.decRel _
                        have hlt :
                            Fintype.card (GraphContraction.collapseEdge G hab).Target < n := by
                          have hraw :
                              Fintype.card (GraphContraction.collapseEdge G hab).Target <
                                Fintype.card V :=
                            GraphContraction.collapseEdge_target_card_lt G hab
                          omega
                        have hIH :
                            P (Fintype.card (GraphContraction.collapseEdge G hab).Target) :=
                          IHv (Fintype.card (GraphContraction.collapseEdge G hab).Target)
                            hlt
                        exact
                          hIH
                            (V := (GraphContraction.collapseEdge G hab).Target) rfl
                            (G := (GraphContraction.collapseEdge G hab).graph)
                            (IsPlanar.collapseEdge h_planar hab)
                      rcases hsource hG h_planar hlarge hmin hcontract_embedded with
                        ⟨a, b, hab, hcofacial_of_deleted⟩
                      refine ⟨a, b, hab, ?_⟩
                      intro hdeleted_planar
                      have hdeleted :
                          HasEulerRotationSystem (EdgeDeletion.deletedGraph G a b) := by
                        have hlt_edge :
                            (EdgeDeletion.deletedGraph G a b).edgeFinset.card < m := by
                          have hraw :
                              (EdgeDeletion.deletedGraph G a b).edgeFinset.card <
                                G.edgeFinset.card := by
                            simpa [EdgeDeletion.deletedGraph] using
                              (edgeFinset_card_deleteEdge_lt (G := G) hab)
                          omega
                        have hIE :
                            Q ((EdgeDeletion.deletedGraph G a b).edgeFinset.card) :=
                          IHe ((EdgeDeletion.deletedGraph G a b).edgeFinset.card)
                            hlt_edge
                        exact
                          hIE
                            (G := EdgeDeletion.deletedGraph G a b)
                            rfl hdeleted_planar
                      exact hcofacial_of_deleted hdeleted)
              · exact
                  HasEulerRotationSystem.of_isPlanar_connectedComponents
                    (G := G) h_planar (by
                      intro C hC_planar
                      letI : Fintype C := C.supp.toFinite.fintype
                      letI : DecidableEq C := Classical.decEq C
                      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
                      have hltC : Fintype.card C < n := by
                        have hraw :
                            Fintype.card C < Fintype.card V :=
                          connectedComponent_card_lt_of_not_preconnected
                            (G := G) hG C
                        omega
                      have hIH : P (Fintype.card C) :=
                        IHv (Fintype.card C) hltC
                      exact
                        hIH
                          (V := C) rfl
                          (G := C.toSimpleGraph) hC_planar)
        have hQG : Q G.edgeFinset.card := hQ G.edgeFinset.card
        exact hQG (G := G) rfl h_planar
  intro V _ _ G _ h_planar
  have hPV : P (Fintype.card V) := hP (Fintype.card V)
  exact hPV (V := V) rfl (G := G) h_planar

/-- Deletion-contraction induction for the ordinary source theorem. -/
theorem hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSource
    (hsource : CofacialDeletionSourceTheorem.{u}) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G :=
  hasEulerRotationSystem_of_isPlanar_of_cofacialDeletionSourceWithContraction
    (by
      intro V _ _ G _ hG hplanar hlarge hmin _hcontract
      exact hsource hG hplanar hlarge hmin)
end FourColor

end Schematic.Math.GraphTheory
