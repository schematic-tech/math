import Schematic.Math.GraphTheory.Embedding.RotationSystemPathGluing.PreservedFacialCycles
import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.FacialPathSplits

/-! Gluing facial paths while preserving both complementary faces. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

open RotationSystemFan

/-- Cycle-sum gluing of two facial-path splits, retaining the two
complementary boundary faces.  This is the face-marked form needed for disk
gluing: the selected fan faces are removed by the cycle sum, while the other
two fan faces remain facial by directional dart disjointness. -/
theorem exists_cycleSum_preserving_complementary_faces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel K.Adj]
    {R : RotationSystem G} {T : RotationSystem K}
    {r r' s t : V}
    {c : G.Walk r r} {d : K.Walk r' r'}
    {p : G.Walk s t} {q : K.Walk t s}
    {hp : p.IsPath} {hq : q.IsPath} {hst : s ≠ t}
    [DecidableRel
      (RotationSystemFan.addNodeGraph G (insert t ({s} : Set V))).Adj]
    [DecidableRel
      (RotationSystemFan.addNodeGraph K (insert s ({t} : Set V))).Adj]
    (D₁ : RotationSystemFan.FacialPathSplitData R c p hp hst)
    (D₂ : RotationSystemFan.FacialPathSplitData T d q hq hst.symm)
    (hc : c.IsCycle) (hd : d.IsCycle)
    (hpSegment : p.support = ((c.drop 1).take p.length).support)
    (hpProper : p.length + 1 < c.length)
    (hqSegment : q.support = ((d.drop 1).take q.length).support)
    (hqProper : q.length + 1 < d.length)
    (hsupport : q.support = p.reverse.support)
    (hcommon : forall ⦃x y : Option V⦄,
      (RotationSystemFan.addNodeGraph G
          (insert t ({s} : Set V))).Adj x y ->
        (RotationSystemFan.addNodeGraph K
            (insert s ({t} : Set V))).Adj x y ->
          (RotationSystemFan.addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe.Adj
            x y)
    (hmeet : forall ⦃v : Option V⦄,
      v ∈ (RotationSystemFan.addNodeGraph G
          (insert t ({s} : Set V))).support ->
        v ∈ (RotationSystemFan.addNodeGraph K
            (insert s ({t} : Set V))).support ->
          v ∈ (RotationSystemFan.addNodeGraphPathCycleAtNew p).support)
    (hG : (G.induce G.support).Preconnected)
    (hK : (K.induce K.support).Preconnected)
    (hsG : s ∈ G.support) (htG : t ∈ G.support)
    (htK : t ∈ K.support) (hsK : s ∈ K.support) :
    Exists fun a : G.Walk t s =>
      Exists fun ha : a.IsPath =>
        a.darts = c.darts.drop (p.length + 1) ++ c.darts.take 1 ∧
          a.darts.map (orientedEdgeDartEquiv (G := G)).symm =
              D₁.next :: D₁.outer ++ [D₁.closing] ∧
            Exists fun b : K.Walk s t =>
              Exists fun hb : b.IsPath =>
                b.darts = d.darts.drop (q.length + 1) ++ d.darts.take 1 ∧
                  b.darts.map (orientedEdgeDartEquiv (G := K)).symm =
                      D₂.next :: D₂.outer ++ [D₂.closing] ∧
                  let left :=
                    ((a.darts.map
                        (orientedEdgeDartEquiv (G := G)).symm).map
                      (RotationSystemFan.addNodeGraphSomeOrientedEdge G
                        (insert t ({s} : Set V)))).map
                        (liftOrientedEdge (show
                          RotationSystemFan.addNodeGraph G
                              (insert t ({s} : Set V)) <=
                            RotationSystemFan.addNodeGraph G
                                (insert t ({s} : Set V)) ⊔
                              RotationSystemFan.addNodeGraph K
                                (insert s ({t} : Set V)) from le_sup_left))
                  let right :=
                    ((b.darts.map
                        (orientedEdgeDartEquiv (G := K)).symm).map
                      (RotationSystemFan.addNodeGraphSomeOrientedEdge K
                        (insert s ({t} : Set V)))).map
                        (liftOrientedEdge (show
                          RotationSystemFan.addNodeGraph K
                              (insert s ({t} : Set V)) <=
                            RotationSystemFan.addNodeGraph G
                                (insert t ({s} : Set V)) ⊔
                              RotationSystemFan.addNodeGraph K
                                (insert s ({t} : Set V)) from le_sup_right))
                  (left ++ right).Nodup ∧
                  Exists fun U : RotationSystem
                    (RotationSystemFan.addNodeGraph G
                        (insert t ({s} : Set V)) ⊔
                      RotationSystemFan.addNodeGraph K
                        (insert s ({t} : Set V))) =>
                  U.toHypermap.dual.EulerPlanar ∧
                    IsFacialCycle U
                      ((RotationSystemFan.addNodeGraphPathCycleAtNewIn G
                          (insert t ({s} : Set V)) (by simp) (by simp) a).mapLe
                        le_sup_left)
                      ((RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
                          (insert t ({s} : Set V)) (by simp) (by simp)
                            hst.symm a ha).mapLe le_sup_left) ∧
                    IsFacialCycle U
                      ((RotationSystemFan.addNodeGraphPathCycleAtNewIn K
                          (insert s ({t} : Set V)) (by simp) (by simp) b).mapLe
                        le_sup_right)
                      ((RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
                          (insert s ({t} : Set V)) (by simp) (by simp)
                            hst b hb).mapLe le_sup_right) := by
  classical
  rcases D₁.exists_complementaryFacialPath hc hpSegment hpProper with
    ⟨a, ha, haRawDarts, haDarts, haFacial⟩
  rcases D₂.exists_complementaryFacialPath hd hqSegment hqProper with
    ⟨b, hb, hbRawDarts, hbDarts, hbFacial⟩
  let H₁ := RotationSystemFan.addNodeGraph G (insert t ({s} : Set V))
  let H₂ := RotationSystemFan.addNodeGraph K (insert s ({t} : Set V))
  let selected : H₁.Walk none none :=
    RotationSystemFan.addNodeGraphPathCycleAtNew p
  let selected₂ : H₂.Walk none none :=
    RotationSystemFan.addNodeGraphPathCycleAtNew q
  let C : SimpleGraph (Option V) := selected.toSubgraph.spanningCoe
  let common : C.Walk none none := SimpleGraph.Walk.toSpanningCoe selected
  have hC₁ : C ≤ H₁ := selected.toSubgraph.spanningCoe_le
  have hspanEq :
      selected.toSubgraph.spanningCoe =
        selected₂.toSubgraph.spanningCoe :=
    RotationSystemFan.addNodeGraphPathCycleAtNew_spanningCoe_eq_of_reverse_support
      p q hsupport
  have hC₂ : C ≤ H₂ := by
    rw [show C = selected₂.toSubgraph.spanningCoe by exact hspanEq]
    exact selected₂.toSubgraph.spanningCoe_le
  have hselectedCycle : selected.IsCycle :=
    RotationSystemFan.addNodeGraphPathCycleAtNew_isCycle hst p hp
  have hcommonCycle : common.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_mapLe hC₁
    simpa [common, C, selected] using hselectedCycle
  have hspan : common.toSubgraph.spanningCoe = C := by
    calc
      common.toSubgraph.spanningCoe = selected.toSubgraph.spanningCoe :=
        SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq
          common selected (by
            simp [common, SimpleGraph.Walk.support_toSpanningCoe])
      _ = C := rfl
  have hfacial₁ :
      IsFacialCycle D₁.rotation
        (common.mapLe hC₁) (hcommonCycle.mapLe hC₁) := by
    simpa [common, C, selected] using D₁.selected_facial
  have hwalk₁ : common.mapLe hC₁ = selected := by
    apply SimpleGraph.Walk.support_injective
    simp [common]
  have hwalk₂ : (common.mapLe hC₂).reverse = selected₂ := by
    apply SimpleGraph.Walk.support_injective
    rw [_root_.SimpleGraph.Walk.support_reverse,
      _root_.SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_toSpanningCoe]
    simpa [selected, selected₂,
      _root_.SimpleGraph.Walk.support_reverse] using
        (RotationSystemFan.addNodeGraphPathCycleAtNew_support_eq_reverse
          p q hsupport).symm
  have hfacial₂ :
      IsFacialCycle D₂.rotation
        (common.mapLe hC₂).reverse
        (hcommonCycle.mapLe hC₂).reverse := by
    simpa [hwalk₂, selected₂] using D₂.selected_facial
  have hmeetCommon : forall ⦃v : Option V⦄,
      v ∈ H₁.support -> v ∈ H₂.support -> v ∈ common.support := by
    intro v hv₁ hv₂
    have hv := hmeet hv₁ hv₂
    simpa [common, selected] using hv
  let U := RotationSystemGluing.cycleSum
    D₁.rotation D₂.rotation hC₁ hC₂ hcommon
      common hcommonCycle hspan hfacial₁ hfacial₂ hmeetCommon
  have hconn₁ : D₁.rotation.toHypermap.Connected :=
    D₁.toHypermap_connected hG hsG htG
  have hconn₂ : D₂.rotation.toHypermap.Connected :=
    D₂.toHypermap_connected hK htK hsK
  have hU : U.toHypermap.dual.EulerPlanar :=
    RotationSystemGluing.cycleSum_dual_eulerPlanar
      D₁.rotation D₂.rotation hC₁ hC₂ hcommon
        common hcommonCycle hspan hfacial₁ hfacial₂ hmeetCommon
        hconn₁ hconn₂ D₁.dual_eulerPlanar D₂.dual_eulerPlanar
  let outer₁ := RotationSystemFan.addNodeGraphPathCycleAtNewIn G
    (insert t ({s} : Set V)) (by simp) (by simp) a
  let houter₁ : outer₁.IsCycle :=
    RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
      (insert t ({s} : Set V)) (by simp) (by simp) hst.symm a ha
  let outer₂ := RotationSystemFan.addNodeGraphPathCycleAtNewIn K
    (insert s ({t} : Set V)) (by simp) (by simp) b
  let houter₂ : outer₂.IsCycle :=
    RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
      (insert s ({t} : Set V)) (by simp) (by simp) hst b hb
  have hdisjoint₁ : forall e : OrientedEdge H₁,
      CycleForwardDart outer₁ e ->
        Not (CycleForwardDart (common.mapLe hC₁) e) := by
    intro e he hcommonForward
    exact D₁.complementary_forward_disjoint_selected hc haDarts e
      (by simpa [outer₁, H₁] using he)
      (by simpa [hwalk₁, selected] using hcommonForward)
  have hdisjoint₂ : forall e : OrientedEdge H₂,
      CycleForwardDart outer₂ e ->
        Not (CycleBackwardDart (common.mapLe hC₂) e) := by
    intro e he hcommonBackward
    apply D₂.complementary_forward_disjoint_selected hd hbDarts e
      (by simpa [outer₂, H₂] using he)
    change CycleForwardDart selected₂ e
    rw [← hwalk₂]
    exact (cycleForwardDart_reverse_iff_backward (common.mapLe hC₂) e).2
      hcommonBackward
  have houterFacial₁ :
      IsFacialCycle U (outer₁.mapLe le_sup_left)
        (houter₁.mapLe le_sup_left) :=
    RotationSystemGluing.cycleSum_isFacialCycle_of_left
      D₁.rotation D₂.rotation hC₁ hC₂ hcommon
        common hcommonCycle hspan hfacial₁ hfacial₂ hmeetCommon
        outer₁ houter₁ (by simpa [outer₁] using haFacial) hdisjoint₁
  have houterFacial₂ :
      IsFacialCycle U (outer₂.mapLe le_sup_right)
        (houter₂.mapLe le_sup_right) :=
    RotationSystemGluing.cycleSum_isFacialCycle_of_right
      D₁.rotation D₂.rotation hC₁ hC₂ hcommon
        common hcommonCycle hspan hfacial₁ hfacial₂ hmeetCommon
        outer₂ houter₂ (by simpa [outer₂] using hbFacial) hdisjoint₂
  let old₁ : List (OrientedEdge H₁) :=
    (a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
      (RotationSystemFan.addNodeGraphSomeOrientedEdge G
        (insert t ({s} : Set V)))
  let old₂ : List (OrientedEdge H₂) :=
    (b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
      (RotationSystemFan.addNodeGraphSomeOrientedEdge K
        (insert s ({t} : Set V)))
  let left : List (OrientedEdge (H₁ ⊔ H₂)) :=
    old₁.map (liftOrientedEdge (show H₁ <= H₁ ⊔ H₂ from le_sup_left))
  let right : List (OrientedEdge (H₁ ⊔ H₂)) :=
    old₂.map (liftOrientedEdge (show H₂ <= H₁ ⊔ H₂ from le_sup_right))
  have haDartsNodup : a.darts.Nodup := by
    apply List.Nodup.of_map SimpleGraph.Dart.edge
    change a.edges.Nodup
    exact ha.isTrail.edges_nodup
  have hbDartsNodup : b.darts.Nodup := by
    apply List.Nodup.of_map SimpleGraph.Dart.edge
    change b.edges.Nodup
    exact hb.isTrail.edges_nodup
  have hold₁Nodup : old₁.Nodup := by
    exact
      (haDartsNodup.map
          (orientedEdgeDartEquiv (G := G)).symm.injective).map
        (RotationSystemFan.addNodeGraphSomeOrientedEdge_injective G
          (insert t ({s} : Set V)))
  have hold₂Nodup : old₂.Nodup := by
    exact
      (hbDartsNodup.map
          (orientedEdgeDartEquiv (G := K)).symm.injective).map
        (RotationSystemFan.addNodeGraphSomeOrientedEdge_injective K
          (insert s ({t} : Set V)))
  have hleftNodup : left.Nodup :=
    hold₁Nodup.map (liftOrientedEdge_injective
      (show H₁ <= H₁ ⊔ H₂ from le_sup_left))
  have hrightNodup : right.Nodup :=
    hold₂Nodup.map (liftOrientedEdge_injective
      (show H₂ <= H₁ ⊔ H₂ from le_sup_right))
  have holdDisjoint : left.Disjoint right := by
    rw [List.disjoint_left]
    intro e heLeft heRight
    rcases List.mem_map.mp heLeft with ⟨e₁, he₁Old, he₁Eq⟩
    rcases List.mem_map.mp heRight with ⟨e₂, he₂Old, he₂Eq⟩
    have heLift :
        liftOrientedEdge (show H₁ <= H₁ ⊔ H₂ from le_sup_left) e₁ =
          liftOrientedEdge (show H₂ <= H₁ ⊔ H₂ from le_sup_right) e₂ :=
      he₁Eq.trans he₂Eq.symm
    have htail : e₁.tail = e₂.tail :=
      congrArg OrientedEdge.tail heLift
    have hhead : e₁.head = e₂.head :=
      congrArg OrientedEdge.head heLift
    have he₂AdjAt₁ : H₂.Adj e₁.tail e₁.head := by
      simp [htail, hhead]
    have heCommon : C.Adj e₁.tail e₁.head :=
      hcommon e₁.adj he₂AdjAt₁
    have he₁Outer : CycleForwardDart outer₁ e₁ := by
      apply
        (RotationSystemFan.cycleForwardDart_iff_mem_orientedDarts
          outer₁ e₁).mpr
      rw [show outer₁ =
          RotationSystemFan.addNodeGraphPathCycleAtNewIn G
            (insert t ({s} : Set V)) (by simp) (by simp) a by rfl,
        RotationSystemFan.addNodeGraphPathCycleAtNewIn_orientedDarts]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ he₁Old)
    have he₂Outer : CycleForwardDart outer₂ e₂ := by
      apply
        (RotationSystemFan.cycleForwardDart_iff_mem_orientedDarts
          outer₂ e₂).mpr
      rw [show outer₂ =
          RotationSystemFan.addNodeGraphPathCycleAtNewIn K
            (insert s ({t} : Set V)) (by simp) (by simp) b by rfl,
        RotationSystemFan.addNodeGraphPathCycleAtNewIn_orientedDarts]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ he₂Old)
    rcases cycleForward_or_backward_of_common hC₁ hspan e₁ heCommon with
      heForward | heBackward
    · exact hdisjoint₁ e₁ he₁Outer heForward
    · have heCommon₂ : C.Adj e₂.tail e₂.head := by
        simpa [htail, hhead] using heCommon
      have heTransferred :
          CycleBackwardDart (common.mapLe hC₂)
            (transferCommonDart hC₂ e₁ heCommon) :=
        cycleBackwardDart_transferCommonDart hC₁ hC₂ heBackward
      have htransferEq : transferCommonDart hC₂ e₁ heCommon = e₂ := by
        apply Subtype.ext
        exact Prod.ext htail hhead
      exact hdisjoint₂ e₂ he₂Outer (by simpa [htransferEq] using heTransferred)
  have hsectorsNodup : (left ++ right).Nodup :=
    hleftNodup.append hrightNodup holdDisjoint
  refine ⟨a, ha, haRawDarts, haDarts, b, hb, hbRawDarts, hbDarts,
    ?_, U, hU, ?_, ?_⟩
  · simpa [left, right, old₁, old₂, H₁, H₂] using hsectorsNodup
  · simpa [outer₁, houter₁, U] using houterFacial₁
  · simpa [outer₂, houter₂, U] using houterFacial₂


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
