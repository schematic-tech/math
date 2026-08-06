import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.DegreeTwoSuppression

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness

/-- A strict subdivision of any finite two-connected Euler obstruction is
again an Euler obstruction, provided the obstruction survives contraction at
a degree-at-most-two carrier vertex. -/
theorem not_hasEulerRotationSystem_of_strictSubdivision_of_contraction_closed
    {W : Type w} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (h2 : IsTwoConnected H)
    (hbase : Not (HasEulerRotationSystem H))
    (hcontract :
      forall {V : Type u} [Fintype V] [DecidableEq V]
        {G : SimpleGraph V} [DecidableRel G.Adj]
        {v w : V} (hvw : G.Adj v w),
        G.degree v <= 2 ->
        ContainsStrictSubdivision H G ->
        ContainsStrictSubdivision H
          (GraphContraction.collapseEdge G hvw).graph)
    (n : Nat) :
    forall {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
      Fintype.card V = n ->
      StrictSubdivisionModel H G ->
      Not (HasEulerRotationSystem G) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V _ _ G _ hcard M hEuler
      classical
      letI : LinearOrder W :=
        LinearOrder.lift' (Fintype.equivFin W)
          (Fintype.equivFin W).injective
      let N := orderedStrictSubdivisionModel M
      let C := strictSubdivisionCarrierGraph N
      let L := edgeRestrictStrictSubdivisionCarrier N
      have hsource : forall x : W, Exists fun y : W => H.Adj x y := by
        intro x
        have hxdegree : 2 <= H.degree x := h2.degree_atLeast x
        have hxneighbors : 0 < (H.neighborSet x).ncard := by
          rw [← Set.fintypeCard_eq_ncard,
            SimpleGraph.card_neighborSet_eq_degree]
          omega
        exact (Set.ncard_pos).mp hxneighbors
      let K := L.targetRestrictSupport hsource
      let Core := C.induce C.support
      have hEulerC : HasEulerRotationSystem C :=
        hEuler.mono (strictSubdivisionCarrierGraph_le N)
      have hEulerCore : HasEulerRotationSystem Core :=
        RotationSoundness.HasEulerRotationSystem.induceSupport hEulerC
      have h2Core : IsTwoConnected Core :=
        strictSubdivisionCarrierCore_isTwoConnected M h2
      by_cases hsurj : Function.Surjective K.branchVertex
      · exact hbase (HasEulerRotationSystem.of_iso_univ
          (strictSubdivisionCarrierCoreIso M hsource hsurj) hEulerCore)
      · rw [Function.Surjective] at hsurj
        push Not at hsurj
        obtain ⟨v, hv⟩ := hsurj
        have hvSupport : (v : V) ∈ C.support := v.2
        rw [SimpleGraph.mem_support] at hvSupport
        obtain ⟨r, hvr⟩ := hvSupport
        rcases (strictSubdivisionCarrierGraph_adj_iff N).mp hvr with
          ⟨x, y, hxy, hvrPath⟩
        have hvPath : (v : V) ∈ (N.edgePath hxy).support := by
          rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
          exact (N.edgePath hxy).toSubgraph.edge_vert hvrPath
        have hvInternal :
            (v : V) ∈ Walk.InternalVertices (N.edgePath hxy) := by
          refine ⟨hvPath, ?_, ?_⟩
          · intro hvx
            apply hv x
            apply Subtype.ext
            exact hvx.symm
          · intro hvy
            apply hv y
            apply Subtype.ext
            exact hvy.symm
        have hdegreeC : C.degree (v : V) = 2 :=
          orderedStrictSubdivisionCarrier_internal_degree_eq_two M hxy hvInternal
        have hdegree : Core.degree v = 2 := by
          rw [SimpleGraph.degree_induce_support]
          exact hdegreeC
        have hneighbors : 1 < (Core.neighborSet v).ncard := by
          rw [← Set.fintypeCard_eq_ncard,
            SimpleGraph.card_neighborSet_eq_degree, hdegree]
          omega
        obtain ⟨w, u, hvw, hvu, hwu⟩ :=
          (Set.one_lt_ncard_iff (s := Core.neighborSet v)).mp hneighbors
        have hvwAdj : Core.Adj v w := hvw
        have hvuAdj : Core.Adj v u := hvu
        have hpairSubset : ({w, u} : Set C.support) ⊆ Core.neighborSet v := by
          intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl | hz
          · exact hvw
          · simpa using hz ▸ hvu
        have hpairCard : ({w, u} : Set C.support).ncard = 2 := by
          simp [hwu]
        have hneighborCard : (Core.neighborSet v).ncard = 2 := by
          rw [← Set.fintypeCard_eq_ncard,
            SimpleGraph.card_neighborSet_eq_degree, hdegree]
        have hpair : ({w, u} : Set C.support) = Core.neighborSet v :=
          Set.eq_of_subset_of_ncard_le hpairSubset (by omega)
        have hneigh : forall z : C.support,
            Core.Adj v z -> z = w ∨ z = u := by
          intro z hvz
          have hzpair : z ∈ ({w, u} : Set C.support) := by
            rw [hpair]
            exact hvz
          simpa using hzpair
        have hEulerContracted : HasEulerRotationSystem
            (GraphContraction.collapseEdge Core hvwAdj).graph :=
          RotationSoundness.HasEulerRotationSystem.collapseEdge_of_degree_two_of_isTwoConnected
            h2Core hvwAdj hvuAdj hvuAdj.ne' hwu.symm hneigh hEulerCore
        have hcontains : ContainsStrictSubdivision H Core := ⟨K⟩
        have hcontainsContracted : ContainsStrictSubdivision H
            (GraphContraction.collapseEdge Core hvwAdj).graph :=
          hcontract hvwAdj (by rw [hdegree]) hcontains
        have hcoreCardLe : Fintype.card C.support <= Fintype.card V :=
          Fintype.card_subtype_le _
        have htargetLtCore :
            Fintype.card (GraphContraction.collapseEdge Core hvwAdj).Target <
              Fintype.card C.support :=
          GraphContraction.collapseEdge_target_card_lt Core hvwAdj
        have htargetLt :
            Fintype.card (GraphContraction.collapseEdge Core hvwAdj).Target < n := by
          omega
        exact ih _ htargetLt rfl (Classical.choice hcontainsContracted)
          hEulerContracted


end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
