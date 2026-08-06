import Schematic.Math.GraphTheory.Minors.Society.Basic.MiddleLegLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Rim-contact companion to
`liftAppendOuterTailsReplaceMiddleLegWithTailAllowMiddleBoundary`.

The middle attach point is moved to an internal rim hit `x`, while the two
outer legs are extended by cut-path tails.  The outer tails may pass through
the old middle boundary foot, but the rim-clean hypotheses rule out using
that relaxed contact as an outer-leg/rim intersection. -/
def liftAppendOuterTailsReplaceMiddleRimWithTailAllowMiddleBoundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (newBoundary : Fin 3 -> V)
    (hnew_boundary : forall i : Fin 3, newBoundary i ∈ S.boundarySet)
    (hnew_injective : Function.Injective newBoundary)
    (tail0 : S.graph.Walk (T.boundary 0) (newBoundary 0))
    {x : V}
    (hx : x ∈ Walk.InternalVertices (T.rim 1))
    (middleTail : S.graph.Walk x (newBoundary 1))
    (tail2 : S.graph.Walk (T.boundary 2) (newBoundary 2))
    (htail0_path : tail0.IsPath)
    (hmiddle_path : middleTail.IsPath)
    (htail2_path : tail2.IsPath)
    (htail0_clean :
      forall z : V, z ∈ tail0.support -> z ∈ T.vertexSet ->
        z = T.boundary 0 ∨ z = T.boundary 1)
    (hmiddle_clean :
      forall z : V, z ∈ middleTail.support -> z ∈ T.vertexSet ->
        z = x)
    (htail2_clean :
      forall z : V, z ∈ tail2.support -> z ∈ T.vertexSet ->
        z = T.boundary 2 ∨ z = T.boundary 1)
    (htail0_rim_clean :
      forall j : Fin 3, forall z : V,
        z ∈ tail0.support -> z ∈ (T.rim j).support ->
          z = T.boundary 0)
    (htail2_rim_clean :
      forall j : Fin 3, forall z : V,
        z ∈ tail2.support -> z ∈ (T.rim j).support ->
          z = T.boundary 2)
    (htail0_middle_disjoint :
      Disjoint {z : V | z ∈ tail0.support}
        {z : V | z ∈ middleTail.support})
    (htail0_tail2_disjoint :
      Disjoint {z : V | z ∈ tail0.support}
        {z : V | z ∈ tail2.support})
    (hmiddle_tail2_disjoint :
      Disjoint {z : V | z ∈ middleTail.support}
        {z : V | z ∈ tail2.support}) :
    S.Tripod := by
  let oldLeg : forall i : Fin 3, S.graph.Walk (T.attach i) (T.boundary i) :=
    fun i => (T.leg i).mapLe hgraph
  have hx_not_leg0 : x ∉ (T.leg 0).support := by
    intro hx0
    have hx_attach0 : x = T.attach 0 :=
      T.legs_meet_rims_only_at_attach 0 1 x hx0 hx.1
    have hx_rim0 : x ∈ Walk.InternalVertices (T.rim 0) := by
      simpa [hx_attach0] using T.attach_mem_rim 0
    exact Set.disjoint_left.mp (T.rim_internals_disjoint 0 1 (by decide))
      hx_rim0 hx
  have hx_not_leg2 : x ∉ (T.leg 2).support := by
    intro hx2
    have hx_attach2 : x = T.attach 2 :=
      T.legs_meet_rims_only_at_attach 2 1 x hx2 hx.1
    have hx_rim2 : x ∈ Walk.InternalVertices (T.rim 2) := by
      simpa [hx_attach2] using T.attach_mem_rim 2
    exact Set.disjoint_left.mp (T.rim_internals_disjoint 2 1 (by decide))
      hx_rim2 hx
  refine {
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := fun i => (T.rim i).mapLe hgraph
    rim_isPath := ?_
    attach := fun
      | 0 => T.attach 0
      | 1 => x
      | 2 => T.attach 2
    attach_mem_rim := ?_
    boundary := newBoundary
    boundary_mem := hnew_boundary
    boundary_injective := hnew_injective
    leg := fun
      | 0 => (oldLeg 0).append tail0
      | 1 => middleTail
      | 2 => (oldLeg 2).append tail2
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }
  · intro i
    exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
  · intro i
    fin_cases i
    · simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.attach_mem_rim 0
    · simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using hx
    · simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
        using T.attach_mem_rim 2
  · intro i
    fin_cases i
    ·
      have hold_path : (oldLeg 0).IsPath :=
        SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 0)
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hold_path htail0_path ?_
      intro z hzOld hzTail
      have hzOldT : z ∈ (T.leg 0).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
      rcases htail0_clean z hzTail (T.leg_mem_vertexSet (i := 0) hzOldT)
        with hz_eq | hz_eq
      · exact hz_eq
      · exact False.elim
          (T.boundary_not_mem_leg_of_ne (i := 0) (j := 1)
            (by decide) (by simpa [hz_eq] using hzOldT))
    · exact hmiddle_path
    ·
      have hold_path : (oldLeg 2).IsPath :=
        SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 2)
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hold_path htail2_path ?_
      intro z hzOld hzTail
      have hzOldT : z ∈ (T.leg 2).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
      rcases htail2_clean z hzTail (T.leg_mem_vertexSet (i := 2) hzOldT)
        with hz_eq | hz_eq
      · exact hz_eq
      · exact False.elim
          (T.boundary_not_mem_leg_of_ne (i := 2) (j := 1)
            (by decide) (by simpa [hz_eq] using hzOldT))
  · intro i j hij
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.rim_internals_disjoint i j hij
  ·
    have hdisj01 :
        Disjoint
          {z : V | z ∈ ((oldLeg 0).append tail0).support}
          {z : V | z ∈ middleTail.support} := by
      rw [Set.disjoint_left]
      intro z hz0 hz1
      change z ∈ ((oldLeg 0).append tail0).support at hz0
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz0
      rcases hz0 with hz0Old | hz0Tail
      · have hz0OldT : z ∈ (T.leg 0).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz0Old
        have hz_eq : z = x :=
          hmiddle_clean z hz1 (T.leg_mem_vertexSet (i := 0) hz0OldT)
        exact hx_not_leg0 (by simpa [hz_eq] using hz0OldT)
      · exact Set.disjoint_left.mp htail0_middle_disjoint hz0Tail hz1
    have hdisj02 :
        Disjoint
          {z : V | z ∈ ((oldLeg 0).append tail0).support}
          {z : V | z ∈ ((oldLeg 2).append tail2).support} := by
      rw [Set.disjoint_left]
      intro z hz0 hz2
      change z ∈ ((oldLeg 0).append tail0).support at hz0
      change z ∈ ((oldLeg 2).append tail2).support at hz2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz0
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz2
      rcases hz0 with hz0Old | hz0Tail
      · have hz0OldT : z ∈ (T.leg 0).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz0Old
        rcases hz2 with hz2Old | hz2Tail
        · have hz2OldT : z ∈ (T.leg 2).support := by
            simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz2Old
          exact Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 2 (by decide))
            hz0OldT hz2OldT
        · rcases htail2_clean z hz2Tail (T.leg_mem_vertexSet (i := 0) hz0OldT)
            with hz_eq | hz_eq
          · exact T.boundary_not_mem_leg_of_ne (i := 0) (j := 2)
              (by decide) (by simpa [hz_eq] using hz0OldT)
          · exact T.boundary_not_mem_leg_of_ne (i := 0) (j := 1)
              (by decide) (by simpa [hz_eq] using hz0OldT)
      · rcases hz2 with hz2Old | hz2Tail
        · have hz2OldT : z ∈ (T.leg 2).support := by
            simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz2Old
          rcases htail0_clean z hz0Tail (T.leg_mem_vertexSet (i := 2) hz2OldT)
            with hz_eq | hz_eq
          · exact T.boundary_not_mem_leg_of_ne (i := 2) (j := 0)
              (by decide) (by simpa [hz_eq] using hz2OldT)
          · exact T.boundary_not_mem_leg_of_ne (i := 2) (j := 1)
              (by decide) (by simpa [hz_eq] using hz2OldT)
        · exact Set.disjoint_left.mp htail0_tail2_disjoint hz0Tail hz2Tail
    have hdisj12 :
        Disjoint
          {z : V | z ∈ middleTail.support}
          {z : V | z ∈ ((oldLeg 2).append tail2).support} := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      change z ∈ ((oldLeg 2).append tail2).support at hz2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz2
      rcases hz2 with hz2Old | hz2Tail
      · have hz2OldT : z ∈ (T.leg 2).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz2Old
        have hz_eq : z = x :=
          hmiddle_clean z hz1 (T.leg_mem_vertexSet (i := 2) hz2OldT)
        exact hx_not_leg2 (by simpa [hz_eq] using hz2OldT)
      · exact Set.disjoint_left.mp hmiddle_tail2_disjoint hz1 hz2Tail
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa using hdisj01
    · simpa using hdisj02
    · simpa using hdisj01.symm
    · exact False.elim (hij rfl)
    · simpa using hdisj12
    · simpa using hdisj02.symm
    · simpa using hdisj12.symm
    · exact False.elim (hij rfl)
  · intro i j z hzleg hzr
    have hzRimOld : z ∈ (T.rim j).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    fin_cases i
    ·
      change z ∈ ((oldLeg 0).append tail0).support at hzleg
      rw [SimpleGraph.Walk.mem_support_append_iff] at hzleg
      rcases hzleg with hzOld | hzTail
      · have hzOldT : z ∈ (T.leg 0).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
        exact T.legs_meet_rims_only_at_attach 0 j z hzOldT hzRimOld
      · have hz_eq : z = T.boundary 0 :=
          htail0_rim_clean j z hzTail hzRimOld
        have hboundary_rim : T.boundary 0 ∈ (T.rim j).support := by
          simpa [hz_eq] using hzRimOld
        have hboundary_attach :
            T.boundary 0 = T.attach 0 :=
          T.legs_meet_rims_only_at_attach 0 j (T.boundary 0)
            (T.leg 0).end_mem_support hboundary_rim
        exact hz_eq.trans hboundary_attach
    ·
      have hz_eq : z = x :=
        hmiddle_clean z hzleg (T.rim_mem_vertexSet (i := j) hzRimOld)
      simpa using hz_eq
    ·
      change z ∈ ((oldLeg 2).append tail2).support at hzleg
      rw [SimpleGraph.Walk.mem_support_append_iff] at hzleg
      rcases hzleg with hzOld | hzTail
      · have hzOldT : z ∈ (T.leg 2).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
        exact T.legs_meet_rims_only_at_attach 2 j z hzOldT hzRimOld
      · have hz_eq : z = T.boundary 2 :=
          htail2_rim_clean j z hzTail hzRimOld
        have hboundary_rim : T.boundary 2 ∈ (T.rim j).support := by
          simpa [hz_eq] using hzRimOld
        have hboundary_attach :
            T.boundary 2 = T.attach 2 :=
          T.legs_meet_rims_only_at_attach 2 j (T.boundary 2)
            (T.leg 2).end_mem_support hboundary_rim
        exact hz_eq.trans hboundary_attach


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
