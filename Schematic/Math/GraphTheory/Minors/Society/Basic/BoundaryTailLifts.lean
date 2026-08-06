import Schematic.Math.GraphTheory.Minors.Society.Basic.BranchPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Lift a tripod across a graph inclusion while replacing all three boundary
feet by clean tails to boundary vertices of the larger society.

This is the multi-foot constructor needed by the GM IX `(2.4)` side-tripod
case: when several feet of a side tripod lie on the cut path, replacing the
feet one at a time forces false "the other feet are already old boundary"
side conditions. -/
def liftAppendBoundaryTails {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (newBoundary : Fin 3 -> V)
    (hnew_boundary : forall i : Fin 3, newBoundary i ∈ S.boundarySet)
    (hnew_injective : Function.Injective newBoundary)
    (tail : forall i : Fin 3, S.graph.Walk (T.boundary i) (newBoundary i))
    (htail_path : forall i : Fin 3, (tail i).IsPath)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (tail i).support -> z ∈ T.vertexSet -> z = T.boundary i)
    (htail_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint {z : V | z ∈ (tail i).support}
          {z : V | z ∈ (tail j).support}) :
    S.Tripod := by
  let oldLeg : forall i : Fin 3, S.graph.Walk (T.attach i) (T.boundary i) :=
    fun i => (T.leg i).mapLe hgraph
  refine {
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := fun i => (T.rim i).mapLe hgraph
    rim_isPath := ?_
    attach := T.attach
    attach_mem_rim := ?_
    boundary := newBoundary
    boundary_mem := hnew_boundary
    boundary_injective := hnew_injective
    leg := fun i => (oldLeg i).append (tail i)
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }
  · intro i
    exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
  · intro i
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.attach_mem_rim i
  · intro i
    have hold_path : (oldLeg i).IsPath := by
      exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath i)
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hold_path (htail_path i) ?_
    intro z hzOld hzTail
    have hzOldT : z ∈ (T.leg i).support := by
      simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
    exact htail_clean i z hzTail (T.leg_mem_vertexSet (i := i) hzOldT)
  · intro i j hij
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.rim_internals_disjoint i j hij
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    change z ∈ ((oldLeg i).append (tail i)).support at hzi
    change z ∈ ((oldLeg j).append (tail j)).support at hzj
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzi
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzj
    rcases hzi with hziOld | hziTail
    · have hziOldT : z ∈ (T.leg i).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hziOld
      rcases hzj with hzjOld | hzjTail
      · have hzjOldT : z ∈ (T.leg j).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzjOld
        exact
          Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
            hziOldT hzjOldT
      · have hz_eq :
            z = T.boundary j :=
          htail_clean j z hzjTail (T.leg_mem_vertexSet (i := i) hziOldT)
        exact
          T.boundary_not_mem_leg_of_ne hij (by
            simpa [hz_eq] using hziOldT)
    · rcases hzj with hzjOld | hzjTail
      · have hzjOldT : z ∈ (T.leg j).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzjOld
        have hz_eq :
            z = T.boundary i :=
          htail_clean i z hziTail (T.leg_mem_vertexSet (i := j) hzjOldT)
        exact
          T.boundary_not_mem_leg_of_ne (i := j) (j := i)
            (fun h => hij h.symm) (by
              simpa [hz_eq] using hzjOldT)
      · exact
          Set.disjoint_left.mp (htail_disjoint i j hij)
            hziTail hzjTail
  · intro i j z hzleg hzr
    change z ∈ ((oldLeg i).append (tail i)).support at hzleg
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzleg
    have hzRimOld : z ∈ (T.rim j).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases hzleg with hzOld | hzTail
    · have hzOldT : z ∈ (T.leg i).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
      exact T.legs_meet_rims_only_at_attach i j z hzOldT hzRimOld
    · have hz_eq :
          z = T.boundary i :=
        htail_clean i z hzTail (T.rim_mem_vertexSet (i := j) hzRimOld)
      have hboundary_rim :
          T.boundary i ∈ (T.rim j).support := by
        simpa [hz_eq] using hzRimOld
      have hboundary_attach :
          T.boundary i = T.attach i :=
        T.legs_meet_rims_only_at_attach i j (T.boundary i)
          (T.leg i).end_mem_support hboundary_rim
      exact hz_eq.trans hboundary_attach

/-- Lift a tripod while appending clean tails on the two outer legs and
replacing the middle leg from an internal clean-tail contact.

This is the side-tripod constructor used in the literal GM IX `(2.4)` proof:
the two outside old feet are routed along the cut path to the two cut
endpoints, while a clean tail from a last contact on the middle leg supplies
the middle boundary vertex. -/
def liftAppendOuterTailsReplaceMiddleLegWithTail {S H : GeneralSociety V}
    [DecidableEq V]
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (newBoundary : Fin 3 -> V)
    (hnew_boundary : forall i : Fin 3, newBoundary i ∈ S.boundarySet)
    (hnew_injective : Function.Injective newBoundary)
    (tail0 : S.graph.Walk (T.boundary 0) (newBoundary 0))
    {x : V}
    (hx : x ∈ (T.leg 1).support)
    (middleTail : S.graph.Walk x (newBoundary 1))
    (tail2 : S.graph.Walk (T.boundary 2) (newBoundary 2))
    (htail0_path : tail0.IsPath)
    (hmiddle_path : middleTail.IsPath)
    (htail2_path : tail2.IsPath)
    (htail0_clean :
      forall z : V, z ∈ tail0.support -> z ∈ T.vertexSet ->
        z = T.boundary 0)
    (hmiddle_clean :
      forall z : V, z ∈ middleTail.support -> z ∈ T.vertexSet ->
        z = x)
    (htail2_clean :
      forall z : V, z ∈ tail2.support -> z ∈ T.vertexSet ->
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
  let middleOld : S.graph.Walk (T.attach 1) (T.boundary 1) := oldLeg 1
  have hxMiddleOld : x ∈ middleOld.support := by
    simpa [middleOld, oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hx
  refine {
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := fun i => (T.rim i).mapLe hgraph
    rim_isPath := ?_
    attach := T.attach
    attach_mem_rim := ?_
    boundary := newBoundary
    boundary_mem := hnew_boundary
    boundary_injective := hnew_injective
    leg := fun
      | 0 => (oldLeg 0).append tail0
      | 1 => (middleOld.takeUntil x hxMiddleOld).append middleTail
      | 2 => (oldLeg 2).append tail2
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }
  · intro i
    exact SimpleGraph.Walk.IsPath.mapLe hgraph (T.rim_isPath i)
  · intro i
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.attach_mem_rim i
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
      exact htail0_clean z hzTail (T.leg_mem_vertexSet (i := 0) hzOldT)
    ·
      have hprefix_path :
          (middleOld.takeUntil x hxMiddleOld).IsPath := by
        have hmiddle_old_path : middleOld.IsPath :=
          SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 1)
        exact hmiddle_old_path.takeUntil hxMiddleOld
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hprefix_path hmiddle_path ?_
      intro z hzPrefix hzTail
      have hzOldT : z ∈ (T.leg 1).support := by
        have hzOld :
            z ∈ middleOld.support :=
          SimpleGraph.Walk.support_takeUntil_subset middleOld hxMiddleOld
            hzPrefix
        simpa [middleOld, oldLeg, SimpleGraph.Walk.support_mapLe_eq_support]
          using hzOld
      exact hmiddle_clean z hzTail (T.leg_mem_vertexSet (i := 1) hzOldT)
    ·
      have hold_path : (oldLeg 2).IsPath :=
        SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath 2)
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hold_path htail2_path ?_
      intro z hzOld hzTail
      have hzOldT : z ∈ (T.leg 2).support := by
        simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
      exact htail2_clean z hzTail (T.leg_mem_vertexSet (i := 2) hzOldT)
  · intro i j hij
    simpa [Walk.InternalVertices, SimpleGraph.Walk.support_mapLe_eq_support]
      using T.rim_internals_disjoint i j hij
  ·
    have hdisj01 :
        Disjoint
          {z : V | z ∈ ((oldLeg 0).append tail0).support}
          {z : V |
            z ∈ ((middleOld.takeUntil x hxMiddleOld).append middleTail).support} := by
      rw [Set.disjoint_left]
      intro z hz0 hz1
      change z ∈ ((oldLeg 0).append tail0).support at hz0
      change z ∈ ((middleOld.takeUntil x hxMiddleOld).append middleTail).support at hz1
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz0
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz1
      rcases hz0 with hz0Old | hz0Tail
      · have hz0OldT : z ∈ (T.leg 0).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz0Old
        rcases hz1 with hz1Old | hz1Tail
        · have hz1OldT : z ∈ (T.leg 1).support := by
            have hz1Middle : z ∈ middleOld.support :=
              SimpleGraph.Walk.support_takeUntil_subset middleOld hxMiddleOld
                hz1Old
            simpa [middleOld, oldLeg, SimpleGraph.Walk.support_mapLe_eq_support]
              using hz1Middle
          exact Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 1 (by decide))
            hz0OldT hz1OldT
        · have hz_eq : z = x :=
            hmiddle_clean z hz1Tail (T.leg_mem_vertexSet (i := 0) hz0OldT)
          exact Set.disjoint_left.mp (T.legs_pairwise_disjoint 0 1 (by decide))
            hz0OldT (by simpa [hz_eq] using hx)
      · rcases hz1 with hz1Old | hz1Tail
        · have hz1OldT : z ∈ (T.leg 1).support := by
            have hz1Middle : z ∈ middleOld.support :=
              SimpleGraph.Walk.support_takeUntil_subset middleOld hxMiddleOld
                hz1Old
            simpa [middleOld, oldLeg, SimpleGraph.Walk.support_mapLe_eq_support]
              using hz1Middle
          have hz_eq : z = T.boundary 0 :=
            htail0_clean z hz0Tail (T.leg_mem_vertexSet (i := 1) hz1OldT)
          exact T.boundary_not_mem_leg_of_ne (i := 1) (j := 0)
            (by decide) (by simpa [hz_eq] using hz1OldT)
        · exact Set.disjoint_left.mp htail0_middle_disjoint hz0Tail hz1Tail
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
        · have hz_eq : z = T.boundary 2 :=
            htail2_clean z hz2Tail (T.leg_mem_vertexSet (i := 0) hz0OldT)
          exact T.boundary_not_mem_leg_of_ne (i := 0) (j := 2)
            (by decide) (by simpa [hz_eq] using hz0OldT)
      · rcases hz2 with hz2Old | hz2Tail
        · have hz2OldT : z ∈ (T.leg 2).support := by
            simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz2Old
          have hz_eq : z = T.boundary 0 :=
            htail0_clean z hz0Tail (T.leg_mem_vertexSet (i := 2) hz2OldT)
          exact T.boundary_not_mem_leg_of_ne (i := 2) (j := 0)
            (by decide) (by simpa [hz_eq] using hz2OldT)
        · exact Set.disjoint_left.mp htail0_tail2_disjoint hz0Tail hz2Tail
    have hdisj12 :
        Disjoint
          {z : V |
            z ∈ ((middleOld.takeUntil x hxMiddleOld).append middleTail).support}
          {z : V | z ∈ ((oldLeg 2).append tail2).support} := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      change z ∈ ((middleOld.takeUntil x hxMiddleOld).append middleTail).support at hz1
      change z ∈ ((oldLeg 2).append tail2).support at hz2
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz1
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz2
      rcases hz1 with hz1Old | hz1Tail
      · have hz1OldT : z ∈ (T.leg 1).support := by
          have hz1Middle : z ∈ middleOld.support :=
            SimpleGraph.Walk.support_takeUntil_subset middleOld hxMiddleOld
              hz1Old
          simpa [middleOld, oldLeg, SimpleGraph.Walk.support_mapLe_eq_support]
            using hz1Middle
        rcases hz2 with hz2Old | hz2Tail
        · have hz2OldT : z ∈ (T.leg 2).support := by
            simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz2Old
          exact Set.disjoint_left.mp (T.legs_pairwise_disjoint 1 2 (by decide))
            hz1OldT hz2OldT
        · have hz_eq : z = T.boundary 2 :=
            htail2_clean z hz2Tail (T.leg_mem_vertexSet (i := 1) hz1OldT)
          exact T.boundary_not_mem_leg_of_ne (i := 1) (j := 2)
            (by decide) (by simpa [hz_eq] using hz1OldT)
      · rcases hz2 with hz2Old | hz2Tail
        · have hz2OldT : z ∈ (T.leg 2).support := by
            simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hz2Old
          have hz_eq : z = x :=
            hmiddle_clean z hz1Tail (T.leg_mem_vertexSet (i := 2) hz2OldT)
          exact Set.disjoint_left.mp (T.legs_pairwise_disjoint 1 2 (by decide))
            (by simpa [hz_eq] using hx) hz2OldT
        · exact Set.disjoint_left.mp hmiddle_tail2_disjoint hz1Tail hz2Tail
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
          htail0_clean z hzTail (T.rim_mem_vertexSet (i := j) hzRimOld)
        have hboundary_rim : T.boundary 0 ∈ (T.rim j).support := by
          simpa [hz_eq] using hzRimOld
        have hboundary_attach :
            T.boundary 0 = T.attach 0 :=
          T.legs_meet_rims_only_at_attach 0 j (T.boundary 0)
            (T.leg 0).end_mem_support hboundary_rim
        exact hz_eq.trans hboundary_attach
    ·
      change z ∈ ((middleOld.takeUntil x hxMiddleOld).append middleTail).support at hzleg
      rw [SimpleGraph.Walk.mem_support_append_iff] at hzleg
      rcases hzleg with hzOld | hzTail
      · have hzOldT : z ∈ (T.leg 1).support := by
          have hzMiddle : z ∈ middleOld.support :=
            SimpleGraph.Walk.support_takeUntil_subset middleOld hxMiddleOld hzOld
          simpa [middleOld, oldLeg, SimpleGraph.Walk.support_mapLe_eq_support]
            using hzMiddle
        exact T.legs_meet_rims_only_at_attach 1 j z hzOldT hzRimOld
      · have hz_eq : z = x :=
          hmiddle_clean z hzTail (T.rim_mem_vertexSet (i := j) hzRimOld)
        exact T.legs_meet_rims_only_at_attach 1 j z
          (by simpa [hz_eq] using hx) hzRimOld
    ·
      change z ∈ ((oldLeg 2).append tail2).support at hzleg
      rw [SimpleGraph.Walk.mem_support_append_iff] at hzleg
      rcases hzleg with hzOld | hzTail
      · have hzOldT : z ∈ (T.leg 2).support := by
          simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzOld
        exact T.legs_meet_rims_only_at_attach 2 j z hzOldT hzRimOld
      · have hz_eq : z = T.boundary 2 :=
          htail2_clean z hzTail (T.rim_mem_vertexSet (i := j) hzRimOld)
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
