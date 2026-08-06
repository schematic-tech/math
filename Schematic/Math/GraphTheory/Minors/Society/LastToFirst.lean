import Schematic.Math.GraphTheory.Minors.Society.Terminal

/-!
The structured last-to-first exchange in the final GM IX `(2.4)` case.

The source transition runs from the last right arm to the first left arm.
Following the first-left arm back to the old common left end turns it into a
same-first transition after reversing the cut-path order.  That extension is
not carrier-clean, so the generic same-first checker does not apply directly;
this file checks exactly the resulting three rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Extend an `i`-right to `k`-left transition along the old `k`-left arm to
the common left end. -/
def Tripod.lastToFirstExtendedTransition
    {S H : GeneralSociety V}
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph)
    {k : Fin 3} {u v : V}
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v) :
    S.graph.Walk u T.left :=
  transition.append
    (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).reverse

theorem Tripod.lastToFirstExtendedTransition_isPath
    {S H : GeneralSociety V}
    (T : H.Tripod) (hgraph : H.graph ≤ S.graph)
    {i k : Fin 3} (hik : i ≠ k) {u v : V}
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    (Tripod.lastToFirstExtendedTransition T hgraph hv transition).IsPath := by
  let suffix : S.graph.Walk v T.left :=
    (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).reverse
  have hsuffix_path : suffix.IsPath := by
    simpa [suffix] using
      (SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.leftToAttach_isPath k).takeUntil hv)).reverse
  change (transition.append suffix).IsPath
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    htransition_path hsuffix_path ?_
  intro z hzTransition hzSuffix
  have hzPrefixMap : z ∈
      (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).support := by
    simpa [suffix, SimpleGraph.Walk.support_reverse] using hzSuffix
  have hzPrefix : z ∈ ((T.leftToAttach k).takeUntil v hv).support := by
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
  have hzK : z ∈ (T.rim k).support :=
    T.leftToAttach_support_subset_rim k
      (SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach k) hv hzPrefix)
  rcases htransition_clean z hzTransition (T.rim_mem_vertexSet hzK) with
    hzu | hzv
  · subst z
    exact False.elim
      (Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
        hu_internal
        (T.rim_support_internal_of_not_endpoint hzK
          ⟨hu_internal.2.1, hu_internal.2.2⟩))
  · exact hzv

theorem Tripod.lastToFirstExtendedTransition_outside
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {k : Fin 3} {u v : V}
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (hprefix_outside : forall z : V,
      z ∈ ((T.leftToAttach k).takeUntil v hv).support -> z ∈ P.outside) :
    forall z : V,
      z ∈ (Tripod.lastToFirstExtendedTransition T hgraph hv transition).support ->
        z ∈ P.outside := by
  intro z hz
  change z ∈
    (transition.append
      (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).reverse).support at hz
  rw [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzTransition | hzSuffix
  · exact htransition_outside z hzTransition
  · apply hprefix_outside z
    have hzPrefixMap : z ∈
        (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzSuffix
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap

/-- The same-first theta built from the structured extension above. -/
def Tripod.allNilSameFirstViaLastTransitionRim
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v) :
    Fin 3 -> S.graph.Walk (T.attach j) u :=
  Tripod.allNilSameFirstTransitionRim P T hgraph
    hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order hu
    (T.leftToAttach i).start_mem_support
    (Tripod.lastToFirstExtendedTransition T hgraph hv transition)

theorem Tripod.allNilSameFirstViaLastTransitionRim_isPath
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r : Fin 3,
      (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
        hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
        hu hv transition r).IsPath := by
  intro r
  fin_cases r
  · let segment : S.graph.Walk (T.attach j) (T.attach i) :=
      (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order)).reverse.copy
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
    have huForward : u ∈ (T.attachToRight i).support := by
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hu
    let arm : S.graph.Walk (T.attach i) u :=
      ((T.attachToRight i).takeUntil u huForward).mapLe hgraph
    have hsegment_path : segment.IsPath := by
      simpa [segment] using
        (SimpleGraph.Walk.isPath_copy
          (P.pathSegmentBetween hi hj
            (Nat.le_of_lt hij_order)).reverse
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).mpr
            (P.pathSegmentBetween_isPath hi hj
              (Nat.le_of_lt hij_order)).reverse
    have harm_path : arm.IsPath := by
      simpa [arm] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.attachToRight_isPath i).takeUntil huForward)
    simp only [Tripod.allNilSameFirstViaLastTransitionRim,
      Tripod.allNilSameFirstTransitionRim]
    change (segment.append arm).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hsegment_path harm_path ?_
    intro z hzSegment hzArm
    have hzSegmentOld : z ∈
        (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order)).support := by
      simpa [segment, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse] using hzSegment
    have hzArmOld : z ∈ (T.attachToRight i).support := by
      apply SimpleGraph.Walk.support_takeUntil_subset
        (T.attachToRight i) huForward
      simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
        T hij hik hjk hi hj hij_order hjk_order hpath_contacts
        hzSegmentOld
        (T.rim_mem_vertexSet
          (T.attachToRight_support_subset_rim i hzArmOld)) with hzi | hzj
    · exact hzi.trans
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
    · exact False.elim
        (T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using
            T.attachToRight_support_subset_rim i hzArmOld))
  · let lastPrefix : S.graph.Walk T.left v :=
      ((T.leftToAttach k).takeUntil v hv).mapLe hgraph
    let first : S.graph.Walk (T.attach j) v :=
      (((T.attachToLeft j).mapLe hgraph).append
        (((T.leftToAttach i).takeUntil T.left
          (T.leftToAttach i).start_mem_support).mapLe hgraph)).append lastPrefix
    have hfirst_path : first.IsPath := by
      have hfirst_eq : first =
          ((T.attachToLeft j).mapLe hgraph).append lastPrefix := by
        simp [first, SimpleGraph.Walk.mapLe]
      rw [hfirst_eq]
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        (SimpleGraph.Walk.IsPath.mapLe hgraph (T.attachToLeft_isPath j))
        (by simpa [lastPrefix] using
          (SimpleGraph.Walk.IsPath.mapLe hgraph
            ((T.leftToAttach_isPath k).takeUntil hv))) ?_
      intro z hzJ hzK
      exact T.leftToAttach_support_inter_rim_eq_left
        (i := k) (j := j) (fun h => hjk h.symm)
        (SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv (by
            simpa [lastPrefix,
              SimpleGraph.Walk.support_mapLe_eq_support] using hzK))
        (T.attachToLeft_support_subset_rim j (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzJ))
    simp only [Tripod.allNilSameFirstViaLastTransitionRim,
      Tripod.allNilSameFirstTransitionRim,
      Tripod.lastToFirstExtendedTransition,
      SimpleGraph.Walk.takeUntil_first,
      SimpleGraph.Walk.reverse_append,
      SimpleGraph.Walk.reverse_reverse,
      SimpleGraph.Walk.append_assoc]
    let actualFirst : S.graph.Walk (T.attach j) v :=
      (((T.attachToLeft j).mapLe hgraph).append
        ((SimpleGraph.Walk.nil : H.graph.Walk T.left T.left).mapLe hgraph)).append
          lastPrefix
    change (actualFirst.append transition.reverse).IsPath
    have hactualFirst_path : actualFirst.IsPath := by
      simpa [actualFirst, first, SimpleGraph.Walk.mapLe] using hfirst_path
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hactualFirst_path htransition_path.reverse ?_
    intro z hzFirst hzTransitionRev
    have hzTransition : z ∈ transition.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzTransitionRev
    have hzCarrier : z ∈ T.vertexSet := by
      have hzFirst' : z ∈ first.support := by
        simpa [actualFirst, first, SimpleGraph.Walk.mapLe] using hzFirst
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst' with
        hzJ | hzK
      · exact T.rim_mem_vertexSet
          (T.attachToLeft_support_subset_rim j (by
            simpa [first,
              SimpleGraph.Walk.support_mapLe_eq_support] using hzJ))
      · exact T.rim_mem_vertexSet
          (T.leftToAttach_support_subset_rim k
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.leftToAttach k) hv (by
                simpa [first, lastPrefix,
                  SimpleGraph.Walk.support_mapLe_eq_support] using hzK)))
    rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
    · subst z
      have huFirst : u ∈ first.support := by
        simpa [actualFirst, first, SimpleGraph.Walk.mapLe] using hzFirst
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp huFirst with
        huJ | huK
      · have huJRim : u ∈ (T.rim j).support :=
          T.attachToLeft_support_subset_rim j (by
            simpa [first,
              SimpleGraph.Walk.support_mapLe_eq_support] using huJ)
        exact False.elim
          (Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            hu_internal
            (T.rim_support_internal_of_not_endpoint huJRim
              ⟨hu_internal.2.1, hu_internal.2.2⟩))
      · have huKRim : u ∈ (T.rim k).support :=
          T.leftToAttach_support_subset_rim k
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.leftToAttach k) hv (by
                simpa [first, lastPrefix,
                  SimpleGraph.Walk.support_mapLe_eq_support] using huK))
        exact False.elim
          (Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
            hu_internal
            (T.rim_support_internal_of_not_endpoint huKRim
              ⟨hu_internal.2.1, hu_internal.2.2⟩))
    · exact hzv
  · let segment : S.graph.Walk (T.attach j) (T.attach k) :=
      (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).copy
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
    let toRight : S.graph.Walk (T.attach j) T.right :=
      segment.append ((T.attachToRight k).mapLe hgraph)
    let arm : S.graph.Walk T.right u :=
      ((T.rightToAttach i).takeUntil u hu).mapLe hgraph
    have hsegment_path : segment.IsPath := by
      simpa [segment] using
        (SimpleGraph.Walk.isPath_copy
          (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order))
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).mpr
            (P.pathSegmentBetween_isPath hj hk
              (Nat.le_of_lt hjk_order))
    have htoRight_path : toRight.IsPath := by
      dsimp [toRight]
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hsegment_path
        (SimpleGraph.Walk.IsPath.mapLe hgraph (T.attachToRight_isPath k)) ?_
      intro z hzSegment hzArmK
      have hzSegmentOld : z ∈
          (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
        simpa [segment, SimpleGraph.Walk.support_copy] using hzSegment
      have hzArmKOld : z ∈ (T.attachToRight k).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArmK
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts
          hzSegmentOld
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim k hzArmKOld)) with hzj | hzk
      · exact False.elim
          (T.boundary_not_mem_rim_of_ne_index hjk
            (by simpa [hzj] using
              T.attachToRight_support_subset_rim k hzArmKOld))
      · exact hzk.trans
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
    have harm_path : arm.IsPath := by
      simpa [arm] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.rightToAttach_isPath i).takeUntil hu)
    simp only [Tripod.allNilSameFirstViaLastTransitionRim,
      Tripod.allNilSameFirstTransitionRim]
    change (toRight.append arm).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      htoRight_path harm_path ?_
    intro z hzToRight hzArmI
    have hzArmIOld : z ∈ (T.rightToAttach i).support :=
      SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach i) hu (by
          simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArmI)
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzToRight with
      hzSegment | hzArmK
    · have hzSegmentOld : z ∈
          (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
        simpa [toRight, segment, SimpleGraph.Walk.support_copy] using hzSegment
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts
          hzSegmentOld
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzArmIOld)) with hzj | hzk
      · exact False.elim
          (T.boundary_not_mem_rim_of_ne_index
            (i := j) (s := i) (fun h => hij h.symm)
            (by simpa [hzj] using
              T.rightToAttach_support_subset_rim i hzArmIOld))
      · exact False.elim
          (T.boundary_not_mem_rim_of_ne_index
            (i := k) (s := i) (fun h => hik h.symm)
            (by simpa [hzk] using
              T.rightToAttach_support_subset_rim i hzArmIOld))
    · have hzArmKOld : z ∈ (T.attachToRight k).support := by
        simpa [toRight,
          SimpleGraph.Walk.support_mapLe_eq_support] using hzArmK
      exact T.rightToAttach_support_inter_rim_eq_right
        (i := i) (j := k) hik hzArmIOld
          (T.attachToRight_support_subset_rim k hzArmKOld)

theorem Tripod.allNilSameFirstViaLastTransitionRim_one_support_cases
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    {u v z : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
        hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
        hu hv transition 1).support) :
    z ∈ (T.attachToLeft j).support ∨
      z ∈ ((T.leftToAttach k).takeUntil v hv).support ∨
        z ∈ transition.support := by
  rcases Tripod.allNilSameFirstTransitionRim_one_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu (T.leftToAttach i).start_mem_support
      (Tripod.lastToFirstExtendedTransition T hgraph hv transition)
      (by simpa [Tripod.allNilSameFirstViaLastTransitionRim] using hz) with
    hzJ | hzEmpty | hzBridge
  · exact Or.inl hzJ
  · have hzLeft : z = T.left := by
      simpa [SimpleGraph.Walk.takeUntil_first] using hzEmpty
    exact Or.inr (Or.inl (by
      simp [hzLeft]))
  · change z ∈
      (transition.append
        (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).reverse).support at hzBridge
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzBridge
    rcases hzBridge with hzTransition | hzSuffix
    · exact Or.inr (Or.inr hzTransition)
    · right; left
      have hzMap : z ∈
          (((T.leftToAttach k).takeUntil v hv).mapLe hgraph).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSuffix
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzMap

theorem Tripod.allNilSameFirstViaLastTransitionRim_zero_one_internal_disjoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 0))
      (Walk.InternalVertices
        (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 1)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzOne
  rcases Tripod.allNilSameFirstTransitionRim_zero_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu (T.leftToAttach i).start_mem_support
      (Tripod.lastToFirstExtendedTransition T hgraph hv transition)
      (by simpa [Tripod.allNilSameFirstViaLastTransitionRim] using hzZero.1) with
    hzSegment | hzRightPrefix
  · rcases Tripod.allNilSameFirstViaLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with
      hzJ | hzLastPrefix | hzTransition
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzJ)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hij
          (by simpa [hzi] using T.attachToLeft_support_subset_rim j hzJ)
      · exact hzZero.2.1
          (hzj.trans
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
    · have hzLast : z ∈ (T.leftToAttach k).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzLastPrefix
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim k hzLast)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hik
          (by simpa [hzi] using T.leftToAttach_support_subset_rim k hzLast)
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := k) hjk
          (by simpa [hzj] using T.leftToAttach_support_subset_rim k hzLast)
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hi hj
          (Nat.le_of_lt hij_order) z hzSegment)
  · have huForward : u ∈ (T.attachToRight i).support := by
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hu
    have hzRight : z ∈ (T.rightToAttach i).support := by
      have hzForward : z ∈ (T.attachToRight i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) huForward hzRightPrefix
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hzForward
    rcases Tripod.allNilSameFirstViaLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with
      hzJ | hzLastPrefix | hzTransition
    · have hzRightEnd : z = T.right :=
        T.rightToAttach_support_inter_rim_eq_right hij hzRight
          (T.attachToLeft_support_subset_rim j hzJ)
      have hrightNotPrefix :
          T.right ∉ ((T.attachToRight i).takeUntil u huForward).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.attachToRight_isPath i) huForward
          (by simpa [ne_eq] using hu_internal.2.2.symm)
      exact hrightNotPrefix (by simpa [hzRightEnd] using hzRightPrefix)
    · have hzLast : z ∈ (T.leftToAttach k).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzLastPrefix
      have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left
          (i := k) (j := i) (fun h => hik h.symm) hzLast
          (T.rightToAttach_support_subset_rim i hzRight)
      exact T.left_not_mem_attachToRight i (by
        simpa [Tripod.rightToAttach,
          SimpleGraph.Walk.support_reverse, hzLeft] using hzRight)
    · have hzCarrier : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet
          (T.rightToAttach_support_subset_rim i hzRight)
      rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
      · exact hzZero.2.2 hzu
      · have hvI : v ∈ (T.rim i).support := by
          simpa [hzv] using T.rightToAttach_support_subset_rim i hzRight
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          (T.rim_support_internal_of_not_endpoint hvI
            ⟨hv_internal.2.1, hv_internal.2.2⟩) hv_internal

theorem Tripod.allNilSameFirstViaLastTransitionRim_one_two_internal_disjoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 1))
      (Walk.InternalVertices
        (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzOne hzTwo
  rcases Tripod.allNilSameFirstViaLastTransitionRim_one_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu hv transition hzOne.1 with
    hzJ | hzLastPrefix | hzTransition
  · rcases Tripod.allNilSameFirstTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu (T.leftToAttach i).start_mem_support
        (Tripod.lastToFirstExtendedTransition T hgraph hv transition)
        (by simpa [Tripod.allNilSameFirstViaLastTransitionRim] using hzTwo.1) with
      hzSegment | hzArmK | hzRightPrefix
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzJ)) with hzj | hzk
      · exact hzOne.2.1
          (hzj.trans
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := j) (fun h => hjk h.symm)
          (by simpa [hzk] using T.attachToLeft_support_subset_rim j hzJ)
    · have hzLeftJ : z ∈ (T.leftToAttach j).support := by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzJ
      have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJ
          (T.attachToRight_support_subset_rim k hzArmK)
      exact T.left_not_mem_attachToRight k (by simpa [hzLeft] using hzArmK)
    · have hzRightI : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRightPrefix
      have hzRight : z = T.right :=
        T.rightToAttach_support_inter_rim_eq_right
          (i := i) (j := j) hij hzRightI
            (T.attachToLeft_support_subset_rim j hzJ)
      exact T.right_not_mem_attachToLeft j (by simpa [hzRight] using hzJ)
  · have hzLast : z ∈ (T.leftToAttach k).support :=
      SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach k) hv hzLastPrefix
    rcases Tripod.allNilSameFirstTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu (T.leftToAttach i).start_mem_support
        (Tripod.lastToFirstExtendedTransition T hgraph hv transition)
        (by simpa [Tripod.allNilSameFirstViaLastTransitionRim] using hzTwo.1) with
      hzSegment | hzArmK | hzRightPrefix
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim k hzLast)) with hzj | hzk
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := k) hjk
          (by simpa [hzj] using T.leftToAttach_support_subset_rim k hzLast)
      · have hzAttach : z = T.attach k :=
          hzk.trans ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
        exact
          (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.leftToAttach_isPath k) hv hv_ne_attach.symm)
            (by simpa [hzAttach] using hzLastPrefix)
    · have hzAttach : z = T.attach k :=
        T.leftToAttach_support_inter_rightToAttach_eq_attach k hzLast (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzArmK)
      exact
        (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leftToAttach_isPath k) hv hv_ne_attach.symm)
          (by simpa [hzAttach] using hzLastPrefix)
    · have hzRightI : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRightPrefix
      have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left
          (i := k) (j := i) (fun h => hik h.symm) hzLast
          (T.rightToAttach_support_subset_rim i hzRightI)
      exact T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightI)
  · rcases Tripod.allNilSameFirstTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu (T.leftToAttach i).start_mem_support
        (Tripod.lastToFirstExtendedTransition T hgraph hv transition)
        (by simpa [Tripod.allNilSameFirstViaLastTransitionRim] using hzTwo.1) with
      hzSegment | hzArmK | hzRightPrefix
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegment)
    · have hzCarrier : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (T.attachToRight_support_subset_rim k hzArmK)
      rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
      · have huK : u ∈ (T.rim k).support := by
          simpa [hzu] using T.attachToRight_support_subset_rim k hzArmK
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          hu_internal
          (T.rim_support_internal_of_not_endpoint huK
            ⟨hu_internal.2.1, hu_internal.2.2⟩)
      · have hvRight : v ∈ (T.rightToAttach k).support := by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse, hzv] using hzArmK
        exact hv_ne_attach
          (T.leftToAttach_support_inter_rightToAttach_eq_attach k hv hvRight)
    · have hzRightI : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRightPrefix
      have hzCarrier : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzRightI)
      rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
      · exact hzOne.2.2 hzu
      · have hvI : v ∈ (T.rim i).support := by
          simpa [hzv] using T.rightToAttach_support_subset_rim i hzRightI
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          (T.rim_support_internal_of_not_endpoint hvI
            ⟨hv_internal.2.1, hv_internal.2.2⟩) hv_internal

theorem Tripod.allNilSameFirstViaLastTransitionRims_internal_disjoint
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order : Walk.supportIndex P.path (T.boundary i) <
      Walk.supportIndex P.path (T.boundary j))
    (hjk_order : Walk.supportIndex P.path (T.boundary j) <
      Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
            hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
            hu hv transition r))
        (Walk.InternalVertices
          (Tripod.allNilSameFirstViaLastTransitionRim P T hgraph
            hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
            hu hv transition s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact Tripod.allNilSameFirstViaLastTransitionRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hpath_contacts hu hu_internal hv
      hv_internal transition htransition_outside htransition_clean
  · simpa [Tripod.allNilSameFirstViaLastTransitionRim] using
      (Tripod.allNilSameFirstTransitionRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        (T.leftToAttach i).start_mem_support
        (Tripod.lastToFirstExtendedTransition T hgraph hv transition))
  · exact
      (Tripod.allNilSameFirstViaLastTransitionRim_zero_one_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hpath_contacts hu hu_internal hv
        hv_internal transition htransition_outside htransition_clean).symm
  · exact False.elim (hrs rfl)
  · exact Tripod.allNilSameFirstViaLastTransitionRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hpath_contacts hu hu_internal hv hv_ne_attach
      hv_internal transition htransition_outside htransition_clean
  · simpa [Tripod.allNilSameFirstViaLastTransitionRim] using
      (Tripod.allNilSameFirstTransitionRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        (T.leftToAttach i).start_mem_support
        (Tripod.lastToFirstExtendedTransition T hgraph hv transition)).symm
  · exact
      (Tripod.allNilSameFirstViaLastTransitionRim_one_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hpath_contacts hu hu_internal hv hv_ne_attach
        hv_internal transition htransition_outside htransition_clean).symm
  · exact False.elim (hrs rfl)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
