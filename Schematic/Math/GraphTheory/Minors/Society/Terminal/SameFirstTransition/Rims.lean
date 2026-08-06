import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameFirstTransition.CommonLegs

/-!
The same-first-arm transition rims and their incidence properties.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- The three rims used when a clean carrier transition starts and ends on
the two strict arms of the first ordered old rim.

The new common ends are the median old attachment and the right-arm contact.
The first and last rims use the two ordered subpaths of the induced cut path;
the middle rim runs through the old left common end and the new transition.
This is the first of the finite theta exchanges hidden in the last "easily"
of GM IX `(2.4)`. -/
def Tripod.allNilSameFirstTransitionRim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v) :
    Fin 3 -> S.graph.Walk (T.attach j) u
  | 0 =>
      ((P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order)).reverse.copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).append
        (((T.attachToRight i).takeUntil u (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hu)).mapLe hgraph)
  | 1 =>
      (((T.attachToLeft j).mapLe hgraph).append
        (((T.leftToAttach i).takeUntil v hv).mapLe hgraph)).append
          transition.reverse
  | 2 =>
      (((P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).append
        ((T.attachToRight k).mapLe hgraph)).append
          (((T.rightToAttach i).takeUntil u hu).mapLe hgraph)

/-- Each rim in the same-first-arm transition exchange is a simple path. -/
theorem Tripod.allNilSameFirstTransitionRim_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition r).IsPath := by
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
      simpa [arm] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.attachToRight_isPath i).takeUntil huForward)
    change (segment.append arm).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hsegment_path harm_path ?_
    intro z hzSegment hzArm
    have hzSegmentOld :
        z ∈ (P.pathSegmentBetween hi hj
          (Nat.le_of_lt hij_order)).support := by
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
  · let first : S.graph.Walk (T.attach j) v :=
      ((T.attachToLeft j).mapLe hgraph).append
        (((T.leftToAttach i).takeUntil v hv).mapLe hgraph)
    have hfirst_path : first.IsPath := by
      dsimp [first]
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        (SimpleGraph.Walk.IsPath.mapLe hgraph (T.attachToLeft_isPath j))
        (SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.leftToAttach_isPath i).takeUntil hv)) ?_
      intro z hzJ hzI
      have hzJRim : z ∈ (T.rim j).support :=
        T.attachToLeft_support_subset_rim j (by
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzJ)
      have hzIArm : z ∈ (T.leftToAttach i).support := by
        apply SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach i) hv
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzI
      exact T.leftToAttach_support_inter_rim_eq_left
        (i := i) (j := j) hij hzIArm hzJRim
    change (first.append transition.reverse).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hfirst_path htransition_path.reverse ?_
    intro z hzFirst hzTransitionRev
    have hzTransition : z ∈ transition.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzTransitionRev
    have hzFirstCarrier : z ∈ T.vertexSet := by
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
        hzJ | hzI
      · exact T.rim_mem_vertexSet
          (T.attachToLeft_support_subset_rim j (by
            simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzJ))
      · exact T.rim_mem_vertexSet
          (T.leftToAttach_support_subset_rim i
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.leftToAttach i) hv (by
                simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzI)))
    rcases htransition_clean z hzTransition hzFirstCarrier with hzu | hzv
    · subst z
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
        huJ | huI
      · have huJRim : u ∈ (T.rim j).support :=
          T.attachToLeft_support_subset_rim j (by
            simpa [SimpleGraph.Walk.support_mapLe_eq_support] using huJ)
        exact False.elim
          (Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            hu_internal
            (T.rim_support_internal_of_not_endpoint huJRim
              (by exact ⟨hu_internal.2.1, hu_internal.2.2⟩)))
      · have huLeft : u ∈ (T.leftToAttach i).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.leftToAttach i) hv (by
              simpa [SimpleGraph.Walk.support_mapLe_eq_support] using huI)
        exact False.elim (hu_ne_attach
          (T.leftToAttach_support_inter_rightToAttach_eq_attach i
            huLeft hu))
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
      have hzSegmentOld :
          z ∈ (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [segment, SimpleGraph.Walk.support_copy] using hzSegment
      have hzArmKOld : z ∈ (T.attachToRight k).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArmK
      rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegmentOld
            (T.rim_mem_vertexSet
              (T.attachToRight_support_subset_rim k hzArmKOld)) with
        hzj | hzk
      · exact False.elim
          (T.boundary_not_mem_rim_of_ne_index hjk
            (by simpa [hzj] using
              T.attachToRight_support_subset_rim k hzArmKOld))
      · exact hzk.trans
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
    have harm_path : arm.IsPath := by
      simpa [arm] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.rightToAttach_isPath i).takeUntil hu)
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
    · have hzSegmentOld :
          z ∈ (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [toRight, segment, SimpleGraph.Walk.support_copy] using hzSegment
      rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegmentOld
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim i hzArmIOld)) with
        hzj | hzk
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
        simpa [toRight, SimpleGraph.Walk.support_mapLe_eq_support] using hzArmK
      exact T.rightToAttach_support_inter_rim_eq_right
        (i := i) (j := k) hik hzArmIOld
          (T.attachToRight_support_subset_rim k hzArmKOld)

/-- The old outer attachments and old left common end are internal on the
three same-first transition rims. -/
theorem Tripod.allNilSameFirstTransitionAttach_mem_rim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v) :
    forall r : Fin 3,
      GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k r ∈
        Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
            P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
            hij_order hjk_order hu hv transition r) := by
  intro r
  fin_cases r
  · refine ⟨?_, T.attach_ne_of_ne hij, hu_ne_attach.symm⟩
    rw [Tripod.allNilSameFirstTransitionRim.eq_def,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    exact
      ((P.pathSegmentBetween hi hj
        (Nat.le_of_lt hij_order)).reverse.copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).end_mem_support
  · refine ⟨?_, (T.attach_mem_rim j).2.1.symm, hu_internal.2.1.symm⟩
    rw [Tripod.allNilSameFirstTransitionRim.eq_def,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    simp [Tripod.allNilCleanBridgeAttach,
      SimpleGraph.Walk.support_mapLe_eq_support]
  · refine ⟨?_, T.attach_ne_of_ne (fun h => hjk h.symm), ?_⟩
    · rw [Tripod.allNilSameFirstTransitionRim.eq_def,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      rw [SimpleGraph.Walk.mem_support_append_iff]
      left
      exact
        ((P.pathSegmentBetween hj hk
          (Nat.le_of_lt hjk_order)).copy
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
            ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).end_mem_support
    · intro hku
      have hku' : T.attach k = u := by
        simpa [Tripod.allNilCleanBridgeAttach] using hku
      have hkRimI : T.attach k ∈ (T.rim i).support := by
        rw [hku']
        exact Walk.internalVertices_subset_support (T.rim i) hu_internal
      exact T.attach_not_mem_rim_of_ne
        (i := k) (j := i) (fun h => hik h.symm) hkRimI

theorem Tripod.allNilSameFirstTransitionRim_zero_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {u v z : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 0).support) :
    z ∈ (P.pathSegmentBetween hi hj
        (Nat.le_of_lt hij_order)).support ∨
      z ∈ ((T.attachToRight i).takeUntil u (by
        simpa [Tripod.rightToAttach,
          SimpleGraph.Walk.support_reverse] using hu)).support := by
  rw [Tripod.allNilSameFirstTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzSegment | hzArm
  · exact Or.inl (by
      simpa [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse] using hzSegment)
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)

theorem Tripod.allNilSameFirstTransitionRim_one_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {u v z : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 1).support) :
    z ∈ (T.attachToLeft j).support ∨
      z ∈ ((T.leftToAttach i).takeUntil v hv).support ∨
        z ∈ transition.support := by
  rw [Tripod.allNilSameFirstTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzOld | hzTransition
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzOld
    rcases hzOld with hzJ | hzI
    · exact Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzJ)
    · exact Or.inr (Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzI))
  · exact Or.inr (Or.inr (by
      simpa [SimpleGraph.Walk.support_reverse] using hzTransition))

theorem Tripod.allNilSameFirstTransitionRim_two_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {u v z : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 2).support) :
    z ∈ (P.pathSegmentBetween hj hk
        (Nat.le_of_lt hjk_order)).support ∨
      z ∈ (T.attachToRight k).support ∨
        z ∈ ((T.rightToAttach i).takeUntil u hu).support := by
  rw [Tripod.allNilSameFirstTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzFirst | hzI
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzSegment | hzK
    · exact Or.inl (by
        simpa [SimpleGraph.Walk.support_copy] using hzSegment)
    · exact Or.inr (Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzK))
  · exact Or.inr (Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzI))

/-- The cut-path/first-arm rim and transition rim meet internally nowhere. -/
theorem Tripod.allNilSameFirstTransitionRim_zero_one_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 1)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzOne
  rcases
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzZero.1 with
    hzSegment | hzRightPrefix
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzOne.1 with
      hzJ | hzLeftPrefix | hzTransition
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
    · have hzLeft : z ∈ (T.leftToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach i) hv hzLeftPrefix
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim i hzLeft)) with hzi | hzj
      · have hattachNotPrefix :
            T.attach i ∉ ((T.leftToAttach i).takeUntil v hv).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.leftToAttach_isPath i) hv
            (by simpa [ne_eq] using hv_ne_attach.symm)
        exact hattachNotPrefix (by
          simpa [hzi,
            (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using
              hzLeftPrefix)
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.leftToAttach_support_subset_rim i hzLeft)
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
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzOne.1 with
      hzJ | hzLeftPrefix | hzTransition
    · have hzRightEnd : z = T.right :=
        T.rightToAttach_support_inter_rim_eq_right hij hzRight
          (T.attachToLeft_support_subset_rim j hzJ)
      have hrightNotPrefix :
          T.right ∉ ((T.attachToRight i).takeUntil u huForward).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.attachToRight_isPath i) huForward
          (by simpa [ne_eq] using hu_internal.2.2.symm)
      exact hrightNotPrefix (by simpa [hzRightEnd] using hzRightPrefix)
    · have hzLeft : z ∈ (T.leftToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach i) hv hzLeftPrefix
      have hzAttach : z = T.attach i :=
        T.leftToAttach_support_inter_rightToAttach_eq_attach i hzLeft hzRight
      have hattachNotLeftPrefix :
          T.attach i ∉ ((T.leftToAttach i).takeUntil v hv).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leftToAttach_isPath i) hv
          (by simpa [ne_eq] using hv_ne_attach.symm)
      exact hattachNotLeftPrefix (by simpa [hzAttach] using hzLeftPrefix)
    · have hzCarrier : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet
          (T.rightToAttach_support_subset_rim i hzRight)
      rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
      · exact hzZero.2.2 hzu
      · have hvAttach : v = T.attach i :=
          T.leftToAttach_support_inter_rightToAttach_eq_attach i hv
            (by simpa [hzv] using hzRight)
        exact hv_ne_attach hvAttach

/-- The two cut-path rims of the same-first transition theta meet only at
their common ends. -/
theorem Tripod.allNilSameFirstTransitionRim_zero_two_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzTwo
  rcases
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzZero.1 with
    hzSegmentIJ | hzForwardPrefix
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegmentJK | hzArmK | hzReversePrefix
    · have hz_le_j :
          Walk.supportIndex P.path z <=
            Walk.supportIndex P.path (T.boundary j) := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          Walk.segmentBetween_supportIndex_right_le
            (by simpa [GMIX24CutPath.pathSet] using hi)
            (by simpa [GMIX24CutPath.pathSet] using hj)
            (Nat.le_of_lt hij_order) hzSegmentIJ
      have hj_le_z :
          Walk.supportIndex P.path (T.boundary j) <=
            Walk.supportIndex P.path z := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          Walk.segmentBetween_supportIndex_left_le P.path_isPath
            (by simpa [GMIX24CutPath.pathSet] using hj)
            (by simpa [GMIX24CutPath.pathSet] using hk)
            (Nat.le_of_lt hjk_order) hzSegmentJK
      have hzPath : z ∈ P.path.support := by
        simpa [GMIX24CutPath.pathSet] using
          P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegmentIJ
      have hjPath : T.boundary j ∈ P.path.support := by
        simpa [GMIX24CutPath.pathSet] using hj
      have hzj : z = T.boundary j :=
        Walk.supportIndex_injective_of_mem hzPath
          (le_antisymm hz_le_j hj_le_z)
      exact hzZero.2.1
        (hzj.trans
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegmentIJ
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim k hzArmK)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hik
          (by simpa [hzi] using T.attachToRight_support_subset_rim k hzArmK)
      · exact T.boundary_not_mem_rim_of_ne_index hjk
          (by simpa [hzj] using T.attachToRight_support_subset_rim k hzArmK)
    · have hzRight : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzReversePrefix
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegmentIJ
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzRight)) with hzi | hzj
      · have hattachNotPrefix :
            T.attach i ∉ ((T.rightToAttach i).takeUntil u hu).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.rightToAttach_isPath i) hu
            (by simpa [ne_eq] using hu_ne_attach.symm)
        exact hattachNotPrefix (by
          simpa [hzi,
            (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using
              hzReversePrefix)
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.rightToAttach_support_subset_rim i hzRight)
  · have huForward : u ∈ (T.attachToRight i).support := by
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hu
    have hzForward : z ∈ (T.attachToRight i).support :=
      SimpleGraph.Walk.support_takeUntil_subset
        (T.attachToRight i) huForward hzForwardPrefix
    have hzRight : z ∈ (T.rightToAttach i).support := by
      simpa [Tripod.rightToAttach,
        SimpleGraph.Walk.support_reverse] using hzForward
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegmentJK | hzArmK | hzReversePrefix
    · rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegmentJK
            (T.rim_mem_vertexSet
              (T.attachToRight_support_subset_rim i hzForward)) with
        hzj | hzk
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.attachToRight_support_subset_rim i hzForward)
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := i) (fun h => hik h.symm)
          (by simpa [hzk] using T.attachToRight_support_subset_rim i hzForward)
    · have hzRightEnd : z = T.right :=
        T.rightToAttach_support_inter_rim_eq_right
          (i := i) (j := k) hik hzRight
            (T.attachToRight_support_subset_rim k hzArmK)
      have hrightNotPrefix :
          T.right ∉ ((T.attachToRight i).takeUntil u huForward).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.attachToRight_isPath i) huForward
          (by simpa [ne_eq] using hu_internal.2.2.symm)
      exact hrightNotPrefix (by simpa [hzRightEnd] using hzForwardPrefix)
    · have hzReverseOnReversed :
          z ∈
            ((T.attachToRight i).reverse.takeUntil u (by
              simpa [SimpleGraph.Walk.support_reverse] using huForward)).reverse.support := by
        simpa [Tripod.rightToAttach,
          SimpleGraph.Walk.support_reverse] using hzReversePrefix
      have hzu : z = u :=
        Walk.IsPath.eq_of_mem_takeUntil_and_reverse_takeUntil
          (T.attachToRight_isPath i) huForward
          (by simpa [SimpleGraph.Walk.support_reverse] using huForward)
          hzForwardPrefix hzReverseOnReversed
      exact hzZero.2.2 hzu

/-- The transition rim and last cut-path rim meet only at their common ends. -/
theorem Tripod.allNilSameFirstTransitionRim_one_two_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim i) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 1))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzOne hzTwo
  rcases
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with
    hzJ | hzLeftPrefix | hzTransition
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegmentJK | hzArmK | hzRightPrefix
    · rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegmentJK
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
  · have hzLeftI : z ∈ (T.leftToAttach i).support :=
      SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach i) hv hzLeftPrefix
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegmentJK | hzArmK | hzRightPrefix
    · rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegmentJK
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim i hzLeftI)) with hzj | hzk
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.leftToAttach_support_subset_rim i hzLeftI)
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := i) (fun h => hik h.symm)
          (by simpa [hzk] using T.leftToAttach_support_subset_rim i hzLeftI)
    · have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left hik hzLeftI
          (T.attachToRight_support_subset_rim k hzArmK)
      exact T.left_not_mem_attachToRight k (by simpa [hzLeft] using hzArmK)
    · exact Set.disjoint_left.mp
        (T.leftToAttach_takeUntil_support_disjoint_rightToAttach
          hv hv_ne_attach) hzLeftPrefix
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach i) hu hzRightPrefix)
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegmentJK | hzArmK | hzRightPrefix
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegmentJK)
    · have hzCarrier : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (T.attachToRight_support_subset_rim k hzArmK)
      rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
      · have huK : u ∈ (T.rim k).support := by
          simpa [hzu] using T.attachToRight_support_subset_rim k hzArmK
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          hu_internal
          (T.rim_support_internal_of_not_endpoint huK
            ⟨hu_internal.2.1, hu_internal.2.2⟩)
      · have hvK : v ∈ (T.rim k).support := by
          simpa [hzv] using T.attachToRight_support_subset_rim k hzArmK
        rcases hleft_contact with hvInternal | hvLeft
        · exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
            hvInternal
            (T.rim_support_internal_of_not_endpoint hvK
              ⟨hvInternal.2.1, hvInternal.2.2⟩)
        · exact T.left_not_mem_attachToRight k
            (by simpa [hzv, hvLeft] using hzArmK)
    · have hzRightI : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRightPrefix
      have hzCarrier : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzRightI)
      rcases htransition_clean z hzTransition hzCarrier with hzu | hzv
      · exact hzOne.2.2 hzu
      · exact hv_ne_attach
          (T.leftToAttach_support_inter_rightToAttach_eq_attach i hv
            (by simpa [hzv] using hzRightI))

theorem Tripod.allNilSameFirstTransitionRims_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim i) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
            P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
            hij_order hjk_order hu hv transition r))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
            P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
            hij_order hjk_order hu hv transition s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_one_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu
        hu_internal hv hv_ne_attach transition htransition_outside
        htransition_clean
  · exact
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv transition
  · exact
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_one_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu
        hu_internal hv hv_ne_attach transition htransition_outside
        htransition_clean).symm
  · exact False.elim (hrs rfl)
  · exact
      GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hu_internal
        hv hv_ne_attach hleft_contact transition htransition_outside
        htransition_clean
  · exact
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hu_internal hv transition).symm
  · exact
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hu_internal
        hv hv_ne_attach hleft_contact transition htransition_outside
        htransition_clean).symm
  · exact False.elim (hrs rfl)

/-- The three standard boundary legs meet the same-first transition theta
only at their selected attachments. -/
theorem Tripod.allNilSameFirstTransitionLegs_meet_rims_only_at_attach
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a u v : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = T.left) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
          hleg_i_nil hleg_k_nil hi hk q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition s).support ->
      z = GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k r := by
  intro r s z hzLeg hzRim
  fin_cases r <;> fin_cases s
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArm
    · have hzi : z = T.boundary i := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.pathTailToStart_support_inter_segmentBetween_subset_left
            hi hj (Nat.le_of_lt hij_order) hzTail hzSegment
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
    · have hzArmOld : z ∈ (T.attachToRight i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArm
      have hzi : z = T.boundary i :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim i hzArmOld))
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzJ | hzLeft | hzTransition
    · have hzi :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzJ))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.attachToLeft_support_subset_rim j hzJ))
    · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach i) hv hzLeft
      have hzi :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim i hzLeftOld))
      have hattachNotPrefix :
          T.attach i ∉ ((T.leftToAttach i).takeUntil v hv).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leftToAttach_isPath i) hv
          (by simpa [ne_eq] using hv_ne_attach.symm)
      exact False.elim (hattachNotPrefix (by
        simpa [hzi,
          (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzLeft))
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail))
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzK | hzRight
    · exact False.elim (Set.disjoint_left.mp
        (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
          hi hj hk hij_order (Nat.le_of_lt hjk_order)) hzTail
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment))
    · have hzi :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim k hzK))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hzi] using T.attachToRight_support_subset_rim k hzK))
    · have hzRightOld : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRight
      have hzi :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzRightOld))
      have hattachNotPrefix :
          T.attach i ∉ ((T.rightToAttach i).takeUntil u hu).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.rightToAttach_isPath i) hu
          (by simpa [ne_eq] using hu_ne_attach.symm)
      exact False.elim (hattachNotPrefix (by
        simpa [hzi,
          (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzRight))
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArm
    · exact False.elim ((hq_outside z
          (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)).2
        (P.pathSegmentBetween_support_subset_pathSet hi hj
          (Nat.le_of_lt hij_order) z hzSegment))
    · have hzArmOld : z ∈ (T.attachToRight i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArm
      have hzLeft := hq_clean z
        (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
        (T.rim_mem_vertexSet
          (T.attachToRight_support_subset_rim i hzArmOld))
      exact False.elim (T.left_not_mem_attachToRight i
        (by simpa [hzLeft] using hzArmOld))
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzJ | hzLeft | hzTransition
    · exact hq_clean z
        (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
        (T.rim_mem_vertexSet
          (T.attachToLeft_support_subset_rim j hzJ))
    · exact hq_clean z
        (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
        (T.rim_mem_vertexSet
          (T.leftToAttach_support_subset_rim i
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.leftToAttach i) hv hzLeft)))
    · simpa [Tripod.allNilCleanBridgeAttach] using
        htransition_q z hzTransition
          (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
  · rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzK | hzRight
    · exact False.elim ((hq_outside z
          (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegment))
    · have hzLeft := hq_clean z
        (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
        (T.rim_mem_vertexSet
          (T.attachToRight_support_subset_rim k hzK))
      exact False.elim (T.left_not_mem_attachToRight k
        (by simpa [hzLeft] using hzK))
    · have hzRightOld : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRight
      have hzLeft := hq_clean z
        (by simpa [Tripod.allNilCleanBridgeLeg] using hzLeg)
        (T.rim_mem_vertexSet
          (T.rightToAttach_support_subset_rim i hzRightOld))
      exact False.elim (T.left_not_mem_rightToAttach i
        (by simpa [hzLeft] using hzRightOld))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArm
    · exact False.elim (Set.disjoint_left.mp
        (P.segmentBetween_support_disjoint_pathTailToEnd_of_lt
          hi hj hk (Nat.le_of_lt hij_order) hjk_order)
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment) hzTail)
    · have hzArmOld : z ∈ (T.attachToRight i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArm
      have hzk :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim i hzArmOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := i) (fun h => hik h.symm)
        (by simpa [hzk] using T.attachToRight_support_subset_rim i hzArmOld))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzJ | hzLeft | hzTransition
    · have hzk :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzJ))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.attachToLeft_support_subset_rim j hzJ))
    · have hzLeftOld : z ∈ (T.leftToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach i) hv hzLeft
      have hzk :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim i hzLeftOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := i) (fun h => hik h.symm)
        (by simpa [hzk] using T.leftToAttach_support_subset_rim i hzLeftOld))
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzK | hzRight
    · have hzk : z = T.boundary k := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.segmentBetween_support_inter_pathTailToEnd_subset_right
            hj hk (Nat.le_of_lt hjk_order) hzSegment hzTail
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk
    · have hzk :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim k hzK))
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk
    · have hzRightOld : z ∈ (T.rightToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRight
      have hzk :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzRightOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := i) (fun h => hik h.symm)
        (by simpa [hzk] using T.rightToAttach_support_subset_rim i hzRightOld))

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
