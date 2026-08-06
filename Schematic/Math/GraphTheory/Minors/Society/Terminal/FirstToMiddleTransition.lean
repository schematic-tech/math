import Schematic.Math.GraphTheory.Minors.Society.Terminal.CarrierTails
import Schematic.Math.GraphTheory.Minors.Society.Terminal.CleanBridge
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameMiddleTransition

/-!
All-nil transitions between the first and middle ordered rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Rims for a clean transition from the first right arm to the median left
arm.  The two cut-path rims are the same as in the diagonal first-arm
exchange; the middle rim stops on the median left arm before following the
transition backwards. -/
def Tripod.allNilFirstToMiddleTransitionRim
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
    (hv : v ∈ (T.leftToAttach j).support)
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
      (((T.attachToLeft j).takeUntil v (by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hv)).mapLe hgraph).append
        transition.reverse
  | 2 =>
      (((P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).append
        ((T.attachToRight k).mapLe hgraph)).append
          (((T.rightToAttach i).takeUntil u hu).mapLe hgraph)

theorem Tripod.allNilFirstToMiddleTransitionRim_isPath
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
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
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
  · have hvForward : v ∈ (T.attachToLeft j).support := by
      simpa [Tripod.attachToLeft,
        SimpleGraph.Walk.support_reverse] using hv
    let arm : S.graph.Walk (T.attach j) v :=
      ((T.attachToLeft j).takeUntil v hvForward).mapLe hgraph
    have harm_path : arm.IsPath := by
      simpa [arm] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.attachToLeft_isPath j).takeUntil hvForward)
    change (arm.append transition.reverse).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      harm_path htransition_path.reverse ?_
    intro z hzArm hzTransitionRev
    have hzTransition : z ∈ transition.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzTransitionRev
    have hzArmOld : z ∈ (T.attachToLeft j).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.attachToLeft j) hvForward
        (by simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
    rcases htransition_clean z hzTransition
        (T.rim_mem_vertexSet
          (T.attachToLeft_support_subset_rim j hzArmOld)) with hzu | hzv
    · have huRimJ : u ∈ (T.rim j).support := by
        simpa [hzu] using T.attachToLeft_support_subset_rim j hzArmOld
      exact False.elim (Set.disjoint_left.mp
        (T.rim_internals_disjoint i j hij) hu_internal
        (T.rim_support_internal_of_not_endpoint huRimJ
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
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [segment, SimpleGraph.Walk.support_copy] using hzSegment
      have hzArmKOld : z ∈ (T.attachToRight k).support := by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArmK
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts
          hzSegmentOld
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim k hzArmKOld)) with hzj | hzk
      · exact False.elim (T.boundary_not_mem_rim_of_ne_index hjk
          (by simpa [hzj] using T.attachToRight_support_subset_rim k hzArmKOld))
      · exact hzk.trans
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
    have harm_path : arm.IsPath := by
      simpa [arm] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.rightToAttach_isPath i).takeUntil hu)
    change (toRight.append arm).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      htoRight_path harm_path ?_
    intro z hzToRight hzArmI
    have hzArmIOld : z ∈ (T.rightToAttach i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach i) hu
        (by simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArmI)
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzToRight with
      hzSegment | hzArmK
    · have hzSegmentOld : z ∈
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [toRight, segment, SimpleGraph.Walk.support_copy] using hzSegment
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts
          hzSegmentOld
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzArmIOld)) with hzj | hzk
      · exact False.elim (T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.rightToAttach_support_subset_rim i hzArmIOld))
      · exact False.elim (T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := i) (fun h => hik h.symm)
          (by simpa [hzk] using T.rightToAttach_support_subset_rim i hzArmIOld))
    · have hzArmKOld : z ∈ (T.attachToRight k).support := by
        simpa [toRight, SimpleGraph.Walk.support_mapLe_eq_support] using hzArmK
      exact T.rightToAttach_support_inter_rim_eq_right
        (i := i) (j := k) hik hzArmIOld
          (T.attachToRight_support_subset_rim k hzArmKOld)

theorem Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
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
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 0).support) :
    z ∈ (P.pathSegmentBetween hi hj
        (Nat.le_of_lt hij_order)).support ∨
      z ∈ ((T.attachToRight i).takeUntil u (by
        simpa [Tripod.rightToAttach,
          SimpleGraph.Walk.support_reverse] using hu)).support := by
  rw [Tripod.allNilFirstToMiddleTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzSegment | hzArm
  · exact Or.inl (by
      simpa [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse] using hzSegment)
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)

theorem Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
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
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 1).support) :
    z ∈ ((T.attachToLeft j).takeUntil v (by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hv)).support ∨
      z ∈ transition.support := by
  rw [Tripod.allNilFirstToMiddleTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzArm | hzTransition
  · exact Or.inl (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_reverse] using hzTransition)

theorem Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
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
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 2).support) :
    z ∈ (P.pathSegmentBetween hj hk
        (Nat.le_of_lt hjk_order)).support ∨
      z ∈ (T.attachToRight k).support ∨
        z ∈ ((T.rightToAttach i).takeUntil u hu).support := by
  rw [Tripod.allNilFirstToMiddleTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzFirst | hzRight
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
      hzSegment | hzK
    · exact Or.inl (by
        simpa [SimpleGraph.Walk.support_copy] using hzSegment)
    · exact Or.inr (Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzK))
  · exact Or.inr (Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzRight))

theorem Tripod.allNilFirstToMiddleTransitionAttach_mem_rim
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
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v) :
    forall r : Fin 3,
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v r ∈
        Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
            P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
            hij_order hjk_order hu hv transition r) := by
  intro r
  fin_cases r
  · change T.attach i ∈ Walk.InternalVertices
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 0)
    refine ⟨?_, T.attach_ne_of_ne hij, hu_ne_attach.symm⟩
    · rw [Tripod.allNilFirstToMiddleTransitionRim.eq_def,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      exact ((P.pathSegmentBetween hi hj
        (Nat.le_of_lt hij_order)).reverse.copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).end_mem_support
  · change v ∈ Walk.InternalVertices
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 1)
    refine ⟨?_, hv_ne_attach, ?_⟩
    · rw [Tripod.allNilFirstToMiddleTransitionRim.eq_def,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      simp [SimpleGraph.Walk.support_mapLe_eq_support]
    · intro hvu
      have hvRimI : v ∈ Walk.InternalVertices (T.rim i) := by
        rw [hvu]
        exact hu_internal
      exact Set.disjoint_left.mp
        (T.rim_internals_disjoint j i (fun h => hij h.symm))
          hv_internal hvRimI
  · change T.attach k ∈ Walk.InternalVertices
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition 2)
    refine ⟨?_, T.attach_ne_of_ne (fun h => hjk h.symm), ?_⟩
    · rw [Tripod.allNilFirstToMiddleTransitionRim.eq_def,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      rw [SimpleGraph.Walk.mem_support_append_iff]
      left
      exact ((P.pathSegmentBetween hj hk
        (Nat.le_of_lt hjk_order)).copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).end_mem_support
    · intro haku
      have hakRimI : T.attach k ∈ (T.rim i).support := by
        rw [haku]
        exact hu_internal.1
      exact T.attach_not_mem_rim_of_ne (fun h => hik h.symm) hakRimI

theorem Tripod.allNilFirstToMiddleTransitionRim_zero_one_internal_disjoint
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
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 1)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzOne
  rcases GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu hv transition hzZero.1 with hzSegment | hzArmI
  · rcases GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzTransition
    · have hzArmJOld : z ∈ (T.attachToLeft j).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.attachToLeft j) (by
          simpa [Tripod.attachToLeft,
            SimpleGraph.Walk.support_reverse] using hv) hzArmJ
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzArmJOld)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hij
          (by simpa [hzi] using T.attachToLeft_support_subset_rim j hzArmJOld)
      · exact hzZero.2.1
          (hzj.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hi hj
          (Nat.le_of_lt hij_order) z hzSegment)
  · have hzArmIOld : z ∈ (T.attachToRight i).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.attachToRight i) (by
        simpa [Tripod.rightToAttach,
          SimpleGraph.Walk.support_reverse] using hu) hzArmI
    rcases GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzTransition
    · have hzLeftJ : z ∈ (T.leftToAttach j).support := by
        have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft j) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmJ
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzOld
      have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left (fun h => hij h.symm)
          hzLeftJ (T.attachToRight_support_subset_rim i hzArmIOld)
      exact T.left_not_mem_attachToRight i (by simpa [hzLeft] using hzArmIOld)
    · rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim i hzArmIOld)) with hzu | hzv
      · exact hzZero.2.2 hzu
      · have hzRimI : z ∈ (T.rim i).support :=
          T.attachToRight_support_subset_rim i hzArmIOld
        have hzInternalI := T.rim_support_internal_of_not_endpoint hzRimI
          ⟨by simpa [hzv] using hv_internal.2.1,
            by simpa [hzv] using hv_internal.2.2⟩
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hzInternalI (by simpa [hzv] using hv_internal)

theorem Tripod.allNilFirstToMiddleTransitionRim_one_two_internal_disjoint
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
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 1))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzOne hzTwo
  rcases GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzTransition
  · have hzArmJOld : z ∈ (T.attachToLeft j).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.attachToLeft j) (by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hv) hzArmJ
    have hzLeftJ : z ∈ (T.leftToAttach j).support := by
      simpa [Tripod.attachToLeft,
        SimpleGraph.Walk.support_reverse] using hzArmJOld
    rcases GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegment | hzArmK | hzRightI
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzArmJOld)) with hzj | hzk
      · exact hzOne.2.1
          (hzj.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := j) (fun h => hjk h.symm)
          (by simpa [hzk] using T.attachToLeft_support_subset_rim j hzArmJOld)
    · have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJ
          (T.attachToRight_support_subset_rim k hzArmK)
      exact T.left_not_mem_attachToRight k (by simpa [hzLeft] using hzArmK)
    · have hzRightOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach i) hu hzRightI
      have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left (fun h => hij h.symm)
          hzLeftJ (T.rightToAttach_support_subset_rim i hzRightOld)
      exact T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightOld)
  · rcases GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with
      hzSegment | hzArmK | hzRightI
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegment)
    · rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim k hzArmK)) with hzu | hzv
      · have hzRimK := T.attachToRight_support_subset_rim k hzArmK
        have hzInternalK := T.rim_support_internal_of_not_endpoint hzRimK
          ⟨by simpa [hzu] using hu_internal.2.1,
            by simpa [hzu] using hu_internal.2.2⟩
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          (by simpa [hzu] using hu_internal) hzInternalK
      · have hzRimK := T.attachToRight_support_subset_rim k hzArmK
        have hzInternalK := T.rim_support_internal_of_not_endpoint hzRimK
          ⟨by simpa [hzv] using hv_internal.2.1,
            by simpa [hzv] using hv_internal.2.2⟩
        exact Set.disjoint_left.mp (T.rim_internals_disjoint j k hjk)
          (by simpa [hzv] using hv_internal) hzInternalK
    · have hzRightOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach i) hu hzRightI
      rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzRightOld)) with hzu | hzv
      · exact hzOne.2.2 hzu
      · have hzRimI := T.rightToAttach_support_subset_rim i hzRightOld
        have hzInternalI := T.rim_support_internal_of_not_endpoint hzRimI
          ⟨by simpa [hzv] using hv_internal.2.1,
            by simpa [hzv] using hv_internal.2.2⟩
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hzInternalI (by simpa [hzv] using hv_internal)

theorem Tripod.allNilFirstToMiddleTransitionRims_internal_disjoint
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
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
            P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
            hij_order hjk_order hu hv transition r))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
            P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
            hij_order hjk_order hu hv transition s)) := by
  have hzero_two : Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition 2)) := by
    let dummy : S.graph.Walk u T.left :=
      (((T.rightToAttach i).dropUntil u hu).mapLe hgraph).append
        ((T.attachToLeft i).mapLe hgraph)
    simpa [Tripod.allNilFirstToMiddleTransitionRim,
      Tripod.allNilSameFirstTransitionRim] using
      (GMIX24SourceProof.Tripod.allNilSameFirstTransitionRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        (T.leftToAttach i).start_mem_support dummy)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hv hv_internal
      transition htransition_outside htransition_clean
  · exact hzero_two
  · exact (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hv hv_internal
      transition htransition_outside htransition_clean).symm
  · exact False.elim (hrs rfl)
  · exact GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hu_internal hv hv_internal
      transition htransition_outside htransition_clean
  · exact hzero_two.symm
  · exact (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hu_internal hv hv_internal
      transition htransition_outside htransition_clean).symm
  · exact False.elim (hrs rfl)

theorem Tripod.allNilFirstToMiddleTransitionLegs_meet_rims_only_at_attach
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
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
          P T hgraph hleg_i_nil hleg_k_nil hi hk hv q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition s).support ->
      z = GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v r := by
  intro r s z hzLeg hzRim
  fin_cases r <;> fin_cases s
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzSegment | hzArm
    · have hzi : z = T.boundary i := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.pathTailToStart_support_inter_segmentBetween_subset_left
            hi hj (Nat.le_of_lt hij_order) hzTail hzSegment
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
    · have hzArmOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArm
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim i hzArmOld))
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzArm | hzTransition
    · have hzArmOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft j) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArm
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzArmOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.attachToLeft_support_subset_rim j hzArmOld))
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail))
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArmK | hzRightI
    · exact False.elim (Set.disjoint_left.mp
        (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
          hi hj hk hij_order (Nat.le_of_lt hjk_order)) hzTail
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment))
    · have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim k hzArmK))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hzi] using T.attachToRight_support_subset_rim k hzArmK))
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRightI
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzOld))
      have hza : z = T.attach i := hzi.trans
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
      have hattachNotPrefix :
          T.attach i ∉ ((T.rightToAttach i).takeUntil u hu).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.rightToAttach_isPath i) hu hu_ne_attach.symm
      exact False.elim (hattachNotPrefix (by simpa [hza] using hzRightI))
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzMiddleArm | hzq
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support :=
        Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMiddleArm
      have hzLeftJ := SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach j) hv hzPrefix
      rcases Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with hzSegment | hzArmI
      · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJ)) with hzi | hzj
        · exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
            (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzLeftJ))
        · have hattachNotPrefix :
              T.attach j ∉ ((T.leftToAttach j).takeUntil v hv).support :=
            SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              (T.leftToAttach_isPath j) hv hv_ne_attach.symm
          exact False.elim (hattachNotPrefix (by simpa [hzj,
            (T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil] using hzPrefix))
      · have hzLeft := T.leftToAttach_support_inter_rim_eq_left
            (fun h => hij h.symm) hzLeftJ
            (T.attachToRight_support_subset_rim i (by
              exact SimpleGraph.Walk.support_takeUntil_subset
                (T.attachToRight i) (by
                  simpa [Tripod.rightToAttach,
                    SimpleGraph.Walk.support_reverse] using hu) hzArmI))
        have hzArmIFull : z ∈ (T.attachToRight i).support := by
          exact SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight i) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArmI
        exact False.elim (T.left_not_mem_attachToRight i
          (by simpa [hzLeft] using hzArmIFull))
    · rcases Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with hzSegment | hzArmI
      · exact False.elim ((hq_outside z hzq).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment))
      · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight i) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArmI
        have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim i hzOld))
        exact False.elim (T.left_not_mem_attachToRight i
          (by simpa [hzLeft] using hzOld))
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzMiddleArm | hzq
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support :=
        Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMiddleArm
      rcases Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with hzArmJ | hzTransition
      · have hzArmJRev : z ∈
            ((T.leftToAttach j).reverse.takeUntil v (by
              simpa [SimpleGraph.Walk.support_reverse] using hv)).reverse.support := by
          simpa [Tripod.attachToLeft,
            SimpleGraph.Walk.support_reverse] using hzArmJ
        have hzv := Walk.IsPath.eq_of_mem_takeUntil_and_reverse_takeUntil
          (T.leftToAttach_isPath j) hv
          (by simpa [SimpleGraph.Walk.support_reverse] using hv)
          hzPrefix hzArmJRev
        simpa [Tripod.allNilSameMiddleTransitionAttach] using hzv
      · have hzLeftJ := SimpleGraph.Walk.support_takeUntil_subset
            (T.leftToAttach j) hv hzPrefix
        rcases htransition_clean z hzTransition
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJ)) with hzu | hzv
        · have huRimJ : u ∈ (T.rim j).support := by
            simpa [hzu] using T.leftToAttach_support_subset_rim j hzLeftJ
          exact False.elim (Set.disjoint_left.mp
            (T.rim_internals_disjoint i j hij) hu_internal
            (T.rim_support_internal_of_not_endpoint huRimJ
              ⟨by simpa [hzu] using hu_internal.2.1,
                by simpa [hzu] using hu_internal.2.2⟩))
        · simpa [Tripod.allNilSameMiddleTransitionAttach] using hzv
    · rcases Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with hzArmJ | hzTransition
      · have hzArmOld := SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToLeft j) (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv) hzArmJ
        have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzArmOld))
        have hleftNotArm : T.left ∉
            ((T.attachToLeft j).takeUntil v (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv)).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.attachToLeft_isPath j) (by
              simpa [Tripod.attachToLeft,
                SimpleGraph.Walk.support_reverse] using hv)
              hv_internal.2.1.symm
        exact False.elim (hleftNotArm (by simpa [hzLeft] using hzArmJ))
      · exact False.elim (htransition_q z hzTransition hzq)
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzMiddleArm | hzq
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support :=
        Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMiddleArm
      have hzLeftJ := SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach j) hv hzPrefix
      rcases Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
        hzSegment | hzArmK | hzRightI
      · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJ)) with hzj | hzk
        · have hattachNotPrefix :
              T.attach j ∉ ((T.leftToAttach j).takeUntil v hv).support :=
            SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              (T.leftToAttach_isPath j) hv hv_ne_attach.symm
          exact False.elim (hattachNotPrefix (by simpa [hzj,
            (T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil] using hzPrefix))
        · exact False.elim (T.boundary_not_mem_rim_of_ne_index
            (i := k) (s := j) (fun h => hjk h.symm)
            (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzLeftJ))
      · have hzLeft := T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJ
          (T.attachToRight_support_subset_rim k hzArmK)
        exact False.elim (T.left_not_mem_attachToRight k
          (by simpa [hzLeft] using hzArmK))
      · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach i) hu hzRightI
        have hzLeft := T.leftToAttach_support_inter_rim_eq_left
          (fun h => hij h.symm) hzLeftJ
          (T.rightToAttach_support_subset_rim i hzOld)
        exact False.elim (T.left_not_mem_rightToAttach i
          (by simpa [hzLeft] using hzOld))
    · rcases Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
          P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
        hzSegment | hzArmK | hzRightI
      · exact False.elim ((hq_outside z hzq).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
      · have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim k hzArmK))
        exact False.elim (T.left_not_mem_attachToRight k
          (by simpa [hzLeft] using hzArmK))
      · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach i) hu hzRightI
        have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzOld))
        exact False.elim (T.left_not_mem_rightToAttach i
          (by simpa [hzLeft] using hzOld))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzSegment | hzArmI
    · exact False.elim (Set.disjoint_left.mp
        (P.segmentBetween_support_disjoint_pathTailToEnd_of_lt
          hi hj hk (Nat.le_of_lt hij_order) hjk_order)
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment) hzTail)
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArmI
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim i hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := i) (fun h => hik h.symm)
        (by simpa [hzk] using T.attachToRight_support_subset_rim i hzOld))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToMiddleTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzArmJ | hzTransition
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft j) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmJ
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.attachToLeft_support_subset_rim j hzOld))
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArmK | hzRightI
    · have hzk : z = T.boundary k := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.segmentBetween_support_inter_pathTailToEnd_subset_right
            hj hk (Nat.le_of_lt hjk_order) hzSegment hzTail
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk
    · have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim k hzArmK))
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach i) hu hzRightI
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := i) (fun h => hik h.symm)
        (by simpa [hzk] using T.rightToAttach_support_subset_rim i hzOld))

/-- Ambient tripod produced by a clean transition from the strict right arm
of the first ordered rim to the strict left arm of the median ordered rim. -/
theorem Tripod.liftAllNilOfFirstToMiddleArmTransition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach i).support)
    (hu_ne_attach : u ≠ T.attach i)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim i))
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  refine ⟨{
    left := T.attach j
    right := u
    left_ne_right := by
      intro hju
      exact T.attach_not_mem_rim_of_ne (fun h => hij h.symm)
        (by simpa [hju] using hu_internal.1)
    rim := GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
      P T hgraph (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_isPath
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts hu hu_internal
      hv transition htransition_path htransition_clean
    attach :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionAttach_mem_rim
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hu hu_ne_attach hu_internal
        hv hv_ne_attach hv_internal transition
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
      P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg_isPath
        P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q hq_path hq_clean
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach hu_internal
        hv hv_internal transition htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order hpath_contacts hv q hq_outside
    legs_meet_rims_only_at_attach :=
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionLegs_meet_rims_only_at_attach
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts q hq_outside hq_clean
        hu hu_ne_attach hu_internal hv hv_ne_attach hv_internal transition
        htransition_outside htransition_clean htransition_q
  }⟩

/-- Cut-path-reversed counterpart of the first-to-middle exchange. -/
theorem Tripod.liftAllNilOfLastToMiddleArmTransition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
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
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach k).support)
    (hu_ne_attach : u ≠ T.attach k)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  apply GMIX24SourceProof.Tripod.liftAllNilOfFirstToMiddleArmTransition
    (i := k) (j := j) (k := i) (a := a) (u := u) (v := v)
    (q := q) (transition := transition)
    P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact
      (GMIX24SourceProof.GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2
        hjk_order
  · exact
      (GMIX24SourceProof.GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2
        hij_order
  · intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hq_path
  · intro z hzq
    simpa using hq_outside z hzq
  · exact hq_clean
  · exact hu
  · exact hu_ne_attach
  · exact hu_internal
  · exact hv
  · exact hv_ne_attach
  · exact hv_internal
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean
  · exact htransition_q


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
