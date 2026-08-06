import Schematic.Math.GraphTheory.Minors.Society.Terminal.CarrierTails
import Schematic.Math.GraphTheory.Minors.Society.Terminal.CleanBridge
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameMiddleTransition

/-!
All-nil transitions between the first and last ordered rims.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Rims for a clean transition from the first right arm to the last left
arm.  Their common ends are the median attachment and the last-arm contact. -/
def Tripod.allNilFirstToLastTransitionRim
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
    {u v : V}
    (hu : u ∈ (T.rightToAttach i).support)
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v) :
    Fin 3 -> S.graph.Walk (T.attach j) v
  | 0 =>
      (((P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order)).reverse.copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).append
        (((T.attachToRight i).takeUntil u (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hu)).mapLe hgraph)).append
          transition
  | 1 =>
      ((T.attachToLeft j).mapLe hgraph).append
        (((T.leftToAttach k).takeUntil v hv).mapLe hgraph)
  | 2 =>
      ((P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).append
        (((T.attachToLeft k).takeUntil v (by
          simpa [Tripod.attachToLeft,
            SimpleGraph.Walk.support_reverse] using hv)).mapLe hgraph)

theorem Tripod.allNilFirstToLastTransitionRim_zero_support_cases
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
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈ (Tripod.allNilFirstToLastTransitionRim P T hgraph
      hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
      hu hv transition 0).support) :
    z ∈ (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order)).support ∨
      z ∈ ((T.attachToRight i).takeUntil u (by
        simpa [Tripod.rightToAttach,
          SimpleGraph.Walk.support_reverse] using hu)).support ∨
        z ∈ transition.support := by
  rw [Tripod.allNilFirstToLastTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzPrefix | hzTransition
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzPrefix with
      hzSegment | hzArm
    · exact Or.inl (by simpa [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse] using hzSegment)
    · exact Or.inr (Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm))
  · exact Or.inr (Or.inr hzTransition)

theorem Tripod.allNilFirstToLastTransitionRim_one_support_cases
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
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈ (Tripod.allNilFirstToLastTransitionRim P T hgraph
      hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
      hu hv transition 1).support) :
    z ∈ (T.attachToLeft j).support ∨
      z ∈ ((T.leftToAttach k).takeUntil v hv).support := by
  rw [Tripod.allNilFirstToLastTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzJ | hzK
  · exact Or.inl (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzJ)
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzK)

theorem Tripod.allNilFirstToLastTransitionRim_two_support_cases
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
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈ (Tripod.allNilFirstToLastTransitionRim P T hgraph
      hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
      hu hv transition 2).support) :
    z ∈ (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support ∨
      z ∈ ((T.attachToLeft k).takeUntil v (by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hv)).support := by
  rw [Tripod.allNilFirstToLastTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzSegment | hzArm
  · exact Or.inl (by simpa [SimpleGraph.Walk.support_copy] using hzSegment)
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)

theorem Tripod.allNilFirstToLastTransitionRim_isPath
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
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r : Fin 3,
      (Tripod.allNilFirstToLastTransitionRim P T hgraph
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
    let firstPart : S.graph.Walk (T.attach j) u := segment.append arm
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
    have hfirstPart_path : firstPart.IsPath := by
      dsimp [firstPart]
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hsegment_path harm_path ?_
      intro z hzSegment hzArm
      have hzSegmentOld : z ∈
          (P.pathSegmentBetween hi hj
            (Nat.le_of_lt hij_order)).support := by
        simpa [segment, SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_reverse] using hzSegment
      have hzArmOld : z ∈ (T.attachToRight i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) huForward (by
            simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegmentOld
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim i hzArmOld)) with hzi | hzj
      · exact hzi.trans ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)
      · exact False.elim (T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.attachToRight_support_subset_rim i hzArmOld))
    change (firstPart.append transition).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hfirstPart_path htransition_path ?_
    intro z hzPrefix hzTransition
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzPrefix with
      hzSegment | hzArm
    · have hzSegmentOld : z ∈
          (P.pathSegmentBetween hi hj
            (Nat.le_of_lt hij_order)).support := by
        simpa [firstPart, segment, SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_reverse] using hzSegment
      exact False.elim ((htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hi hj
          (Nat.le_of_lt hij_order) z hzSegmentOld))
    · have hzArmOld : z ∈ (T.attachToRight i).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) huForward (by
            simpa [firstPart, arm,
              SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
      rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim i hzArmOld)) with hzu | hzv
      · exact hzu
      · have hzRimI := T.attachToRight_support_subset_rim i hzArmOld
        have hzInternalI := T.rim_support_internal_of_not_endpoint hzRimI
          ⟨by simpa [hzv] using hv_internal.2.1,
            by simpa [hzv] using hv_internal.2.2⟩
        exact False.elim (Set.disjoint_left.mp
          (T.rim_internals_disjoint i k hik) hzInternalI
          (by simpa [hzv] using hv_internal))
  · let armJ : S.graph.Walk (T.attach j) T.left :=
      (T.attachToLeft j).mapLe hgraph
    let armK : S.graph.Walk T.left v :=
      ((T.leftToAttach k).takeUntil v hv).mapLe hgraph
    have harmJ_path : armJ.IsPath := by
      simpa [armJ] using SimpleGraph.Walk.IsPath.mapLe hgraph
        (T.attachToLeft_isPath j)
    have harmK_path : armK.IsPath := by
      simpa [armK] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.leftToAttach_isPath k).takeUntil hv)
    change (armJ.append armK).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      harmJ_path harmK_path ?_
    intro z hzJ hzK
    have hzJOld : z ∈ (T.attachToLeft j).support := by
      simpa [armJ, SimpleGraph.Walk.support_mapLe_eq_support] using hzJ
    have hzLeftJ : z ∈ (T.leftToAttach j).support := by
      simpa [Tripod.attachToLeft,
        SimpleGraph.Walk.support_reverse] using hzJOld
    have hzKOld : z ∈ (T.leftToAttach k).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach k) hv (by
        simpa [armK, SimpleGraph.Walk.support_mapLe_eq_support] using hzK)
    exact T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJ
      (T.leftToAttach_support_subset_rim k hzKOld)
  · let segment : S.graph.Walk (T.attach j) (T.attach k) :=
      (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).copy
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
    have hvBack : v ∈ (T.attachToLeft k).support := by
      simpa [Tripod.attachToLeft,
        SimpleGraph.Walk.support_reverse] using hv
    let arm : S.graph.Walk (T.attach k) v :=
      ((T.attachToLeft k).takeUntil v hvBack).mapLe hgraph
    have hsegment_path : segment.IsPath := by
      simpa [segment] using
        (SimpleGraph.Walk.isPath_copy
          (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order))
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).mpr
            (P.pathSegmentBetween_isPath hj hk (Nat.le_of_lt hjk_order))
    have harm_path : arm.IsPath := by
      simpa [arm] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.attachToLeft_isPath k).takeUntil hvBack)
    change (segment.append arm).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hsegment_path harm_path ?_
    intro z hzSegment hzArm
    have hzSegmentOld : z ∈
        (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
      simpa [segment, SimpleGraph.Walk.support_copy] using hzSegment
    have hzArmOld : z ∈ (T.attachToLeft k).support :=
      SimpleGraph.Walk.support_takeUntil_subset (T.attachToLeft k) hvBack (by
        simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm)
    rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
        T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegmentOld
        (T.rim_mem_vertexSet
          (T.attachToLeft_support_subset_rim k hzArmOld)) with hzj | hzk
    · exact False.elim (T.boundary_not_mem_rim_of_ne_index hjk
        (by simpa [hzj] using T.attachToLeft_support_subset_rim k hzArmOld))
    · exact hzk.trans ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)

theorem Tripod.allNilFirstToLastTransitionAttach_mem_rim
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
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v) :
    forall r : Fin 3,
      Tripod.allNilCleanBridgeAttach T i k r ∈
        Walk.InternalVertices
          (Tripod.allNilFirstToLastTransitionRim P T hgraph
            hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
            hu hv transition r) := by
  intro r
  fin_cases r
  · change T.attach i ∈ Walk.InternalVertices
      (Tripod.allNilFirstToLastTransitionRim P T hgraph
        hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
        hu hv transition 0)
    refine ⟨?_, T.attach_ne_of_ne hij, ?_⟩
    · rw [Tripod.allNilFirstToLastTransitionRim,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      rw [SimpleGraph.Walk.mem_support_append_iff]
      left
      exact ((P.pathSegmentBetween hi hj
        (Nat.le_of_lt hij_order)).reverse.copy
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
          ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil)).end_mem_support
    · intro haiv
      exact T.attach_not_mem_rim_of_ne hik
        (by simpa [haiv] using hv_internal.1)
  · change T.left ∈ Walk.InternalVertices
      (Tripod.allNilFirstToLastTransitionRim P T hgraph
        hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
        hu hv transition 1)
    refine ⟨?_, ?_, hv_internal.2.1.symm⟩
    · rw [Tripod.allNilFirstToLastTransitionRim,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      simp [SimpleGraph.Walk.support_mapLe_eq_support]
    · intro hleft
      exact (T.attach_mem_rim j).2.1 (by simp [hleft])
  · change T.attach k ∈ Walk.InternalVertices
      (Tripod.allNilFirstToLastTransitionRim P T hgraph
        hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
        hu hv transition 2)
    refine ⟨?_, T.attach_ne_of_ne (fun h => hjk h.symm), hv_ne_attach.symm⟩
    rw [Tripod.allNilFirstToLastTransitionRim,
      SimpleGraph.Walk.mem_support_append_iff]
    left
    exact ((P.pathSegmentBetween hj hk
      (Nat.le_of_lt hjk_order)).copy
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)).end_mem_support

theorem Tripod.allNilFirstToLastTransitionRim_zero_one_internal_disjoint
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
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim i) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (Tripod.allNilFirstToLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 0))
      (Walk.InternalVertices
        (Tripod.allNilFirstToLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 1)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzOne
  rcases Tripod.allNilFirstToLastTransitionRim_zero_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu hv transition hzZero.1 with
    hzSegment | hzArmI | hzTransition
  · rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzArmK
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzArmJ)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hij
          (by simpa [hzi] using T.attachToLeft_support_subset_rim j hzArmJ)
      · exact hzZero.2.1
          (hzj.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
    · have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzArmK
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegment
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim k hzArmKOld)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hik
          (by simpa [hzi] using T.leftToAttach_support_subset_rim k hzArmKOld)
      · exact T.boundary_not_mem_rim_of_ne_index hjk
          (by simpa [hzj] using T.leftToAttach_support_subset_rim k hzArmKOld)
  · have hzArmIOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.attachToRight i) (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hu) hzArmI
    rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzArmK
    · have hzLeftJ : z ∈ (T.leftToAttach j).support := by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzArmJ
      have hzLeft := T.leftToAttach_support_inter_rim_eq_left
        (fun h => hij h.symm) hzLeftJ
        (T.attachToRight_support_subset_rim i hzArmIOld)
      exact T.left_not_mem_attachToRight i (by simpa [hzLeft] using hzArmIOld)
    · have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzArmK
      have hzLeft := T.leftToAttach_support_inter_rim_eq_left
        (fun h => hik h.symm) hzArmKOld
        (T.attachToRight_support_subset_rim i hzArmIOld)
      exact T.left_not_mem_attachToRight i (by simpa [hzLeft] using hzArmIOld)
  · rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzArmK
    · rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzArmJ)) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · have hzInternalJ := T.rim_support_internal_of_not_endpoint
              (T.attachToLeft_support_subset_rim j hzArmJ)
              ⟨by simpa [hzu] using huInternal.2.1,
                by simpa [hzu] using huInternal.2.2⟩
          exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            (by simpa [hzu] using huInternal) hzInternalJ
        · exact T.right_not_mem_attachToLeft j
            (by simpa [hzu, huRight] using hzArmJ)
      · have hzInternalJ := T.rim_support_internal_of_not_endpoint
            (T.attachToLeft_support_subset_rim j hzArmJ)
            ⟨by simpa [hzv] using hv_internal.2.1,
              by simpa [hzv] using hv_internal.2.2⟩
        exact Set.disjoint_left.mp
          (T.rim_internals_disjoint k j (fun h => hjk h.symm))
          (by simpa [hzv] using hv_internal) hzInternalJ
    · have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzArmK
      rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim k hzArmKOld)) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · have hzInternalK := T.rim_support_internal_of_not_endpoint
              (T.leftToAttach_support_subset_rim k hzArmKOld)
              ⟨by simpa [hzu] using huInternal.2.1,
                by simpa [hzu] using huInternal.2.2⟩
          exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
            (by simpa [hzu] using huInternal) hzInternalK
        · exact T.right_not_mem_leftToAttach k
            (by simpa [hzu, huRight] using hzArmKOld)
      · exact hzZero.2.2 hzv

theorem Tripod.allNilFirstToLastTransitionRim_zero_two_internal_disjoint
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
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim i) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach k).support)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (Tripod.allNilFirstToLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 0))
      (Walk.InternalVertices
        (Tripod.allNilFirstToLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzTwo
  rcases Tripod.allNilFirstToLastTransitionRim_zero_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu hv transition hzZero.1 with
    hzSegmentIJ | hzArmI | hzTransition
  · rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with hzSegmentJK | hzArmK
    · have hzj : z = T.boundary j := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          Walk.segmentBetween_support_inter_subset_common P.path_isPath
            hi hj hk (Nat.le_of_lt hij_order) (Nat.le_of_lt hjk_order)
            hzSegmentIJ hzSegmentJK
      exact hzZero.2.1
        (hzj.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
    · have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmK
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts hzSegmentIJ
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim k hzArmKOld)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hik
          (by simpa [hzi] using T.attachToLeft_support_subset_rim k hzArmKOld)
      · exact T.boundary_not_mem_rim_of_ne_index hjk
          (by simpa [hzj] using T.attachToLeft_support_subset_rim k hzArmKOld)
  · have hzArmIOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.attachToRight i) (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hu) hzArmI
    rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with hzSegmentJK | hzArmK
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegmentJK
          (T.rim_mem_vertexSet
            (T.attachToRight_support_subset_rim i hzArmIOld)) with hzj | hzk
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := i) (fun h => hij h.symm)
          (by simpa [hzj] using T.attachToRight_support_subset_rim i hzArmIOld)
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := i) (fun h => hik h.symm)
          (by simpa [hzk] using T.attachToRight_support_subset_rim i hzArmIOld)
    · have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmK
      have hzLeftK : z ∈ (T.leftToAttach k).support := by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzArmKOld
      have hzLeft := T.leftToAttach_support_inter_rim_eq_left
        (fun h => hik h.symm) hzLeftK
        (T.attachToRight_support_subset_rim i hzArmIOld)
      exact T.left_not_mem_attachToRight i (by simpa [hzLeft] using hzArmIOld)
  · rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with hzSegmentJK | hzArmK
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegmentJK)
    · have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmK
      rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim k hzArmKOld)) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · have hzInternalK := T.rim_support_internal_of_not_endpoint
              (T.attachToLeft_support_subset_rim k hzArmKOld)
              ⟨by simpa [hzu] using huInternal.2.1,
                by simpa [hzu] using huInternal.2.2⟩
          exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
            (by simpa [hzu] using huInternal) hzInternalK
        · exact T.right_not_mem_attachToLeft k
            (by simpa [hzu, huRight] using hzArmKOld)
      · exact hzZero.2.2 hzv

theorem Tripod.allNilFirstToLastTransitionRim_one_two_internal_disjoint
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
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v) :
    Disjoint
      (Walk.InternalVertices
        (Tripod.allNilFirstToLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 1))
      (Walk.InternalVertices
        (Tripod.allNilFirstToLastTransitionRim P T hgraph
          hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
          hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzOne hzTwo
  rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
      P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
      hij_order hjk_order hu hv transition hzOne.1 with hzArmJ | hzPrefixK
  · rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with hzSegment | hzArmK
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim j hzArmJ)) with hzj | hzk
      · exact hzOne.2.1
          (hzj.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := j) (fun h => hjk h.symm)
          (by simpa [hzk] using T.attachToLeft_support_subset_rim j hzArmJ)
    · have hzLeftJ : z ∈ (T.leftToAttach j).support := by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzArmJ
      have hzArmKOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.attachToLeft k) (by
          simpa [Tripod.attachToLeft,
            SimpleGraph.Walk.support_reverse] using hv) hzArmK
      have hzLeft := T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJ
        (T.attachToLeft_support_subset_rim k hzArmKOld)
      have hleftNotArm : T.left ∉
          ((T.attachToLeft k).takeUntil v (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv)).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.attachToLeft_isPath k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv)
            hv_internal.2.1.symm
      exact hleftNotArm (by simpa [hzLeft] using hzArmK)
  · have hzPrefixKOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach k) hv hzPrefixK
    rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzTwo.1 with hzSegment | hzArmK
    · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
          T hij hik hjk hj hk hij_order hjk_order hpath_contacts hzSegment
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim k hzPrefixKOld)) with hzj | hzk
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := j) (s := k) hjk
          (by simpa [hzj] using T.leftToAttach_support_subset_rim k hzPrefixKOld)
      · have hattachNotPrefix :
            T.attach k ∉ ((T.leftToAttach k).takeUntil v hv).support :=
          SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            (T.leftToAttach_isPath k) hv hv_ne_attach.symm
        exact hattachNotPrefix (by simpa [hzk,
          (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzPrefixK)
    · have hzArmKRev : z ∈
          ((T.leftToAttach k).reverse.takeUntil v (by
            simpa [SimpleGraph.Walk.support_reverse] using hv)).reverse.support := by
        simpa [Tripod.attachToLeft,
          SimpleGraph.Walk.support_reverse] using hzArmK
      have hzv := Walk.IsPath.eq_of_mem_takeUntil_and_reverse_takeUntil
        (T.leftToAttach_isPath k) hv
        (by simpa [SimpleGraph.Walk.support_reverse] using hv)
        hzPrefixK hzArmKRev
      exact hzOne.2.2 hzv

theorem Tripod.allNilFirstToLastTransitionRims_internal_disjoint
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
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim i) ∨ u = T.right)
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
          (Tripod.allNilFirstToLastTransitionRim P T hgraph
            hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
            hu hv transition r))
        (Walk.InternalVertices
          (Tripod.allNilFirstToLastTransitionRim P T hgraph
            hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
            hu hv transition s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact Tripod.allNilFirstToLastTransitionRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hright_contact hv hv_internal
      transition htransition_clean
  · exact Tripod.allNilFirstToLastTransitionRim_zero_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hright_contact hv
      transition htransition_outside htransition_clean
  · exact (Tripod.allNilFirstToLastTransitionRim_zero_one_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hright_contact hv hv_internal
      transition htransition_clean).symm
  · exact False.elim (hrs rfl)
  · exact Tripod.allNilFirstToLastTransitionRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hv hv_ne_attach hv_internal
      transition
  · exact (Tripod.allNilFirstToLastTransitionRim_zero_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hright_contact hv
      transition htransition_outside htransition_clean).symm
  · exact (Tripod.allNilFirstToLastTransitionRim_one_two_internal_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_j_nil hleg_k_nil
      hi hj hk hij_order hjk_order hpath_contacts hu hv hv_ne_attach hv_internal
      transition).symm
  · exact False.elim (hrs rfl)

theorem Tripod.allNilFirstToLastTransitionLegs_meet_rims_only_at_attach
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
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    forall r s : Fin 3, forall z : V,
      z ∈ (Tripod.allNilCleanBridgeLeg P T hleg_i_nil hleg_k_nil
        hi hk q r).support ->
      z ∈ (Tripod.allNilFirstToLastTransitionRim P T hgraph
        hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk hij_order hjk_order
        hu hv transition s).support ->
      z = Tripod.allNilCleanBridgeAttach T i k r := by
  intro r s z hzLeg hzRim
  fin_cases r <;> fin_cases s
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToLastTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArmI | hzTransition
    · have hzi : z = T.boundary i := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.pathTailToStart_support_inter_segmentBetween_subset_left
            hi hj (Nat.le_of_lt hij_order) hzTail hzSegment
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArmI
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim i hzOld))
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail))
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzArmJ | hzArmK
    · have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzArmJ))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.attachToLeft_support_subset_rim j hzArmJ))
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzArmK
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim k hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hzi] using T.leftToAttach_support_subset_rim k hzOld))
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzSegment | hzArmK
    · exact False.elim (Set.disjoint_left.mp
        (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
          hi hj hk hij_order (Nat.le_of_lt hjk_order)) hzTail
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment))
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmK
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim k hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hzi] using T.attachToLeft_support_subset_rim k hzOld))
  · rcases Tripod.allNilFirstToLastTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArmI | hzTransition
    · exact False.elim ((hq_outside z hzLeg).2
        (P.pathSegmentBetween_support_subset_pathSet hi hj
          (Nat.le_of_lt hij_order) z hzSegment))
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToRight i) (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hu) hzArmI
      have hzLeft := hq_clean z hzLeg
        (T.rim_mem_vertexSet (T.attachToRight_support_subset_rim i hzOld))
      exact False.elim (T.left_not_mem_attachToRight i
        (by simpa [hzLeft] using hzOld))
    · exact False.elim (htransition_q z hzTransition hzLeg)
  · rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzArmJ | hzArmK
    · have hzLeft := hq_clean z hzLeg
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzArmJ))
      simpa [Tripod.allNilCleanBridgeAttach] using hzLeft
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzArmK
      have hzLeft := hq_clean z hzLeg
        (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim k hzOld))
      simpa [Tripod.allNilCleanBridgeAttach] using hzLeft
  · rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzSegment | hzArmK
    · exact False.elim ((hq_outside z hzLeg).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegment))
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmK
      have hzLeft := hq_clean z hzLeg
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim k hzOld))
      have hleftNotArm : T.left ∉
          ((T.attachToLeft k).takeUntil v (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv)).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.attachToLeft_isPath k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv)
            hv_internal.2.1.symm
      exact False.elim (hleftNotArm (by simpa [hzLeft] using hzArmK))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToLastTransitionRim_zero_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with
      hzSegment | hzArmI | hzTransition
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
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToLastTransitionRim_one_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzArmJ | hzArmK
    · have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim j hzArmJ))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.attachToLeft_support_subset_rim j hzArmJ))
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach k) hv hzArmK
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim k hzOld))
      have hza : z = T.attach k := hzk.trans
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil)
      have hattachNotPrefix :
          T.attach k ∉ ((T.leftToAttach k).takeUntil v hv).support :=
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          (T.leftToAttach_isPath k) hv hv_ne_attach.symm
      exact False.elim (hattachNotPrefix (by simpa [hza] using hzArmK))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilCleanBridgeLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases Tripod.allNilFirstToLastTransitionRim_two_support_cases
        P T hgraph hleg_i_nil hleg_j_nil hleg_k_nil hi hj hk
        hij_order hjk_order hu hv transition hzRim with hzSegment | hzArmK
    · have hzk : z = T.boundary k := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.segmentBetween_support_inter_pathTailToEnd_subset_right
            hj hk (Nat.le_of_lt hjk_order) hzSegment hzTail
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.attachToLeft k) (by
            simpa [Tripod.attachToLeft,
              SimpleGraph.Walk.support_reverse] using hv) hzArmK
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim k hzOld))
      simpa [Tripod.allNilCleanBridgeAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk

theorem Tripod.liftAllNilOfFirstToLastArmTransition
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
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim i) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  have hleft_ne_right : T.attach j ≠ v := by
    intro hjv
    exact T.attach_not_mem_rim_of_ne hjk
      (by simpa [hjv] using hv_internal.1)
  refine ⟨{
    left := T.attach j
    right := v
    left_ne_right := hleft_ne_right
    rim := Tripod.allNilFirstToLastTransitionRim P T hgraph
      (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath := Tripod.allNilFirstToLastTransitionRim_isPath
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts hu hv hv_internal
      transition htransition_path htransition_outside htransition_clean
    attach := Tripod.allNilCleanBridgeAttach T i k
    attach_mem_rim := Tripod.allNilFirstToLastTransitionAttach_mem_rim
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hu hv hv_ne_attach hv_internal transition
    boundary := P.boundaryTriple a
    boundary_mem := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_mem_of_leftArc ha
      · exact P.boundaryTriple_mem_of_rightArc ha
    boundary_injective := by
      rcases ha with ha | ha
      · exact P.boundaryTriple_injective_of_leftArc ha
      · exact P.boundaryTriple_injective_of_rightArc ha
    leg := Tripod.allNilCleanBridgeLeg P T
      (hlegs_nil i) (hlegs_nil k) hi hk q
    leg_isPath := Tripod.allNilCleanBridgeLeg_isPath P T
      (hlegs_nil i) (hlegs_nil k) hi hk q hq_path
    rim_internals_disjoint :=
      Tripod.allNilFirstToLastTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact hv
        hv_ne_attach hv_internal transition htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      Tripod.allNilCleanBridgeLegs_pairwise_disjoint
        P T (j := j) (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order q hq_outside
    legs_meet_rims_only_at_attach :=
      Tripod.allNilFirstToLastTransitionLegs_meet_rims_only_at_attach
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts q hq_outside hq_clean
        hu hv hv_ne_attach hv_internal transition htransition_outside htransition_q
  }⟩

/-- Cut-path-reversed counterpart of the first-to-last exchange. -/
theorem Tripod.liftAllNilOfLastToFirstArmTransition
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
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_ne_attach : v ≠ T.attach i)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> False) :
    Nonempty S.Tripod := by
  apply Tripod.liftAllNilOfFirstToLastArmTransition
    (i := k) (j := j) (k := i) (a := a) (u := u) (v := v)
    (q := q) (transition := transition)
    P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact
      (GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order
  · exact
      (GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order
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
  · exact Or.inl hu_internal
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
