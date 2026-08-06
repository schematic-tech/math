import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.WalkTransport
import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle

/-!
All-nil clean-transition constructions based at the middle ordered rim.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/- Checked median-rim transition constructor. -/

/-- Rebuilt rims when both clean-transition contacts lie on the strict arms
of the median ordered old rim. -/
def Tripod.allNilSameMiddleTransitionRim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v) :
    Fin 3 -> S.graph.Walk T.right (T.attach j)
  | 0 =>
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 0).copy rfl
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)
  | 1 =>
      ((((T.rightToAttach j).takeUntil u hu).mapLe hgraph).append
        transition).append
          (((T.leftToAttach j).dropUntil v hv).mapLe hgraph)
  | 2 =>
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 2).copy rfl
          ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)

/-- Simplicity of the median-arm transition rims. -/
theorem Tripod.allNilSameMiddleTransitionRim_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.allNilSameMiddleTransitionRim] using
      (SimpleGraph.Walk.isPath_copy
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 0) rfl
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)).mpr
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
            P T hgraph hij hik hjk hi hj hk
            hij_order hjk_order hpath_contacts 0)
  · let rightPart : S.graph.Walk T.right u :=
      ((T.rightToAttach j).takeUntil u hu).mapLe hgraph
    let leftPart : S.graph.Walk v (T.attach j) :=
      ((T.leftToAttach j).dropUntil v hv).mapLe hgraph
    have hright_path : rightPart.IsPath := by
      simpa [rightPart] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.rightToAttach_isPath j).takeUntil hu)
    have hleft_path : leftPart.IsPath := by
      simpa [leftPart] using
        SimpleGraph.Walk.IsPath.mapLe hgraph
          ((T.leftToAttach_isPath j).dropUntil hv)
    have hfirst_path : (rightPart.append transition).IsPath := by
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hright_path htransition_path ?_
      intro z hzRight hzTransition
      have hzRightOld : z ∈ (T.rightToAttach j).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach j) hu (by
            simpa [rightPart, SimpleGraph.Walk.support_mapLe_eq_support]
              using hzRight)
      rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim j hzRightOld)) with hzu | hzv
      · exact hzu
      · exact False.elim (hv_ne_attach
          (T.leftToAttach_support_inter_rightToAttach_eq_attach j hv
            (by simpa [hzv] using hzRightOld)))
    change ((rightPart.append transition).append leftPart).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hfirst_path hleft_path ?_
    intro z hzFirst hzLeft
    have hzLeftOld : z ∈ (T.leftToAttach j).support :=
      SimpleGraph.Walk.support_dropUntil_subset
        (T.leftToAttach j) hv (by
          simpa [leftPart, SimpleGraph.Walk.support_mapLe_eq_support]
            using hzLeft)
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
      hzRight | hzTransition
    · have hzRightPrefix :
          z ∈ ((T.rightToAttach j).takeUntil u hu).support := by
        simpa [rightPart, SimpleGraph.Walk.support_mapLe_eq_support] using hzRight
      exact False.elim
        (Set.disjoint_left.mp
          (T.rightToAttach_takeUntil_support_disjoint_leftToAttach
            hu hu_ne_attach) hzRightPrefix hzLeftOld)
    · rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzLeftOld)) with hzu | hzv
      · exact False.elim (hu_ne_attach
          (T.leftToAttach_support_inter_rightToAttach_eq_attach j
            (by simpa [hzu] using hzLeftOld) hu))
      · exact hzv
  · simpa [Tripod.allNilSameMiddleTransitionRim] using
      (SimpleGraph.Walk.isPath_copy
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order 2) rfl
        ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil)).mpr
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
            P T hgraph hij hik hjk hi hj hk
            hij_order hjk_order hpath_contacts 2)

def Tripod.allNilSameMiddleTransitionAttach
    {H : GeneralSociety V} (T : H.Tripod)
    (i k : Fin 3) (v : V) : Fin 3 -> V
  | 0 => T.attach i
  | 1 => v
  | 2 => T.attach k

def Tripod.allNilSameMiddleTransitionLeg
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a v : V}
    (hv : v ∈ (T.leftToAttach j).support)
    (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v r)
        (P.boundaryTriple a r)
  | 0 =>
      (P.pathTailToStart hi).copy
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl
  | 1 =>
      ((((T.leftToAttach j).takeUntil v hv).reverse).mapLe hgraph).append q
  | 2 =>
      (P.pathTailToEnd hk).copy
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl

theorem Tripod.allNilSameMiddleTransitionAttach_mem_rim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k)
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v) :
    forall r : Fin 3,
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v r ∈
        Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition r) := by
  intro r
  fin_cases r
  · refine ⟨?_, (T.attach_mem_rim i).2.2, ?_⟩
    · rw [Tripod.allNilSameMiddleTransitionRim.eq_def,
        SimpleGraph.Walk.support_copy]
      rw [Tripod.outerNilMiddleNonNilCommonLeftRim,
        Tripod.rightToBoundaryViaLegTail,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      simp [Tripod.allNilSameMiddleTransitionAttach,
        SimpleGraph.Walk.support_mapLe_eq_support]
    · exact T.attach_ne_of_ne hij
  · refine ⟨?_, ?_, hv_ne_attach⟩
    · rw [Tripod.allNilSameMiddleTransitionRim.eq_def,
        SimpleGraph.Walk.mem_support_append_iff]
      right
      simp [Tripod.allNilSameMiddleTransitionAttach]
    · rcases hleft_contact with hvInternal | hvLeft
      · exact hvInternal.2.2
      · simpa [hvLeft] using T.left_ne_right
  · refine ⟨?_, (T.attach_mem_rim k).2.2, ?_⟩
    · rw [Tripod.allNilSameMiddleTransitionRim.eq_def,
        SimpleGraph.Walk.support_copy]
      rw [Tripod.outerNilMiddleNonNilCommonLeftRim,
        Tripod.rightToBoundaryViaLegTail,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      simp [Tripod.allNilSameMiddleTransitionAttach,
        SimpleGraph.Walk.support_mapLe_eq_support]
    · exact T.attach_ne_of_ne (fun h => hjk h.symm)

theorem Tripod.allNilSameMiddleTransitionLeg_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a v : V}
    (hv : v ∈ (T.leftToAttach j).support)
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
        P T hgraph hleg_i_nil hleg_k_nil hi hk hv q r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.allNilSameMiddleTransitionLeg] using
      (SimpleGraph.Walk.isPath_copy (P.pathTailToStart hi)
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl).mpr
          (P.pathTailToStart_isPath hi)
  · refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.leftToAttach_isPath j).takeUntil hv).reverse)
      hq_path ?_
    intro z hzArm hzq
    apply hq_clean z hzq
    apply T.rim_mem_vertexSet
    apply T.leftToAttach_support_subset_rim j
    apply SimpleGraph.Walk.support_takeUntil_subset
      (T.leftToAttach j) hv
    exact Walk.mem_support_of_mem_reverse_mapLe hgraph
      ((T.leftToAttach j).takeUntil v hv) hzArm
  · simpa [Tripod.allNilSameMiddleTransitionLeg] using
      (SimpleGraph.Walk.isPath_copy (P.pathTailToEnd hk)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
          (P.pathTailToEnd_isPath hk)

theorem Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
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
    {a v : V}
    (hv : v ∈ (T.leftToAttach j).support)
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
            P T hgraph hleg_i_nil hleg_k_nil hi hk hv q r).support}
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
            P T hgraph hleg_i_nil hleg_k_nil hi hk hv q s).support} := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · rw [Set.disjoint_left]
    intro z hzStart hzMiddle
    have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzStart
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzMiddle with
      hzArm | hzq
    · have hzArmOld : z ∈ (T.leftToAttach j).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach j) hv (by
            exact Walk.mem_support_of_mem_reverse_mapLe hgraph
              ((T.leftToAttach j).takeUntil v hv) hzArm)
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet
          (T.leftToAttach_support_subset_rim j hzArmOld))
      exact T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzArmOld)
    · exact (hq_outside z hzq).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail)
  · simpa [Tripod.allNilSameMiddleTransitionLeg] using
      P.pathTailToStart_support_disjoint_pathTailToEnd hi hk
        (lt_trans hij_order hjk_order)
  · exact
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order hpath_contacts hv q hq_outside 0 1
          (by decide)).symm
  · exact False.elim (hrs rfl)
  · rw [Set.disjoint_left]
    intro z hzMiddle hzEnd
    have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzEnd
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzMiddle with
      hzArm | hzq
    · have hzArmOld : z ∈ (T.leftToAttach j).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.leftToAttach j) hv (by
            exact Walk.mem_support_of_mem_reverse_mapLe hgraph
              ((T.leftToAttach j).takeUntil v hv) hzArm)
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet
          (T.leftToAttach_support_subset_rim j hzArmOld))
      exact T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzArmOld)
    · exact (hq_outside z hzq).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail)
  · simpa [Tripod.allNilSameMiddleTransitionLeg] using
      (P.pathTailToStart_support_disjoint_pathTailToEnd hi hk
        (lt_trans hij_order hjk_order)).symm
  · exact
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
        hij_order hjk_order hpath_contacts hv q hq_outside 1 2
          (by decide)).symm
  · exact False.elim (hrs rfl)

theorem Tripod.allNilSameMiddleTransitionRim_zero_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition 0).support) :
    z ∈ (T.rim i).support ∨
      z ∈ (P.pathSegmentBetween hi hj
        (Nat.le_of_lt hij_order)).support := by
  have hzOld : z ∈
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 0).support := by
    simpa [Tripod.allNilSameMiddleTransitionRim,
      SimpleGraph.Walk.support_copy] using hz
  rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
      (by simpa [Tripod.outerNilMiddleNonNilCommonLeftRim] using hzOld) with
    hzArm | hzLeg | hzSegment
  · exact Or.inl (T.rightToAttach_support_subset_rim i hzArm)
  · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_i_nil
    have hza : z = T.attach i := by simpa [hsupport] using hzLeg
    exact Or.inl (by simpa [hza] using (T.attach_mem_rim i).1)
  · exact Or.inr hzSegment

theorem Tripod.allNilSameMiddleTransitionRim_one_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition 1).support) :
    z ∈ ((T.rightToAttach j).takeUntil u hu).support ∨
      z ∈ transition.support ∨
        z ∈ ((T.leftToAttach j).dropUntil v hv).support := by
  rw [Tripod.allNilSameMiddleTransitionRim,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzFirst | hzLeft
  · rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
    rcases hzFirst with hzRight | hzTransition
    · exact Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzRight)
    · exact Or.inr (Or.inl hzTransition)
  · exact Or.inr (Or.inr (by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzLeft))

theorem Tripod.allNilSameMiddleTransitionRim_two_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition 2).support) :
    z ∈ (T.rim k).support ∨
      z ∈ (P.pathSegmentBetween hj hk
        (Nat.le_of_lt hjk_order)).support := by
  have hzOld : z ∈
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 2).support := by
    simpa [Tripod.allNilSameMiddleTransitionRim,
      SimpleGraph.Walk.support_copy] using hz
  rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
      (by simpa [Tripod.outerNilMiddleNonNilCommonLeftRim] using hzOld) with
    hzArm | hzLeg | hzSegmentRev
  · exact Or.inl (T.rightToAttach_support_subset_rim k hzArm)
  · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
    have hza : z = T.attach k := by simpa [hsupport] using hzLeg
    exact Or.inl (by simpa [hza] using (T.attach_mem_rim k).1)
  · exact Or.inr (by
      simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev)

theorem Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition 0).support) :
    z ∈ (T.rightToAttach i).support ∨
      z ∈ (T.leg i).support ∨
        z ∈ (P.pathSegmentBetween hi hj
          (Nat.le_of_lt hij_order)).support := by
  have hzOld : z ∈
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 0).support := by
    simpa [Tripod.allNilSameMiddleTransitionRim,
      SimpleGraph.Walk.support_copy] using hz
  exact T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
    (by simpa [Tripod.outerNilMiddleNonNilCommonLeftRim] using hzOld)

theorem Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach j).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition 2).support) :
    z ∈ (T.rightToAttach k).support ∨
      z ∈ (T.leg k).support ∨
        z ∈ (P.pathSegmentBetween hj hk
          (Nat.le_of_lt hjk_order)).reverse.support := by
  have hzOld : z ∈
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 2).support := by
    simpa [Tripod.allNilSameMiddleTransitionRim,
      SimpleGraph.Walk.support_copy] using hz
  exact T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
    (by simpa [Tripod.outerNilMiddleNonNilCommonLeftRim] using hzOld)

theorem Tripod.allNilSameMiddleTransitionRim_zero_one_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_nil : (T.leg j).Nil)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition 0))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition 1)) := by
  rw [Set.disjoint_left]
  intro z hzZero hzOne
  rcases
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition hzZero.1 with
    hzRightI | hzLegI | hzSegment
  · rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzOne.1 with
      hzRightJ | hzTransition | hzLeftJ
    · have hzRightJOld : z ∈ (T.rightToAttach j).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach j) hu hzRightJ
      exact hzZero.2.1
        (T.rightToAttach_support_inter_rim_eq_right
          (fun h => hij h.symm) hzRightJOld
            (T.rightToAttach_support_subset_rim i hzRightI))
    · rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim i hzRightI)) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            (T.rim_support_internal_of_not_endpoint
              (T.rightToAttach_support_subset_rim i hzRightI)
              ⟨by simpa [hzu] using huInternal.2.1,
                by simpa [hzu] using huInternal.2.2⟩)
            (by simpa [hzu] using huInternal)
        · exact hzOne.2.1 (hzu.trans huRight)
      · rcases hleft_contact with hvInternal | hvLeft
        · exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            (T.rim_support_internal_of_not_endpoint
              (T.rightToAttach_support_subset_rim i hzRightI)
              ⟨by simpa [hzv] using hvInternal.2.1,
                by simpa [hzv] using hvInternal.2.2⟩)
            (by simpa [hzv] using hvInternal)
        · exact T.left_not_mem_rightToAttach i
            (by simpa [hzv, hvLeft] using hzRightI)
    · have hzLeftJOld : z ∈ (T.leftToAttach j).support :=
        SimpleGraph.Walk.support_dropUntil_subset
          (T.leftToAttach j) hv hzLeftJ
      have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left
          (fun h => hij h.symm) hzLeftJOld
            (T.rightToAttach_support_subset_rim i hzRightI)
      exact T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzRightI)
  · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_i_nil
    have hza : z = T.attach i := by simpa [hsupport] using hzLegI
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzOne.1 with
      hzRightJ | hzTransition | hzLeftJ
    · exact T.attach_not_mem_rim_of_ne hij
        (by simpa [hza] using
          (T.rightToAttach_support_subset_rim j
            (SimpleGraph.Walk.support_takeUntil_subset
              (T.rightToAttach j) hu hzRightJ)))
    · rcases htransition_clean z hzTransition
          (by simpa [hza] using T.attach_mem_vertexSet i) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · have haiu : T.attach i = u := hza.symm.trans hzu
          exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            (T.attach_mem_rim i) (by rw [haiu]; exact huInternal)
        · exact hzOne.2.1 (hzu.trans huRight)
      · rcases hleft_contact with hvInternal | hvLeft
        · have haiv : T.attach i = v := hza.symm.trans hzv
          exact Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
            (T.attach_mem_rim i) (by rw [haiv]; exact hvInternal)
        · exact (T.attach_mem_rim i).2.1
            (hza.symm.trans (hzv.trans hvLeft))
    · exact T.attach_not_mem_rim_of_ne hij
        (by simpa [hza] using
          (T.leftToAttach_support_subset_rim j
            (SimpleGraph.Walk.support_dropUntil_subset
              (T.leftToAttach j) hv hzLeftJ)))
  · rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzOne.1 with
      hzRightJ | hzTransition | hzLeftJ
    · have hzRightJOld : z ∈ (T.rightToAttach j).support :=
        SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach j) hu hzRightJ
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim j hzRightJOld)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hij
          (by simpa [hzi] using T.rightToAttach_support_subset_rim j hzRightJOld)
      · exact hzZero.2.2
          (hzj.trans
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
    · exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hi hj
          (Nat.le_of_lt hij_order) z hzSegment)
    · have hzLeftJOld : z ∈ (T.leftToAttach j).support :=
        SimpleGraph.Walk.support_dropUntil_subset
          (T.leftToAttach j) hv hzLeftJ
      rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
          T hij hik hjk hi hj hij_order hjk_order hpath_contacts
          hzSegment
          (T.rim_mem_vertexSet
            (T.leftToAttach_support_subset_rim j hzLeftJOld)) with hzi | hzj
      · exact T.boundary_not_mem_rim_of_ne_index hij
          (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzLeftJOld)
      · exact hzZero.2.2
          (hzj.trans
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))

theorem Tripod.allNilSameMiddleTransitionRim_one_two_internal_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Disjoint
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition 1))
      (Walk.InternalVertices
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition 2)) := by
  rw [Set.disjoint_left]
  intro z hzOne hzTwo
  rcases
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition hzOne.1 with
    hzRightJ | hzTransition | hzLeftJ
  · have hzRightJOld : z ∈ (T.rightToAttach j).support :=
      SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach j) hu hzRightJ
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzRightK | hzLegK | hzSegmentRev
    · exact hzOne.2.1
        (T.rightToAttach_support_inter_rim_eq_right hjk hzRightJOld
          (T.rightToAttach_support_subset_rim k hzRightK))
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
      have hza : z = T.attach k := by simpa [hsupport] using hzLegK
      exact T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
        (by simpa [hza] using T.rightToAttach_support_subset_rim j hzRightJOld)
    · have hzSegment : z ∈
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
      rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegment
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim j hzRightJOld)) with
        hzj | hzk
      · exact hzOne.2.2
          (hzj.trans
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := j) (fun h => hjk h.symm)
          (by simpa [hzk] using T.rightToAttach_support_subset_rim j hzRightJOld)
  · rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzRightK | hzLegK | hzSegmentRev
    · rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim k hzRightK)) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · exact Set.disjoint_left.mp (T.rim_internals_disjoint j k hjk)
            (by simpa [hzu] using huInternal)
            (T.rim_support_internal_of_not_endpoint
              (T.rightToAttach_support_subset_rim k hzRightK)
              ⟨by simpa [hzu] using huInternal.2.1,
                by simpa [hzu] using huInternal.2.2⟩)
        · exact hzOne.2.1 (hzu.trans huRight)
      · rcases hleft_contact with hvInternal | hvLeft
        · exact Set.disjoint_left.mp (T.rim_internals_disjoint j k hjk)
            (by simpa [hzv] using hvInternal)
            (T.rim_support_internal_of_not_endpoint
              (T.rightToAttach_support_subset_rim k hzRightK)
              ⟨by simpa [hzv] using hvInternal.2.1,
                by simpa [hzv] using hvInternal.2.2⟩)
        · exact T.left_not_mem_rightToAttach k
            (by simpa [hzv, hvLeft] using hzRightK)
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
      have hza : z = T.attach k := by simpa [hsupport] using hzLegK
      rcases htransition_clean z hzTransition
          (by simpa [hza] using T.attach_mem_vertexSet k) with hzu | hzv
      · rcases hright_contact with huInternal | huRight
        · have hku : T.attach k = u := hza.symm.trans hzu
          exact Set.disjoint_left.mp (T.rim_internals_disjoint j k hjk)
            huInternal (by simpa only [hku] using T.attach_mem_rim k)
        · exact hzOne.2.1 (hzu.trans huRight)
      · rcases hleft_contact with hvInternal | hvLeft
        · have hkv : T.attach k = v := hza.symm.trans hzv
          exact Set.disjoint_left.mp (T.rim_internals_disjoint j k hjk)
            hvInternal (by simpa only [hkv] using T.attach_mem_rim k)
        · exact (T.attach_mem_rim k).2.1
            (hza.symm.trans (hzv.trans hvLeft))
    · have hzSegment : z ∈
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
      exact (htransition_outside z hzTransition).2
        (P.pathSegmentBetween_support_subset_pathSet hj hk
          (Nat.le_of_lt hjk_order) z hzSegment)
  · have hzLeftJOld : z ∈ (T.leftToAttach j).support :=
      SimpleGraph.Walk.support_dropUntil_subset
        (T.leftToAttach j) hv hzLeftJ
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzTwo.1 with
      hzRightK | hzLegK | hzSegmentRev
    · have hzLeft : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJOld
          (T.rightToAttach_support_subset_rim k hzRightK)
      exact T.left_not_mem_rightToAttach k (by simpa [hzLeft] using hzRightK)
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
      have hza : z = T.attach k := by simpa [hsupport] using hzLegK
      exact T.attach_not_mem_rim_of_ne (fun h => hjk h.symm)
        (by simpa [hza] using T.leftToAttach_support_subset_rim j hzLeftJOld)
    · have hzSegment : z ∈
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
      rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegment
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJOld)) with
        hzj | hzk
      · exact hzOne.2.2
          (hzj.trans
            ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
      · exact T.boundary_not_mem_rim_of_ne_index
          (i := k) (s := j) (fun h => hjk h.symm)
          (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzLeftJOld)

theorem Tripod.allNilSameMiddleTransitionRims_internal_disjoint
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition r))
        (Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition s)) := by
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · exact
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_one_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean
  · simpa [Tripod.allNilSameMiddleTransitionRim,
        Walk.InternalVertices, SimpleGraph.Walk.support_copy,
        (T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil] using
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts
  · exact
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_one_internal_disjoint
        P T hgraph hij hik hjk hleg_i_nil hleg_j_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean).symm
  · exact False.elim (hrs rfl)
  · exact
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_two_internal_disjoint
        P T hgraph hij hik hjk hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean
  · simpa [Tripod.allNilSameMiddleTransitionRim,
        Walk.InternalVertices, SimpleGraph.Walk.support_copy,
        (T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil] using
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_zero_two_internal_disjoint
        P T hgraph hij hik hjk hi hj hk
        hij_order hjk_order hpath_contacts).symm
  · exact
      (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_two_internal_disjoint
        P T hgraph hij hik hjk hleg_j_nil hleg_k_nil
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean).symm
  · exact False.elim (hrs rfl)

theorem Tripod.allNilSameMiddleTransitionLegs_meet_rims_only_at_attach
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
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = v) :
    forall r s : Fin 3, forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
          P T hgraph hleg_i_nil hleg_k_nil hi hk hv q r).support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition s).support ->
      z = GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v r := by
  intro r s z hzLeg hzRim
  fin_cases r <;> fin_cases s
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzArm | hzOldLeg | hzSegment
    · have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm))
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_i_nil
      have hza : z = T.attach i := by simpa [hsupport] using hzOldLeg
      simpa [Tripod.allNilSameMiddleTransitionAttach] using hza
    · have hzi : z = T.boundary i := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.pathTailToStart_support_inter_segmentBetween_subset_left
            hi hj (Nat.le_of_lt hij_order) hzTail hzSegment
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using hzi
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzRight | hzTransition | hzLeft
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach j) hu hzRight
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.rightToAttach_support_subset_rim j hzOld))
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToStart_support_subset_pathSet hi z hzTail))
    · have hzOld := SimpleGraph.Walk.support_dropUntil_subset
        (T.leftToAttach j) hv hzLeft
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim j hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzOld))
  · have hzTail : z ∈ (P.pathTailToStart hi).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzArm | hzOldLeg | hzSegmentRev
    · have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index hik
        (by simpa [hzi] using T.rightToAttach_support_subset_rim k hzArm))
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
      have hza : z = T.attach k := by simpa [hsupport] using hzOldLeg
      have hzi := P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
        (by simpa [hza] using T.attach_mem_vertexSet k)
      have hai_ak : T.attach i = T.attach k :=
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil).symm.trans
          (hzi.symm.trans hza)
      exact False.elim (T.attach_ne_of_ne hik hai_ak)
    · have hzSegment : z ∈
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
      exact False.elim (Set.disjoint_left.mp
        (P.pathTailToStart_support_disjoint_segmentBetween_of_lt
          hi hj hk hij_order (Nat.le_of_lt hjk_order)) hzTail
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment))
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzMiddleArm | hzq
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support := by
        exact Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMiddleArm
      have hzLeftJ := SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach j) hv hzPrefix
      rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition hzRim with
        hzArm | hzOldLeg | hzSegment
      · have hzLeft := T.leftToAttach_support_inter_rim_eq_left
          (fun h => hij h.symm) hzLeftJ
            (T.rightToAttach_support_subset_rim i hzArm)
        exact False.elim (T.left_not_mem_rightToAttach i
          (by simpa [hzLeft] using hzArm))
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_i_nil
        have hza : z = T.attach i := by simpa [hsupport] using hzOldLeg
        exact False.elim (T.attach_not_mem_rim_of_ne
          (i := i) (j := j) hij (by simpa [hza] using
            T.leftToAttach_support_subset_rim j hzLeftJ))
      · rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order hpath_contacts
            hzSegment
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJ)) with hzi | hzj
        · exact False.elim (T.boundary_not_mem_rim_of_ne_index hij
            (by simpa [hzi] using T.leftToAttach_support_subset_rim j hzLeftJ))
        · have hattachNotPrefix :
              T.attach j ∉ ((T.leftToAttach j).takeUntil v hv).support :=
            SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              (T.leftToAttach_isPath j) hv
              (by simpa [ne_eq] using hv_ne_attach.symm)
          exact False.elim (hattachNotPrefix (by simpa [hzj,
            (T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil] using hzPrefix))
    · rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition hzRim with
        hzArm | hzOldLeg | hzSegment
      · have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm))
        exact False.elim (T.left_not_mem_rightToAttach i
          (by simpa [hzLeft] using hzArm))
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_i_nil
        have hza : z = T.attach i := by simpa [hsupport] using hzOldLeg
        have hzLeft := hq_clean z hzq (by simpa [hza] using T.attach_mem_vertexSet i)
        exact False.elim ((T.attach_mem_rim i).2.1 (by simpa [hza] using hzLeft))
      · exact False.elim ((hq_outside z hzq).2
          (P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzSegment))
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzMiddleArm | hzq
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support := by
        exact Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMiddleArm
      have hzLeftJ := SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach j) hv hzPrefix
      rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition hzRim with
        hzRight | hzTransition | hzLeftSuffix
      · exact False.elim (Set.disjoint_left.mp
          (T.leftToAttach_takeUntil_support_disjoint_rightToAttach
            hv hv_ne_attach) hzPrefix
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach j) hu hzRight))
      · rcases htransition_clean z hzTransition
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJ)) with hzu | hzv
        · exact False.elim (hu_ne_attach
            (T.leftToAttach_support_inter_rightToAttach_eq_attach j
              (by simpa [hzu] using hzLeftJ) hu))
        · simpa [Tripod.allNilSameMiddleTransitionAttach] using hzv
      · have hzSuffix := SimpleGraph.Walk.support_dropUntil_subset
          (T.leftToAttach j) hv hzLeftSuffix
        have hzv : z = v :=
          Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
            (T.leftToAttach_isPath j) hv hzPrefix hzLeftSuffix
        simpa [Tripod.allNilSameMiddleTransitionAttach] using hzv
    · rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition hzRim with
        hzRight | hzTransition | hzLeftSuffix
      · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
          (T.rightToAttach j) hu hzRight
        have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzOld))
        exact False.elim (T.left_not_mem_rightToAttach j
          (by simpa [hzLeft] using hzOld))
      · simpa [Tripod.allNilSameMiddleTransitionAttach] using
          htransition_q z hzTransition hzq
      · have hzOld := SimpleGraph.Walk.support_dropUntil_subset
          (T.leftToAttach j) hv hzLeftSuffix
        have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim j hzOld))
        rcases hleft_contact with hvInternal | hvLeft
        · have hleftNotSuffix :
              T.left ∉ ((T.leftToAttach j).dropUntil v hv).support :=
            Walk.IsPath.start_not_mem_dropUntil_support_of_ne
              (T.leftToAttach_isPath j) hv hvInternal.2.1
          exact False.elim
            (hleftNotSuffix (by simpa [hzLeft] using hzLeftSuffix))
        · simpa [Tripod.allNilSameMiddleTransitionAttach, hvLeft] using hzLeft
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzLeg with
      hzMiddleArm | hzq
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support := by
        exact Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMiddleArm
      have hzLeftJ := SimpleGraph.Walk.support_takeUntil_subset
        (T.leftToAttach j) hv hzPrefix
      rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition hzRim with
        hzArm | hzOldLeg | hzSegmentRev
      · have hzLeft := T.leftToAttach_support_inter_rim_eq_left hjk hzLeftJ
          (T.rightToAttach_support_subset_rim k hzArm)
        exact False.elim (T.left_not_mem_rightToAttach k
          (by simpa [hzLeft] using hzArm))
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
        have hza : z = T.attach k := by simpa [hsupport] using hzOldLeg
        exact False.elim (T.attach_not_mem_rim_of_ne
          (i := k) (j := j) (fun h => hjk h.symm) (by simpa [hza] using
            (T.leftToAttach_support_subset_rim j hzLeftJ)))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        rcases P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegment
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJ)) with hzj | hzk
        · have hattachNotPrefix :
              T.attach j ∉ ((T.leftToAttach j).takeUntil v hv).support :=
            SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              (T.leftToAttach_isPath j) hv
              (by simpa [ne_eq] using hv_ne_attach.symm)
          exact False.elim (hattachNotPrefix (by simpa [hzj,
            (T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil] using hzPrefix))
        · exact False.elim (T.boundary_not_mem_rim_of_ne_index
            (i := k) (s := j) (fun h => hjk h.symm)
            (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzLeftJ))
    · rcases
          GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition hzRim with
        hzArm | hzOldLeg | hzSegmentRev
      · have hzLeft := hq_clean z hzq
          (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArm))
        exact False.elim (T.left_not_mem_rightToAttach k
          (by simpa [hzLeft] using hzArm))
      · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
        have hza : z = T.attach k := by simpa [hsupport] using hzOldLeg
        have hzLeft := hq_clean z hzq (by simpa [hza] using T.attach_mem_vertexSet k)
        exact False.elim ((T.attach_mem_rim k).2.1 (by simpa [hza] using hzLeft))
      · have hzSegment : z ∈
            (P.pathSegmentBetween hj hk
              (Nat.le_of_lt hjk_order)).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
        exact False.elim ((hq_outside z hzq).2
          (P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzSegment))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_zero_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzArm | hzOldLeg | hzSegment
    · have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim i hzArm))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := i) (fun h => hik h.symm)
        (by simpa [hzk] using T.rightToAttach_support_subset_rim i hzArm))
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_i_nil
      have hza : z = T.attach i := by simpa [hsupport] using hzOldLeg
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (by simpa [hza] using T.attach_mem_vertexSet i)
      have hai_ak : T.attach i = T.attach k :=
        hza.symm.trans
          (hzk.trans ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil))
      exact False.elim (T.attach_ne_of_ne hik hai_ak)
    · exact False.elim (Set.disjoint_left.mp
        (P.segmentBetween_support_disjoint_pathTailToEnd_of_lt
          hi hj hk (Nat.le_of_lt hij_order) hjk_order)
          (by simpa [GMIX24CutPath.pathSegmentBetween] using hzSegment) hzTail)
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzRight | hzTransition | hzLeft
    · have hzOld := SimpleGraph.Walk.support_takeUntil_subset
        (T.rightToAttach j) hu hzRight
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim j hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.rightToAttach_support_subset_rim j hzOld))
    · exact False.elim ((htransition_outside z hzTransition).2
        (P.pathTailToEnd_support_subset_pathSet hk z hzTail))
    · have hzOld := SimpleGraph.Walk.support_dropUntil_subset
        (T.leftToAttach j) hv hzLeft
      have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.leftToAttach_support_subset_rim j hzOld))
      exact False.elim (T.boundary_not_mem_rim_of_ne_index
        (i := k) (s := j) (fun h => hjk h.symm)
        (by simpa [hzk] using T.leftToAttach_support_subset_rim j hzOld))
  · have hzTail : z ∈ (P.pathTailToEnd hk).support := by
      simpa [Tripod.allNilSameMiddleTransitionLeg,
        SimpleGraph.Walk.support_copy] using hzLeg
    rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_two_precise_support_cases
          P T hgraph hleg_j_nil hi hj hk
          hij_order hjk_order hu hv transition hzRim with
      hzArm | hzOldLeg | hzSegmentRev
    · have hzk := P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
        (T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArm))
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk
    · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp hleg_k_nil
      have hza : z = T.attach k := by simpa [hsupport] using hzOldLeg
      simpa [Tripod.allNilSameMiddleTransitionAttach] using hza
    · have hzSegment : z ∈
          (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSegmentRev
      have hzk : z = T.boundary k := by
        simpa [GMIX24CutPath.pathSegmentBetween] using
          P.segmentBetween_support_inter_pathTailToEnd_subset_right
            hj hk (Nat.le_of_lt hjk_order) hzSegment hzTail
      simpa [Tripod.allNilSameMiddleTransitionAttach,
        (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using hzk

/-- Ambient tripod produced by a clean transition between the two strict
arms of the median ordered old rim. -/
theorem Tripod.liftAllNilOfSameMiddleArmTransition
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
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hleft_contact :
      v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_q : forall z : V, z ∈ transition.support ->
      z ∈ q.support -> z = v) :
    Nonempty S.Tripod := by
  have hright_ne_attach : T.right ≠ T.attach j := by
    intro h
    exact T.right_ne_boundary j
      (h.trans ((T.leg_nil_iff_boundary_eq_attach j).mp (hlegs_nil j)).symm)
  refine ⟨{
    left := T.right
    right := T.attach j
    left_ne_right := hright_ne_attach
    rim := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
      P T hgraph (hlegs_nil j)
      hi hj hk hij_order hjk_order hu hv transition
    rim_isPath :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hv hv_ne_attach transition htransition_path htransition_clean
    attach :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k v
    attach_mem_rim :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach_mem_rim
        P T hgraph hij hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hu hv hv_ne_attach hleft_contact transition
    boundary := P.boundaryTriple a
    boundary_mem := P.boundaryTriple_mem_of_leftArc ha
    boundary_injective := P.boundaryTriple_injective_of_leftArc ha
    leg := GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
      P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q
    leg_isPath :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg_isPath
        P T hgraph (hlegs_nil i) (hlegs_nil k) hi hk hv q hq_path hq_clean
    rim_internals_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean
    legs_pairwise_disjoint :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil k) hi hk
        hij_order hjk_order hpath_contacts hv q hq_outside
    legs_meet_rims_only_at_attach :=
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_meet_rims_only_at_attach
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts q hq_outside hq_clean
        hu hu_ne_attach hv hv_ne_attach hleft_contact transition htransition_outside
        htransition_clean htransition_q
  }⟩


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
