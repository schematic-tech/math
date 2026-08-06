import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes
import Schematic.Math.GraphTheory.Minors.Society.Terminal.SameMiddleTransition

/-!
Clean carrier chords, component tails, and disjoint common-end escapes.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/- Checked increment: middle-to-first off-diagonal transition path. -/

/-- Rebuilt rims for a clean transition from the right arm of the median
ordered rim to the left arm of the first ordered rim.  The two outer rims are
unchanged; the middle rim follows the transition and returns through the old
left common end. -/
def Tripod.allNilMiddleToFirstBridge
    [DecidableEq V]
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j : Fin 3} {u v : V}
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v) :
    S.graph.Walk T.right T.left :=
  ((((T.rightToAttach j).takeUntil u hu).mapLe hgraph).append transition).append
    (((T.leftToAttach i).takeUntil v hv).reverse.mapLe hgraph)

theorem Tripod.allNilMiddleToFirstBridge_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j : Fin 3} {u v z : V}
    (hu : u ∈ (T.rightToAttach j).support)
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.allNilMiddleToFirstBridge
        T hgraph hu hv transition).support) :
    z ∈ ((T.rightToAttach j).takeUntil u hu).support ∨
      z ∈ transition.support ∨
        z ∈ ((T.leftToAttach i).takeUntil v hv).support := by
  rw [Tripod.allNilMiddleToFirstBridge,
    SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzFirst | hzLeft
  · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
      hzRight | hzTransition
    · exact Or.inl (by
        simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzRight)
    · exact Or.inr (Or.inl hzTransition)
  · exact Or.inr (Or.inr
      (Walk.mem_support_of_mem_reverse_mapLe hgraph
        ((T.leftToAttach i).takeUntil v hv) hzLeft))

def Tripod.allNilMiddleToFirstTransitionRim
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
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v) :
    Fin 3 -> S.graph.Walk T.right (T.boundary j)
  | 0 =>
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 0
  | 1 =>
      ((GMIX24SourceProof.Tripod.allNilMiddleToFirstBridge
        T hgraph hu hv transition).append
            ((T.leftToAttach j).mapLe hgraph)).copy rfl
              ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil).symm
  | 2 =>
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 2

theorem Tripod.allNilMiddleToFirstTransitionRim_isPath
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
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach i).support)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim i))
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.allNilMiddleToFirstTransitionRim] using
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
          P T hgraph hij hik hjk hi hj hk
          hij_order hjk_order hpath_contacts 0)
  · let rightPart : S.graph.Walk T.right u :=
      ((T.rightToAttach j).takeUntil u hu).mapLe hgraph
    let leftIPart : S.graph.Walk v T.left :=
      ((T.leftToAttach i).takeUntil v hv).reverse.mapLe hgraph
    let leftJPart : S.graph.Walk T.left (T.attach j) :=
      (T.leftToAttach j).mapLe hgraph
    have hright_path : rightPart.IsPath := by
      simpa [rightPart] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.rightToAttach_isPath j).takeUntil hu)
    have hleftI_path : leftIPart.IsPath := by
      simpa [leftIPart] using SimpleGraph.Walk.IsPath.mapLe hgraph
        ((T.leftToAttach_isPath i).takeUntil hv).reverse
    have hleftJ_path : leftJPart.IsPath := by
      simpa [leftJPart] using
        SimpleGraph.Walk.IsPath.mapLe hgraph (T.leftToAttach_isPath j)
    have hfirst_path : (rightPart.append transition).IsPath := by
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hright_path htransition_path ?_
      intro z hzRight hzTransition
      have hzRightOld : z ∈ (T.rightToAttach j).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach j) hu (by
          simpa [rightPart, SimpleGraph.Walk.support_mapLe_eq_support]
            using hzRight)
      rcases htransition_clean z hzTransition
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim j hzRightOld)) with hzu | hzv
      · exact hzu
      · have hvRight : v ∈ (T.rightToAttach j).support := by
          simpa [hzv] using hzRightOld
        have hvRightEnd : v = T.right :=
          T.rightToAttach_support_inter_rim_eq_right
            (fun h => hij h.symm) hvRight hv_internal.1
        exact False.elim (hv_internal.2.2 hvRightEnd)
    have hsecond_path :
        ((rightPart.append transition).append leftIPart).IsPath := by
      refine Walk.IsPath.append_of_support_inter_eq_endpoint
        hfirst_path hleftI_path ?_
      intro z hzFirst hzLeftI
      have hzLeftPrefix :
          z ∈ ((T.leftToAttach i).takeUntil v hv).support := by
        simpa [leftIPart, SimpleGraph.Walk.support_mapLe_eq_support,
          SimpleGraph.Walk.support_reverse] using hzLeftI
      have hzLeftOld : z ∈ (T.leftToAttach i).support :=
        SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hv
          hzLeftPrefix
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
        hzRight | hzTransition
      · have hzRightOld : z ∈ (T.rightToAttach j).support :=
          SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach j) hu (by
            simpa [rightPart, SimpleGraph.Walk.support_mapLe_eq_support]
              using hzRight)
        have hzRightEnd : z = T.right :=
          T.rightToAttach_support_inter_rim_eq_right
            (fun h => hij h.symm) hzRightOld
              (T.leftToAttach_support_subset_rim i hzLeftOld)
        exact False.elim
          (T.right_not_mem_leftToAttach i (by simpa [hzRightEnd] using hzLeftOld))
      · rcases htransition_clean z hzTransition
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim i hzLeftOld)) with hzu | hzv
        · have huLeft : u ∈ (T.leftToAttach i).support := by
            simpa [hzu] using hzLeftOld
          rcases hright_contact with huInternal | huRight
          · have huLeftEnd : u = T.left :=
              T.leftToAttach_support_inter_rim_eq_left hij huLeft huInternal.1
            exact False.elim (huInternal.2.1 huLeftEnd)
          · exact False.elim
              (T.right_not_mem_leftToAttach i (by simpa [huRight] using huLeft))
        · exact hzv
    rw [Tripod.allNilMiddleToFirstTransitionRim.eq_def,
      Tripod.allNilMiddleToFirstBridge]
    apply (SimpleGraph.Walk.isPath_copy
      (((rightPart.append transition).append leftIPart).append leftJPart)
      rfl ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil).symm).mpr
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hsecond_path hleftJ_path ?_
    intro z hzSecond hzLeftJ
    have hzLeftJOld : z ∈ (T.leftToAttach j).support := by
      simpa [leftJPart, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeftJ
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzSecond with
      hzFirst | hzLeftI
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
        hzRight | hzTransition
      · have hzPrefix : z ∈ ((T.rightToAttach j).takeUntil u hu).support := by
          simpa [rightPart, SimpleGraph.Walk.support_mapLe_eq_support] using hzRight
        exact False.elim
          (Set.disjoint_left.mp
            (T.rightToAttach_takeUntil_support_disjoint_leftToAttach
              hu hu_ne_attach) hzPrefix hzLeftJOld)
      · rcases htransition_clean z hzTransition
            (T.rim_mem_vertexSet
              (T.leftToAttach_support_subset_rim j hzLeftJOld)) with hzu | hzv
        · have huLeft : u ∈ (T.leftToAttach j).support := by
            simpa [hzu] using hzLeftJOld
          exact False.elim (hu_ne_attach
            (T.leftToAttach_support_inter_rightToAttach_eq_attach j huLeft hu))
        · have hvLeft : v ∈ (T.leftToAttach j).support := by
            simpa [hzv] using hzLeftJOld
          have hvEnd : v = T.left :=
            T.leftToAttach_support_inter_rim_eq_left
              (fun h => hij h.symm) hvLeft hv_internal.1
          exact False.elim (hv_internal.2.1 hvEnd)
    · have hzLeftPrefix :
          z ∈ ((T.leftToAttach i).takeUntil v hv).support := by
        simpa [leftIPart, SimpleGraph.Walk.support_mapLe_eq_support,
          SimpleGraph.Walk.support_reverse] using hzLeftI
      exact T.leftToAttach_takeUntil_support_inter_rim_eq_left hij hv
        hzLeftPrefix (T.leftToAttach_support_subset_rim j hzLeftJOld)
  · simpa [Tripod.allNilMiddleToFirstTransitionRim] using
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
          P T hgraph hij hik hjk hi hj hk
          hij_order hjk_order hpath_contacts 2)

def Tripod.allNilMiddleToFirstTransitionAttach
    {H : GeneralSociety V} (T : H.Tripod)
    (i k : Fin 3) : Fin 3 -> V :=
  GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach T i k T.left

def Tripod.allNilMiddleToFirstTransitionLeg
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk
        (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionAttach T i k r)
        (P.boundaryTriple a r) :=
  GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
    P T hgraph hleg_i_nil hleg_k_nil hi hk
      (T.leftToAttach j).start_mem_support q

theorem Tripod.allNilMiddleToFirstTransitionAttach_mem_rim
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
    (hv : v ∈ (T.leftToAttach i).support)
    (transition : S.graph.Walk u v) :
    forall r : Fin 3,
      GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionAttach T i k r ∈
        Walk.InternalVertices
          (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim
            P T hgraph hleg_j_nil hi hj hk
            hij_order hjk_order hu hv transition r) := by
  intro r
  fin_cases r
  · change T.attach i ∈ Walk.InternalVertices
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 0)
    refine ⟨?_, (T.attach_mem_rim i).2.2, ?_⟩
    · rw [Tripod.outerNilMiddleNonNilCommonLeftRim,
        Tripod.rightToBoundaryViaLegTail,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      simp [SimpleGraph.Walk.support_mapLe_eq_support]
    · intro hai
      exact T.attach_ne_of_ne hij
        (hai.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))
  · change T.left ∈ Walk.InternalVertices
      (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionRim
        P T hgraph hleg_j_nil hi hj hk
        hij_order hjk_order hu hv transition 1)
    refine ⟨?_, T.left_ne_right, T.left_ne_boundary j⟩
    · rw [Tripod.allNilMiddleToFirstTransitionRim.eq_def,
        SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.mem_support_append_iff]
      right
      simp [SimpleGraph.Walk.support_mapLe_eq_support]
  · change T.attach k ∈ Walk.InternalVertices
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order 2)
    refine ⟨?_, (T.attach_mem_rim k).2.2, ?_⟩
    · rw [Tripod.outerNilMiddleNonNilCommonLeftRim,
        Tripod.rightToBoundaryViaLegTail,
        SimpleGraph.Walk.mem_support_append_iff]
      left
      simp [SimpleGraph.Walk.support_mapLe_eq_support]
    · intro hak
      exact T.attach_ne_of_ne (fun h => hjk h.symm)
        (hak.trans ((T.leg_nil_iff_boundary_eq_attach j).mp hleg_j_nil))

theorem Tripod.allNilMiddleToFirstTransitionLeg_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = T.left) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionLeg
        P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).IsPath := by
  intro r
  simpa [Tripod.allNilMiddleToFirstTransitionLeg,
    Tripod.allNilMiddleToFirstTransitionAttach] using
    (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg_isPath
      P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk
      (T.leftToAttach j).start_mem_support q hq_path hq_clean r)

theorem Tripod.allNilMiddleToFirstTransitionLegs_pairwise_disjoint
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
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionLeg
            P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).support}
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilMiddleToFirstTransitionLeg
            P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q s).support} := by
  intro r s hrs
  simpa [Tripod.allNilMiddleToFirstTransitionLeg,
    Tripod.allNilMiddleToFirstTransitionAttach] using
    (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_pairwise_disjoint
      P T hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk
      hij_order hjk_order hpath_contacts
      (T.leftToAttach j).start_mem_support q hq_outside r s hrs)

/-- The first non-end carrier contact of an outside path starting at the
right end of an all-collapsed tripod gives a genuinely clean chord prefix.

This is the forward half of the carrier-bridge normalization used in the
last sentence of GM IX `(2.4)`.  The selected endpoint is neither old common
end.  Since every collapsed attachment lies on the deleted cut path whereas
the chord stays outside it, the endpoint is an internal, non-attachment point
of one old rim. -/
theorem Tripod.exists_first_internalCarrierChord_from_right
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
    (hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hnot_clean : Not (forall z : V,
      z ∈ bridge.support -> z ∈ T.vertexSet ->
        z = T.right ∨ z = T.left)) :
    Exists fun x : V =>
      Exists fun chord : S.graph.Walk T.right x =>
        (Exists fun r : Fin 3 =>
          x ∈ Walk.InternalVertices (T.rim r) ∧ x ≠ T.attach r) ∧
          chord.IsPath ∧
            (forall z : V, z ∈ chord.support -> z ∈ P.outside) ∧
              forall z : V, z ∈ chord.support -> z ∈ T.vertexSet ->
                z = T.right ∨ z = x := by
  classical
  push Not at hnot_clean
  rcases hnot_clean with ⟨w, hwBridge, hwT, hw_ne_right, hw_ne_left⟩
  let internalCarrier : Set V :=
    T.vertexSet \ ({T.right, T.left} : Set V)
  have hwInternalCarrier : w ∈ internalCarrier := by
    exact ⟨hwT, by simp [hw_ne_right, hw_ne_left]⟩
  let initial : S.graph.Walk T.right w := bridge.takeUntil w hwBridge
  have hinitial_path : initial.IsPath := by
    simpa [initial] using hbridge_path.takeUntil hwBridge
  obtain ⟨x, hxInitial, hxInternalCarrier, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) hinitial_path internalCarrier hwInternalCarrier
  have hxBridge : x ∈ bridge.support :=
    SimpleGraph.Walk.support_takeUntil_subset bridge hwBridge
      (by simpa [initial] using hxInitial)
  let chord : S.graph.Walk T.right x := initial.takeUntil x hxInitial
  have hx_ne_right : x ≠ T.right := by
    exact fun h => hxInternalCarrier.2 (by simp [h])
  have hx_ne_left : x ≠ T.left := by
    exact fun h => hxInternalCarrier.2 (by simp [h])
  have hxOutside : x ∈ P.outside :=
    hbridge_outside x hxBridge
  have hxResidual :=
    GMIX24SourceProof.Tripod.lastCarrierContact_endpoint_or_internal_of_all_legs_nil
      P T hlegs_nil hfeet_path hxInternalCarrier.1 hxOutside
  have hxInternal : Exists fun r : Fin 3 =>
      x ∈ Walk.InternalVertices (T.rim r) ∧ x ≠ T.attach r := by
    rcases hxResidual with hxEnd | hxInt
    · rcases hxEnd with hxRight | hxLeft
      · exact False.elim (hx_ne_left hxRight)
      · exact False.elim (hx_ne_right hxLeft)
    · exact hxInt
  refine ⟨x, chord, hxInternal, ?_, ?_, ?_⟩
  · simpa [chord] using hinitial_path.takeUntil hxInitial
  · intro z hz
    exact hbridge_outside z
      (SimpleGraph.Walk.support_takeUntil_subset bridge hwBridge
        (SimpleGraph.Walk.support_takeUntil_subset initial hxInitial
          (by simpa [chord] using hz)))
  · intro z hzChord hzT
    by_cases hzRight : z = T.right
    · exact Or.inl hzRight
    by_cases hzLeft : z = T.left
    · have hleft_not_chord : T.left ∉ chord.support := by
        have hleft_not_initial : T.left ∉ initial.support := by
          simpa [initial] using
            SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              hbridge_path hwBridge hw_ne_left.symm
        exact fun hz => hleft_not_initial
          (SimpleGraph.Walk.support_takeUntil_subset initial hxInitial
            (by simpa [chord] using hz))
      exact False.elim (hleft_not_chord (by simpa [hzLeft] using hzChord))
    · exact Or.inr
        (hfirst z (by simpa [chord] using hzChord)
          ⟨hzT, by simp [hzRight, hzLeft]⟩)

/-- Left-right symmetric form of
`exists_first_internalCarrierChord_from_right`. -/
theorem Tripod.exists_first_internalCarrierChord_from_left
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
    (hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (bridge : S.graph.Walk T.left T.right)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside)
    (hnot_clean : Not (forall z : V,
      z ∈ bridge.support -> z ∈ T.vertexSet ->
        z = T.left ∨ z = T.right)) :
    Exists fun x : V =>
      Exists fun chord : S.graph.Walk T.left x =>
        (Exists fun r : Fin 3 =>
          x ∈ Walk.InternalVertices (T.rim r) ∧ x ≠ T.attach r) ∧
          chord.IsPath ∧
            (forall z : V, z ∈ chord.support -> z ∈ P.outside) ∧
              forall z : V, z ∈ chord.support -> z ∈ T.vertexSet ->
                z = T.left ∨ z = x := by
  let U : H.Tripod := T.flip
  have hlegs_nil_U : forall r : Fin 3, (U.leg r).Nil := by
    simpa [U] using T.legsNil_flip hlegs_nil
  have hfeet_path_U : forall r : Fin 3, U.boundary r ∈ P.pathSet := by
    intro r
    simpa [U] using hfeet_path r
  have hnot_clean_U : Not (forall z : V,
      z ∈ bridge.support -> z ∈ U.vertexSet ->
        z = U.right ∨ z = U.left) := by
    intro hclean
    apply hnot_clean
    intro z hzBridge hzT
    simpa [U] using hclean z hzBridge (by simpa [U] using hzT)
  rcases
      GMIX24SourceProof.Tripod.exists_first_internalCarrierChord_from_right
        P U hlegs_nil_U hfeet_path_U bridge hbridge_path hbridge_outside
        hnot_clean_U with
    ⟨x, chord, hxInternal, hchordPath, hchordOutside, hchordClean⟩
  refine ⟨x, chord, ?_, hchordPath, hchordOutside, ?_⟩
  · rcases hxInternal with ⟨r, hxr, hxAttach⟩
    exact ⟨r, by simpa [U, Walk.internalVertices_reverse] using hxr,
      by simpa [U] using hxAttach⟩
  · intro z hzChord hzT
    simpa [U] using hchordClean z hzChord (by simpa [U] using hzT)

/-- Every vertex of a fixed outside component meeting the left boundary arc
belongs to the canonical caught left side. -/
theorem GMIX24CutPath.induceComponentSupport_subset_leftSide
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (haC : a ∈ induceComponentSupport (G := S.graph) C) :
    induceComponentSupport (G := S.graph) C ⊆ P.leftSide := by
  intro z hzC
  rcases hzC with ⟨hzOutside, hzSupp⟩
  rcases haC with ⟨haOutside, haSupp⟩
  exact
    ⟨hzOutside, C, hzSupp, a, haOutside, ha, haSupp⟩

/-- A common-component escape in the all-collapsed branch has the exact
last-contact residual used in the printed proof: a clean `X -> Omega` tail
whose source is a common theta end or an internal non-attachment rim point. -/
theorem Tripod.exists_clean_component_tail_with_all_nil_residual
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
    (hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    {a : V}
    (q : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C) :
    Exists fun x : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ T.vertexSet ∧ a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
          (forall z : V, z ∈ tail.support ->
            z ∈ induceComponentSupport (G := S.graph) C) ∧
            (forall z : V, z ∈ tail.support -> z ∈ P.leftSide) ∧
            (forall z : V, z ∈ tail.support ->
              z ∈ T.vertexSet -> z = x) ∧
              ((x = T.left ∨ x = T.right) ∨
                Exists fun r : Fin 3 =>
                  x ∈ Walk.InternalVertices (T.rim r) ∧
                    x ≠ T.attach r) := by
  rcases
      GMIX24SourceProof.Tripod.exists_lastCarrierContactTail_in_component
        P T C q T.left_mem_vertexSet hqPath hqComponent with
    ⟨x, tail, hxT, htailPath, htailComponent, htailClean⟩
  have hxOutside : x ∈ P.outside :=
    (induceComponentSupport_subset (G := S.graph) C
      (htailComponent x tail.start_mem_support))
  have hcomponentSide :
      induceComponentSupport (G := S.graph) C ⊆ P.leftSide :=
    GMIX24SourceProof.GMIX24CutPath.induceComponentSupport_subset_leftSide
      P C ha (hqComponent a q.end_mem_support)
  exact
    ⟨x, tail, hxT, ha, htailPath, htailComponent,
      (fun z hz => hcomponentSide (htailComponent z hz)), htailClean,
      GMIX24SourceProof.Tripod.lastCarrierContact_endpoint_or_internal_of_all_legs_nil
        P T hlegs_nil hfeet_path hxT hxOutside⟩

/-- Right-common-end version of
`exists_clean_component_tail_with_all_nil_residual`.

The printed GM IX `(2.4)` argument treats the two common ends symmetrically.
Keeping this symmetry explicit is useful in the final common-component
rerouting: both caught-component paths are shortened after their last old
theta contact before their two residual contacts are compared. -/
theorem Tripod.exists_clean_component_tail_from_right_with_all_nil_residual
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
    (hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (C : (S.graph.induce P.outside).ConnectedComponent)
    {a : V}
    (q : S.graph.Walk T.right a)
    (ha : a ∈ P.leftBoundaryArc)
    (hqPath : q.IsPath)
    (hqComponent : forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := S.graph) C) :
    Exists fun x : V =>
      Exists fun tail : S.graph.Walk x a =>
        x ∈ T.vertexSet ∧ a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
          (forall z : V, z ∈ tail.support ->
            z ∈ induceComponentSupport (G := S.graph) C) ∧
            (forall z : V, z ∈ tail.support -> z ∈ P.leftSide) ∧
            (forall z : V, z ∈ tail.support ->
              z ∈ T.vertexSet -> z = x) ∧
              ((x = T.left ∨ x = T.right) ∨
                Exists fun r : Fin 3 =>
                  x ∈ Walk.InternalVertices (T.rim r) ∧
                    x ≠ T.attach r) := by
  let U : H.Tripod := T.flip
  have hlegsU : forall r : Fin 3, (U.leg r).Nil := by
    simpa [U] using T.legsNil_flip hlegs_nil
  have hfeetU : forall r : Fin 3, U.boundary r ∈ P.pathSet := by
    intro r
    simpa [U] using hfeet_path r
  rcases
      GMIX24SourceProof.Tripod.exists_clean_component_tail_with_all_nil_residual
        P U hlegsU hfeetU C q ha hqPath hqComponent with
    ⟨x, tail, hxU, ha', htailPath, htailComponent, htailSide,
      htailCleanU, hresidual⟩
  refine
    ⟨x, tail, (by simpa [U] using hxU), ha', htailPath,
      htailComponent, htailSide, ?_, ?_⟩
  · intro z hzTail hzT
    exact htailCleanU z hzTail (by simpa [U] using hzT)
  · rcases hresidual with hend | hinternal
    · left
      rcases hend with hxRight | hxLeft
      · exact Or.inr (by simpa [U] using hxRight)
      · exact Or.inl (by simpa [U] using hxLeft)
    · right
      rcases hinternal with ⟨r, hxr, hxAttach⟩
      refine ⟨r, ?_, ?_⟩
      · simpa [U, Walk.internalVertices_reverse] using hxr
      · simpa [U] using hxAttach

/-- Simultaneous last-contact normal form for the common-component branch.

This theorem is the exact data produced before the final bridge exchange in
the printed common-end paragraph.  Cross-freeness first puts the two old
common ends in one component of `G - V(P)`.  Both component paths are then
shortened after their last old-theta contact.  The returned tails stay in the
same caught component and are clean against the old tripod; each source is
classified as an old theta end or an internal non-attachment rim point. -/
theorem left_side_tripod_common_component_clean_residual_tails_of_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    Exists fun _hlegs_nil : forall r : Fin 3, (T.leg r).Nil =>
      Exists fun _hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet =>
        Exists fun C : (S.graph.induce P.outside).ConnectedComponent =>
          T.left ∈ induceComponentSupport (G := S.graph) C ∧
          T.right ∈ induceComponentSupport (G := S.graph) C ∧
          Exists fun x : V =>
            Exists fun a : V =>
              Exists fun qLeft : S.graph.Walk x a =>
                x ∈ T.vertexSet ∧ a ∈ P.leftBoundaryArc ∧
                  qLeft.IsPath ∧
                  (forall z : V, z ∈ qLeft.support ->
                    z ∈ induceComponentSupport (G := S.graph) C) ∧
                  (forall z : V, z ∈ qLeft.support -> z ∈ P.leftSide) ∧
                  (forall z : V, z ∈ qLeft.support ->
                    z ∈ T.vertexSet -> z = x) ∧
                  ((x = T.left ∨ x = T.right) ∨
                    Exists fun r : Fin 3 =>
                      x ∈ Walk.InternalVertices (T.rim r) ∧
                        x ≠ T.attach r) ∧
                  Exists fun y : V =>
                    Exists fun b : V =>
                      Exists fun qRight : S.graph.Walk y b =>
                        y ∈ T.vertexSet ∧ b ∈ P.leftBoundaryArc ∧
                          qRight.IsPath ∧
                          (forall z : V, z ∈ qRight.support ->
                            z ∈ induceComponentSupport (G := S.graph) C) ∧
                          (forall z : V, z ∈ qRight.support ->
                            z ∈ P.leftSide) ∧
                          (forall z : V, z ∈ qRight.support ->
                            z ∈ T.vertexSet -> z = y) ∧
                          ((y = T.left ∨ y = T.right) ∨
                            Exists fun r : Fin 3 =>
                              y ∈ Walk.InternalVertices (T.rim r) ∧
                                y ≠ T.attach r) := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  have hlegs_nil : forall r : Fin 3, (T.leg r).Nil :=
    left_side_tripod_all_legs_nil_of_source_clean_no_hidden_contact
      hno_cross hno_tripod P T hsource_clean hno_hidden
  rcases
      left_side_tripod_common_endpoints_same_outsideComponent_of_no_hidden_contact
        (S := S) hno_cross hno_tripod P T hsource_clean hno_hidden with
    ⟨C, hleftOutside, hleftC, a, rawLeft, ha, hrawLeftPath,
      hrawLeftComponent, hrightOutside, hrightC, b, rawRight, hb,
      hrawRightPath, hrawRightComponent⟩
  rcases
      GMIX24SourceProof.Tripod.exists_clean_component_tail_with_all_nil_residual
        P T hlegs_nil hfeet_path C rawLeft ha hrawLeftPath
        hrawLeftComponent with
    ⟨x, qLeft, hxT, ha', hqLeftPath, hqLeftComponent, hqLeftSide,
      hqLeftClean, hxResidual⟩
  rcases
      GMIX24SourceProof.Tripod.exists_clean_component_tail_from_right_with_all_nil_residual
        P T hlegs_nil hfeet_path C rawRight hb hrawRightPath
        hrawRightComponent with
    ⟨y, qRight, hyT, hb', hqRightPath, hqRightComponent, hqRightSide,
      hqRightClean, hyResidual⟩
  exact
    ⟨hlegs_nil, hfeet_path, C, ⟨hleftOutside, hleftC⟩,
      ⟨hrightOutside, hrightC⟩, x, a, qLeft, hxT, ha', hqLeftPath,
      hqLeftComponent, hqLeftSide, hqLeftClean, hxResidual,
      y, b, qRight, hyT, hb', hqRightPath, hqRightComponent,
      hqRightSide, hqRightClean, hyResidual⟩

/-- Disjoint exact common-end escape tails give the ambient cross in the
`P.s, b, a, P.t` cyclic order.

The first cross path follows the initial cut-path tail to the first collapsed
foot, the left arm of that old rim, and then `qLeft`.  The second follows
`qRight` backwards, the right arm of the last old rim, and the final cut-path
tail.  The source's paths need not be boundary-clean: the final call to
`Cross.of_disjoint_alternating_paths` performs the joint normalization. -/
theorem Tripod.crossOfDisjointCommonEndpointTails_leftOrder
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a b : V}
    (qLeft : S.graph.Walk T.left a)
    (qRight : S.graph.Walk T.right b)
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hqLeft_path : qLeft.IsPath)
    (hqRight_path : qRight.IsPath)
    (hqLeft_outside : forall z : V, z ∈ qLeft.support -> z ∈ P.outside)
    (hqRight_outside : forall z : V, z ∈ qRight.support -> z ∈ P.outside)
    (hqLeft_clean :
      forall z : V, z ∈ qLeft.support -> z ∈ T.vertexSet -> z = T.left)
    (hqRight_clean :
      forall z : V, z ∈ qRight.support -> z ∈ T.vertexSet -> z = T.right)
    (hq_disjoint :
      Disjoint {z : V | z ∈ qLeft.support} {z : V | z ∈ qRight.support})
    (hfirst_order :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s a b)
    (hsecond_order :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary a P.s P.t) :
    Nonempty S.Cross := by
  classical
  have hbi : T.boundary i = T.attach i :=
    (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil
  have hbk : T.boundary k = T.attach k :=
    (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil
  let startTail : S.graph.Walk P.s (T.attach i) :=
    (P.pathTailToStart hi).reverse.copy rfl hbi
  let startArm : S.graph.Walk (T.attach i) T.left :=
    (T.attachToLeft i).mapLe hgraph
  let firstCore : S.graph.Walk P.s T.left := startTail.append startArm
  let firstPath : S.graph.Walk P.s a := firstCore.append qLeft
  let endArm : S.graph.Walk T.right (T.attach k) :=
    (T.rightToAttach k).mapLe hgraph
  let endTail : S.graph.Walk (T.attach k) P.t :=
    (P.pathTailToEnd hk).copy hbk rfl
  let secondCore : S.graph.Walk T.right P.t := endArm.append endTail
  let secondPath : S.graph.Walk b P.t := qRight.reverse.append secondCore
  have hstartTail_path : startTail.IsPath := by
    simpa [startTail] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToStart hi).reverse rfl hbi).mpr
          (P.pathTailToStart_isPath hi).reverse
  have hstartArm_path : startArm.IsPath := by
    simpa [startArm] using
      SimpleGraph.Walk.IsPath.mapLe hgraph (T.attachToLeft_isPath i)
  have hendArm_path : endArm.IsPath := by
    simpa [endArm] using
      SimpleGraph.Walk.IsPath.mapLe hgraph (T.rightToAttach_isPath k)
  have hendTail_path : endTail.IsPath := by
    simpa [endTail] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToEnd hk) hbk rfl).mpr
          (P.pathTailToEnd_isPath hk)
  have hfirstCore_path : firstCore.IsPath := by
    dsimp [firstCore]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hstartTail_path hstartArm_path ?_
    intro z hzTail hzArm
    have hzTailOld : z ∈ (P.pathTailToStart hi).support := by
      simpa [startTail, SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse] using hzTail
    have hzArmOld : z ∈ (T.attachToLeft i).support := by
      simpa [startArm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    have hzT : z ∈ T.vertexSet :=
      T.rim_mem_vertexSet (T.attachToLeft_support_subset_rim i hzArmOld)
    exact
      (P.pathTailToStart_clean_first_foot_of_path_contacts
        T hij hik hjk hi hij_order hjk_order hpath_contacts
        hzTailOld hzT).trans hbi
  have hfirstPath_path : firstPath.IsPath := by
    dsimp [firstPath]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hfirstCore_path hqLeft_path ?_
    intro z hzCore hzq
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzCore with
      hzTail | hzArm
    · have hzTailOld : z ∈ (P.pathTailToStart hi).support := by
        simpa [startTail, SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_reverse] using hzTail
      exact False.elim
        ((hqLeft_outside z hzq).2
          (P.pathTailToStart_support_subset_pathSet hi z hzTailOld))
    · apply hqLeft_clean z hzq
      apply T.rim_mem_vertexSet
      apply T.attachToLeft_support_subset_rim i
      simpa [startArm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
  have hsecondCore_path : secondCore.IsPath := by
    dsimp [secondCore]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hendArm_path hendTail_path ?_
    intro z hzArm hzTail
    have hzArmOld : z ∈ (T.rightToAttach k).support := by
      simpa [endArm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    have hzTailOld : z ∈ (P.pathTailToEnd hk).support := by
      simpa [endTail, SimpleGraph.Walk.support_copy] using hzTail
    have hzT : z ∈ T.vertexSet :=
      T.rim_mem_vertexSet (T.rightToAttach_support_subset_rim k hzArmOld)
    exact
      (P.pathTailToEnd_clean_last_foot_of_path_contacts
        T hij hik hjk hk hij_order hjk_order hpath_contacts
        hzTailOld hzT).trans hbk
  have hsecondPath_path : secondPath.IsPath := by
    dsimp [secondPath]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hqRight_path.reverse hsecondCore_path ?_
    intro z hzqRev hzCore
    have hzq : z ∈ qRight.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hzqRev
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzCore with
      hzArm | hzTail
    · apply hqRight_clean z hzq
      apply T.rim_mem_vertexSet
      apply T.rightToAttach_support_subset_rim k
      simpa [endArm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    · have hzTailOld : z ∈ (P.pathTailToEnd hk).support := by
        simpa [endTail, SimpleGraph.Walk.support_copy] using hzTail
      exact False.elim
        ((hqRight_outside z hzq).2
          (P.pathTailToEnd_support_subset_pathSet hk z hzTailOld))
  have hpaths_disjoint :
      Disjoint {z : V | z ∈ firstPath.support}
        {z : V | z ∈ secondPath.support} := by
    rw [Set.disjoint_left]
    intro z hzFirst hzSecond
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirst with
      hzFirstCore | hzLeft <;>
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzSecond with
        hzRightRev | hzSecondCore
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirstCore with
        hzStart | hzLeftArm
      · have hzStartOld : z ∈ (P.pathTailToStart hi).support := by
          simpa [startTail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_reverse] using hzStart
        have hzRight : z ∈ qRight.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzRightRev
        exact (hqRight_outside z hzRight).2
          (P.pathTailToStart_support_subset_pathSet hi z hzStartOld)
      · have hzLeftArmOld : z ∈ (T.attachToLeft i).support := by
          simpa [startArm, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzLeftArm
        have hzRight : z ∈ qRight.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hzRightRev
        have hzRightEnd : z = T.right := hqRight_clean z hzRight
          (T.rim_mem_vertexSet
            (T.attachToLeft_support_subset_rim i hzLeftArmOld))
        exact T.right_not_mem_attachToLeft i
          (by simpa [hzRightEnd] using hzLeftArmOld)
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzFirstCore with
        hzStart | hzLeftArm <;>
        rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzSecondCore with
          hzRightArm | hzEnd
      · have hzStartOld : z ∈ (P.pathTailToStart hi).support := by
          simpa [startTail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_reverse] using hzStart
        have hzRightArmOld : z ∈ (T.rightToAttach k).support := by
          simpa [endArm, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzRightArm
        have hzi : z = T.boundary i :=
          P.pathTailToStart_clean_first_foot_of_path_contacts
            T hij hik hjk hi hij_order hjk_order hpath_contacts hzStartOld
            (T.rim_mem_vertexSet
              (T.rightToAttach_support_subset_rim k hzRightArmOld))
        exact T.boundary_not_mem_rim_of_ne_index hik
          (by simpa [hzi] using
            T.rightToAttach_support_subset_rim k hzRightArmOld)
      · have hzStartOld : z ∈ (P.pathTailToStart hi).support := by
          simpa [startTail, SimpleGraph.Walk.support_copy,
            SimpleGraph.Walk.support_reverse] using hzStart
        have hzEndOld : z ∈ (P.pathTailToEnd hk).support := by
          simpa [endTail, SimpleGraph.Walk.support_copy] using hzEnd
        exact Set.disjoint_left.mp
          (P.pathTailToStart_support_disjoint_pathTailToEnd
            hi hk (lt_trans hij_order hjk_order)) hzStartOld hzEndOld
      · have hzLeftArmOld : z ∈ (T.attachToLeft i).support := by
          simpa [startArm, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzLeftArm
        have hzRightArmOld : z ∈ (T.rightToAttach k).support := by
          simpa [endArm, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzRightArm
        have hzRight : z = T.right :=
          T.rightToAttach_support_inter_rim_eq_right
            (i := k) (j := i) (fun h => hik h.symm) hzRightArmOld
            (T.attachToLeft_support_subset_rim i hzLeftArmOld)
        exact T.right_not_mem_attachToLeft i
          (by simpa [hzRight] using hzLeftArmOld)
      · have hzLeftArmOld : z ∈ (T.attachToLeft i).support := by
          simpa [startArm, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzLeftArm
        have hzEndOld : z ∈ (P.pathTailToEnd hk).support := by
          simpa [endTail, SimpleGraph.Walk.support_copy] using hzEnd
        have hzk : z = T.boundary k :=
          P.pathTailToEnd_clean_last_foot_of_path_contacts
            T hij hik hjk hk hij_order hjk_order hpath_contacts hzEndOld
            (T.rim_mem_vertexSet
              (T.attachToLeft_support_subset_rim i hzLeftArmOld))
        exact T.boundary_not_mem_rim_of_ne_index (fun h => hik h.symm)
          (by simpa [hzk] using
            T.attachToLeft_support_subset_rim i hzLeftArmOld)
    · have hzRight : z ∈ qRight.support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzRightRev
      exact Set.disjoint_left.mp hq_disjoint hzLeft hzRight
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hzSecondCore with
        hzRightArm | hzEnd
      · have hzRightArmOld : z ∈ (T.rightToAttach k).support := by
          simpa [endArm, SimpleGraph.Walk.support_mapLe_eq_support] using
            hzRightArm
        have hzLeftEnd : z = T.left := hqLeft_clean z hzLeft
          (T.rim_mem_vertexSet
            (T.rightToAttach_support_subset_rim k hzRightArmOld))
        exact T.left_not_mem_rightToAttach k
          (by simpa [hzLeftEnd] using hzRightArmOld)
      · have hzEndOld : z ∈ (P.pathTailToEnd hk).support := by
          simpa [endTail, SimpleGraph.Walk.support_copy] using hzEnd
        exact (hqLeft_outside z hzLeft).2
          (P.pathTailToEnd_support_subset_pathSet hk z hzEndOld)
  let endpoint : Fin 4 -> V
    | 0 => P.s
    | 1 => b
    | 2 => a
    | 3 => P.t
  have endpoint_mem : forall r : Fin 4, endpoint r ∈ S.boundarySet := by
    intro r
    fin_cases r
    · exact P.s_mem_boundary
    · exact P.leftBoundaryArc_subset hb
    · exact P.leftBoundaryArc_subset ha
    · exact P.t_mem_boundary
  have endpoint_injective : Function.Injective endpoint := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp only [endpoint] at hrs ⊢ <;>
      first
      | rfl
      | exact False.elim (hfirst_order.2.1 hrs.symm)
      | exact False.elim (hfirst_order.2.1 hrs)
      | exact False.elim (P.leftBoundaryArc_ne_s ha hrs.symm)
      | exact False.elim (P.leftBoundaryArc_ne_s ha hrs)
      | exact False.elim (P.s_ne_t hrs)
      | exact False.elim (P.s_ne_t hrs.symm)
      | exact False.elim (hfirst_order.2.2 hrs)
      | exact False.elim (hfirst_order.2.2 hrs.symm)
      | exact False.elim (P.leftBoundaryArc_ne_t hb hrs)
      | exact False.elim (P.leftBoundaryArc_ne_t hb hrs.symm)
      | exact False.elim (P.leftBoundaryArc_ne_t ha hrs)
      | exact False.elim (P.leftBoundaryArc_ne_t ha hrs.symm)
  let E : CrossEndpoints S.boundary := {
    endpoint := endpoint
    endpoint_mem := endpoint_mem
    endpoint_injective := endpoint_injective
    cyclic_alternating := by
      dsimp [CrossEndpointAlternating, endpoint]
      exact ⟨hfirst_order, hsecond_order⟩
  }
  exact Cross.of_disjoint_alternating_paths E hfirstPath_path
    hsecondPath_path (by simpa [firstPath, secondPath] using hpaths_disjoint)

/-- The opposite cyclic ordering of the disjoint exact common-end escape
tails.  This is the preceding construction applied to `T.flip`: reversing the
three old rims exchanges the roles of the old left and right common ends while
leaving every foot, leg, and carrier vertex unchanged. -/
theorem Tripod.crossOfDisjointCommonEndpointTails_rightOrder
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a b : V}
    (qLeft : S.graph.Walk T.left a)
    (qRight : S.graph.Walk T.right b)
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hqLeft_path : qLeft.IsPath)
    (hqRight_path : qRight.IsPath)
    (hqLeft_outside : forall z : V, z ∈ qLeft.support -> z ∈ P.outside)
    (hqRight_outside : forall z : V, z ∈ qRight.support -> z ∈ P.outside)
    (hqLeft_clean :
      forall z : V, z ∈ qLeft.support -> z ∈ T.vertexSet -> z = T.left)
    (hqRight_clean :
      forall z : V, z ∈ qRight.support -> z ∈ T.vertexSet -> z = T.right)
    (hq_disjoint :
      Disjoint {z : V | z ∈ qLeft.support} {z : V | z ∈ qRight.support})
    (hfirst_order :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s b a)
    (hsecond_order :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary b P.s P.t) :
    Nonempty S.Cross := by
  classical
  let U : H.Tripod := T.flip
  have hpath_contacts_U :
      forall z : V, z ∈ P.pathSet -> z ∈ U.vertexSet ->
        Exists fun m : Fin 3 => z = U.boundary m := by
    simpa [U] using T.pathContacts_flip hpath_contacts
  have hqRight_clean_U :
      forall z : V, z ∈ qRight.support -> z ∈ U.vertexSet -> z = U.left := by
    intro z hz hzU
    have hzT : z ∈ T.vertexSet := by
      simpa [U] using hzU
    simpa [U] using hqRight_clean z hz hzT
  have hqLeft_clean_U :
      forall z : V, z ∈ qLeft.support -> z ∈ U.vertexSet -> z = U.right := by
    intro z hz hzU
    have hzT : z ∈ T.vertexSet := by
      simpa [U] using hzU
    simpa [U] using hqLeft_clean z hz hzT
  exact Tripod.crossOfDisjointCommonEndpointTails_leftOrder
    P U hgraph hij hik hjk
    (by simpa [U] using hi) (by simpa [U] using hk)
    (by simpa [U] using hleg_i_nil) (by simpa [U] using hleg_k_nil)
    (by simpa [U] using hij_order) (by simpa [U] using hjk_order)
    hpath_contacts_U qRight qLeft hb ha hqRight_path hqLeft_path
    hqRight_outside hqLeft_outside hqRight_clean_U hqLeft_clean_U
    hq_disjoint.symm hfirst_order hsecond_order

/-- Complete disjoint-tail half of the source common-end alternative.

The two escape endpoints are distinct because the tails are vertex-disjoint.
Their order on the caught boundary arc selects one of the two concrete route
constructors above. -/
theorem Tripod.crossOfDisjointCommonEndpointTails
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a b : V}
    (qLeft : S.graph.Walk T.left a)
    (qRight : S.graph.Walk T.right b)
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hqLeft_path : qLeft.IsPath)
    (hqRight_path : qRight.IsPath)
    (hqLeft_outside : forall z : V, z ∈ qLeft.support -> z ∈ P.outside)
    (hqRight_outside : forall z : V, z ∈ qRight.support -> z ∈ P.outside)
    (hqLeft_clean :
      forall z : V, z ∈ qLeft.support -> z ∈ T.vertexSet -> z = T.left)
    (hqRight_clean :
      forall z : V, z ∈ qRight.support -> z ∈ T.vertexSet -> z = T.right)
    (hq_disjoint :
      Disjoint {z : V | z ∈ qLeft.support} {z : V | z ∈ qRight.support}) :
    Nonempty S.Cross := by
  classical
  have hab : a ≠ b := by
    intro hab
    exact Set.disjoint_left.mp hq_disjoint qLeft.end_mem_support
      (by simp [hab])
  have horder :=
    GMIX24CutPath.leftBoundaryArc_pair_alternating (S := S) P ha hb hab
  rcases horder with
    hrightOrder | hleftOrder
  · exact Tripod.crossOfDisjointCommonEndpointTails_rightOrder
      P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts qLeft qRight ha hb
      hqLeft_path hqRight_path hqLeft_outside hqRight_outside
      hqLeft_clean hqRight_clean hq_disjoint hrightOrder.1 hrightOrder.2
  · exact Tripod.crossOfDisjointCommonEndpointTails_leftOrder
      P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
      hij_order hjk_order hpath_contacts qLeft qRight ha hb
      hqLeft_path hqRight_path hqLeft_outside hqRight_outside
      hqLeft_clean hqRight_clean hq_disjoint hleftOrder.1 hleftOrder.2


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
