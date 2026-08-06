import Schematic.Math.GraphTheory.Minors.Society.General.Foundations
import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.WalkTransport

/-! Transitions joining contacts on the middle rim. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Same-median transition against an outer-left prefixed escape.  The left
contact may be strict or the old left end; transition/escape contact is
allowed exactly at that left contact. -/
theorem Tripod.liftAllNilOfOuterLeftArmResidualAndSameMiddleTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact : u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hleft_contact : v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_escape : forall z : V, z ∈ transition.support ->
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z = v) :
    Nonempty S.Tripod := by
  let escapeData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let escape : S.graph.Walk T.left a := escapeData.walk
  have hrj : r ≠ j := by
    rcases hr with rfl | rfl
    · exact hij
    · exact fun h => hjk h.symm
  have hescape_path : escape.IsPath := by
    simpa [escape] using escapeData.walk_isPath
  have hescape_outside : forall z : V,
      z ∈ escape.support -> z ∈ P.outside := by
    simpa [escape] using hq_prefix_outside
  have hescape_distinct : forall z : V, z ∈ escape.support ->
      z ∈ (T.rim j).support -> z = T.left := by
    simpa [escape] using escapeData.inter_distinct_rim_eq_left hrj
  have hescape_right (s : Fin 3) : forall z : V, z ∈ escape.support ->
      z ∈ (T.attachToRight s).support -> False := by
    simpa [escape] using escapeData.disjoint_attachToRight s
  have hescape_rim : forall s : Fin 3, forall z : V,
      z ∈ escape.support ->
      z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
          P T hgraph (hlegs_nil j)
          hi hj hk hij_order hjk_order hu hv transition s).support ->
      z = v := by
    intro s z hzEscape hzRim
    fin_cases s
    · exact False.elim ((hescape_outside z hzEscape).2 (by
        have hzOuter : z ∈
            (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
              P T hgraph hi hj hk
              hij_order hjk_order 0).support := by
          simpa [Tripod.allNilSameMiddleTransitionRim,
            SimpleGraph.Walk.support_copy] using hzRim
        rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph i
            hzOuter with hzArm | hzLeg | hzPath
        · exact False.elim (hescape_right i z hzEscape (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hzArm))
        · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp (hlegs_nil i)
          have hzi : z = T.attach i := by simpa [hsupport] using hzLeg
          exact False.elim ((hescape_outside z hzEscape).2
            (by
              rw [hzi, ← (T.leg_nil_iff_boundary_eq_attach i).mp (hlegs_nil i)]
              exact hi))
        · exact P.pathSegmentBetween_support_subset_pathSet hi hj
            (Nat.le_of_lt hij_order) z hzPath))
    · rcases
        GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_one_support_cases
          P T hgraph (hlegs_nil j)
          hi hj hk hij_order hjk_order hu hv transition hzRim with
        hzRight | hzTransition | hzLeftSuffix
      · exact False.elim (hescape_right j z hzEscape (by
          have hzOld := SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach j) hu hzRight
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzOld))
      · exact htransition_escape z hzTransition (by simpa [escape] using hzEscape)
      · have hzLeft : z ∈ (T.rim j).support :=
          T.leftToAttach_support_subset_rim j
            (SimpleGraph.Walk.support_dropUntil_subset
              (T.leftToAttach j) hv hzLeftSuffix)
        have hzEq : z = T.left := hescape_distinct z hzEscape hzLeft
        rcases hleft_contact with hvInternal | hvLeft
        · have hleftNotSuffix : T.left ∉
              ((T.leftToAttach j).dropUntil v hv).support :=
            Walk.IsPath.start_not_mem_dropUntil_support_of_ne
              (T.leftToAttach_isPath j) hv hvInternal.2.1
          exact False.elim (hleftNotSuffix (by simpa [hzEq] using hzLeftSuffix))
        · exact hzEq.trans hvLeft.symm
    · exact False.elim ((hescape_outside z hzEscape).2 (by
        have hzOuter : z ∈
            (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
              P T hgraph hi hj hk
              hij_order hjk_order 2).support := by
          simpa [Tripod.allNilSameMiddleTransitionRim,
            SimpleGraph.Walk.support_copy] using hzRim
        rcases T.rightToBoundaryViaLegTail_support_precise_cases hgraph k
            hzOuter with hzArm | hzLeg | hzPathRev
        · exact False.elim (hescape_right k z hzEscape (by
            simpa [Tripod.rightToAttach,
              SimpleGraph.Walk.support_reverse] using hzArm))
        · have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp (hlegs_nil k)
          have hzk : z = T.attach k := by simpa [hsupport] using hzLeg
          exact False.elim ((hescape_outside z hzEscape).2
            (by
              rw [hzk, ← (T.leg_nil_iff_boundary_eq_attach k).mp (hlegs_nil k)]
              exact hk))
        · have hzPath : z ∈
              (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).support := by
            simpa [SimpleGraph.Walk.support_reverse] using hzPathRev
          exact P.pathSegmentBetween_support_subset_pathSet hj hk
            (Nat.le_of_lt hjk_order) z hzPath))
  have harm_escape : forall z : V,
      z ∈ (((T.leftToAttach j).takeUntil v hv).reverse.mapLe hgraph).support ->
      z ∈ escape.support -> z = T.left := by
    intro z hzArm hzEscape
    apply hescape_distinct z hzEscape
    apply T.leftToAttach_support_subset_rim j
    apply SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach j) hv
    exact Walk.mem_support_of_mem_reverse_mapLe hgraph
      ((T.leftToAttach j).takeUntil v hv) hzArm
  exact GMIX24SourceProof.Tripod.liftAllNilOfSameMiddleArmTransitionOfRimClean
    P T hgraph hij hik hjk hlegs_nil hi hj hk hij_order hjk_order
    hpath_contacts escape ha hescape_path hescape_outside hu hu_ne_attach
    hright_contact hv hv_ne_attach hleft_contact transition htransition_path
    htransition_outside htransition_clean harm_escape hescape_rim

/-- Same-median exchange when the selected outer-left escape meets the
transition.  The transition lies on the middle rebuilt rim, so the suffix
after the escape's last middle-rim contact is an exact replacement boundary
leg; no transition/escape disjointness is needed. -/
theorem Tripod.liftAllNilOfOuterLeftArmResidualAndIntersectingSameMiddleTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k r : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hr : r = i ∨ r = k)
    (hlegs_nil : forall s : Fin 3, (T.leg s).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts : forall z : V,
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x a u v : V}
    (q : S.graph.Walk x a)
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim r))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact : u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hleft_contact : v ∈ Walk.InternalVertices (T.rim j) ∨ v = T.left)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v)
    (htransition_escape : Exists fun z : V =>
      z ∈ transition.support ∧
        z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support) :
    Nonempty S.Tripod := by
  let escapeData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let escape : S.graph.Walk T.left a := escapeData.walk
  let rim : Fin 3 -> S.graph.Walk T.right (T.attach j) :=
    GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim
      P T hgraph (hlegs_nil j)
      hi hj hk hij_order hjk_order hu hv transition
  have hrj : r ≠ j := by
    rcases hr with rfl | rfl
    · exact hij
    · exact fun h => hjk h.symm
  have hescape_path : escape.IsPath := by
    simpa [escape] using escapeData.walk_isPath
  have hescape_outside : forall z : V,
      z ∈ escape.support -> z ∈ P.outside := by
    simpa [escape] using hq_prefix_outside
  have hescape_right (s : Fin 3) : forall z : V,
      z ∈ escape.support -> z ∈ (T.attachToRight s).support -> False := by
    simpa [escape] using escapeData.disjoint_attachToRight s
  have houter_avoid : forall s : Fin 3, forall z : V,
      z ∈ escape.support ->
      z ∈
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
          P T hgraph hi hj hk
          hij_order hjk_order s).support -> False := by
    simpa [escape] using
      GMIX24SourceProof.Tripod.leftArmPrefixTail_avoids_outerNilMiddleNonNilCommonLeftRims
        P T hgraph hi hj hk
        hij_order hjk_order hx_arm hx_ne_attach hx_internal q hq_clean
        hq_prefix_outside
  have hescape_outer : forall z : V, z ∈ escape.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False := by
    intro z hzEscape hzOuter
    rcases hzOuter with hzZero | hzTwo
    · exact houter_avoid 0 z hzEscape (by
        simpa [rim, Tripod.allNilSameMiddleTransitionRim,
          SimpleGraph.Walk.support_copy] using hzZero)
    · exact houter_avoid 2 z hzEscape (by
        simpa [rim, Tripod.allNilSameMiddleTransitionRim,
          SimpleGraph.Walk.support_copy] using hzTwo)
  have hescape_middle : Exists fun z : V =>
      z ∈ escape.support ∧ z ∈ (rim 1).support := by
    rcases htransition_escape with ⟨z, hzTransition, hzEscape⟩
    refine ⟨z, by simpa [escape] using hzEscape, ?_⟩
    simp only [rim, Tripod.allNilSameMiddleTransitionRim,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inr hzTransition)
  have hescape_ne_rightEnd : forall z : V,
      z ∈ escape.support -> z ≠ T.right := by
    intro z hzEscape hzRight
    exact hescape_right r z hzEscape (by
      have hzOld : T.right ∈ (T.attachToRight r).support :=
        (T.attachToRight r).end_mem_support
      rw [hzRight]
      exact hzOld)
  have hescape_ne_leftEnd : forall z : V,
      z ∈ escape.support -> z ≠ T.attach j := by
    intro z hzEscape hzAttach
    have hzLeft : z = T.left :=
      escapeData.inter_distinct_rim_eq_left hrj z
        (by simpa [escape] using hzEscape)
        (by simpa [hzAttach] using (T.attach_mem_rim j).1)
    exact (T.attach_mem_rim j).2.1 (hzAttach.symm.trans hzLeft)
  have hrim_path : forall s : Fin 3, (rim s).IsPath := by
    intro s
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRim_isPath
        P T hgraph hij hik hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hpath_contacts hu hu_ne_attach
        hv hv_ne_attach transition htransition_path htransition_clean s
  have hrim_disjoint : forall s t : Fin 3, s ≠ t ->
      Disjoint (Walk.InternalVertices (rim s))
        (Walk.InternalVertices (rim t)) := by
    intro s t hst
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionRims_internal_disjoint
        P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
        hi hj hk hij_order hjk_order hpath_contacts hu hright_contact
        hv hleft_contact transition htransition_outside htransition_clean s t hst
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hescape_outside T.left escape.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _
    simpa [qnil] using hz
  have hu_ne_left : u ≠ T.left := by
    intro huLeft
    rcases hright_contact with huInternal | huRight
    · exact huInternal.2.1 huLeft
    · exact T.left_ne_right (huLeft.symm.trans huRight)
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> z = v := by
    intro z hzTransition hzNil
    have hzLeft : z = T.left := by simpa [qnil] using hzNil
    rcases htransition_clean z hzTransition (by
        rw [hzLeft]
        exact T.left_mem_vertexSet) with hzu | hzv
    · exact False.elim (hu_ne_left (hzu.symm.trans hzLeft))
    · exact hzv
  have hbase :=
    GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLegs_meet_rims_only_at_attach
      P T hgraph hij hik hjk (hlegs_nil i) (hlegs_nil j) (hlegs_nil k)
      hi hj hk hij_order hjk_order hpath_contacts qnil hqnil_outside
      hqnil_clean hu hu_ne_attach hv hv_ne_attach hleft_contact transition
      htransition_outside htransition_clean htransition_qnil
  have houter_incidence : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
          (hlegs_nil i) (hlegs_nil k) hi hk escape p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach
        T i k T.left p := by
    intro p s hp z hzLeg hzRim
    fin_cases p
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilSameMiddleTransitionLeg,
        Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilSameMiddleTransitionAttach, rim, qnil] using
        hbase 0 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilSameMiddleTransitionLeg, qnil] using hzLeg)
          (by simpa [rim] using hzRim)
    · exact False.elim (hp rfl)
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilSameMiddleTransitionLeg,
        Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilSameMiddleTransitionAttach, rim, qnil] using
        hbase 2 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilSameMiddleTransitionLeg, qnil] using hzLeg)
          (by simpa [rim] using hzRim)
  apply GMIX24SourceProof.Tripod.liftCheckedRimsAtLastMiddleContact
    P T (hlegs_nil i) (hlegs_nil k) hi hk hij_order hjk_order
    (by
      intro h
      exact T.right_ne_boundary j
        (h.trans ((T.leg_nil_iff_boundary_eq_attach j).mp
          (hlegs_nil j)).symm)) rim hrim_path hrim_disjoint
  · simpa [rim, Tripod.allNilSplicedTransitionAttach,
      Tripod.allNilSameMiddleTransitionAttach] using
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach_mem_rim
        P T hgraph hij hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hu hv hv_ne_attach hleft_contact
        transition 0
  · simpa [rim, Tripod.allNilSplicedTransitionAttach,
      Tripod.allNilSameMiddleTransitionAttach] using
      GMIX24SourceProof.Tripod.allNilSameMiddleTransitionAttach_mem_rim
        P T hgraph hij hjk (hlegs_nil j)
        hi hj hk hij_order hjk_order hu hv hv_ne_attach hleft_contact
        transition 2
  · exact ha
  · exact hescape_path
  · exact hescape_outside
  · exact hescape_middle
  · exact hescape_outer
  · exact hescape_ne_rightEnd
  · exact hescape_ne_leftEnd
  · exact houter_incidence

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
