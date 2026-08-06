import Schematic.Math.GraphTheory.Minors.Society.General.MiddleToFirstTransition
import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.WalkTransport

/-! Last-to-middle and reversed middle-to-last transitions. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Last-to-middle exchange with the selected boundary escape on the opposite
first rim.  After reversing the cut path this is the checked first-to-middle
theta.  Its unused median-left suffix is prepended to the selected escape, and
the suffix after the last middle-rim contact becomes the middle boundary leg. -/
theorem Tripod.liftAllNilOfOuterFirstLeftArmResidualAndLastToMiddleTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
    (hx_arm : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim i))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach k).support)
    (hu_ne_attach : u ≠ T.attach k)
    (hu_internal : u ∈ Walk.InternalVertices (T.rim k))
    (hv : v ∈ (T.leftToAttach j).support)
    (hv_ne_attach : v ≠ T.attach j)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim j))
    (hmedian_left_prefix_outside : forall z : V,
      z ∈ ((T.leftToAttach j).takeUntil v hv).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Nonempty S.Tripod := by
  let selectedData : T.LeftArmPrefixTailData hgraph hx_arm q :=
    ⟨hx_ne_attach, hx_internal, hq_path, hq_clean⟩
  let selected : S.graph.Walk T.left a := selectedData.walk
  let medianSuffix : S.graph.Walk v T.left :=
    ((T.leftToAttach j).takeUntil v hv).reverse.mapLe hgraph
  let escape : S.graph.Walk v a := medianSuffix.append selected
  let rim : Fin 3 -> S.graph.Walk (T.attach j) u :=
    GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim
      P.reverse T hgraph (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
      (by simpa using hk) (by simpa using hj) (by simpa using hi)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
      hu hv transition
  have hselected_path : selected.IsPath := by
    simpa [selected] using selectedData.walk_isPath
  have hselected_outside : forall z : V,
      z ∈ selected.support -> z ∈ P.outside := by
    simpa [selected] using hq_prefix_outside
  have hmedianSuffix_path : medianSuffix.IsPath := by
    simpa [medianSuffix] using SimpleGraph.Walk.IsPath.mapLe hgraph
      ((T.leftToAttach_isPath j).takeUntil hv).reverse
  have hescape_path : escape.IsPath := by
    dsimp [escape]
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hmedianSuffix_path hselected_path ?_
    intro z hzMedian hzSelected
    apply selectedData.inter_distinct_rim_eq_left hij z
      (by simpa [selected] using hzSelected)
    apply T.leftToAttach_support_subset_rim j
    apply SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach j) hv
    exact Walk.mem_support_of_mem_reverse_mapLe hgraph
      ((T.leftToAttach j).takeUntil v hv) hzMedian
  have hescape_outside : forall z : V,
      z ∈ escape.support -> z ∈ P.reverse.outside := by
    intro z hz
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp
        (by simpa [escape] using hz) with hzMedian | hzSelected
    · have hzPrefix : z ∈ ((T.leftToAttach j).takeUntil v hv).support :=
        Walk.mem_support_of_mem_reverse_mapLe hgraph
          ((T.leftToAttach j).takeUntil v hv) hzMedian
      simpa using hmedian_left_prefix_outside z hzPrefix
    · simpa using hselected_outside z (by simpa [selected] using hzSelected)
  have hcontacts_reverse : forall z : V,
      z ∈ P.reverse.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m := by
    intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  have hrim_path : forall s : Fin 3, (rim s).IsPath := by
    intro s
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_isPath
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hcontacts_reverse hu hu_internal hv transition
        htransition_path htransition_clean s
  have hrim_disjoint : forall s t : Fin 3, s ≠ t ->
      Disjoint (Walk.InternalVertices (rim s))
        (Walk.InternalVertices (rim t)) := by
    intro s t hst
    simpa [rim] using
      GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRims_internal_disjoint
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hcontacts_reverse hu hu_ne_attach hu_internal hv hv_internal transition
        (by
          intro z hz
          simpa using htransition_outside z hz)
        htransition_clean s t hst
  have hv_ne_u : v ≠ u := by
    intro hvu
    exact Set.disjoint_left.mp
      (T.rim_internals_disjoint j k (fun h => hjk h)) hv_internal
      (by simpa [hvu] using hu_internal)
  have hv_rim_one : v ∈ Walk.InternalVertices (rim 1) := by
    simpa [rim, Tripod.allNilSameMiddleTransitionAttach] using
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionAttach_mem_rim
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hu hu_ne_attach hu_internal hv hv_ne_attach hv_internal transition 1)
  let qnil : S.graph.Walk T.left T.left := SimpleGraph.Walk.nil
  have hqnil_outside : forall z : V,
      z ∈ qnil.support -> z ∈ P.reverse.outside := by
    intro z hz
    have hzLeft : z = T.left := by simpa [qnil] using hz
    simpa [hzLeft] using hselected_outside T.left selected.start_mem_support
  have hqnil_clean : forall z : V, z ∈ qnil.support ->
      z ∈ T.vertexSet -> z = T.left := by
    intro z hz _hzT
    simpa [qnil] using hz
  have htransition_qnil : forall z : V, z ∈ transition.support ->
      z ∈ qnil.support -> False := by
    intro z hzTransition hzNil
    have hzLeft : z = T.left := by simpa [qnil] using hzNil
    rcases htransition_clean z hzTransition (by
        rw [hzLeft]
        exact T.left_mem_vertexSet) with hzu | hzv
    · exact hu_internal.2.1 (hzu.symm.trans hzLeft)
    · exact hv_internal.2.1 (hzv.symm.trans hzLeft)
  have hbase :=
    GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionLegs_meet_rims_only_at_attach
      P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
      (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
      (by simpa using hk) (by simpa using hj) (by simpa using hi)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
      ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
      hcontacts_reverse qnil hqnil_outside hqnil_clean hu hu_ne_attach
      hu_internal hv hv_ne_attach hv_internal transition
      (by intro z hz; simpa using htransition_outside z hz)
      htransition_clean htransition_qnil
  have hselected_right (s : Fin 3) : forall z : V,
      z ∈ selected.support -> z ∈ (T.attachToRight s).support -> False := by
    simpa [selected] using selectedData.disjoint_attachToRight s
  have hselected_outer : forall z : V, z ∈ selected.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False := by
    intro z hzSelected hzOuter
    rcases hzOuter with hzZero | hzTwo
    · rcases
        GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_zero_support_cases
          P.reverse T hgraph (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
          (by simpa using hk) (by simpa using hj) (by simpa using hi)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
          hu hv transition (by simpa [rim] using hzZero) with hzPath | hzArm
      · exact (hselected_outside z hzSelected).2 (by
          simpa using P.reverse.pathSegmentBetween_support_subset_pathSet
            (by simpa using hk) (by simpa using hj)
            (Nat.le_of_lt
              ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order))
            z hzPath)
      · exact hselected_right k z hzSelected
          (SimpleGraph.Walk.support_takeUntil_subset
            (T.attachToRight k) (by
              simpa [Tripod.rightToAttach,
                SimpleGraph.Walk.support_reverse] using hu) hzArm)
    · rcases
        GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionRim_two_support_cases
          P.reverse T hgraph (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
          (by simpa using hk) (by simpa using hj) (by simpa using hi)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
          ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
          hu hv transition (by simpa [rim] using hzTwo) with
        hzPath | hzArmI | hzRightK
      · exact (hselected_outside z hzSelected).2 (by
          simpa using P.reverse.pathSegmentBetween_support_subset_pathSet
            (by simpa using hj) (by simpa using hi)
            (Nat.le_of_lt
              ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order))
            z hzPath)
      · exact hselected_right i z hzSelected hzArmI
      · have hzOld : z ∈ (T.rightToAttach k).support :=
          SimpleGraph.Walk.support_takeUntil_subset
            (T.rightToAttach k) hu hzRightK
        exact hselected_right k z hzSelected (by
          simpa [Tripod.rightToAttach,
            SimpleGraph.Walk.support_reverse] using hzOld)
  have hmedian_outer : forall z : V, z ∈ medianSuffix.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False := by
    intro z hzMedian hzOuter
    have hzLeg : z ∈
        (GMIX24SourceProof.Tripod.allNilSameMiddleTransitionLeg
          P.reverse T hgraph (hlegs_nil k) (hlegs_nil i)
          (by simpa using hk) (by simpa using hi) hv qnil 1).support := by
      rw [Tripod.allNilSameMiddleTransitionLeg]
      exact (SimpleGraph.Walk.mem_support_append_iff _ _).2
        (Or.inl (by simpa [medianSuffix] using hzMedian))
    rcases hzOuter with hzZero | hzTwo
    · have hzv : z = v := by
        simpa [Tripod.allNilSameMiddleTransitionAttach] using
          hbase 1 0 z hzLeg (by simpa [rim] using hzZero)
      have hvOuter : v ∈ Walk.InternalVertices (rim 0) :=
        ⟨by simpa [hzv] using hzZero, hv_ne_attach, hv_ne_u⟩
      exact Set.disjoint_left.mp (hrim_disjoint 1 0 (by decide))
        hv_rim_one hvOuter
    · have hzv : z = v := by
        simpa [Tripod.allNilSameMiddleTransitionAttach] using
          hbase 1 2 z hzLeg (by simpa [rim] using hzTwo)
      have hvOuter : v ∈ Walk.InternalVertices (rim 2) :=
        ⟨by simpa [hzv] using hzTwo, hv_ne_attach, hv_ne_u⟩
      exact Set.disjoint_left.mp (hrim_disjoint 1 2 (by decide))
        hv_rim_one hvOuter
  have hescape_outer : forall z : V, z ∈ escape.support ->
      z ∈ (rim 0).support ∨ z ∈ (rim 2).support -> False := by
    intro z hzEscape hzOuter
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp
        (by simpa [escape] using hzEscape) with hzMedian | hzSelected
    · exact hmedian_outer z (by simpa [medianSuffix] using hzMedian) hzOuter
    · exact hselected_outer z (by simpa [selected] using hzSelected) hzOuter
  have hescape_ne_leftEnd : forall z : V,
      z ∈ escape.support -> z ≠ T.attach j := by
    intro z hz h
    exact hescape_outer z hz (Or.inl (by
      rw [h]
      exact (rim 0).start_mem_support))
  have hescape_ne_rightEnd : forall z : V,
      z ∈ escape.support -> z ≠ u := by
    intro z hz h
    exact hescape_outer z hz (Or.inl (by
      rw [h]
      exact (rim 0).end_mem_support))
  have houter_incidence : forall p s : Fin 3, p ≠ 1 -> forall z : V,
      z ∈
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P.reverse T
          (hlegs_nil k) (hlegs_nil i) (by simpa using hk) (by simpa using hi)
          escape p).support ->
      z ∈ (rim s).support ->
      z = GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach
        T k i v p := by
    intro p s hp z hzLeg hzRim
    fin_cases p
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilSameMiddleTransitionLeg,
        Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilSameMiddleTransitionAttach, qnil] using
        hbase 0 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilSameMiddleTransitionLeg, qnil] using hzLeg)
          (by simpa [rim] using hzRim)
    · exact False.elim (hp rfl)
    · simpa [Tripod.allNilSplicedTransitionLeg,
        Tripod.allNilSameMiddleTransitionLeg,
        Tripod.allNilSplicedTransitionAttach,
        Tripod.allNilSameMiddleTransitionAttach, qnil] using
        hbase 2 s z (by
          simpa [Tripod.allNilSplicedTransitionLeg,
            Tripod.allNilSameMiddleTransitionLeg, qnil] using hzLeg)
          (by simpa [rim] using hzRim)
  apply GMIX24SourceProof.Tripod.liftCheckedRimsAtLastMiddleContact
    P.reverse T (hlegs_nil k) (hlegs_nil i) (by simpa using hk)
    (by simpa using hi)
    ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
    ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
    (by
      intro hju
      exact T.attach_not_mem_rim_of_ne (i := j) (j := k) hjk
        (by simpa [hju] using hu_internal.1)) rim hrim_path hrim_disjoint
  · simpa [rim, Tripod.allNilSameMiddleTransitionAttach] using
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionAttach_mem_rim
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hu hu_ne_attach hu_internal hv hv_ne_attach hv_internal transition 0)
  · simpa [rim, Tripod.allNilSameMiddleTransitionAttach] using
      (GMIX24SourceProof.Tripod.allNilFirstToMiddleTransitionAttach_mem_rim
        P.reverse T hgraph (fun h => hjk h.symm) (fun h => hik h.symm)
        (fun h => hij h.symm) (hlegs_nil k) (hlegs_nil j) (hlegs_nil i)
        (by simpa using hk) (by simpa using hj) (by simpa using hi)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order)
        ((GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order)
        hu hu_ne_attach hu_internal hv hv_ne_attach hv_internal transition 2)
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hescape_path
  · exact hescape_outside
  · exact ⟨v, escape.start_mem_support, hv_rim_one.1⟩
  · exact hescape_outer
  · exact hescape_ne_leftEnd
  · exact hescape_ne_rightEnd
  · exact houter_incidence

/-- Cut-path-reversed form of the selected-first last-contact exchange.  This
closes the median-to-last cell without introducing another theta. -/
theorem Tripod.liftAllNilOfOuterLastLeftArmResidualAndMiddleToLastTransition
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
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
    (hx_arm : x ∈ (T.leftToAttach k).support)
    (hx_ne_attach : x ≠ T.attach k)
    (hx_internal : x ∈ Walk.InternalVertices (T.rim k))
    (ha : a ∈ P.leftBoundaryArc ∨ a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean : forall z : V, z ∈ q.support ->
      z ∈ T.vertexSet -> z = x)
    (hq_prefix_outside : forall z : V,
      z ∈ (T.leftArmPrefixTail hgraph hx_arm q).support -> z ∈ P.outside)
    (hu : u ∈ (T.rightToAttach j).support)
    (hu_ne_attach : u ≠ T.attach j)
    (hright_contact :
      u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right)
    (hright_prefix_outside : forall z : V,
      z ∈ ((T.rightToAttach j).takeUntil u hu).support -> z ∈ P.outside)
    (hv : v ∈ (T.leftToAttach k).support)
    (hv_ne_attach : v ≠ T.attach k)
    (hv_internal : v ∈ Walk.InternalVertices (T.rim k))
    (hleft_prefix_outside : forall z : V,
      z ∈ ((T.leftToAttach k).takeUntil v hv).support -> z ∈ P.outside)
    (transition : S.graph.Walk u v)
    (htransition_path : transition.IsPath)
    (htransition_outside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside)
    (htransition_clean : forall z : V, z ∈ transition.support ->
      z ∈ T.vertexSet -> z = u ∨ z = v) :
    Nonempty S.Tripod := by
  apply
    GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToFirstTransition
      (i := k) (j := j) (k := i) (q := q) (hx_arm := hx_arm)
      (u := u) (v := v) (hu := hu) (hv := hv) (transition := transition)
      P.reverse T hgraph
      (fun h => hjk h.symm) (fun h => hik h.symm) (fun h => hij h.symm)
      (Or.inl rfl) hlegs_nil
  · simpa using hk
  · simpa using hj
  · simpa using hi
  · exact (GMIX24CutPath.reverse_supportIndex_lt_iff P hk hj).2 hjk_order
  · exact (GMIX24CutPath.reverse_supportIndex_lt_iff P hj hi).2 hij_order
  · intro z hzPath hzT
    exact hpath_contacts z (by simpa using hzPath) hzT
  · exact hx_ne_attach
  · exact hx_internal
  · rcases ha with ha | ha
    · exact Or.inr (by simpa using ha)
    · exact Or.inl (by simpa using ha)
  · exact hq_path
  · exact hq_clean
  · intro z hz
    simpa using hq_prefix_outside z hz
  · exact hu_ne_attach
  · exact hright_contact
  · intro z hz
    simpa using hright_prefix_outside z hz
  · exact hv_ne_attach
  · exact hv_internal
  · intro z hz
    simpa using hleft_prefix_outside z hz
  · exact htransition_path
  · intro z hz
    simpa using htransition_outside z hz
  · exact htransition_clean

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
