import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes.CarrierContacts

/-!
Clean transitions between the two sides of an all-collapsed tripod carrier.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- In the all-collapsed branch, an outside last carrier contact is either an
old common end or a genuine internal non-attachment point of one old rim. -/
theorem Tripod.lastCarrierContact_endpoint_or_internal_of_all_legs_nil
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
    (hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    {x : V}
    (hxT : x ∈ T.vertexSet)
    (hxOutside : x ∈ P.outside) :
    (x = T.left ∨ x = T.right) ∨
      Exists fun r : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim r) ∧ x ≠ T.attach r := by
  rcases T.vertexSet_leg_or_rim_internal_or_endpoint hxT with hleg | hrest
  · rcases hleg with ⟨r, hxr⟩
    have hsupport := SimpleGraph.Walk.nil_iff_support_eq.mp (hlegs_nil r)
    have hxAttach : x = T.attach r := by
      simpa [hsupport] using hxr
    exact False.elim (hxOutside.2 (by
      simpa [hxAttach,
        (T.leg_nil_iff_boundary_eq_attach r).mp (hlegs_nil r)] using
        hfeet_path r))
  · rcases hrest with hinternal | hend
    · right
      rcases hinternal with ⟨r, hxr⟩
      refine ⟨r, hxr, ?_⟩
      intro hxAttach
      exact hxOutside.2 (by
        simpa [hxAttach,
          (T.leg_nil_iff_boundary_eq_attach r).mp (hlegs_nil r)] using
          hfeet_path r)
    · exact Or.inl hend

/-- An outside path from the right end to the left end of an all-collapsed
tripod contains a clean transition from a right rim arm to a left rim arm.

Take the first left-arm contact and then the last right-arm contact before it.
Strict support-index inequalities exclude the collapsed attachments and make
the two arm regions disjoint.  This is the consecutive-carrier-contact
normalization used in the final common-end rerouting of GM IX `(2.4)`. -/
theorem Tripod.exists_clean_rightArm_to_leftArm_transition
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hlegs_nil : forall r : Fin 3, (T.leg r).Nil)
    (hfeet_path : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (bridge : S.graph.Walk T.right T.left)
    (hbridge_path : bridge.IsPath)
    (hbridge_outside : forall z : V,
      z ∈ bridge.support -> z ∈ P.outside) :
    Exists fun u : V =>
      Exists fun v : V =>
        Exists fun transition : S.graph.Walk u v =>
          (u = T.right ∨
            Exists fun r : Fin 3 =>
              u ∈ Walk.InternalVertices (T.rim r) ∧
                u ∈ (T.rightToAttach r).support ∧
                  u ≠ T.attach r) ∧
          (v = T.left ∨
            Exists fun r : Fin 3 =>
              v ∈ Walk.InternalVertices (T.rim r) ∧
                v ∈ (T.leftToAttach r).support ∧
                  v ≠ T.attach r) ∧
          u ≠ v ∧ transition.IsPath ∧
          (forall z : V, z ∈ transition.support -> z ∈ P.outside) ∧
          forall z : V, z ∈ transition.support -> z ∈ T.vertexSet ->
            z = u ∨ z = v := by
  classical
  let rightArm : Set V :=
    {z : V | z = T.right ∨
      Exists fun r : Fin 3 =>
        z ∈ Walk.InternalVertices (T.rim r) ∧
          Walk.supportIndex (T.rim r) (T.attach r) <
            Walk.supportIndex (T.rim r) z}
  let leftArm : Set V :=
    {z : V | z = T.left ∨
      Exists fun r : Fin 3 =>
        z ∈ Walk.InternalVertices (T.rim r) ∧
          Walk.supportIndex (T.rim r) z <
            Walk.supportIndex (T.rim r) (T.attach r)}
  have harms_disjoint : Disjoint rightArm leftArm := by
    rw [Set.disjoint_left]
    intro z hzRight hzLeft
    change (z = T.right ∨ Exists fun r : Fin 3 =>
      z ∈ Walk.InternalVertices (T.rim r) ∧
        Walk.supportIndex (T.rim r) (T.attach r) <
          Walk.supportIndex (T.rim r) z) at hzRight
    change (z = T.left ∨ Exists fun r : Fin 3 =>
      z ∈ Walk.InternalVertices (T.rim r) ∧
        Walk.supportIndex (T.rim r) z <
          Walk.supportIndex (T.rim r) (T.attach r)) at hzLeft
    rcases hzRight with hzRight | ⟨r, hzRimRight, _hrightIndex⟩
    · rcases hzLeft with hzLeft | ⟨s, hzRimLeft, _hleftIndex⟩
      · exact T.left_ne_right (hzLeft.symm.trans hzRight)
      · exact hzRimLeft.2.2 (hzRight.trans rfl)
    · rcases hzLeft with hzLeft | ⟨s, hzRimLeft, hleftIndex⟩
      · exact hzRimRight.2.1 hzLeft
      · by_cases hrs : r = s
        · subst s
          omega
        · exact
            Set.disjoint_left.mp (T.rim_internals_disjoint r s hrs)
              hzRimRight hzRimLeft
  have hleftEnd : T.left ∈ leftArm := by
    exact Or.inl rfl
  obtain ⟨v, hvBridge, hvLeft, hfirstLeft⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) hbridge_path leftArm hleftEnd
  let pref : S.graph.Walk T.right v := bridge.takeUntil v hvBridge
  have hpref_path : pref.IsPath := by
    simpa [pref] using hbridge_path.takeUntil hvBridge
  have hrightStart : T.right ∈ rightArm := by
    exact Or.inl rfl
  obtain ⟨u, huPrefix, huRight, htransitionPath, hlastRight,
      htransitionSubset, _htransitionCovers, _huIndex⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hpref_path rightArm hrightStart
  let transition : S.graph.Walk u v := pref.dropUntil u huPrefix
  have htransitionOutside : forall z : V,
      z ∈ transition.support -> z ∈ P.outside := by
    intro z hz
    have hzPrefix : z ∈ pref.support :=
      htransitionSubset z (by simpa [transition] using hz)
    exact hbridge_outside z
      (SimpleGraph.Walk.support_takeUntil_subset bridge hvBridge
        (by simpa [pref] using hzPrefix))
  refine ⟨u, v, transition, ?_, ?_, ?_, ?_, htransitionOutside, ?_⟩
  · change (u = T.right ∨ Exists fun r : Fin 3 =>
        u ∈ Walk.InternalVertices (T.rim r) ∧
          Walk.supportIndex (T.rim r) (T.attach r) <
            Walk.supportIndex (T.rim r) u) at huRight
    rcases huRight with huRight | ⟨r, huInternal, huIndex⟩
    · exact Or.inl huRight
    · refine Or.inr ⟨r, huInternal, ?_, ?_⟩
      · have huAttachToRight :
            u ∈ (T.attachToRight r).support :=
          T.mem_attachToRight_of_attach_supportIndex_le_rim huInternal.1
            (le_of_lt huIndex)
        simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse] using
          huAttachToRight
      · intro huAttach
        have huIndexEq :
            Walk.supportIndex (T.rim r) u =
              Walk.supportIndex (T.rim r) (T.attach r) := by
          simp [huAttach]
        omega
  · change (v = T.left ∨ Exists fun r : Fin 3 =>
        v ∈ Walk.InternalVertices (T.rim r) ∧
          Walk.supportIndex (T.rim r) v <
            Walk.supportIndex (T.rim r) (T.attach r)) at hvLeft
    rcases hvLeft with hvLeft | ⟨r, hvInternal, hvIndex⟩
    · exact Or.inl hvLeft
    · exact Or.inr
        ⟨r, hvInternal,
          T.mem_leftToAttach_of_rim_supportIndex_le_attach hvInternal.1
            (le_of_lt hvIndex),
          by
            intro hvAttach
            have hvIndexEq :
                Walk.supportIndex (T.rim r) v =
                  Walk.supportIndex (T.rim r) (T.attach r) := by
              simp [hvAttach]
            omega⟩
  · intro huv
    subst v
    exact Set.disjoint_left.mp harms_disjoint huRight hvLeft
  · simpa [transition] using htransitionPath
  · intro z hzTransition hzT
    have hzOutside := htransitionOutside z hzTransition
    have hzResidual :=
      GMIX24SourceProof.Tripod.lastCarrierContact_endpoint_or_internal_of_all_legs_nil
        P T hlegs_nil hfeet_path hzT hzOutside
    rcases hzResidual with hzEnd | ⟨r, hzInternal, hz_ne_attach⟩
    · rcases hzEnd with hzLeft | hzRight
      · right
        apply hfirstLeft z
        · have hzPrefix : z ∈ pref.support :=
            htransitionSubset z (by simpa [transition] using hzTransition)
          simpa [pref] using hzPrefix
        · exact Or.inl hzLeft
      · left
        apply hlastRight z
        · simpa [transition] using hzTransition
        · exact Or.inl hzRight
    · have hzSupport : z ∈ (T.rim r).support :=
        Walk.internalVertices_subset_support (T.rim r) hzInternal
      have hattachSupport : T.attach r ∈ (T.rim r).support :=
        Walk.internalVertices_subset_support (T.rim r) (T.attach_mem_rim r)
      have hindex_ne :
          Walk.supportIndex (T.rim r) z ≠
            Walk.supportIndex (T.rim r) (T.attach r) := by
        intro hindex
        exact hz_ne_attach
          (Walk.supportIndex_injective_of_mem hzSupport hindex)
      rcases lt_or_gt_of_ne hindex_ne with hleftIndex | hrightIndex
      · right
        apply hfirstLeft z
        · have hzPrefix : z ∈ pref.support :=
            htransitionSubset z (by simpa [transition] using hzTransition)
          simpa [pref] using hzPrefix
        · exact Or.inr ⟨r, hzInternal, hleftIndex⟩
      · left
        apply hlastRight z
        · simpa [transition] using hzTransition
        · exact Or.inr ⟨r, hzInternal, hrightIndex⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
