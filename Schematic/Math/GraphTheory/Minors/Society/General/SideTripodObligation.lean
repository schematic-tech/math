import Schematic.Math.GraphTheory.Minors.Society.General.CleanTransitions

/-! The direct left-side tripod contradiction from the GM IX `(2.4)` source proof. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

theorem left_side_tripod_obligation
    [Fintype V] [Fintype (Sym2 V)]
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  intro hT
  obtain ⟨T, hsource_clean, hmax, hminimal⟩ :=
    Tripod.exists_footCount_maximal_linkageLength_minimal_sourceClean_tripod
      P.pathSet hT
  by_cases hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False
  · /-
    This is the source paragraph after its three `Q_i` contacts with the cut
    path have been normalized.  The direct noncollapsed constructors force
    all three legs to be nil.  Cross-freeness then puts the old theta ends in
    one component of `G - V(P)`, and the two paths supplied by caughtness are
    shortened after their last old-theta contacts.
    -/
    obtain ⟨hlegs_nil, hfeet_path, C, hleftC, hrightC,
        x, a, qLeft, _hxT, ha,
        hqLeft_path, hqLeft_component, _hqLeft_side, hqLeft_clean,
        hx_residual, y, b, qRight, _hyT, hb, hqRight_path,
        hqRight_component, _hqRight_side, hqRight_clean,
        hy_residual⟩ :=
      left_side_tripod_common_component_clean_residual_tails_of_no_hidden_contact
        (S := S) hno_cross hno_tripod P T hsource_clean hno_hidden
    let hpath_contacts :
        forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m :=
      GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
        P hno_cross T hsource_clean hno_hidden
    obtain ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩ :=
      P.exists_ordered_tripod_boundary_indices T hfeet_path
    have hqLeft_outside :
        forall z : V, z ∈ qLeft.support -> z ∈ P.outside := by
      intro z hz
      exact
        induceComponentSupport_subset (G := S.graph) C
          (hqLeft_component z hz)
    have hqRight_outside :
        forall z : V, z ∈ qRight.support -> z ∈ P.outside := by
      intro z hz
      exact
        induceComponentSupport_subset (G := S.graph) C
          (hqRight_component z hz)
    obtain ⟨componentBridge, hcomponentBridge_path,
        hcomponentBridge_component⟩ :=
      connected_induce_exists_path_support_subset
        (G := S.graph)
        (induceComponentSupport_connected (G := S.graph) C)
        hrightC hleftC
    have hcomponentBridge_outside : forall z : V,
        z ∈ componentBridge.support -> z ∈ P.outside := by
      intro z hz
      exact induceComponentSupport_subset (G := S.graph) C
        (hcomponentBridge_component z hz)
    have hx_residual' :
        (x = T.left ∨ x = T.right) ∨
          Exists fun r : Fin 3 =>
            r ≠ j ∧ x ∈ Walk.InternalVertices (T.rim r) ∧
              x ≠ T.attach r := by
      rcases hx_residual with hxEnd | ⟨r, hxInt, hxAttach⟩
      · exact Or.inl hxEnd
      · by_cases hrj : r = j
        · subst r
          exact False.elim
            (hno_tripod
              (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
                P hno_cross T hij hik hjk qLeft (Or.inr hxInt) ha
                (fun r : Fin 3 => hfeet_path (fin3Order i j k r))
                hqLeft_path hij_order hjk_order hqLeft_outside
                hpath_contacts hqLeft_clean))
        · exact Or.inr ⟨r, hrj, hxInt, hxAttach⟩
    have hy_residual' :
        (y = T.left ∨ y = T.right) ∨
          Exists fun r : Fin 3 =>
            r ≠ j ∧ y ∈ Walk.InternalVertices (T.rim r) ∧
              y ≠ T.attach r := by
      rcases hy_residual with hyEnd | ⟨r, hyInt, hyAttach⟩
      · exact Or.inl hyEnd
      · by_cases hrj : r = j
        · subst r
          exact False.elim
            (hno_tripod
              (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
                P hno_cross T hij hik hjk qRight (Or.inr hyInt) hb
                (fun r : Fin 3 => hfeet_path (fin3Order i j k r))
                hqRight_path hij_order hjk_order hqRight_outside
                hpath_contacts hqRight_clean))
        · exact Or.inr ⟨r, hrj, hyInt, hyAttach⟩
    by_cases hdistinct_ends :
        (x = T.left ∨ x = T.right) ∧
          (y = T.left ∨ y = T.right) ∧ x ≠ y
    · exact
        Tripod.distinctEndpointResidualTails_impossible
          P T
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
          hij hik hjk (hfeet_path i) (hfeet_path k)
          (hlegs_nil i) (hlegs_nil k) hij_order hjk_order
          hpath_contacts qLeft qRight hdistinct_ends.1
          hdistinct_ends.2.1 hdistinct_ends.2.2 ha hb
          hqLeft_path hqRight_path hqLeft_outside hqRight_outside
          hqLeft_clean hqRight_clean hno_cross hno_tripod
    · /-
      Remaining source return configuration.  In the no-hidden branch the two
      last contacts are equal old ends or at least one is internal to one of
      the two outer old rims; the median-rim alternatives were eliminated
      above by the checked ordered-tail constructor.  In the hidden branch
      lexicographic minimality gives the same
      endpoint/internal-collapsed-rim alternatives.  The final bridge exchange
      must treat these together, exactly as in the printed "common end" line.
      -/
      clear hx_residual hy_residual
      by_cases hx_left : x = T.left
      · subst x
        exact hno_tripod
          (GMIX24SourceProof.Tripod.liftAllNilOfOutsideRightToLeftBridge
            P T
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hij hik hjk hlegs_nil (hfeet_path i) (hfeet_path j)
            (hfeet_path k) hij_order hjk_order hpath_contacts
            qLeft ha hqLeft_path hqLeft_outside hqLeft_clean
            (fun r w hw hne =>
              GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
                P hno_cross T hpath_contacts hw hne)
            (fun r w hw hne =>
              GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                P hno_cross T hpath_contacts hw hne)
            componentBridge hcomponentBridge_path hcomponentBridge_outside)
      · rcases hx_residual' with hxEnd | hxOuter
        · have hx_right : x = T.right := hxEnd.resolve_left hx_left
          subst x
          let U :
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod :=
            T.flip
          let reverseBridge : S.graph.Walk U.right U.left :=
            componentBridge.reverse
          have hpath_contacts_U : forall z : V,
              z ∈ P.pathSet -> z ∈ U.vertexSet ->
                Exists fun m : Fin 3 => z = U.boundary m := by
            intro z hzPath hzU
            rcases hpath_contacts z hzPath (by simpa [U] using hzU) with ⟨m, hm⟩
            exact ⟨m, by simpa [U] using hm⟩
          exact hno_tripod
            (GMIX24SourceProof.Tripod.liftAllNilOfOutsideRightToLeftBridge
              P U
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
              hij hik hjk (by intro r; simpa [U] using hlegs_nil r)
              (by simpa [U] using hfeet_path i)
              (by simpa [U] using hfeet_path j)
              (by simpa [U] using hfeet_path k)
              (by simpa [U] using hij_order) (by simpa [U] using hjk_order)
              hpath_contacts_U qLeft ha hqLeft_path hqLeft_outside
              (by
                intro z hzq hzU
                exact hqLeft_clean z hzq (by simpa [U] using hzU))
              (fun r w hw hne =>
                GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
                  P hno_cross U hpath_contacts_U hw hne)
              (fun r w hw hne =>
                GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                  P hno_cross U hpath_contacts_U hw hne)
              reverseBridge (by
                change componentBridge.reverse.IsPath
                exact hcomponentBridge_path.reverse)
              (by
                intro z hz
                have hz' : z ∈ componentBridge.reverse.support := by
                  simpa only [reverseBridge] using hz
                rw [SimpleGraph.Walk.support_reverse] at hz'
                exact hcomponentBridge_outside z (List.mem_reverse.mp hz')))
        · /- The selected clean escape starts internally on one of the two
          outer old rims. -/
          rcases hxOuter with ⟨r, hr_ne_j, hxInternal, hx_ne_attach⟩
          have hr_outer : r = i ∨ r = k := by
            rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
            · exact Or.inl hri
            · rcases hrjk with hrj | hrk
              · exact False.elim (hr_ne_j hrj)
              · exact Or.inr hrk
          have hx_arm :
              x ∈ (T.leftToAttach r).support ∨
                x ∈ (T.attachToRight r).support := by
            have hsplit := Nat.le_total
              (Walk.supportIndex (T.rim r) x)
              (Walk.supportIndex (T.rim r) (T.attach r))
            rcases hsplit with hbefore | hafter
            · exact Or.inl
                (T.mem_leftToAttach_of_rim_supportIndex_le_attach
                  hxInternal.1 hbefore)
            · exact Or.inr
                (T.mem_attachToRight_of_attach_supportIndex_le_rim
                  hxInternal.1 hafter)
          by_cases hcomponentBridge_clean : forall z : V,
              z ∈ componentBridge.support -> z ∈ T.vertexSet ->
                z = T.right ∨ z = T.left
          · rcases hx_arm with hxLeftArm | hxRightArm
            · exact hno_tripod
                (GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndCarrierCleanBridge
                  P hno_cross T hij hik hjk hr_outer hlegs_nil
                  (hfeet_path i) (hfeet_path j) (hfeet_path k)
                  hij_order hjk_order hpath_contacts qLeft hxLeftArm
                  hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                  hqLeft_clean componentBridge hcomponentBridge_path
                  hcomponentBridge_outside hcomponentBridge_clean)
            · let reverseBridge : S.graph.Walk T.left T.right :=
                componentBridge.reverse
              have hreverseBridge_path : reverseBridge.IsPath := by
                simpa [reverseBridge] using hcomponentBridge_path.reverse
              have hreverseBridge_outside : forall z : V,
                  z ∈ reverseBridge.support -> z ∈ P.outside := by
                intro z hz
                have hz' : z ∈ componentBridge.reverse.support := by
                  simpa only [reverseBridge] using hz
                rw [SimpleGraph.Walk.support_reverse] at hz'
                exact hcomponentBridge_outside z (List.mem_reverse.mp hz')
              have hreverseBridge_clean : forall z : V,
                  z ∈ reverseBridge.support -> z ∈ T.vertexSet ->
                    z = T.left ∨ z = T.right := by
                intro z hz hzT
                have hz' : z ∈ componentBridge.reverse.support := by
                  simpa only [reverseBridge] using hz
                rw [SimpleGraph.Walk.support_reverse] at hz'
                rcases hcomponentBridge_clean z (List.mem_reverse.mp hz') hzT with
                  hzRight | hzLeft
                · exact Or.inr hzRight
                · exact Or.inl hzLeft
              exact hno_tripod
                (GMIX24SourceProof.Tripod.liftAllNilOfOuterRightArmResidualAndCarrierCleanBridge
                  P hno_cross T hij hik hjk hr_outer hlegs_nil
                  (hfeet_path i) (hfeet_path j) (hfeet_path k)
                  hij_order hjk_order hpath_contacts qLeft hxRightArm
                  hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                  hqLeft_clean reverseBridge hreverseBridge_path
                  hreverseBridge_outside hreverseBridge_clean)
          · rcases
                GMIX24SourceProof.Tripod.exists_clean_rightArm_to_leftArm_transition
                  P T hlegs_nil hfeet_path componentBridge
                  hcomponentBridge_path hcomponentBridge_outside with
              ⟨u, v, transition, huContact, hvContact, huv,
                htransitionPath, htransitionOutside, htransitionClean⟩
            /- The remaining finite exchange has an internal outer-rim escape
            `x -> a` and one consecutive carrier-clean transition `u -> v`.
            Its endpoints are each either an old common end or a strict arm
            contact; no arbitrary linkage or matching remains. -/
            let hgraph :=
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            by_cases hleft_resolved :
                (u = T.right ∧ v = T.left) ∨
                  Exists fun hxLeftArm : x ∈ (T.leftToAttach r).support =>
                    (forall z : V, z ∈ transition.support ->
                      z ∈ (T.leftArmPrefixTail hgraph hxLeftArm qLeft).support ->
                        False) ∧
                    (u = T.right ∨
                      (u ∈ Walk.InternalVertices (T.rim j) ∧
                        u ∈ (T.rightToAttach j).support ∧
                          u ≠ T.attach j)) ∧
                    (v ∈ Walk.InternalVertices (T.rim j) ∧
                      v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j)
            · rcases hleft_resolved with hfullEnds | hsame_middle_left
              · rcases hfullEnds with ⟨huRight, hvLeft⟩
                subst u
                subst v
                rcases hx_arm with hxLeftArm | hxRightArm
                · exact hno_tripod
                    (GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndCarrierCleanBridge
                      P hno_cross T hij hik hjk hr_outer hlegs_nil
                      (hfeet_path i) (hfeet_path j) (hfeet_path k)
                      hij_order hjk_order hpath_contacts qLeft hxLeftArm
                      hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                      hqLeft_clean transition htransitionPath
                      htransitionOutside htransitionClean)
                · exact hno_tripod
                    (GMIX24SourceProof.Tripod.liftAllNilOfOuterRightArmResidualAndCarrierCleanBridge
                      P hno_cross T hij hik hjk hr_outer hlegs_nil
                      (hfeet_path i) (hfeet_path j) (hfeet_path k)
                      hij_order hjk_order hpath_contacts qLeft hxRightArm
                      hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                      hqLeft_clean transition.reverse htransitionPath.reverse
                      (by
                        intro z hz
                        apply htransitionOutside z
                        simpa [SimpleGraph.Walk.support_reverse] using hz)
                      (by
                        intro z hz hzT
                        have hzTransition : z ∈ transition.support := by
                          simpa [SimpleGraph.Walk.support_reverse] using hz
                        rcases htransitionClean z hzTransition hzT with
                          hzRight | hzLeft
                        · exact Or.inr hzRight
                        · exact Or.inl hzLeft))
              · rcases hsame_middle_left with
                  ⟨hxLeftArm, htransition_qLeft, huMiddle, hvInternal,
                    hvArm, hvNe⟩
                have huArm : u ∈ (T.rightToAttach j).support := by
                  rcases huMiddle with huRight | huStrict
                  · rw [huRight]
                    exact (T.rightToAttach j).start_mem_support
                  · exact huStrict.2.1
                have huNe : u ≠ T.attach j := by
                  rcases huMiddle with huRight | huStrict
                  · intro huAttach
                    exact T.right_ne_boundary j
                      (huRight.symm.trans (huAttach.trans
                        ((T.leg_nil_iff_boundary_eq_attach j).mp
                          (hlegs_nil j)).symm))
                  · exact huStrict.2.2
                have huInternalOrRight :
                    u ∈ Walk.InternalVertices (T.rim j) ∨ u = T.right := by
                  rcases huMiddle with huRight | huStrict
                  · exact Or.inr huRight
                  · exact Or.inl huStrict.1
                exact hno_tripod
                  (GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndDisjointSameMiddleTransition
                    P hno_cross T hij hik hjk hr_outer hlegs_nil
                    (hfeet_path i) (hfeet_path j) (hfeet_path k)
                    hij_order hjk_order hpath_contacts qLeft hxLeftArm
                    hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                    hqLeft_clean huArm huNe huInternalOrRight hvArm hvNe
                    hvInternal transition htransitionPath htransitionOutside
                    htransitionClean (by simpa [hgraph] using htransition_qLeft))
            · by_cases hfirst_last_left :
                  r = i ∧
                    Exists fun hxFirst : x ∈ (T.leftToAttach i).support =>
                      (forall z : V, z ∈ transition.support ->
                        z ∈ (T.leftArmPrefixTail hgraph hxFirst qLeft).support ->
                          False) ∧
                      (u = T.right ∨
                        (u ∈ Walk.InternalVertices (T.rim i) ∧
                          u ∈ (T.rightToAttach i).support ∧
                            u ≠ T.attach i)) ∧
                      (v ∈ Walk.InternalVertices (T.rim k) ∧
                        v ∈ (T.leftToAttach k).support ∧ v ≠ T.attach k)
              · rcases hfirst_last_left with
                  ⟨hri, hxFirst, htransition_qFirst, huFirst,
                    hvInternal, hvArm, hvNe⟩
                subst r
                have huArm : u ∈ (T.rightToAttach i).support := by
                  rcases huFirst with huRight | huStrict
                  · rw [huRight]
                    exact (T.rightToAttach i).start_mem_support
                  · exact huStrict.2.1
                have huInternalOrRight :
                    u ∈ Walk.InternalVertices (T.rim i) ∨ u = T.right := by
                  rcases huFirst with huRight | huStrict
                  · exact Or.inr huRight
                  · exact Or.inl huStrict.1
                exact hno_tripod
                  (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToLastTransition
                    P hno_cross T hij hik hjk hlegs_nil
                    (hfeet_path i) (hfeet_path j) (hfeet_path k)
                    hij_order hjk_order hpath_contacts qLeft hxFirst
                    hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                    hqLeft_clean huArm huInternalOrRight hvArm hvNe hvInternal
                    transition htransitionPath htransitionOutside
                    htransitionClean
                    (by simpa [hgraph] using htransition_qFirst))
              · by_cases hfirst_middle_left :
                    r = i ∧
                      Exists fun hxFirst : x ∈ (T.leftToAttach i).support =>
                        (forall z : V, z ∈ transition.support ->
                          z ∈ (T.leftArmPrefixTail hgraph hxFirst qLeft).support ->
                            False) ∧
                        (u ∈ Walk.InternalVertices (T.rim i) ∧
                          u ∈ (T.rightToAttach i).support ∧
                            u ≠ T.attach i) ∧
                        (v ∈ Walk.InternalVertices (T.rim j) ∧
                          v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j)
                · rcases hfirst_middle_left with
                    ⟨hri, hxFirst, htransition_qFirst,
                      ⟨huInternal, huArm, huNe⟩,
                      ⟨hvInternal, hvArm, hvNe⟩⟩
                  subst r
                  exact hno_tripod
                    (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndDisjointFirstToMiddleTransition
                      P T hgraph hij hik hjk hlegs_nil
                      (hfeet_path i) (hfeet_path j) (hfeet_path k)
                      hij_order hjk_order hpath_contacts qLeft hxFirst
                      hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                      hqLeft_clean
                      (by
                        simpa [hgraph] using
                          GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                            P hno_cross T hpath_contacts hxFirst hx_ne_attach
                            qLeft hqLeft_outside)
                      huArm huNe huInternal hvArm hvNe hvInternal
                      transition htransitionPath htransitionOutside
                      htransitionClean
                      (by simpa [hgraph] using htransition_qFirst))
                · by_cases hlast_middle_left :
                      r = k ∧
                        Exists fun hxLast : x ∈ (T.leftToAttach k).support =>
                          (forall z : V, z ∈ transition.support ->
                            z ∈ (T.leftArmPrefixTail hgraph hxLast qLeft).support ->
                              False) ∧
                          (u ∈ Walk.InternalVertices (T.rim k) ∧
                            u ∈ (T.rightToAttach k).support ∧
                              u ≠ T.attach k) ∧
                          (v ∈ Walk.InternalVertices (T.rim j) ∧
                            v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j)
                  · rcases hlast_middle_left with
                      ⟨hrk, hxLast, htransition_qLast,
                        ⟨huInternal, huArm, huNe⟩,
                        ⟨hvInternal, hvArm, hvNe⟩⟩
                    subst r
                    exact hno_tripod
                      (GMIX24SourceProof.Tripod.liftAllNilOfOuterLastLeftArmResidualAndDisjointLastToMiddleTransition
                        P T hgraph hij hik hjk hlegs_nil
                        (hfeet_path i) (hfeet_path j) (hfeet_path k)
                        hij_order hjk_order hpath_contacts qLeft hxLast
                        hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                        hqLeft_clean
                        (by
                          simpa [hgraph] using
                            GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                              P hno_cross T hpath_contacts hxLast hx_ne_attach
                              qLeft hqLeft_outside)
                        huArm huNe huInternal hvArm hvNe hvInternal
                        transition htransitionPath htransitionOutside
                        htransitionClean
                        (by simpa [hgraph] using htransition_qLast))
                  · by_cases hmiddle_first_right :
                        r = i ∧
                          Exists fun hxFlip : x ∈ (T.flip.leftToAttach i).support =>
                            (forall z : V, z ∈ transition.reverse.support ->
                              z ∈ (T.flip.leftArmPrefixTail hgraph hxFlip qLeft).support ->
                                False) ∧
                            (u ∈ Walk.InternalVertices (T.rim j) ∧
                              u ∈ (T.rightToAttach j).support ∧
                                u ≠ T.attach j) ∧
                            (v ∈ Walk.InternalVertices (T.rim i) ∧
                              v ∈ (T.leftToAttach i).support ∧ v ≠ T.attach i)
                    · rcases hmiddle_first_right with
                        ⟨hri, hxFlip, htransition_qFlip,
                          ⟨huInternal, huArm, huNe⟩,
                          ⟨hvInternal, hvArm, hvNe⟩⟩
                      subst r
                      have hpath_contacts_flip : forall z : V,
                          z ∈ P.pathSet -> z ∈ T.flip.vertexSet ->
                            Exists fun m : Fin 3 => z = T.flip.boundary m := by
                        intro z hzPath hzFlip
                        rcases hpath_contacts z hzPath (by simpa using hzFlip) with
                          ⟨m, hm⟩
                        exact ⟨m, by simpa using hm⟩
                      exact hno_tripod
                        (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstRightArmResidualAndDisjointMiddleToFirstTransition
                          P T hgraph hij hik hjk hlegs_nil
                          (hfeet_path i) (hfeet_path j) (hfeet_path k)
                          hij_order hjk_order hpath_contacts qLeft hxFlip
                          hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                          hqLeft_clean
                          (by
                            simpa [hgraph] using
                              GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                P hno_cross T.flip hpath_contacts_flip hxFlip
                                (by simpa using hx_ne_attach) qLeft hqLeft_outside)
                          huArm huNe huInternal hvArm hvNe hvInternal
                          transition htransitionPath htransitionOutside
                          htransitionClean
                          (by simpa [hgraph] using htransition_qFlip))
                    · by_cases hmiddle_last_right :
                          r = k ∧
                            Exists fun hxFlip : x ∈ (T.flip.leftToAttach k).support =>
                              (forall z : V, z ∈ transition.reverse.support ->
                                z ∈ (T.flip.leftArmPrefixTail hgraph hxFlip qLeft).support ->
                                  False) ∧
                              (u ∈ Walk.InternalVertices (T.rim j) ∧
                                u ∈ (T.rightToAttach j).support ∧
                                  u ≠ T.attach j) ∧
                              (v ∈ Walk.InternalVertices (T.rim k) ∧
                                v ∈ (T.leftToAttach k).support ∧ v ≠ T.attach k)
                      · rcases hmiddle_last_right with
                          ⟨hrk, hxFlip, htransition_qFlip,
                            ⟨huInternal, huArm, huNe⟩,
                            ⟨hvInternal, hvArm, hvNe⟩⟩
                        subst r
                        have hpath_contacts_flip : forall z : V,
                            z ∈ P.pathSet -> z ∈ T.flip.vertexSet ->
                              Exists fun m : Fin 3 => z = T.flip.boundary m := by
                          intro z hzPath hzFlip
                          rcases hpath_contacts z hzPath (by simpa using hzFlip) with
                            ⟨m, hm⟩
                          exact ⟨m, by simpa using hm⟩
                        exact hno_tripod
                          (GMIX24SourceProof.Tripod.liftAllNilOfOuterLastRightArmResidualAndDisjointMiddleToLastTransition
                            P T hgraph hij hik hjk hlegs_nil
                            (hfeet_path i) (hfeet_path j) (hfeet_path k)
                            hij_order hjk_order hpath_contacts qLeft hxFlip
                            hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                            hqLeft_clean
                            (by
                              simpa [hgraph] using
                                GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                  P hno_cross T.flip hpath_contacts_flip hxFlip
                                  (by simpa using hx_ne_attach) qLeft hqLeft_outside)
                            huArm huNe huInternal hvArm hvNe hvInternal
                            transition htransitionPath htransitionOutside
                            htransitionClean
                            (by simpa [hgraph] using htransition_qFlip))
                      · by_cases hsame_middle_right :
                            Exists fun hxFlipArm : x ∈ (T.flip.leftToAttach r).support =>
                              (forall z : V, z ∈ transition.reverse.support ->
                                z ∈ (T.flip.leftArmPrefixTail hgraph hxFlipArm qLeft).support ->
                                  False) ∧
                              (u ∈ Walk.InternalVertices (T.rim j) ∧
                                u ∈ (T.rightToAttach j).support ∧ u ≠ T.attach j) ∧
                              (v ∈ Walk.InternalVertices (T.rim j) ∧
                                v ∈ (T.leftToAttach j).support ∧ v ≠ T.attach j)
                        · rcases hsame_middle_right with
                            ⟨hxFlipArm, htransition_qRight,
                              ⟨huInternal, huArm, huNe⟩,
                              ⟨hvInternal, hvArm, hvNe⟩⟩
                          exact hno_tripod
                            (GMIX24SourceProof.Tripod.liftAllNilOfOuterRightArmResidualAndDisjointSameMiddleTransition
                              P hno_cross T hij hik hjk hr_outer hlegs_nil
                              (hfeet_path i) (hfeet_path j) (hfeet_path k)
                              hij_order hjk_order hpath_contacts qLeft hxFlipArm
                              hx_ne_attach hxInternal ha hqLeft_path hqLeft_outside
                              hqLeft_clean huArm huNe huInternal hvArm hvNe hvInternal
                              transition htransitionPath htransitionOutside
                              htransitionClean
                              (by simpa [hgraph] using htransition_qRight))
                        · by_cases hfirst_to_left :
                              r = i ∧
                                Exists fun hxFirst :
                                    x ∈ (T.leftToAttach i).support =>
                                  (forall z : V, z ∈ transition.support ->
                                    z ∈ (T.leftArmPrefixTail hgraph hxFirst qLeft).support ->
                                      z = T.left) ∧
                                  (u ∈ Walk.InternalVertices (T.rim i) ∧
                                    u ∈ (T.rightToAttach i).support ∧
                                      u ≠ T.attach i) ∧
                                  v = T.left
                          · rcases hfirst_to_left with
                              ⟨hri, hxFirst, htransition_qFirst,
                                ⟨huInternal, huArm, huNe⟩, hvLeft⟩
                            subst r
                            subst v
                            exact hno_tripod
                              (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndFirstToLeftEndpoint
                                P T hgraph hij hik hjk hlegs_nil
                                (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                hij_order hjk_order hpath_contacts qLeft hxFirst
                                hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                                hqLeft_clean
                                (by
                                  simpa [hgraph] using
                                    GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                      P hno_cross T hpath_contacts hxFirst
                                      hx_ne_attach qLeft hqLeft_outside)
                                huArm huNe huInternal transition htransitionPath
                                htransitionOutside htransitionClean
                                (by simpa [hgraph] using htransition_qFirst))
                          · by_cases hlast_to_left :
                                r = k ∧
                                  Exists fun hxLast :
                                      x ∈ (T.leftToAttach k).support =>
                                    (forall z : V, z ∈ transition.support ->
                                      z ∈ (T.leftArmPrefixTail hgraph hxLast qLeft).support ->
                                        z = T.left) ∧
                                    (u ∈ Walk.InternalVertices (T.rim k) ∧
                                      u ∈ (T.rightToAttach k).support ∧
                                        u ≠ T.attach k) ∧
                                    v = T.left
                            · rcases hlast_to_left with
                                ⟨hrk, hxLast, htransition_qLast,
                                  ⟨huInternal, huArm, huNe⟩, hvLeft⟩
                              subst r
                              subst v
                              exact hno_tripod
                                (GMIX24SourceProof.Tripod.liftAllNilOfOuterLastLeftArmResidualAndLastToLeftEndpoint
                                  P T hgraph hij hik hjk hlegs_nil
                                  (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                  hij_order hjk_order hpath_contacts qLeft hxLast
                                  hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                                  hqLeft_clean
                                  (by
                                    simpa [hgraph] using
                                      GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                        P hno_cross T hpath_contacts hxLast
                                        hx_ne_attach qLeft hqLeft_outside)
                                  huArm huNe huInternal transition htransitionPath
                                  htransitionOutside htransitionClean
                                  (by simpa [hgraph] using htransition_qLast))
                            · by_cases hsame_first_left :
                                  r = i ∧
                                    Exists fun hxFirst :
                                        x ∈ (T.leftToAttach i).support =>
                                      (u ∈ Walk.InternalVertices (T.rim i) ∧
                                        u ∈ (T.rightToAttach i).support ∧
                                          u ≠ T.attach i) ∧
                                      (v ∈ Walk.InternalVertices (T.rim i) ∧
                                        v ∈ (T.leftToAttach i).support ∧
                                          v ≠ T.attach i)
                              · rcases hsame_first_left with
                                  ⟨hri, hxFirst,
                                    ⟨huInternal, huArm, huNe⟩,
                                    ⟨hvInternal, hvArm, hvNe⟩⟩
                                subst r
                                exact hno_tripod
                                  (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameFirstTransition
                                    P T hgraph hij hik hjk hlegs_nil
                                    (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                    hij_order hjk_order hpath_contacts qLeft hxFirst
                                    hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                                    hqLeft_clean
                                    (by
                                      simpa [hgraph] using
                                        GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                          P hno_cross T hpath_contacts hxFirst
                                          hx_ne_attach qLeft hqLeft_outside)
                                    huArm huNe huInternal hvArm hvNe (Or.inl hvInternal)
                                    transition htransitionPath htransitionOutside
                                    htransitionClean)
                              · by_cases hsame_last_left :
                                    r = k ∧
                                      Exists fun hxLast :
                                          x ∈ (T.leftToAttach k).support =>
                                        (u ∈ Walk.InternalVertices (T.rim k) ∧
                                          u ∈ (T.rightToAttach k).support ∧
                                            u ≠ T.attach k) ∧
                                        (v ∈ Walk.InternalVertices (T.rim k) ∧
                                          v ∈ (T.leftToAttach k).support ∧
                                            v ≠ T.attach k)
                                · rcases hsame_last_left with
                                    ⟨hrk, hxLast,
                                      ⟨huInternal, huArm, huNe⟩,
                                      ⟨hvInternal, hvArm, hvNe⟩⟩
                                  subst r
                                  exact hno_tripod
                                    (GMIX24SourceProof.Tripod.liftAllNilOfOuterLastLeftArmResidualAndSameLastTransition
                                      P T hgraph hij hik hjk hlegs_nil
                                      (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                      hij_order hjk_order hpath_contacts qLeft hxLast
                                      hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                                      hqLeft_clean
                                      (by
                                        simpa [hgraph] using
                                          GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                            P hno_cross T hpath_contacts hxLast
                                            hx_ne_attach qLeft hqLeft_outside)
                                      huArm huNe huInternal hvArm hvNe hvInternal
                                      transition htransitionPath htransitionOutside
                                      htransitionClean)
                                · by_cases hmiddle_first_selected :
                                      r = i ∧
                                        Exists fun hxFirst :
                                            x ∈ (T.leftToAttach i).support =>
                                          (u = T.right ∨
                                            (u ∈ Walk.InternalVertices (T.rim j) ∧
                                              u ∈ (T.rightToAttach j).support ∧
                                                u ≠ T.attach j)) ∧
                                          (v ∈ Walk.InternalVertices (T.rim i) ∧
                                            v ∈ (T.leftToAttach i).support ∧
                                              v ≠ T.attach i)
                                  · rcases hmiddle_first_selected with
                                      ⟨hri, hxFirst,
                                        huMiddle,
                                        ⟨hvInternal, hvArm, hvNe⟩⟩
                                    subst r
                                    have huArm : u ∈ (T.rightToAttach j).support := by
                                      rcases huMiddle with huRight | huStrict
                                      · rw [huRight]
                                        exact (T.rightToAttach j).start_mem_support
                                      · exact huStrict.2.1
                                    have huNe : u ≠ T.attach j := by
                                      rcases huMiddle with huRight | huStrict
                                      · intro huAttach
                                        exact T.right_ne_boundary j
                                          (huRight.symm.trans (huAttach.trans
                                            ((T.leg_nil_iff_boundary_eq_attach j).mp
                                              (hlegs_nil j)).symm))
                                      · exact huStrict.2.2
                                    have huContact :
                                        u ∈ Walk.InternalVertices (T.rim j) ∨
                                          u = T.right := by
                                      rcases huMiddle with huRight | huStrict
                                      · exact Or.inr huRight
                                      · exact Or.inl huStrict.1
                                    exact hno_tripod
                                      (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToFirstTransition
                                        P T hgraph hij hik hjk (Or.inl rfl) hlegs_nil
                                        (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                        hij_order hjk_order hpath_contacts qLeft
                                        hxFirst hx_ne_attach hxInternal (Or.inl ha)
                                        hqLeft_path hqLeft_clean
                                        (by
                                          simpa [hgraph] using
                                            GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                              P hno_cross T hpath_contacts hxFirst
                                              hx_ne_attach qLeft hqLeft_outside)
                                        huArm huNe huContact
                                        (GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
                                          P hno_cross T hpath_contacts huArm huNe)
                                        hvArm hvNe hvInternal
                                        (GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                          P hno_cross T hpath_contacts hvArm hvNe)
                                        transition htransitionPath htransitionOutside
                                        htransitionClean)
                                  · by_cases hmiddle_to_left :
                                        Exists fun hxLeft :
                                            x ∈ (T.leftToAttach r).support =>
                                          (forall z : V, z ∈ transition.support ->
                                            z ∈ (T.leftArmPrefixTail hgraph hxLeft qLeft).support ->
                                              z = T.left) ∧
                                          (u ∈ Walk.InternalVertices (T.rim j) ∧
                                            u ∈ (T.rightToAttach j).support ∧
                                              u ≠ T.attach j) ∧
                                          v = T.left
                                    · rcases hmiddle_to_left with
                                        ⟨hxLeft, htransitionEscape,
                                          ⟨huInternal, huArm, huNe⟩, hvLeft⟩
                                      subst v
                                      have hvArm : T.left ∈
                                          (T.leftToAttach j).support :=
                                        (T.leftToAttach j).start_mem_support
                                      have hvNe : T.left ≠ T.attach j := by
                                        intro h
                                        exact T.left_ne_boundary j
                                          (h.trans
                                            ((T.leg_nil_iff_boundary_eq_attach j).mp
                                              (hlegs_nil j)).symm)
                                      exact hno_tripod
                                        (GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndSameMiddleTransition
                                          P T hgraph hij hik hjk hr_outer hlegs_nil
                                          (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                          hij_order hjk_order hpath_contacts qLeft
                                          hxLeft hx_ne_attach hxInternal (Or.inl ha) hqLeft_path
                                          hqLeft_clean
                                          (by
                                            simpa [hgraph] using
                                              GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                P hno_cross T hpath_contacts hxLeft
                                                hx_ne_attach qLeft hqLeft_outside)
                                          huArm huNe (Or.inl huInternal) hvArm hvNe
                                          (Or.inr rfl) transition htransitionPath
                                          htransitionOutside htransitionClean
                                          (by simpa [hgraph] using htransitionEscape))
                                    · by_cases hlast_same_or_left_selected :
                                          r = i ∧
                                            Exists fun hxFirst :
                                                x ∈ (T.leftToAttach i).support =>
                                              (u ∈ Walk.InternalVertices (T.rim k) ∧
                                                u ∈ (T.rightToAttach k).support ∧
                                                  u ≠ T.attach k) ∧
                                              ((v ∈ Walk.InternalVertices (T.rim k) ∧
                                                  v ∈ (T.leftToAttach k).support ∧
                                                    v ≠ T.attach k) ∨
                                                v = T.left)
                                      · rcases hlast_same_or_left_selected with
                                          ⟨hri, hxFirst,
                                            ⟨huInternal, huArm, huNe⟩, hvLast⟩
                                        subst r
                                        have hvArm : v ∈
                                            (T.leftToAttach k).support := by
                                          rcases hvLast with hvStrict | hvLeft
                                          · exact hvStrict.2.1
                                          · rw [hvLeft]
                                            exact (T.leftToAttach k).start_mem_support
                                        have hvNe : v ≠ T.attach k := by
                                          rcases hvLast with hvStrict | hvLeft
                                          · exact hvStrict.2.2
                                          · intro hvAttach
                                            exact T.left_ne_boundary k
                                              (hvLeft.symm.trans (hvAttach.trans
                                                ((T.leg_nil_iff_boundary_eq_attach k).mp
                                                  (hlegs_nil k)).symm))
                                        have hvContact :
                                            v ∈ Walk.InternalVertices (T.rim k) ∨
                                              v = T.left := by
                                          rcases hvLast with hvStrict | hvLeft
                                          · exact Or.inl hvStrict.1
                                          · exact Or.inr hvLeft
                                        exact hno_tripod
                                          (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameLastTransition
                                            P T hgraph hij hik hjk hlegs_nil
                                            (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                            hij_order hjk_order hpath_contacts qLeft
                                            hxFirst hx_ne_attach hxInternal (Or.inl ha)
                                            hqLeft_path hqLeft_clean
                                            (by
                                              simpa [hgraph] using
                                                GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                  P hno_cross T hpath_contacts hxFirst
                                                  hx_ne_attach qLeft hqLeft_outside)
                                            huArm huNe huInternal hvArm hvNe hvContact
                                            transition htransitionPath htransitionOutside
                                            htransitionClean)
                                      · by_cases hmiddle_last_selected :
                                          r = k ∧
                                            Exists fun hxLast :
                                                x ∈ (T.leftToAttach k).support =>
                                              (u = T.right ∨
                                                (u ∈ Walk.InternalVertices (T.rim j) ∧
                                                  u ∈ (T.rightToAttach j).support ∧
                                                    u ≠ T.attach j)) ∧
                                              (v ∈ Walk.InternalVertices (T.rim k) ∧
                                                v ∈ (T.leftToAttach k).support ∧
                                                  v ≠ T.attach k)
                                        · rcases hmiddle_last_selected with
                                            ⟨hrk, hxLast, huMiddle,
                                              ⟨hvInternal, hvArm, hvNe⟩⟩
                                          subst r
                                          have huArm : u ∈
                                              (T.rightToAttach j).support := by
                                            rcases huMiddle with huRight | huStrict
                                            · rw [huRight]
                                              exact (T.rightToAttach j).start_mem_support
                                            · exact huStrict.2.1
                                          have huNe : u ≠ T.attach j := by
                                            rcases huMiddle with huRight | huStrict
                                            · intro huAttach
                                              exact T.right_ne_boundary j
                                                (huRight.symm.trans (huAttach.trans
                                                  ((T.leg_nil_iff_boundary_eq_attach j).mp
                                                    (hlegs_nil j)).symm))
                                            · exact huStrict.2.2
                                          have huContact :
                                              u ∈ Walk.InternalVertices (T.rim j) ∨
                                                u = T.right := by
                                            rcases huMiddle with huRight | huStrict
                                            · exact Or.inr huRight
                                            · exact Or.inl huStrict.1
                                          exact hno_tripod
                                            (GMIX24SourceProof.Tripod.liftAllNilOfOuterLastLeftArmResidualAndMiddleToLastTransition
                                              P T hgraph hij hik hjk hlegs_nil
                                              (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                              hij_order hjk_order hpath_contacts qLeft
                                              hxLast hx_ne_attach hxInternal (Or.inl ha)
                                              hqLeft_path hqLeft_clean
                                              (by
                                                simpa [hgraph] using
                                                  GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                    P hno_cross T hpath_contacts hxLast
                                                    hx_ne_attach qLeft hqLeft_outside)
                                              huArm huNe huContact
                                              (GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
                                                P hno_cross T hpath_contacts huArm huNe)
                                              hvArm hvNe hvInternal
                                              (GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                                P hno_cross T hpath_contacts hvArm hvNe)
                                              transition htransitionPath htransitionOutside
                                              htransitionClean)
                                        · by_cases hlast_middle_selected :
                                              r = i ∧
                                                Exists fun hxFirst :
                                                    x ∈ (T.leftToAttach i).support =>
                                                  (u ∈ Walk.InternalVertices (T.rim k) ∧
                                                    u ∈ (T.rightToAttach k).support ∧
                                                      u ≠ T.attach k) ∧
                                                  (v ∈ Walk.InternalVertices (T.rim j) ∧
                                                    v ∈ (T.leftToAttach j).support ∧
                                                      v ≠ T.attach j)
                                          · rcases hlast_middle_selected with
                                              ⟨hri, hxFirst,
                                                ⟨huInternal, huArm, huNe⟩,
                                                ⟨hvInternal, hvArm, hvNe⟩⟩
                                            subst r
                                            exact hno_tripod
                                              (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndLastToMiddleTransition
                                                P T hgraph hij hik hjk hlegs_nil
                                                (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                                hij_order hjk_order hpath_contacts qLeft
                                                hxFirst hx_ne_attach hxInternal (Or.inl ha)
                                                hqLeft_path hqLeft_clean
                                                (by
                                                  simpa [hgraph] using
                                                    GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                      P hno_cross T hpath_contacts hxFirst
                                                      hx_ne_attach qLeft hqLeft_outside)
                                                huArm huNe huInternal hvArm hvNe hvInternal
                                                (GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                                  P hno_cross T hpath_contacts hvArm hvNe)
                                                transition htransitionPath htransitionOutside
                                                htransitionClean)
                                          · by_cases hlast_first_selected :
                                                r = i ∧
                                                  Exists fun hxFirst :
                                                      x ∈ (T.leftToAttach i).support =>
                                                    (u ∈ Walk.InternalVertices (T.rim k) ∧
                                                      u ∈ (T.rightToAttach k).support ∧
                                                        u ≠ T.attach k) ∧
                                                    (v ∈ Walk.InternalVertices (T.rim i) ∧
                                                      v ∈ (T.leftToAttach i).support ∧
                                                        v ≠ T.attach i)
                                            · rcases hlast_first_selected with
                                                ⟨hri, hxFirst,
                                                  ⟨huInternal, huArm, huNe⟩,
                                                  ⟨hvInternal, hvArm, hvNe⟩⟩
                                              subst r
                                              exact hno_tripod
                                                (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndLastToFirstTransition
                                                  P T hgraph hij hik hjk hlegs_nil
                                                  (hfeet_path i) (hfeet_path j)
                                                  (hfeet_path k) hij_order hjk_order
                                                  hpath_contacts qLeft hxFirst
                                                  hx_ne_attach hxInternal (Or.inl ha)
                                                  hqLeft_path hqLeft_clean
                                                  (by
                                                    simpa [hgraph] using
                                                      GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                        P hno_cross T hpath_contacts hxFirst
                                                        hx_ne_attach qLeft hqLeft_outside)
                                                  huArm huNe huInternal hvArm hvNe
                                                  hvInternal
                                                  (GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                                    P hno_cross T hpath_contacts hvArm hvNe)
                                                  transition htransitionPath
                                                  htransitionOutside htransitionClean)
                                            · by_cases hselected_last_contact :
                                                  (r = i ∧
                                                    Exists fun hxFirst :
                                                        x ∈ (T.leftToAttach i).support =>
                                                      (u ∈ Walk.InternalVertices (T.rim i) ∧
                                                        u ∈ (T.rightToAttach i).support ∧
                                                          u ≠ T.attach i) ∧
                                                      ((v ∈ Walk.InternalVertices (T.rim i) ∧
                                                          v ∈ (T.leftToAttach i).support ∧
                                                            v ≠ T.attach i) ∨
                                                        v = T.left)) ∨
                                                  (Exists fun hxLeft :
                                                      x ∈ (T.leftToAttach r).support =>
                                                    (u = T.right ∨
                                                      (u ∈ Walk.InternalVertices (T.rim j) ∧
                                                        u ∈ (T.rightToAttach j).support ∧
                                                          u ≠ T.attach j)) ∧
                                                    (((v ∈ Walk.InternalVertices (T.rim j) ∧
                                                        v ∈ (T.leftToAttach j).support ∧
                                                          v ≠ T.attach j) ∧
                                                      Exists fun z : V =>
                                                        z ∈ transition.support ∧
                                                          z ∈
                                                            (T.leftArmPrefixTail hgraph hxLeft qLeft).support) ∨
                                                      v = T.left)) ∨
                                                  (r = i ∧
                                                    Exists fun hxFirst :
                                                        x ∈ (T.leftToAttach i).support =>
                                                      (u ∈ Walk.InternalVertices (T.rim i) ∧
                                                        u ∈ (T.rightToAttach i).support ∧
                                                          u ≠ T.attach i) ∧
                                                      (v ∈ Walk.InternalVertices (T.rim j) ∧
                                                        v ∈ (T.leftToAttach j).support ∧
                                                          v ≠ T.attach j) ∧
                                                      Exists fun z : V =>
                                                        z ∈ transition.support ∧
                                                          z ∈
                                                            (T.leftArmPrefixTail hgraph hxFirst qLeft).support) ∨
                                                  (r = i ∧
                                                    Exists fun hxFirst :
                                                        x ∈ (T.leftToAttach i).support =>
                                                      (u ∈ Walk.InternalVertices (T.rim i) ∧
                                                        u ∈ (T.rightToAttach i).support ∧
                                                          u ≠ T.attach i) ∧
                                                      (v ∈ Walk.InternalVertices (T.rim k) ∧
                                                        v ∈ (T.leftToAttach k).support ∧
                                                          v ≠ T.attach k)) ∨
                                                  (r = i ∧
                                                    Exists fun hxFirst :
                                                        x ∈ (T.leftToAttach i).support =>
                                                      (u = T.right ∨
                                                        (u ∈ Walk.InternalVertices (T.rim j) ∧
                                                          u ∈ (T.rightToAttach j).support ∧
                                                            u ≠ T.attach j)) ∧
                                                      (v ∈ Walk.InternalVertices (T.rim k) ∧
                                                        v ∈ (T.leftToAttach k).support ∧
                                                          v ≠ T.attach k))
                                              · rcases hselected_last_contact with
                                                  hsameFirst | hsameMiddleOrFirstMiddle
                                                · rcases hsameFirst with
                                                    ⟨hri, hxFirst,
                                                      ⟨huInternal, huArm, huNe⟩, hvFirst⟩
                                                  subst r
                                                  have hvArm : v ∈
                                                      (T.leftToAttach i).support := by
                                                    rcases hvFirst with hvStrict | hvLeft
                                                    · exact hvStrict.2.1
                                                    · rw [hvLeft]
                                                      exact (T.leftToAttach i).start_mem_support
                                                  have hvNe : v ≠ T.attach i := by
                                                    rcases hvFirst with hvStrict | hvLeft
                                                    · exact hvStrict.2.2
                                                    · intro hvAttach
                                                      exact T.left_ne_boundary i
                                                        (hvLeft.symm.trans (hvAttach.trans
                                                          ((T.leg_nil_iff_boundary_eq_attach i).mp
                                                            (hlegs_nil i)).symm))
                                                  have hvContact :
                                                      v ∈ Walk.InternalVertices (T.rim i) ∨
                                                        v = T.left := by
                                                    rcases hvFirst with hvStrict | hvLeft
                                                    · exact Or.inl hvStrict.1
                                                    · exact Or.inr hvLeft
                                                  exact hno_tripod
                                                    (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndSameFirstTransition
                                                      P T hgraph hij hik hjk hlegs_nil
                                                      (hfeet_path i) (hfeet_path j)
                                                      (hfeet_path k) hij_order hjk_order
                                                      hpath_contacts qLeft hxFirst hx_ne_attach
                                                      hxInternal (Or.inl ha) hqLeft_path
                                                      hqLeft_clean
                                                      (by
                                                        simpa [hgraph] using
                                                          GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                            P hno_cross T hpath_contacts hxFirst
                                                            hx_ne_attach qLeft hqLeft_outside)
                                                      huArm huNe huInternal hvArm hvNe hvContact
                                                      transition htransitionPath
                                                      htransitionOutside htransitionClean)
                                                · rcases hsameMiddleOrFirstMiddle with
                                                    hsameMiddle | hfirstMiddle
                                                  · rcases hsameMiddle with
                                                    ⟨hxLeft, huMiddle, hvMiddle⟩
                                                    have huArm : u ∈
                                                        (T.rightToAttach j).support := by
                                                      rcases huMiddle with huRight | huStrict
                                                      · rw [huRight]
                                                        exact (T.rightToAttach j).start_mem_support
                                                      · exact huStrict.2.1
                                                    have huNe : u ≠ T.attach j := by
                                                      rcases huMiddle with huRight | huStrict
                                                      · intro huAttach
                                                        exact T.right_ne_boundary j
                                                          (huRight.symm.trans (huAttach.trans
                                                            ((T.leg_nil_iff_boundary_eq_attach j).mp
                                                              (hlegs_nil j)).symm))
                                                      · exact huStrict.2.2
                                                    have huContact :
                                                        u ∈ Walk.InternalVertices (T.rim j) ∨
                                                          u = T.right := by
                                                      rcases huMiddle with huRight | huStrict
                                                      · exact Or.inr huRight
                                                      · exact Or.inl huStrict.1
                                                    have hvArm : v ∈
                                                        (T.leftToAttach j).support := by
                                                      rcases hvMiddle with hvStrict | hvLeft
                                                      · exact hvStrict.1.2.1
                                                      · rw [hvLeft]
                                                        exact (T.leftToAttach j).start_mem_support
                                                    have hvNe : v ≠ T.attach j := by
                                                      rcases hvMiddle with hvStrict | hvLeft
                                                      · exact hvStrict.1.2.2
                                                      · intro hvAttach
                                                        exact T.left_ne_boundary j
                                                          (hvLeft.symm.trans (hvAttach.trans
                                                            ((T.leg_nil_iff_boundary_eq_attach j).mp
                                                              (hlegs_nil j)).symm))
                                                    have hvContact :
                                                        v ∈ Walk.InternalVertices (T.rim j) ∨
                                                          v = T.left := by
                                                      rcases hvMiddle with hvStrict | hvLeft
                                                      · exact Or.inl hvStrict.1.1
                                                      · exact Or.inr hvLeft
                                                    have hinter : Exists fun z : V =>
                                                        z ∈ transition.support ∧
                                                          z ∈
                                                            (T.leftArmPrefixTail hgraph hxLeft qLeft).support := by
                                                      rcases hvMiddle with hvStrict | hvLeft
                                                      · exact hvStrict.2
                                                      · refine ⟨T.left, ?_, ?_⟩
                                                        · simpa [hvLeft] using transition.end_mem_support
                                                        · exact (T.leftArmPrefixTail hgraph hxLeft qLeft).start_mem_support
                                                    exact hno_tripod
                                                      (GMIX24SourceProof.Tripod.liftAllNilOfOuterLeftArmResidualAndIntersectingSameMiddleTransition
                                                        P T hgraph hij hik hjk hr_outer hlegs_nil
                                                        (hfeet_path i) (hfeet_path j)
                                                        (hfeet_path k) hij_order hjk_order
                                                        hpath_contacts qLeft hxLeft hx_ne_attach
                                                        hxInternal (Or.inl ha) hqLeft_path
                                                        hqLeft_clean
                                                        (by
                                                          simpa [hgraph] using
                                                            GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                              P hno_cross T hpath_contacts hxLeft
                                                              hx_ne_attach qLeft hqLeft_outside)
                                                        huArm huNe huContact hvArm hvNe hvContact
                                                        transition htransitionPath htransitionOutside
                                                        htransitionClean (by simpa [hgraph] using hinter))
                                                  · rcases hfirstMiddle with
                                                      hfirstMiddle | hfirstLastOrMiddleLast
                                                    · rcases hfirstMiddle with
                                                      ⟨hri, hxFirst,
                                                        ⟨huInternal, huArm, huNe⟩,
                                                        ⟨hvInternal, hvArm, hvNe⟩, hinter⟩
                                                      subst r
                                                      exact hno_tripod
                                                        (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndIntersectingFirstToMiddleTransition
                                                          P T hgraph hij hik hjk hlegs_nil
                                                          (hfeet_path i) (hfeet_path j)
                                                          (hfeet_path k) hij_order hjk_order
                                                          hpath_contacts qLeft hxFirst hx_ne_attach
                                                          hxInternal (Or.inl ha) hqLeft_path
                                                          hqLeft_clean
                                                          (by
                                                            simpa [hgraph] using
                                                              GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                                P hno_cross T hpath_contacts hxFirst
                                                                hx_ne_attach qLeft hqLeft_outside)
                                                          huArm huNe huInternal hvArm hvNe hvInternal
                                                          transition htransitionPath htransitionOutside
                                                          htransitionClean (by simpa [hgraph] using hinter))
                                                    · rcases hfirstLastOrMiddleLast with
                                                        hfirstLast | hmiddleLast
                                                      · rcases hfirstLast with
                                                          ⟨hri, hxFirst,
                                                            ⟨huInternal, huArm, huNe⟩,
                                                            ⟨hvInternal, hvArm, hvNe⟩⟩
                                                        subst r
                                                        exact hno_tripod
                                                          (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndFirstToLastTransition
                                                            P T hgraph hij hik hjk hlegs_nil
                                                            (hfeet_path i) (hfeet_path j)
                                                            (hfeet_path k) hij_order hjk_order
                                                            hpath_contacts qLeft hxFirst hx_ne_attach
                                                            hxInternal (Or.inl ha) hqLeft_path
                                                            hqLeft_clean
                                                            (by
                                                              simpa [hgraph] using
                                                                GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                                  P hno_cross T hpath_contacts hxFirst
                                                                  hx_ne_attach qLeft hqLeft_outside)
                                                            huArm huNe huInternal hvArm hvNe hvInternal
                                                            (GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                                              P hno_cross T hpath_contacts hvArm hvNe)
                                                            transition htransitionPath htransitionOutside
                                                            htransitionClean)
                                                      · rcases hmiddleLast with
                                                          ⟨hri, hxFirst, huMiddle,
                                                            ⟨hvInternal, hvArm, hvNe⟩⟩
                                                        subst r
                                                        have huArm : u ∈
                                                            (T.rightToAttach j).support := by
                                                          rcases huMiddle with huRight | huStrict
                                                          · rw [huRight]
                                                            exact (T.rightToAttach j).start_mem_support
                                                          · exact huStrict.2.1
                                                        have huNe : u ≠ T.attach j := by
                                                          rcases huMiddle with huRight | huStrict
                                                          · intro huAttach
                                                            exact T.right_ne_boundary j
                                                              (huRight.symm.trans (huAttach.trans
                                                                ((T.leg_nil_iff_boundary_eq_attach j).mp
                                                                  (hlegs_nil j)).symm))
                                                          · exact huStrict.2.2
                                                        have huContact :
                                                            u ∈ Walk.InternalVertices (T.rim j) ∨
                                                              u = T.right := by
                                                          rcases huMiddle with huRight | huStrict
                                                          · exact Or.inr huRight
                                                          · exact Or.inl huStrict.1
                                                        exact hno_tripod
                                                          (GMIX24SourceProof.Tripod.liftAllNilOfOuterFirstLeftArmResidualAndMiddleToLastTransition
                                                            P T hgraph hij hik hjk hlegs_nil
                                                            (hfeet_path i) (hfeet_path j)
                                                            (hfeet_path k) hij_order hjk_order
                                                            hpath_contacts qLeft hxFirst hx_ne_attach
                                                            hxInternal (Or.inl ha) hqLeft_path
                                                            hqLeft_clean
                                                            (by
                                                              simpa [hgraph] using
                                                                GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                                  P hno_cross T hpath_contacts hxFirst
                                                                  hx_ne_attach qLeft hqLeft_outside)
                                                            huArm huNe huContact
                                                            (GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
                                                              P hno_cross T hpath_contacts huArm huNe)
                                                            hvArm hvNe hvInternal
                                                            (GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                                              P hno_cross T hpath_contacts hvArm hvNe)
                                                            transition htransitionPath htransitionOutside
                                                            htransitionClean)
                                              · have huCases :
                                                  u = T.right ∨
                                                    (u ∈ Walk.InternalVertices (T.rim i) ∧
                                                      u ∈ (T.rightToAttach i).support ∧
                                                        u ≠ T.attach i) ∨
                                                    (u ∈ Walk.InternalVertices (T.rim j) ∧
                                                      u ∈ (T.rightToAttach j).support ∧
                                                        u ≠ T.attach j) ∨
                                                    (u ∈ Walk.InternalVertices (T.rim k) ∧
                                                      u ∈ (T.rightToAttach k).support ∧
                                                        u ≠ T.attach k) := by
                                                  rcases huContact with huRight | ⟨s, hs⟩
                                                  · exact Or.inl huRight
                                                  · rcases fin3_eq_of_pairwise
                                                      (m := s) hij hik hjk with hsi | hsjk
                                                    · subst s; exact Or.inr (Or.inl hs)
                                                    · rcases hsjk with hsj | hsk
                                                      · subst s; exact Or.inr (Or.inr (Or.inl hs))
                                                      · subst s; exact Or.inr (Or.inr (Or.inr hs))
                                                have hvCases :
                                                  v = T.left ∨
                                                    (v ∈ Walk.InternalVertices (T.rim i) ∧
                                                      v ∈ (T.leftToAttach i).support ∧
                                                        v ≠ T.attach i) ∨
                                                    (v ∈ Walk.InternalVertices (T.rim j) ∧
                                                      v ∈ (T.leftToAttach j).support ∧
                                                        v ≠ T.attach j) ∨
                                                    (v ∈ Walk.InternalVertices (T.rim k) ∧
                                                      v ∈ (T.leftToAttach k).support ∧
                                                        v ≠ T.attach k) := by
                                                  rcases hvContact with hvLeft | ⟨s, hs⟩
                                                  · exact Or.inl hvLeft
                                                  · rcases fin3_eq_of_pairwise
                                                      (m := s) hij hik hjk with hsi | hsjk
                                                    · subst s; exact Or.inr (Or.inl hs)
                                                    · rcases hsjk with hsj | hsk
                                                      · subst s; exact Or.inr (Or.inr (Or.inl hs))
                                                      · subst s; exact Or.inr (Or.inr (Or.inr hs))
                                                rcases hx_arm with hxLeft | hxRight
                                                · exact hno_tripod
                                                    (Tripod.liftAllNilOfOuterLeftArmResidualAndCleanTransition
                                                      P T hgraph hij hik hjk hr_outer hlegs_nil
                                                      (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                                      hij_order hjk_order hpath_contacts qLeft
                                                      hxLeft hx_ne_attach hxInternal (Or.inl ha)
                                                      hqLeft_path hqLeft_clean
                                                      (by
                                                        simpa [hgraph] using
                                                          GMIX24Split.canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
                                                            P hno_cross T hpath_contacts hxLeft
                                                            hx_ne_attach qLeft hqLeft_outside)
                                                      huCases hvCases
                                                      (fun s w hw hne =>
                                                        GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
                                                          P hno_cross T hpath_contacts hw hne)
                                                      (fun s w hw hne =>
                                                        GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
                                                          P hno_cross T hpath_contacts hw hne)
                                                      transition htransitionPath htransitionOutside
                                                      htransitionClean (by
                                                        intro huRight hvLeft
                                                        subst u
                                                        subst v
                                                        exact Tripod.liftAllNilOfOuterLeftArmResidualAndCarrierCleanBridge
                                                          P hno_cross T hij hik hjk hr_outer hlegs_nil
                                                          (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                                          hij_order hjk_order hpath_contacts qLeft
                                                          hxLeft hx_ne_attach hxInternal ha hqLeft_path
                                                          hqLeft_outside hqLeft_clean transition
                                                          htransitionPath htransitionOutside htransitionClean))
                                                · exact hno_tripod
                                                    (Tripod.liftAllNilOfOuterRightArmResidualAndCleanTransition
                                                      P hno_cross T hij hik hjk hr_outer hlegs_nil
                                                      (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                                      hij_order hjk_order hpath_contacts qLeft
                                                      hxRight hx_ne_attach hxInternal (Or.inl ha)
                                                      hqLeft_path hqLeft_outside hqLeft_clean
                                                      huCases hvCases transition htransitionPath
                                                      htransitionOutside htransitionClean (by
                                                        intro huRight hvLeft
                                                        subst u
                                                        subst v
                                                        apply Tripod.liftAllNilOfOuterRightArmResidualAndCarrierCleanBridge
                                                          P hno_cross T hij hik hjk hr_outer hlegs_nil
                                                          (hfeet_path i) (hfeet_path j) (hfeet_path k)
                                                          hij_order hjk_order hpath_contacts qLeft
                                                          hxRight hx_ne_attach hxInternal ha hqLeft_path
                                                          hqLeft_outside hqLeft_clean transition.reverse
                                                          htransitionPath.reverse
                                                        · intro z hz
                                                          apply htransitionOutside z
                                                          simpa [SimpleGraph.Walk.support_reverse] using hz
                                                        · intro z hz hzT
                                                          have hzTransition : z ∈ transition.support := by
                                                            simpa [SimpleGraph.Walk.support_reverse] using hz
                                                          rcases htransitionClean z hzTransition hzT with
                                                            hzRight | hzLeft
                                                          · exact Or.inr hzRight
                                                          · exact Or.inl hzLeft))
  · /- A hidden cut-path contact and the three tripod feet are four
    boundary points of the left society.  The old theta routes every pairing
    of these points, hence in particular the alternating pairing. -/
    push Not at hno_hidden
    rcases hno_hidden with ⟨z, hzPath, hzRim, hzNotFoot⟩
    rcases hzRim with ⟨r, hzr⟩
    have hzBoundary :
        z ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact Or.inr hzPath
    have hzAttach : z ≠ T.attach r :=
      left_side_tripod_hidden_rim_contact_not_attach_of_source_clean
        S hno_cross P T hsource_clean z hzPath hzNotFoot.1 r
    exact
      (GMIX24Split.canonicalOfNoCross_left_cross_free_of_no_tripod
        P hno_cross hno_tripod)
        (cross_of_hidden_rim_contact T hzBoundary hzNotFoot.1 hzr hzAttach)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
