import Schematic.Math.GraphTheory.Minors.Society.Terminal.SourceObligations.Definitions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Checked side-tripod handoff from the two source-normalization assertions
used in the printed GM IX `(2.4)` paragraph.

The hypotheses are deliberately stated only for the chosen cut path and its
canonical left side:

* every contact of the side tripod with the induced cut path is one of the
  three side-tripod feet;
* after those feet are ordered along the cut path, at least one outer ordered
  leg is not collapsed.

All subsequent case analysis, including the clean tail to the opposite
boundary arc and the common-end ambient tripod construction, is already
checked in `GMIX24Split`. -/
theorem left_side_tripod_obligation_of_path_contacts_ordered_first_or_last_non_nil
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hordered_first_or_last_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg i).Nil ∨ Not (T.leg k).Nil) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :=
  GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_ordered_first_or_last_non_nil
    P hno_cross hno_tripod hpath_contacts hordered_first_or_last_not_nil

/-- Checked source-clean side-tripod subcase: no hidden rim contact and a
noncollapsed outer ordered leg already produce the forbidden ambient tripod.

This is the part of the printed side-tripod paragraph that is already fully
covered by the local constructors.  It starts from one concrete source-clean
side tripod, proves path-contact normalization from the no-hidden-rim
hypothesis, chooses the clean tail to the opposite boundary arc, classifies
the residual, and invokes the checked common-end / collapsed-arm lifts.
-/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_ordered_outer
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hordered_first_or_last_not_nil :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          Not (T.leg i).Nil ∨ Not (T.leg k).Nil) :
    False := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      _hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) :=
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_or_last_non_nil
      P hno_cross hno_tripod T hij hik hjk
      (hordered_first_or_last_not_nil hij hik hjk hij_order hjk_order)
      q hxT ha (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts hq_clean
  have hq_clean_vertex :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
    intro z hz hzT
    exact hq_clean z hz (by
      rcases hzT with hzRim | hzLeg
      · rcases hzRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases hzLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts
      hq_clean_vertex)

/-- Source-clean side-tripod contradiction in the noncollapsed-leg subcase.

This packages the easiest fully checked consequence of the preceding ordered
lemma: if hidden rim contacts with the induced cut path have already been
excluded and no side linkage leg has collapsed, then every possible ordering of
the three feet has a nontrivial outer leg, so the ambient tripod contradiction
is immediate. -/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_no_leg_nil
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    False :=
  left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_ordered_outer
    (S := S) hno_cross hno_tripod P T hsource_clean hno_hidden
    (by
      intro i _j k _hij _hik _hjk _hij_order _hjk_order
      exact Or.inl (hleg_not_nil i))

/-- Source-clean side-tripod contradiction in the ordered
`last-or-outer` noncollapsed-leg subcase.

This is the source-proof form of the checked residual constructors immediately
below the global side-tripod eliminators: after hidden rim contacts with the
induced cut path have been excluded, the three feet are ordered along the path.
The proof closes whenever either the last ordered leg is noncollapsed, or the
first two ordered legs are noncollapsed. -/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_ordered_last_or_outer
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hordered_last_or_outer_not_nil :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          Not (T.leg k).Nil ∨
            (Not (T.leg i).Nil ∧ Not (T.leg j).Nil)) :
    False := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      _hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
    rcases
        hordered_last_or_outer_not_nil hij hik hjk hij_order hjk_order with
      hlast | houter
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_last_non_nil
          P hno_cross hno_tripod T hij hik hjk hlast q hxT ha
          (fun r : Fin 3 => hall (fin3Order i j k r)) hq_path
          hij_order hjk_order hq_outside hpath_contacts hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_non_nil
          P hno_cross hno_tripod T hij hik hjk houter.1 q
          hxT ha (fun r : Fin 3 => hall (fin3Order i j k r)) hq_path
          hij_order hjk_order hq_outside hpath_contacts hq_clean
  have hq_clean_vertex :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
    intro z hz hzT
    exact hq_clean z hz (by
      rcases hzT with hzRim | hzLeg
      · rcases hzRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases hzLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts
      hq_clean_vertex)

/-- Source-clean side-tripod contradiction when at most one leg has collapsed
and hidden rim contacts have been excluded.

This packages the preceding ordered eliminator in the source combinatorial
form: if one ordered outer leg is collapsed, the `at most one nil` hypothesis
forces the other two ordered legs to be noncollapsed. -/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_at_most_one_leg_nil
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hat_most_one_nil :
      forall i j : Fin 3, i ≠ j -> (T.leg i).Nil -> Not (T.leg j).Nil) :
    False :=
  left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_ordered_last_or_outer
    (S := S) hno_cross hno_tripod P T hsource_clean hno_hidden
    (by
      intro i j k _hij hik hjk _hij_order _hjk_order
      by_cases hk_not_nil : Not (T.leg k).Nil
      · exact Or.inl hk_not_nil
      · push Not at hk_not_nil
        exact Or.inr
          ⟨hat_most_one_nil k i (fun h => hik h.symm) hk_not_nil,
            hat_most_one_nil k j (fun h => hjk h.symm) hk_not_nil⟩)

/-- Source-clean side-tripod contradiction unless the ordered outer legs both
collapse.

After hidden rim contacts have been excluded, the checked source constructors
close the side-tripod paragraph as soon as either ordered outer leg is
nontrivial.  Thus the genuinely remaining residual is exactly the
double-outer-collapsed case formalized by the following negated hypothesis. -/
theorem left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_no_ordered_outer_nil
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (∃ r : Fin 3, z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False)
    (hno_ordered_outer_nil :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          Not ((T.leg i).Nil ∧ (T.leg k).Nil)) :
    False :=
  left_side_tripod_source_clean_impossible_of_no_hidden_rim_contact_ordered_outer
    (S := S) hno_cross hno_tripod P T hsource_clean hno_hidden
    (by
      intro i j k hij hik hjk hij_order hjk_order
      by_cases hi_nil : (T.leg i).Nil
      · by_cases hk_nil : (T.leg k).Nil
        · exact False.elim
            (hno_ordered_outer_nil hij hik hjk hij_order hjk_order
              ⟨hi_nil, hk_nil⟩)
        · exact Or.inr hk_nil
      · exact Or.inl hi_nil)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
