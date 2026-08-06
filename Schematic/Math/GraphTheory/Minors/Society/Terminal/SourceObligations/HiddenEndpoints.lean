import Schematic.Math.GraphTheory.Minors.Society.Terminal.SourceObligations.OuterNil

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Hidden-contact source subcase: under the branch-off hypotheses used by
the existing clean-tail lifts, a hidden cut-path/rim contact forces one of the
two common old rim endpoints to lie on the induced cut path.

This is the first direct local consequence of the source sentence that the
auxiliary path tail has a common end with the three side-tripod paths.  The
checked tail extractor supplies the last old-tripod contact on the tail to
`s`; the nonendpoint clean-tail lift rules out every non-common endpoint, so
that last contact is `T.left` or `T.right`.  Since the whole tail lies in the
cut path, one of those common endpoints lies in `P.pathSet`. -/
theorem left_side_tripod_hidden_rim_contact_common_endpoint_on_path_of_off_feet
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    T.left ∈ P.pathSet ∨ T.right ∈ P.pathSet := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_hidden_rim_contact_start_tail_endpoint_of_off_feet
        P hno_cross hno_tripod T hzPath hzRim hleg_off hrim_off with
    ⟨x, hxTail, _hxT, _hq_path, _hq_clean, _hq_pathSet, hend⟩
  have hxPath : x ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet hzPath x hxTail
  rcases hend with hx_left | hx_right
  · exact Or.inl (by simpa [hx_left] using hxPath)
  · exact Or.inr (by simpa [hx_right] using hxPath)

/-- End-tail version of
`left_side_tripod_hidden_rim_contact_common_endpoint_on_path_of_off_feet`.

The same hidden cut-path/rim contact can be followed toward `t` instead of
`s`.  Under the identical off-foot hypotheses, the last old-tripod contact on
that tail is forced to be one of the two old rim endpoints, hence that common
endpoint lies on the induced cut path. -/
theorem left_side_tripod_hidden_rim_contact_common_endpoint_on_path_of_off_feet_end
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    T.left ∈ P.pathSet ∨ T.right ∈ P.pathSet := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_hidden_rim_contact_end_tail_endpoint_of_off_feet
        P hno_cross hno_tripod T hzPath hzRim hleg_off hrim_off with
    ⟨x, hxTail, _hxT, _hq_path, _hq_clean, _hq_pathSet, hend⟩
  have hxPath : x ∈ P.pathSet :=
    P.pathTailToEnd_support_subset_pathSet hzPath x hxTail
  rcases hend with hx_left | hx_right
  · exact Or.inl (by simpa [hx_left] using hxPath)
  · exact Or.inr (by simpa [hx_right] using hxPath)

/-- Two-tail hidden-contact extractor.

This keeps the actual witnesses from the two induced-path tails instead of
forgetting them down to membership in `P.pathSet`.  It is the data needed for
the common-end-on-`P` case: if both tails hit the same old rim endpoint, the
new tail-intersection lemma identifies that endpoint with the hidden contact
itself. -/
theorem left_side_tripod_hidden_rim_contact_common_tail_endpoints_of_off_feet
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    (Exists fun xs : V =>
      xs ∈ (P.pathTailToStart hzPath).support ∧
        (xs = T.left ∨ xs = T.right)) ∧
      Exists fun xt : V =>
        xt ∈ (P.pathTailToEnd hzPath).support ∧
          (xt = T.left ∨ xt = T.right) := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_hidden_rim_contact_start_tail_endpoint_of_off_feet
        P hno_cross hno_tripod T hzPath hzRim hleg_off hrim_off with
    ⟨xs, hxsTail, _hxsT, _hqs_path, _hqs_clean, _hqs_pathSet, hxsEnd⟩
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_hidden_rim_contact_end_tail_endpoint_of_off_feet
        P hno_cross hno_tripod T hzPath hzRim hleg_off hrim_off with
    ⟨xt, hxtTail, _hxtT, _hqt_path, _hqt_clean, _hqt_pathSet, hxtEnd⟩
  exact ⟨⟨xs, hxsTail, hxsEnd⟩, ⟨xt, hxtTail, hxtEnd⟩⟩

/-- Concrete two-tail case split for a hidden rim contact.

Under the off-foot hypotheses, the start and end tails each hit an old common
rim endpoint.  If they hit the same endpoint, the two tails meet there, so the
new tail-intersection lemma says the hidden contact is that endpoint.  If they
hit different endpoints, the two old endpoints occur on opposite sides of the
hidden contact along the cut path. -/
theorem left_side_tripod_hidden_rim_contact_tail_endpoint_cases_of_off_feet
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    (z = T.left ∨ z = T.right) ∨
      ((T.left ∈ (P.pathTailToStart hzPath).support ∧
          T.right ∈ (P.pathTailToEnd hzPath).support) ∨
        (T.right ∈ (P.pathTailToStart hzPath).support ∧
          T.left ∈ (P.pathTailToEnd hzPath).support)) := by
  classical
  rcases
      left_side_tripod_hidden_rim_contact_common_tail_endpoints_of_off_feet
        (S := S) hno_cross hno_tripod P T hzPath hzRim hleg_off hrim_off with
    ⟨⟨xs, hxsTail, hxsEnd⟩, ⟨xt, hxtTail, hxtEnd⟩⟩
  rcases hxsEnd with hxs_left | hxs_right
  · rcases hxtEnd with hxt_left | hxt_right
    · left
      have hleftStart : T.left ∈ (P.pathTailToStart hzPath).support := by
        simpa [hxs_left] using hxsTail
      have hleftEnd : T.left ∈ (P.pathTailToEnd hzPath).support := by
        simpa [hxt_left] using hxtTail
      exact Or.inl
        (GMIX24CutPath.pathTailToStart_support_inter_pathTailToEnd_eq
          P hzPath hleftStart hleftEnd).symm
    · right
      exact Or.inl
        ⟨by simpa [hxs_left] using hxsTail,
          by simpa [hxt_right] using hxtTail⟩
  · rcases hxtEnd with hxt_left | hxt_right
    · right
      exact Or.inr
        ⟨by simpa [hxs_right] using hxsTail,
          by simpa [hxt_left] using hxtTail⟩
    · left
      have hrightStart : T.right ∈ (P.pathTailToStart hzPath).support := by
        simpa [hxs_right] using hxsTail
      have hrightEnd : T.right ∈ (P.pathTailToEnd hzPath).support := by
        simpa [hxt_right] using hxtTail
      exact Or.inr
        (GMIX24CutPath.pathTailToStart_support_inter_pathTailToEnd_eq
          P hzPath hrightStart hrightEnd).symm

/-- Opposite-tail hidden-contact reduction.

If the hidden rim contact itself is not one of the old common rim endpoints,
the preceding case split cannot be in the same-endpoint branch.  Thus the two
old common endpoints occur on opposite cut-path tails from the hidden contact.
This is the formal local version of the source proof's normalization before
extracting the final ambient tripod. -/
theorem left_side_tripod_hidden_rim_contact_opposite_tail_cases_of_off_feet
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hz_ne_left : z ≠ T.left)
    (hz_ne_right : z ≠ T.right) :
    (T.left ∈ (P.pathTailToStart hzPath).support ∧
        T.right ∈ (P.pathTailToEnd hzPath).support) ∨
      (T.right ∈ (P.pathTailToStart hzPath).support ∧
        T.left ∈ (P.pathTailToEnd hzPath).support) := by
  rcases
      left_side_tripod_hidden_rim_contact_tail_endpoint_cases_of_off_feet
        (S := S) hno_cross hno_tripod P T hzPath hzRim hleg_off hrim_off with
    hsame | hopp
  · rcases hsame with hz_left | hz_right
    · exact False.elim (hz_ne_left hz_left)
    · exact False.elim (hz_ne_right hz_right)
  · exact hopp

/-- Path-membership consequence of the opposite-tail hidden-contact reduction.

Once the hidden contact is not itself a common endpoint, the two common
endpoints are forced onto the induced cut path.  This isolates the remaining
hard source subcase: the old common endpoint lies on `P`, so the final tripod
extraction must use the source argument's common-end rerouting instead of the
off-path contradiction. -/
theorem left_side_tripod_hidden_rim_contact_common_endpoints_on_path_of_off_feet_not_endpoint
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hz_ne_left : z ≠ T.left)
    (hz_ne_right : z ≠ T.right) :
    T.left ∈ P.pathSet ∧ T.right ∈ P.pathSet := by
  rcases
      left_side_tripod_hidden_rim_contact_opposite_tail_cases_of_off_feet
        (S := S) hno_cross hno_tripod P T hzPath hzRim hleg_off hrim_off
        hz_ne_left hz_ne_right with
    hleft_start_right_end | hright_start_left_end
  · exact
      ⟨P.pathTailToStart_support_subset_pathSet hzPath T.left
          hleft_start_right_end.1,
        P.pathTailToEnd_support_subset_pathSet hzPath T.right
          hleft_start_right_end.2⟩
  · exact
      ⟨P.pathTailToEnd_support_subset_pathSet hzPath T.left
          hright_start_left_end.2,
        P.pathTailToStart_support_subset_pathSet hzPath T.right
          hright_start_left_end.1⟩

/-- One-sided off-path contradiction for the hidden-contact normalization.

In the nonendpoint hidden-contact case, the two-tail argument forces both old
common rim endpoints onto the cut path.  Thus it is enough for either common
endpoint to be known off the cut path to close this source subcase. -/
theorem left_side_tripod_hidden_rim_contact_impossible_of_off_feet_common_endpoint_off_path
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hz_ne_left : z ≠ T.left)
    (hz_ne_right : z ≠ T.right)
    (hendpoint_off : T.left ∉ P.pathSet ∨ T.right ∉ P.pathSet) :
    False := by
  rcases
      left_side_tripod_hidden_rim_contact_common_endpoints_on_path_of_off_feet_not_endpoint
        (S := S) hno_cross hno_tripod P T hzPath hzRim hleg_off hrim_off
        hz_ne_left hz_ne_right with
    ⟨hleft, hright⟩
  rcases hendpoint_off with hleft_off | hright_off
  · exact hleft_off hleft
  · exact hright_off hright

/-- Internal-contact form of the one-sided off-path contradiction.

This is the source-common-end subcase after the source-clean classifier has
already ruled out legs, selected feet, and selected attachments.  An internal
hidden contact on an old rim is a nonendpoint rim-support contact, so the
two-tail argument forces both old common rim endpoints onto the induced cut
path; either endpoint known off the cut path is therefore contradictory. -/
theorem left_side_tripod_hidden_internal_contact_impossible_of_off_feet_common_endpoint_off_path
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {z : V}
    (hzPath : z ∈ P.pathSet)
    (hzInternal :
      Exists fun r : Fin 3 =>
        z ∈ Walk.InternalVertices (T.rim r) ∧
          forall m : Fin 3, z ≠ T.attach m)
    (hleg_off :
      forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hrim_off :
      forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
        (forall j : Fin 3, x ≠ T.attach j) ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hendpoint_off : T.left ∉ P.pathSet ∨ T.right ∉ P.pathSet) :
    False := by
  rcases hzInternal with ⟨r, hzInt, _hzNotAttach⟩
  have hzRim : Exists fun r : Fin 3 => z ∈ (T.rim r).support :=
    ⟨r, Walk.internalVertices_subset_support (T.rim r) hzInt⟩
  exact
    left_side_tripod_hidden_rim_contact_impossible_of_off_feet_common_endpoint_off_path
      (S := S) hno_cross hno_tripod P T hzPath hzRim hleg_off hrim_off
      hzInt.2.1 hzInt.2.2 hendpoint_off

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
