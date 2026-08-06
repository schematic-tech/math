import Schematic.Math.GraphTheory.Minors.Society.Terminal.SourceObligations.HiddenEndpoints

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- A side tripod is impossible in the no-path-foot branch.

This is the literal first branch of the source side-tripod paragraph: if none
of the three side-tripod feet lies on the induced cut path, then all three feet
are already on the original left boundary arc, so the side tripod lifts
directly to an ambient tripod. -/
theorem left_side_tripod_impossible_of_all_feet_off_path
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hfeet_off : forall i : Fin 3, T.boundary i ∉ P.pathSet) :
    False :=
  hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_all_feet_off_path
      P hno_cross T hfeet_off)

/-- In the unique-path-foot branch, a later cut-path contact cannot lie on
any side-tripod leg.

This is the `X -> Ω` cleanliness part of the source side-tripod paragraph.
Every cut-path vertex is a boundary vertex of the left side society.  If such
a vertex lies on a side linkage leg, source cleanliness makes it the terminal
foot of that leg; the unique-foot hypothesis then either contradicts the
chosen contact being different from the unique foot, or contradicts the
off-path status of the other feet. -/
theorem left_side_tripod_unique_path_foot_contact_not_leg_of_source_clean
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    {i : Fin 3}
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    forall {x : V},
      x ∈ P.pathSet ->
        x ≠ T.boundary i ->
          forall k : Fin 3, x ∉ (T.leg k).support := by
  intro x hxPath hx_ne_i k hxLeg
  have hxSideBoundary :
      x ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
    rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
    exact Or.inr hxPath
  have hx_eq_boundary : x = T.boundary k :=
    hsource_clean k x hxLeg hxSideBoundary
  by_cases hki : k = i
  · exact hx_ne_i (by simpa [hki] using hx_eq_boundary)
  · exact hoff k hki (by simpa [hx_eq_boundary] using hxPath)

/-- Source-clean tail-escape normal form in the unique-path-foot branch.

The lower tail theorem only says that each tail from the unique path foot
escapes to an old common endpoint, to a different leg, or to a different rim.
The source `X -> Ω` cleanliness eliminates the different-leg alternatives:
those tail contacts are also cut-path vertices, hence boundary vertices of the
left split society, and the unique-foot hypothesis forbids any leg terminal
other than the chosen foot. -/
theorem left_side_tripod_unique_path_foot_two_tail_endpoint_or_rim_of_source_clean
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    (∃ x : V,
      x ∈ (P.pathTailToStart hpath).support ∧
        x ≠ T.boundary i ∧
          (x = T.left ∨ x = T.right ∨
            ∃ k : Fin 3, k ≠ i ∧ x ∈ Walk.InternalVertices (T.rim k))) ∧
      ∃ y : V,
        y ∈ (P.pathTailToEnd hpath).support ∧
          y ≠ T.boundary i ∧
            (y = T.left ∨ y = T.right ∨
              ∃ k : Fin 3, k ≠ i ∧ y ∈ Walk.InternalVertices (T.rim k)) := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_single_path_foot_two_tail_escapes
        P hno_cross hno_tripod T hpath hoff with
    ⟨⟨x, hxTail, hxne, hxEscape⟩, ⟨y, hyTail, hyne, hyEscape⟩⟩
  have hnotLeg :
      forall {z : V},
        z ∈ P.pathSet ->
          z ≠ T.boundary i ->
            forall k : Fin 3, z ∉ (T.leg k).support :=
    left_side_tripod_unique_path_foot_contact_not_leg_of_source_clean
      (S := S) hno_cross P T hsource_clean hoff
  refine ⟨⟨x, hxTail, hxne, ?_⟩, ⟨y, hyTail, hyne, ?_⟩⟩
  · rcases hxEscape with hxLeft | hxRest
    · exact Or.inl hxLeft
    rcases hxRest with hxRight | hxBranch
    · exact Or.inr (Or.inl hxRight)
    rcases hxBranch with ⟨k, hki, hxLegOrRim⟩
    rcases hxLegOrRim with hxLeg | hxRim
    · have hxPath : x ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hpath x hxTail
      exact False.elim ((hnotLeg hxPath hxne k) hxLeg)
    · exact Or.inr (Or.inr ⟨k, hki, hxRim⟩)
  · rcases hyEscape with hyLeft | hyRest
    · exact Or.inl hyLeft
    rcases hyRest with hyRight | hyBranch
    · exact Or.inr (Or.inl hyRight)
    rcases hyBranch with ⟨k, hki, hyLegOrRim⟩
    rcases hyLegOrRim with hyLeg | hyRim
    · have hyPath : y ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hpath y hyTail
      exact False.elim ((hnotLeg hyPath hyne k) hyLeg)
    · exact Or.inr (Or.inr ⟨k, hki, hyRim⟩)

/-- One-tail consequence of the unique-path-foot normal form.

In the source one-foot case, following either tail from the unique foot must
hit the old common end or a hidden rim point on a different branch.  This
statement records the start-tail version in a form usable by the remaining
common-end contradiction: the different-rim alternative is automatically a
hidden contact because the unique-foot hypothesis excludes all other named
feet from `P`. -/
theorem left_side_tripod_unique_path_foot_common_endpoint_or_hidden_rim_contact
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    (T.left ∈ P.pathSet ∨ T.right ∈ P.pathSet) ∨
      Exists fun z : V =>
        z ∈ P.pathSet ∧
          (Exists fun k : Fin 3 =>
            k ≠ i ∧ z ∈ Walk.InternalVertices (T.rim k)) ∧
          forall m : Fin 3, z ≠ T.boundary m := by
  classical
  rcases
      left_side_tripod_unique_path_foot_two_tail_endpoint_or_rim_of_source_clean
        (S := S) hno_cross hno_tripod P T hsource_clean hpath hoff with
    ⟨⟨x, hxTail, hxne, hxEscape⟩, _hendTail⟩
  have hxPath : x ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet hpath x hxTail
  rcases hxEscape with hxLeft | hxRest
  · exact Or.inl (Or.inl (by simpa [hxLeft] using hxPath))
  rcases hxRest with hxRight | hxRim
  · exact Or.inl (Or.inr (by simpa [hxRight] using hxPath))
  · right
    rcases hxRim with ⟨k, hki, hxInternal⟩
    refine ⟨x, hxPath, ⟨k, hki, hxInternal⟩, ?_⟩
    intro m hxm
    by_cases hmi : m = i
    · exact hxne (by simpa [hmi] using hxm)
    · exact hoff m hmi (by simpa [hxm] using hxPath)

/-- Unique-path-foot branch always produces a hidden rim contact.

This is the cleaned-up source consequence of the preceding alternative.  If
the start tail reaches an old common endpoint, that endpoint is itself a
non-boundary rim contact.  If the start tail reaches a different old rim
internally, the unique-foot hypothesis already proves that contact is not any
named boundary foot. -/
theorem left_side_tripod_unique_path_foot_hidden_rim_contact_of_source_clean
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun z : V =>
      z ∈ P.pathSet ∧
        (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ∧
        forall m : Fin 3, z ≠ T.boundary m := by
  rcases
      left_side_tripod_unique_path_foot_common_endpoint_or_hidden_rim_contact
        (S := S) hno_cross hno_tripod P T hsource_clean hpath hoff with
    hcommon | hhidden
  · rcases hcommon with hleft | hright
    · exact
        ⟨T.left, hleft, ⟨0, (T.rim 0).start_mem_support⟩,
          fun m => T.left_ne_boundary m⟩
    · exact
        ⟨T.right, hright, ⟨0, (T.rim 0).end_mem_support⟩,
          fun m => T.right_ne_boundary m⟩
  · rcases hhidden with ⟨z, hzPath, hzRimInternal, hzNotBoundary⟩
    rcases hzRimInternal with ⟨r, _hri, hzInternal⟩
    exact
      ⟨z, hzPath, ⟨r, Walk.internalVertices_subset_support (T.rim r) hzInternal⟩,
        hzNotBoundary⟩

/-- No-hidden-contact contradiction in the unique-path-foot branch.

This packages the preceding source consequence in the form consumed by
path-contact normalization: a source-clean side tripod cannot have exactly one
foot on the cut path once hidden rim contacts have been excluded. -/
theorem left_side_tripod_unique_path_foot_impossible_of_no_hidden_rim_contact
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
          (forall m : Fin 3, z ≠ T.boundary m) -> False)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    False := by
  rcases
      left_side_tripod_unique_path_foot_hidden_rim_contact_of_source_clean
        (S := S) hno_cross hno_tripod P T hsource_clean hpath hoff with
    ⟨z, hzPath, hzRim, hzNotBoundary⟩
  exact hno_hidden z hzPath hzRim hzNotBoundary

/-- Hidden-contact source subcase with both common endpoints off the induced
cut path.

This packages
`left_side_tripod_hidden_rim_contact_common_endpoint_on_path_of_off_feet` in
the contradiction form needed by the final hidden-contact normalizer. -/
theorem left_side_tripod_hidden_rim_contact_impossible_of_off_feet_common_endpoints_off_path
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
    (hleft_off : T.left ∉ P.pathSet)
    (hright_off : T.right ∉ P.pathSet) :
    False := by
  rcases
      left_side_tripod_hidden_rim_contact_common_endpoint_on_path_of_off_feet
        (S := S) hno_cross hno_tripod P T hzPath hzRim hleg_off hrim_off with
    hleft | hright
  · exact hleft_off hleft
  · exact hright_off hright

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
