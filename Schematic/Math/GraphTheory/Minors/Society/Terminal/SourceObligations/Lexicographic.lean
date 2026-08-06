import Schematic.Math.GraphTheory.Minors.Society.Terminal.SourceObligations.ContactNormalization

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Hidden cut-path contacts of a lexicographically normalized source-clean
side tripod.

Compared with the length-only version above, the internal branch records the
extra fact supplied by maximality: the selected foot of the contacted rim is
itself on the cut path.  Thus a hidden internal contact can neither introduce
a new path foot nor shorten a nontrivial leg. -/
theorem left_side_tripod_hidden_contact_endpoint_or_internal_path_foot_nil_of_lexicographic
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hmax :
      forall
        U :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
        U.LegBoundaryContactClean ->
          U.footCountIn P.pathSet <= T.footCountIn P.pathSet)
    (hminimal :
      forall
        U :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
        U.LegBoundaryContactClean ->
          U.footCountIn P.pathSet = T.footCountIn P.pathSet ->
            T.linkageLength <= U.linkageLength) :
    forall z : V,
      z ∈ P.pathSet ->
        z ∈ T.vertexSet ->
          (forall m : Fin 3, z ≠ T.boundary m) ->
            (z = T.left ∨ z = T.right) ∨
              Exists fun r : Fin 3 =>
                z ∈ Walk.InternalVertices (T.rim r) ∧
                  T.boundary r ∈ P.pathSet ∧
                    (T.leg r).Nil ∧
                      forall m : Fin 3, z ≠ T.attach m := by
  intro z hzPath hzT hzNotBoundary
  rcases
      left_side_tripod_hidden_path_contact_endpoint_or_internal_nonattach
        (S := S) hno_cross P T hsource_clean z hzPath hzT
        hzNotBoundary with
    hend | hinternal
  · exact Or.inl hend
  · rcases hinternal with ⟨r, hzInternal, hzNotAttach⟩
    have hzSideBoundary :
        z ∈
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact Or.inr hzPath
    rcases
        T.internal_boundary_contact_foot_mem_and_leg_nil_of_lexicographic
          hsource_clean P.pathSet hmax hminimal r z hzInternal
          hzSideBoundary hzNotBoundary hzPath with
      ⟨hrPath, hrNil⟩
    exact Or.inr
      ⟨r, hzInternal, hrPath, hrNil, hzNotAttach⟩

/-- The first source consequence of lexicographic normalization.

An ambient-tripod-free side tripod either has two distinct feet on the cut
path, or one of the two common theta endpoints lies on that path.  Indeed, in
the unique-foot case the source two-tail argument produces either such a
common endpoint or a hidden internal contact on a different rim; the latter
would force a second path foot by lexicographic maximality. -/
theorem left_side_tripod_two_path_feet_or_common_endpoint_on_path_of_lexicographic
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hmax :
      forall
        U :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
        U.LegBoundaryContactClean ->
          U.footCountIn P.pathSet <= T.footCountIn P.pathSet)
    (hminimal :
      forall
        U :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
        U.LegBoundaryContactClean ->
          U.footCountIn P.pathSet = T.footCountIn P.pathSet ->
            T.linkageLength <= U.linkageLength) :
    (Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        i ≠ j ∧
          T.boundary i ∈ P.pathSet ∧ T.boundary j ∈ P.pathSet) ∨
      T.left ∈ P.pathSet ∨ T.right ∈ P.pathSet := by
  obtain ⟨i, hiPath⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_has_path_foot
      P hno_cross hno_tripod T
  by_cases hsecond :
      Exists fun j : Fin 3 =>
        i ≠ j ∧ T.boundary j ∈ P.pathSet
  · rcases hsecond with ⟨j, hij, hjPath⟩
    exact Or.inl ⟨i, j, hij, hiPath, hjPath⟩
  · have hoff :
        forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet := by
      intro j hji hjPath
      exact hsecond ⟨j, fun hij => hji hij.symm, hjPath⟩
    rcases
        left_side_tripod_unique_path_foot_common_endpoint_or_hidden_rim_contact
          (S := S) hno_cross hno_tripod P T hsource_clean hiPath hoff with
      hcommon | hhidden
    · exact Or.inr hcommon
    · rcases hhidden with
        ⟨z, hzPath, ⟨r, hri, hzInternal⟩, hzNotBoundary⟩
      have hzT : z ∈ T.vertexSet :=
        T.rim_mem_vertexSet
          (Walk.internalVertices_subset_support (T.rim r) hzInternal)
      rcases
          left_side_tripod_hidden_contact_endpoint_or_internal_path_foot_nil_of_lexicographic
            (S := S) hno_cross P T hsource_clean hmax hminimal z hzPath
            hzT hzNotBoundary with
        hend | hnormalized
      · rcases hend with hzLeft | hzRight
        · exact Or.inr (Or.inl (by simpa [hzLeft] using hzPath))
        · exact Or.inr (Or.inr (by simpa [hzRight] using hzPath))
      · rcases hnormalized with ⟨k, hzkInternal, hkPath, _hkNil, _⟩
        have hkr : k = r := by
          by_contra hkr
          exact
            Set.disjoint_left.mp (T.rim_internals_disjoint k r hkr)
              hzkInternal hzInternal
        exact False.elim (hoff r hri (by simpa [hkr] using hkPath))

/-- Hidden-rim contacts are impossible in the all-off common-end subcase.

This closes the source-common-end branch where none of the three side-tripod
feet and neither old common rim endpoint lies on the induced cut path.  Endpoint
hidden contacts contradict the endpoint-off hypotheses directly; internal
hidden contacts contradict the two-tail off-foot construction. -/
theorem left_side_tripod_hidden_rim_contact_impossible_of_all_feet_common_endpoints_off_path
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hfeet_off : forall i : Fin 3, T.boundary i ∉ P.pathSet)
    (hleft_off : T.left ∉ P.pathSet)
    (hright_off : T.right ∉ P.pathSet) :
    forall z : V,
      z ∈ P.pathSet ->
        (∃ r : Fin 3, z ∈ (T.rim r).support) ->
          (forall m : Fin 3, z ≠ T.boundary m) -> False := by
  intro z hzPath hzRim hzNotBoundary
  rcases
      left_side_tripod_hidden_rim_contact_endpoint_or_internal_nonattach
        (S := S) hno_cross P T hsource_clean z hzPath hzRim
        hzNotBoundary with
    hend | hinternal
  · rcases hend with hz_left | hz_right
    · exact hleft_off (by simpa [hz_left] using hzPath)
    · exact hright_off (by simpa [hz_right] using hzPath)
  · have hleg_off :
        forall x : V, forall i : Fin 3, x ∈ (T.leg i).support ->
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet := by
      intro _x _i _hxLeg j _hji
      exact hfeet_off j
    have hrim_off :
        forall x : V, forall i : Fin 3, x ∈ Walk.InternalVertices (T.rim i) ->
          (forall j : Fin 3, x ≠ T.attach j) ->
            forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet := by
      intro _x _i _hxRim _hxNotAttach j _hji
      exact hfeet_off j
    exact
      left_side_tripod_hidden_internal_contact_impossible_of_off_feet_common_endpoint_off_path
        (S := S) hno_cross hno_tripod P T hzPath hinternal
        hleg_off hrim_off (Or.inl hleft_off)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
