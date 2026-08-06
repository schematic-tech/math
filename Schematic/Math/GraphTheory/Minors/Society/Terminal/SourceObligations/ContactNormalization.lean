import Schematic.Math.GraphTheory.Minors.Society.Terminal.SourceObligations.UniqueFoot

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Hidden-rim contacts are impossible once the side tripod is already
boundary-clean.

This is the closed easy subcase of the GM IX `(2.4)` hidden-contact paragraph:
if every boundary contact of the side tripod is one of its three feet, then a
cut-path vertex on a rim is a side-society boundary contact and hence one of
those feet. -/
theorem left_side_tripod_hidden_rim_contact_impossible_of_boundaryClean
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall z : V,
      z ∈ P.pathSet ->
        (∃ r : Fin 3, z ∈ (T.rim r).support) ->
          (forall m : Fin 3, z ≠ T.boundary m) -> False := by
  intro z hzPath hzRim hzNotBoundary
  have hzT : z ∈ T.vertexSet := by
    rcases hzRim with ⟨r, hzr⟩
    exact T.rim_mem_vertexSet (i := r) hzr
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean
        P hno_cross T hclean z hzPath hzT with
    ⟨m, hm⟩
  exact hzNotBoundary m hm

/-- Hidden-rim contacts are impossible once path-contact normalization has
been proved.

This is the exact target normalization used in the source side-tripod
paragraph: every cut-path contact with the side tripod is one of its three
feet.  The remaining hard work in
`left_side_tripod_hidden_rim_contact_impossible` is therefore not this final
contradiction, but the source derivation of that normalization from the
`Q, P_1, P_2, P_3` common-end argument. -/
theorem left_side_tripod_hidden_rim_contact_impossible_of_path_contacts
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall z : V,
      z ∈ P.pathSet ->
        (∃ r : Fin 3, z ∈ (T.rim r).support) ->
          (forall m : Fin 3, z ≠ T.boundary m) -> False := by
  intro z hzPath hzRim hzNotBoundary
  have hzT : z ∈ T.vertexSet := by
    rcases hzRim with ⟨r, hzr⟩
    exact T.rim_mem_vertexSet (i := r) hzr
  rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
  exact hzNotBoundary m hm

/-- A source-clean hidden cut-path contact cannot lie on any side-tripod leg.

Every cut-path vertex is a boundary vertex of the left split society.  The
GM IX `X -> Ω` cleanliness on each leg therefore turns any leg contact at such
a vertex into the named foot of that leg, contradicting hiddenness. -/
theorem left_side_tripod_hidden_path_contact_not_leg_of_source_clean
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean) :
    forall z : V,
      z ∈ P.pathSet ->
        (forall m : Fin 3, z ≠ T.boundary m) ->
          forall r : Fin 3, z ∉ (T.leg r).support := by
  intro z hzPath hzNotBoundary r hzLeg
  have hzSideBoundary :
      z ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet := by
    rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
    exact Or.inr hzPath
  exact hzNotBoundary r (hsource_clean r z hzLeg hzSideBoundary)

/-- A source-clean hidden cut-path/rim contact cannot be one of the tripod's
three leg attachments.

The attachment is the start of its linkage leg.  Since every cut-path vertex is
a boundary vertex of the left split society, the GM IX `X -> Ω` cleanliness
of that leg forces the attachment to be its terminal boundary foot, contrary
to hiddenness. -/
theorem left_side_tripod_hidden_rim_contact_not_attach_of_source_clean
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean) :
    forall z : V,
      z ∈ P.pathSet ->
        (forall m : Fin 3, z ≠ T.boundary m) ->
          forall r : Fin 3, z ≠ T.attach r := by
  intro z hzPath hzNotBoundary r hzAttach
  have hzLeg : z ∈ (T.leg r).support := by
    subst z
    exact (T.leg r).start_mem_support
  exact
    left_side_tripod_hidden_path_contact_not_leg_of_source_clean
      (S := S) hno_cross P T hsource_clean z hzPath hzNotBoundary r hzLeg

/-- Source-clean classification of an arbitrary hidden cut-path contact with a
side tripod.

The leg case is ruled out by source cleanliness.  What remains from the
tripod vertex-set decomposition is exactly the source common-end split: either
the contact is one of the two old rim endpoints, or it is an internal
non-attachment point of an old rim. -/
theorem left_side_tripod_hidden_path_contact_endpoint_or_internal_nonattach
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean) :
    forall z : V,
      z ∈ P.pathSet ->
        z ∈ T.vertexSet ->
          (forall m : Fin 3, z ≠ T.boundary m) ->
            (z = T.left ∨ z = T.right) ∨
              Exists fun r : Fin 3 =>
                z ∈ Walk.InternalVertices (T.rim r) ∧
                  forall m : Fin 3, z ≠ T.attach m := by
  intro z hzPath hzT hzNotBoundary
  rcases T.vertexSet_leg_or_rim_internal_or_endpoint hzT with hleg | hrest
  · rcases hleg with ⟨r, hzLeg⟩
    exact False.elim
      (left_side_tripod_hidden_path_contact_not_leg_of_source_clean
        (S := S) hno_cross P T hsource_clean z hzPath hzNotBoundary r hzLeg)
  · rcases hrest with hrim | hend
    · right
      rcases hrim with ⟨r, hzInternal⟩
      exact
        ⟨r, hzInternal,
          left_side_tripod_hidden_rim_contact_not_attach_of_source_clean
            (S := S) hno_cross P T hsource_clean z hzPath hzNotBoundary⟩
    · exact Or.inl hend

/-- Source-clean classification of a hidden cut-path/rim contact.

After ruling out selected feet and selected attachments, a rim support contact
with the induced cut path is either one of the two old common rim endpoints or
a genuine internal non-attachment point of one old rim.  This is the local
normal form needed by the source common-end argument. -/
theorem left_side_tripod_hidden_rim_contact_endpoint_or_internal_nonattach
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean) :
    forall z : V,
      z ∈ P.pathSet ->
        (∃ r : Fin 3, z ∈ (T.rim r).support) ->
          (forall m : Fin 3, z ≠ T.boundary m) ->
            (z = T.left ∨ z = T.right) ∨
              Exists fun r : Fin 3 =>
                z ∈ Walk.InternalVertices (T.rim r) ∧
                  forall m : Fin 3, z ≠ T.attach m := by
  intro z hzPath hzRim hzNotBoundary
  have hzT : z ∈ T.vertexSet := by
    rcases hzRim with ⟨r, hzr⟩
    exact T.rim_mem_vertexSet (i := r) hzr
  exact
    left_side_tripod_hidden_path_contact_endpoint_or_internal_nonattach
      (S := S) hno_cross P T hsource_clean z hzPath hzT hzNotBoundary

/-- Hidden cut-path contacts of a minimum source-clean side tripod have the
source residual shape: a common rim endpoint, or an internal point of a branch
whose linkage leg is nil.

This is the contact-normalization theorem actually supplied by the
well-founded descent.  It deliberately does not claim that every cut-path
contact is a named foot; that stronger claim is not made in GM IX `(2.4)` and
was the source of the abandoned legacy route. -/
theorem left_side_tripod_hidden_contact_endpoint_or_internal_nil_of_minimal
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hminimal :
      forall
        U :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
        U.LegBoundaryContactClean ->
          T.linkageLength <= U.linkageLength) :
    forall z : V,
      z ∈ P.pathSet ->
        z ∈ T.vertexSet ->
          (forall m : Fin 3, z ≠ T.boundary m) ->
            (z = T.left ∨ z = T.right) ∨
              Exists fun r : Fin 3 =>
                z ∈ Walk.InternalVertices (T.rim r) ∧
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
    exact Or.inr
      ⟨r, hzInternal,
        T.leg_nil_of_minimal_sourceClean_internal_boundary_contact
          hsource_clean hminimal r z hzInternal hzSideBoundary
          hzNotBoundary,
        hzNotAttach⟩

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
