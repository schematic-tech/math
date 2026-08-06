import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.PathContactNormalization

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- The remaining source facts needed for the left side-tripod paragraph of
GM IX `(2.4)`.

The source proof derives these from the three disjoint side paths `Q_i` and
the final path to the opposite boundary arc: all side-tripod feet are on the
cut path, cut-path contacts with the side tripod are only those feet, and the
clean outside tail starts on the median branch after the three feet are
ordered along the cut path. -/
structure LeftTripodSourceFacts [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) : Prop where
  all_feet :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (i : Fin 3),
      T.boundary i ∈ P.pathSet
  path_contacts :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (z : V),
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m
  median_branch :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
      a ∈ P.leftBoundaryArc ->
      q.IsPath ->
      (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
      (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
      (forall w : V,
        w ∈ q.support ->
          (Exists fun i : Fin 3 =>
            w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) ->
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j)

namespace LeftTripodSourceFacts

theorem left_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (F : LeftTripodSourceFacts P hno_cross) :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
      a ∈ P.leftBoundaryArc ->
      q.IsPath ->
      (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
      (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
      (forall w : V,
        w ∈ q.support ->
          (Exists fun i : Fin 3 =>
            w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) ->
      Nonempty S.Tripod := by
  intro T x a q hxT ha hq_path hq_side hq_outside hq_clean
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_of_median_branch
      P hno_cross T (F.all_feet T) q ha hq_path hq_outside
      (F.path_contacts T)
      (F.median_branch T x a q hxT ha hq_path hq_side hq_outside
        hq_clean)
      hq_clean

theorem left_tripod_free
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (F : LeftTripodSourceFacts P hno_cross) :
    Not (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  intro hT
  rcases hT with ⟨T⟩
  obtain ⟨x, a, q, hxT, ha, hq_path, hq_side, hq_outside,
      hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary
      P hno_cross T ⟨0, F.all_feet T 0⟩
  exact hno_tripod
    (LeftTripodSourceFacts.left_clean_tail P hno_cross F
      T x a q hxT ha hq_path hq_side hq_outside hq_clean)

end LeftTripodSourceFacts

/-- Reduced source facts for the left side-tripod paragraph.

The `all_feet` field is no longer primitive here: with the mixed-foot
constructors above, it follows from ambient tripod-freeness once path contacts
with `P` are normalized.  What remains as source input is exactly the
normalization of path contacts and the median-branch assertion for the final
clean outside tail. -/
structure LeftTripodContactSourceFacts [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) : Prop where
  path_contacts :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (z : V),
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m
  median_branch :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
      a ∈ P.leftBoundaryArc ->
      q.IsPath ->
      (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
      (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
      (forall w : V,
        w ∈ q.support ->
          (Exists fun i : Fin 3 =>
            w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) ->
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j)

namespace LeftTripodContactSourceFacts

theorem to_source_facts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (F : LeftTripodContactSourceFacts P hno_cross) :
    LeftTripodSourceFacts P hno_cross where
  all_feet := by
    intro T i
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
        P hno_cross hno_tripod T (F.path_contacts T) i
  path_contacts := F.path_contacts
  median_branch := F.median_branch

theorem left_tripod_free
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (F : LeftTripodContactSourceFacts P hno_cross) :
    Not (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :=
  LeftTripodSourceFacts.left_tripod_free P hno_cross hno_tripod
    (LeftTripodContactSourceFacts.to_source_facts
      P hno_cross hno_tripod F)

end LeftTripodContactSourceFacts

/-- Source facts with the side-tripod median branch reduced to the exact
checked residual cases.

The `residual_impossible` field is intentionally narrower than the old
`median_branch` field: it only has to rule out the two common-end cases and
the normalized degenerate non-median rim-foot cases left by
`...median_branch_or_residual`.  The degenerate branch is stated as
`(T.leg r).Nil`, after `Tripod.boundary_mem_rim_eq_attach` and
`Tripod.boundary_eq_attach_iff_leg_nil` have removed the old zero-length
linkage. -/
structure LeftTripodResidualSourceFacts [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) : Prop where
  path_contacts :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (z : V),
      z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m
  residual_impossible :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
      a ∈ P.leftBoundaryArc ->
      q.IsPath ->
      (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
      (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
      (forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x) ->
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          Not
            ((x = T.left ∨ x = T.right) ∨
              Exists fun r : Fin 3 =>
                (r = i ∨ r = k) ∧
                  x ∈ Walk.InternalVertices (T.rim r) ∧
                    (T.leg r).Nil)

namespace LeftTripodResidualSourceFacts

def of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hclean :
      forall
        T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
          T.BoundaryClean)
    (hresidual_impossible :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (x a : V) (q : S.graph.Walk x a),
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
        a ∈ P.leftBoundaryArc ->
        q.IsPath ->
        (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
        (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
        (forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) ->
        forall {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not
              ((x = T.left ∨ x = T.right) ∨
                Exists fun r : Fin 3 =>
                  (r = i ∨ r = k) ∧
                    x ∈ Walk.InternalVertices (T.rim r) ∧
                      (T.leg r).Nil)) :
    LeftTripodResidualSourceFacts P hno_cross where
  path_contacts := by
    intro T z hzPath hzT
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean
        P hno_cross T (hclean T) z hzPath hzT
  residual_impossible := hresidual_impossible

theorem to_contact_source_facts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (F : LeftTripodResidualSourceFacts P hno_cross) :
    LeftTripodContactSourceFacts P hno_cross where
  path_contacts := F.path_contacts
  median_branch := by
    intro T x a q hxT ha hq_path hq_side hq_outside hq_clean
      i j k hij hik hjk hij_order hjk_order
    have hall :
        forall r : Fin 3, T.boundary r ∈ P.pathSet :=
      GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
        P hno_cross hno_tripod T (F.path_contacts T)
    have hclass :=
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha
        (fun r : Fin 3 => hall (fin3Order i j k r))
        hq_path hij_order hjk_order hq_outside (F.path_contacts T)
        hq_clean
    rcases hclass with hmedian | hresidual
    · exact hmedian
    · exact False.elim
        (F.residual_impossible T x a q hxT ha hq_path hq_side hq_outside
          hq_clean hij hik hjk hij_order hjk_order
          hresidual)

theorem left_tripod_free
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (F : LeftTripodResidualSourceFacts P hno_cross) :
    Not (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :=
  LeftTripodContactSourceFacts.left_tripod_free
    P hno_cross hno_tripod
    (LeftTripodResidualSourceFacts.to_contact_source_facts
      P hno_cross hno_tripod F)

end LeftTripodResidualSourceFacts

/-- Boundary-clean side-tripod facts with the final residual reduced to the
literal common-end obstruction.

The zero-leg non-median branch is no longer part of this interface: for a
boundary-clean tripod it is impossible because a nil leg makes a named
boundary foot an internal rim attachment.  Thus the only remaining source
argument here is exactly the paper's sentence that `Q, P_1, P_2, P_3` cannot
have a common end without producing an ambient tripod. -/
structure LeftTripodEndpointSourceFacts [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) : Prop where
  boundary_clean :
    forall
      T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
        T.BoundaryClean
  endpoint_impossible :
    forall
      (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
      (x a : V) (q : S.graph.Walk x a),
      (Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
      a ∈ P.leftBoundaryArc ->
      q.IsPath ->
      (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
      (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
      (forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x) ->
      Not (x = T.left ∨ x = T.right)

namespace LeftTripodEndpointSourceFacts

def of_endpoint_lift
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hclean :
      forall
        T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
          T.BoundaryClean)
    (hlift :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (x a : V) (q : S.graph.Walk x a),
        (Exists fun r : Fin 3 =>
          x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support) ->
        a ∈ P.leftBoundaryArc ->
        q.IsPath ->
        (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ->
        (forall w : V, w ∈ q.support -> w ∈ P.outside) ->
        (forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x) ->
        x = T.left ∨ x = T.right ->
          Nonempty S.Tripod) :
    LeftTripodEndpointSourceFacts P hno_cross where
  boundary_clean := hclean
  endpoint_impossible := by
    intro T x a q hxT ha hq_path hq_side hq_outside hq_clean hend
    exact hno_tripod
      (hlift T x a q hxT ha hq_path hq_side hq_outside hq_clean hend)

def to_residual_source_facts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (F : LeftTripodEndpointSourceFacts P hno_cross) :
    LeftTripodResidualSourceFacts P hno_cross :=
  LeftTripodResidualSourceFacts.of_boundaryClean P hno_cross
    F.boundary_clean
    (by
      intro T x a q hxT ha hq_path hq_side hq_outside hq_clean
        i j k _hij _hik _hjk _hij_order _hjk_order hresidual
      rcases hresidual with hend | hnil
      · exact
          F.endpoint_impossible T x a q hxT ha hq_path hq_side
            hq_outside hq_clean hend
      · exact
          GMIX24Split.tripod_leg_nil_residual_impossible_of_boundaryClean
            T (F.boundary_clean T) hnil)

theorem left_tripod_free
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (F : LeftTripodEndpointSourceFacts P hno_cross) :
    Not (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :=
  LeftTripodResidualSourceFacts.left_tripod_free
    P hno_cross hno_tripod
    (LeftTripodEndpointSourceFacts.to_residual_source_facts P hno_cross F)

end LeftTripodEndpointSourceFacts


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
