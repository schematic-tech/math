import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.SourceFactConstructors

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Boundary-clean common-end lift for a left side-tripod of the canonical
split.  This sorts the three feet on `P` and dispatches the old-left and
old-right common-end cases. -/
theorem canonicalOfNoCross_left_tripod_lift_common_endpoint_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.BoundaryClean)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (_hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x)
    (hend : x = T.left ∨ x = T.right) :
    Nonempty S.Tripod := by
  classical
    have hpath_contacts :
        forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m :=
      GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean
        P hno_cross T hclean
    have hall :
        forall r : Fin 3, T.boundary r ∈ P.pathSet :=
      GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_boundaryClean
        P hno_cross hno_tripod T hclean
    rcases P.exists_ordered_tripod_boundary_indices T hall with
      ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
    rcases hend with hx_left | hx_right
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered
          P hno_cross T hij hik hjk
          (T.boundaryClean_leg_not_nil hclean i)
          (T.boundaryClean_leg_not_nil hclean j)
          (hall i) (hall j) (hall k)
          hij_order hjk_order hpath_contacts q hx_left ha hq_path hq_outside
          hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_right_endpoint_ordered
          P hno_cross T hij hik hjk
          (T.boundaryClean_leg_not_nil hclean i)
          (T.boundaryClean_leg_not_nil hclean j)
          (hall i) (hall j) (hall k)
          hij_order hjk_order hpath_contacts q hx_right ha hq_path hq_outside
          hq_clean

/-- Right-side version of
`canonicalOfNoCross_left_tripod_lift_common_endpoint_boundaryClean`, obtained
from the left-side theorem for `P.reverse`. -/
theorem canonicalOfNoCross_right_tripod_lift_common_endpoint_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.BoundaryClean)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x)
    (hend : x = T.left ∨ x = T.right) :
    Nonempty S.Tripod := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety =
        (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety :=
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc ▸ T
  have hclean_rev : Trev.BoundaryClean :=
    Tripod.cast_boundaryClean hSoc T hclean
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_endpoint_boundaryClean
      P.reverse hno_cross hno_tripod Trev hclean_rev q
      (by simpa using ha)
      hq_path
      (by
        intro w hw
        simpa using hq_side w hw)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro w hw hwT
        exact hq_clean w hw (by simpa [Trev] using hwT))
      (by simpa [Trev] using hend)

/-- Direct common-end lift for a left side-tripod under the source hypotheses.

This is the source sentence "then `Q, P_1, P_2, P_3` have a common end; but
again it follows easily that there is a tripod" with the artificial
`BoundaryClean` detour removed.  Path-contact normalization puts all three feet
on the cut path, and nontrivial legs keep those feet off the old rims; the
common-end constructor then builds the ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall r : Fin 3, Not (T.leg r).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (_hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x)
    (hend : x = T.left ∨ x = T.right) :
    Nonempty S.Tripod := by
  classical
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  rcases hend with hx_left | hx_right
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_left_endpoint_ordered
        P hno_cross T hij hik hjk (hleg_not_nil i) (hleg_not_nil j)
        (hall i) (hall j) (hall k)
        hij_order hjk_order hpath_contacts q hx_left ha hq_path hq_outside
        hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_right_endpoint_ordered
        P hno_cross T hij hik hjk (hleg_not_nil i) (hleg_not_nil j)
        (hall i) (hall j) (hall k)
        hij_order hjk_order hpath_contacts q hx_right ha hq_path hq_outside
        hq_clean

/-- Right-side direct common-end lift under the source hypotheses.

This is the right-side analogue of
`canonicalOfNoCross_left_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil`.
It keeps the source construction symmetric: the right side of the canonical
split is the left side for `P.reverse`, so the already checked left-side
constructor applies after casting the tripod and its hypotheses across that
equality. -/
theorem canonicalOfNoCross_right_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall r : Fin 3, Not (T.leg r).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_side : forall w : V, w ∈ q.support -> w ∈ P.rightSide)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (Exists fun r : Fin 3 =>
            w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
          w = x)
    (hend : x = T.left ∨ x = T.right) :
    Nonempty S.Tripod := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  have hpath_contacts_rev :
      forall z : V, z ∈ P.reverse.pathSet -> z ∈ Trev.vertexSet ->
        Exists fun m : Fin 3 => z = Trev.boundary m := by
    intro z hzPath hzT
    have hzPathP : z ∈ P.pathSet := by
      simpa using hzPath
    have hzTorig : z ∈ T.vertexSet := by
      simpa [Trev] using hzT
    simpa [Trev] using hpath_contacts z hzPathP hzTorig
  have hleg_not_nil_rev :
      forall r : Fin 3, Not (Trev.leg r).Nil := by
    intro r hnil
    exact hleg_not_nil r
      ((Tripod.cast_leg_nil hSoc.symm T r).mp (by
        simpa [Trev] using hnil))
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil
      P.reverse hno_cross hno_tripod Trev hpath_contacts_rev
      hleg_not_nil_rev q
      (by simpa using ha)
      hq_path
      (by
        intro w hw
        simpa using hq_side w hw)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro w hw hwT
        exact hq_clean w hw (by simpa [Trev] using hwT))
      (by simpa [Trev] using hend)

/-- Source side-boundary contacts are impossible after cut-path contact
normalization and nontrivial legs.

This is the direct formal form of the GM IX `(2.4)` side-tripod sentence:
once every contact with the induced cut path is one of the three feet, a
remaining contact on the side boundary arc is either a common old rim end or a
collapsed leg.  The collapsed leg contradicts `hleg_not_nil`, while the common
end is lifted to an ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_no_arc_contact_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall r : Fin 3, Not (T.leg r).Nil)
    {x : V}
    (hxArc : x ∈ P.leftBoundaryArc)
    (hxT : x ∈ T.vertexSet) :
    False := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_arc_contact_common_endpoint_or_leg_nil
        P hno_cross hno_tripod T hpath_contacts hxArc hxT with
    hend | hnil
  · let q : S.graph.Walk x x := SimpleGraph.Walk.nil
    have hq_path : q.IsPath := by
      change (SimpleGraph.Walk.nil : S.graph.Walk x x).IsPath
      exact SimpleGraph.Walk.IsPath.nil
    have hq_side : forall w : V, w ∈ q.support -> w ∈ P.leftSide := by
      intro w hw
      have hwx : w = x := by
        simpa [q] using hw
      simpa [hwx] using P.leftBoundaryArc_subset_leftSide hxArc
    have hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside := by
      intro w hw
      have hwx : w = x := by
        simpa [q] using hw
      simpa [hwx] using P.leftBoundaryArc_subset_outside hxArc
    have hq_clean :
        forall w : V,
          w ∈ q.support ->
            (Exists fun r : Fin 3 =>
              w ∈ (T.rim r).support ∨ w ∈ (T.leg r).support) ->
            w = x := by
      intro w hw _hwT
      simpa [q] using hw
    exact hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil
        P hno_cross hno_tripod T hpath_contacts hleg_not_nil
        q hxArc hq_path hq_side hq_outside hq_clean hend)
  · rcases hnil with ⟨r, _hxrim, hnilr⟩
    exact hleg_not_nil r hnilr

/-- Right-side version of
`canonicalOfNoCross_left_tripod_no_arc_contact_of_path_contacts_no_leg_nil`,
obtained by reversing the cut path. -/
theorem canonicalOfNoCross_right_tripod_no_arc_contact_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall r : Fin 3, Not (T.leg r).Nil)
    {x : V}
    (hxArc : x ∈ P.rightBoundaryArc)
    (hxT : x ∈ T.vertexSet) :
    False := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_no_arc_contact_of_path_contacts_no_leg_nil
      P.reverse hno_cross hno_tripod Trev
      (by
        intro z hzPath hzT
        simpa [Trev] using hpath_contacts z (by simpa using hzPath)
          (by simpa [Trev] using hzT))
      (by
        intro r hnil
        exact hleg_not_nil r
          ((Tripod.cast_leg_nil hSoc.symm T r).mp (by simpa [Trev] using hnil)))
      (by simpa using hxArc)
      (by simpa [Trev] using hxT)

/-- Boundary cleanliness follows from the source path-contact normalization
and nontrivial legs.

The side-boundary arc cases are discharged by
`canonicalOfNoCross_left_tripod_no_arc_contact_of_path_contacts_no_leg_nil`;
the cut-path cases are exactly `hpath_contacts`. -/
theorem canonicalOfNoCross_left_tripod_boundaryClean_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall r : Fin 3, Not (T.leg r).Nil) :
    T.BoundaryClean := by
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_boundaryClean_of_arc_path_contacts_of_no_leg_nil
      P hno_cross T ?_ hpath_contacts hleg_not_nil
  intro z hzArc hzT
  exact False.elim
    (GMIX24Split.canonicalOfNoCross_left_tripod_no_arc_contact_of_path_contacts_no_leg_nil
      P hno_cross hno_tripod T hpath_contacts hleg_not_nil hzArc hzT)

/-- Right-side version of
`canonicalOfNoCross_left_tripod_boundaryClean_of_path_contacts_no_leg_nil`. -/
theorem canonicalOfNoCross_right_tripod_boundaryClean_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall r : Fin 3, Not (T.leg r).Nil) :
    T.BoundaryClean := by
  refine
    GMIX24Split.canonicalOfNoCross_right_tripod_boundaryClean_of_arc_path_contacts_of_no_leg_nil
      P hno_cross T ?_ hpath_contacts hleg_not_nil
  intro z hzArc hzT
  exact False.elim
    (GMIX24Split.canonicalOfNoCross_right_tripod_no_arc_contact_of_path_contacts_no_leg_nil
      P hno_cross hno_tripod T hpath_contacts hleg_not_nil hzArc hzT)

/-- Direct residual-source package from the source side-tripod hypotheses.

Endpoint residuals produce an ambient tripod by the common-end lift above; nil
leg residuals contradict the nontrivial-leg hypothesis. -/
def LeftTripodResidualSourceFacts.of_path_contacts_no_leg_nil_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (i : Fin 3),
        Not (T.leg i).Nil) :
    GMIX24Split.LeftTripodResidualSourceFacts P hno_cross where
  path_contacts := hpath_contacts
  residual_impossible := by
    intro T x a q _hxT ha hq_path hq_side hq_outside hq_clean
      i j k _hij _hik _hjk _hij_order _hjk_order hresidual
    rcases hresidual with hend | hnil
    · exact hno_tripod
        (GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil
          P hno_cross hno_tripod T (hpath_contacts T) (hleg_not_nil T)
          q ha hq_path hq_side hq_outside hq_clean hend)
    · rcases hnil with ⟨r, _hr, _hxrim, hnilr⟩
      exact hleg_not_nil T r hnilr

/-- Source side-tripod freeness from the literal path-contact and nontrivial
leg hypotheses.

This is the direct form of the GM IX `(2.4)` side-tripod paragraph used by the
statement route below: path-contact normalization says that the induced cut
path meets a side tripod only at its three feet, and nontrivial legs remove the
degenerate zero-linkage residual.  The remaining common-end residual is closed
by `canonicalOfNoCross_left_tripod_lift_common_endpoint_of_path_contacts_no_leg_nil`. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (i : Fin 3),
        Not (T.leg i).Nil) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :=
  GMIX24Split.LeftTripodResidualSourceFacts.left_tripod_free
    P hno_cross hno_tripod
    (GMIX24Split.LeftTripodResidualSourceFacts.of_path_contacts_no_leg_nil_common_endpoint
      P hno_cross hno_tripod hpath_contacts hleg_not_nil)

/-- Reverse-left side-tripod freeness from path-contact normalization and
nontrivial legs.  This is the original right side of the split, stated in the
same reverse form used by the source induction wrappers. -/
theorem canonicalOfNoCross_reverse_left_tripod_free_of_path_contacts_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hpath_contacts :
      forall
        (T :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (z : V),
        z ∈ P.reverse.pathSet -> z ∈ T.vertexSet ->
          Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil :
      forall
        (T :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        (i : Fin 3),
        Not (T.leg i).Nil) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod) :=
  GMIX24Split.canonicalOfNoCross_left_tripod_free_of_path_contacts_no_leg_nil
    P.reverse hno_cross hno_tripod hpath_contacts hleg_not_nil

/-- Boundary-clean left side tripods are impossible in an ambient tripod-free
society.

This is the reusable form of the source sentence after the common-end lift has
been proved: boundary cleanliness reduces the side-tripod residual to the
common-end case, and the lift constructs an ambient tripod, contradicting the
ambient no-tripod hypothesis. -/
theorem canonicalOfNoCross_left_tripod_free_of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hclean :
      forall
        T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod,
          T.BoundaryClean) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  exact
    GMIX24Split.LeftTripodEndpointSourceFacts.left_tripod_free
      P hno_cross hno_tripod
      (GMIX24Split.LeftTripodEndpointSourceFacts.of_endpoint_lift
        P hno_cross hno_tripod hclean
        (by
          intro T x a q _hxT ha hq_path hq_side hq_outside hq_clean hend
          exact
            GMIX24Split.canonicalOfNoCross_left_tripod_lift_common_endpoint_boundaryClean
              P hno_cross hno_tripod T (hclean T) q ha hq_path
              hq_side hq_outside hq_clean hend))

/-- Reverse-left form of
`canonicalOfNoCross_left_tripod_free_of_boundaryClean`.

This is the form consumed by the statement-level source wrappers, because the
right side of the original cut is represented there as the left side of
`P.reverse`. -/
theorem canonicalOfNoCross_reverse_left_tripod_free_of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hclean :
      forall
        T : (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod,
          T.BoundaryClean) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod) :=
  GMIX24Split.canonicalOfNoCross_left_tripod_free_of_boundaryClean
    P.reverse hno_cross hno_tripod hclean

theorem left_three_connected_of_lift_separation
    {S : GeneralSociety V} {P : GMIX24CutPath S}
    (D : GMIX24Split S P)
    (hthree : S.ThreeConnected)
    (hlift :
      forall T : Separation D.leftSociety.graph,
        D.leftSociety.boundarySet ⊆ T.left ->
          ((T.right \ T.left) ∩ D.leftSociety.activeSet).Nonempty ->
            T.OrderAtMost 2 ->
              Exists fun U : Separation S.graph =>
                S.boundarySet ⊆ U.left ∧
                  ((U.right \ U.left) ∩ S.activeSet).Nonempty ∧
                    U.OrderAtMost 2) :
    D.leftSociety.ThreeConnected := by
  intro T hboundary hright horder
  rcases hlift T hboundary hright horder with
    ⟨U, hUboundary, hUright, hUorder⟩
  exact hthree U hUboundary hUright hUorder

theorem right_three_connected_of_lift_separation
    {S : GeneralSociety V} {P : GMIX24CutPath S}
    (D : GMIX24Split S P)
    (hthree : S.ThreeConnected)
    (hlift :
      forall T : Separation D.rightSociety.graph,
        D.rightSociety.boundarySet ⊆ T.left ->
          ((T.right \ T.left) ∩ D.rightSociety.activeSet).Nonempty ->
            T.OrderAtMost 2 ->
              Exists fun U : Separation S.graph =>
                S.boundarySet ⊆ U.left ∧
                  ((U.right \ U.left) ∩ S.activeSet).Nonempty ∧
                    U.OrderAtMost 2) :
    D.rightSociety.ThreeConnected := by
  intro T hboundary hright horder
  rcases hlift T hboundary hright horder with
    ⟨U, hUboundary, hUright, hUorder⟩
  exact hthree U hUboundary hUright hUorder

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
