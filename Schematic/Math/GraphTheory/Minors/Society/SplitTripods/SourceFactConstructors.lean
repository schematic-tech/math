import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.ReverseFreeness

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Build contact source facts once path contacts are normalized and an
ordered-foot eliminator identifies the median branch.  This centralizes the
common all-feet argument used by the ordered-leg variants below. -/
def LeftTripodContactSourceFacts.of_path_contacts_median_eliminator
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
    (hmedian :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        (x a : V) (q : S.graph.Walk x a),
        (Exists fun i : Fin 3 =>
          x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support) ->
        a ∈ P.leftBoundaryArc ->
        q.IsPath ->
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
          (forall r : Fin 3, T.boundary r ∈ P.pathSet) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j)) :
    GMIX24Split.LeftTripodContactSourceFacts P hno_cross where
  path_contacts := hpath_contacts
  median_branch := by
    intro T x a q hxT ha hq_path _hq_side hq_outside hq_clean
      i j k hij hik hjk hij_order hjk_order
    exact hmedian T x a q hxT ha hq_path hq_outside hq_clean
      hij hik hjk hij_order hjk_order
      (GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
        P hno_cross hno_tripod T (hpath_contacts T))

/-- Contact source facts from path-contact normalization and the exact outer
ordered-leg dichotomy now closed by the direct residual constructors.

This is the side-tripod paragraph with the source clean-tail classifier already
internalized: once the three feet are ordered on the induced cut path, either
outer ordered leg being nontrivial is enough to force the clean tail onto the
median branch under ambient tripod-freeness. -/
def LeftTripodContactSourceFacts.of_path_contacts_ordered_first_or_last_non_nil
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
    GMIX24Split.LeftTripodContactSourceFacts P hno_cross :=
  GMIX24Split.LeftTripodContactSourceFacts.of_path_contacts_median_eliminator
    P hno_cross hno_tripod hpath_contacts (by
    intro T x a q hxT ha hq_path hq_outside hq_clean
      i j k hij hik hjk hij_order hjk_order hall
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_or_last_non_nil
        P hno_cross hno_tripod T hij hik hjk
        (hordered_first_or_last_not_nil T hij hik hjk hij_order hjk_order)
        q hxT ha (fun r : Fin 3 => hall (fin3Order i j k r))
        hq_path hij_order hjk_order hq_outside (hpath_contacts T) hq_clean)

/-- Residual source facts from path-contact normalization and the outer-leg
first/last dichotomy. -/
def LeftTripodResidualSourceFacts.of_path_contacts_ordered_first_or_last_non_nil
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
    GMIX24Split.LeftTripodResidualSourceFacts P hno_cross :=
  GMIX24Split.LeftTripodContactSourceFacts.to_residual_source_facts
    P hno_cross
    (GMIX24Split.LeftTripodContactSourceFacts.of_path_contacts_ordered_first_or_last_non_nil
      P hno_cross hno_tripod hpath_contacts
      hordered_first_or_last_not_nil)

/-- Reverse-left form of the ordered first/last side-tripod residual package. -/
def LeftTripodResidualSourceFacts.of_reverse_path_contacts_ordered_first_or_last_non_nil
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
    (hordered_first_or_last_not_nil :
      forall
        (T :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.reverse.path (T.boundary i) <
              Walk.supportIndex P.reverse.path (T.boundary j) ->
            Walk.supportIndex P.reverse.path (T.boundary j) <
              Walk.supportIndex P.reverse.path (T.boundary k) ->
            Not (T.leg i).Nil ∨ Not (T.leg k).Nil) :
    GMIX24Split.LeftTripodResidualSourceFacts P.reverse hno_cross :=
  GMIX24Split.LeftTripodResidualSourceFacts.of_path_contacts_ordered_first_or_last_non_nil
    P.reverse hno_cross hno_tripod hpath_contacts
    hordered_first_or_last_not_nil

/-- Left side-tripods are impossible when the ordered source proof can close
either of the two nontrivial-leg patterns needed by the local constructors.

This is a direct side-tripod eliminator, not a statement-level handoff: after
the three feet are sorted on the cut path and the clean outside tail is chosen,
it uses the `last`-nontrivial residual constructor if available, and otherwise
uses the complementary `outer`-nontrivial constructor.  The final step is the
same ambient-tripod lift as in the source proof. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_ordered_last_or_outer_non_nil
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
    (hordered_last_or_outer_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg k).Nil ∨
              (Not (T.leg i).Nil ∧ Not (T.leg j).Nil)) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) := by
  classical
  intro hT
  rcases hT with ⟨T⟩
  have hall :
      forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T (hpath_contacts T)
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      _hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
    rcases
        hordered_last_or_outer_not_nil T hij hik hjk hij_order hjk_order with
      hlast | houter
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_last_non_nil
          P hno_cross hno_tripod T hij hik hjk hlast q hxT ha
          (fun r : Fin 3 => hall (fin3Order i j k r)) hq_path
          hij_order hjk_order hq_outside (hpath_contacts T) hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_non_nil
          P hno_cross hno_tripod T hij hik hjk houter.1 q
          hxT ha (fun r : Fin 3 => hall (fin3Order i j k r)) hq_path
          hij_order hjk_order hq_outside (hpath_contacts T) hq_clean
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q hmedian ha
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside (hpath_contacts T)
      hq_clean_vertex)

/-- Contact source facts from the exact ordered-leg disjunction left by the
source side-tripod paragraph.

After the three side-tripod feet have been sorted on the induced cut path, the
formal residual analysis has two constructive closures: either the last
ordered leg is nontrivial, or the first two ordered legs are nontrivial.  This
packages precisely that local dichotomy as the median-branch fact used by the
canonical induction step. -/
def LeftTripodContactSourceFacts.of_path_contacts_ordered_last_or_outer_non_nil
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
    (hordered_last_or_outer_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg k).Nil ∨
              (Not (T.leg i).Nil ∧ Not (T.leg j).Nil)) :
    GMIX24Split.LeftTripodContactSourceFacts P hno_cross :=
  GMIX24Split.LeftTripodContactSourceFacts.of_path_contacts_ordered_first_or_last_non_nil
    P hno_cross hno_tripod hpath_contacts (by
      intro T i j k hij hik hjk hij_order hjk_order
      rcases hordered_last_or_outer_not_nil T hij hik hjk hij_order hjk_order with
        hlast | houter
      · exact Or.inr hlast
      · exact Or.inl houter.1)

/-- Residual source facts from path-contact normalization and the ordered
`last-or-outer` nontrivial-leg dichotomy. -/
def LeftTripodResidualSourceFacts.of_path_contacts_ordered_last_or_outer_non_nil
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
    (hordered_last_or_outer_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg k).Nil ∨
              (Not (T.leg i).Nil ∧ Not (T.leg j).Nil)) :
    GMIX24Split.LeftTripodResidualSourceFacts P hno_cross :=
  GMIX24Split.LeftTripodContactSourceFacts.to_residual_source_facts
    P hno_cross
    (GMIX24Split.LeftTripodContactSourceFacts.of_path_contacts_ordered_last_or_outer_non_nil
      P hno_cross hno_tripod hpath_contacts
      hordered_last_or_outer_not_nil)

/-- Reverse-left form of the ordered `last-or-outer` side-tripod residual
package.

This is the source-proof symmetry for the right canonical society: the right
side of the original cut is treated as the left side of `P.reverse`. -/
def LeftTripodResidualSourceFacts.of_reverse_path_contacts_ordered_last_or_outer_non_nil
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
    (hordered_last_or_outer_not_nil :
      forall
        (T :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.reverse.path (T.boundary i) <
              Walk.supportIndex P.reverse.path (T.boundary j) ->
            Walk.supportIndex P.reverse.path (T.boundary j) <
              Walk.supportIndex P.reverse.path (T.boundary k) ->
            Not (T.leg k).Nil ∨
              (Not (T.leg i).Nil ∧ Not (T.leg j).Nil)) :
    GMIX24Split.LeftTripodResidualSourceFacts P.reverse hno_cross :=
  GMIX24Split.LeftTripodResidualSourceFacts.of_path_contacts_ordered_last_or_outer_non_nil
    P.reverse hno_cross hno_tripod hpath_contacts
    hordered_last_or_outer_not_nil

/-- Contact source facts from path-contact normalization and the source-sharp
last-leg nontrivial hypothesis.

For any ordering of the three feet along the cut path, only the terminal
ordered leg is required to be nontrivial; endpoint and collapsed-first residuals
are eliminated internally by the direct common-end constructors. -/
def LeftTripodContactSourceFacts.of_path_contacts_ordered_last_non_nil
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
    (hordered_last_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg k).Nil) :
    GMIX24Split.LeftTripodContactSourceFacts P hno_cross :=
  GMIX24Split.LeftTripodContactSourceFacts.of_path_contacts_ordered_first_or_last_non_nil
    P hno_cross hno_tripod hpath_contacts (by
      intro T i j k hij hik hjk hij_order hjk_order
      exact Or.inr (hordered_last_not_nil T hij hik hjk hij_order hjk_order))

/-- Residual source facts from the source-sharp last-leg nontrivial
hypothesis. -/
def LeftTripodResidualSourceFacts.of_path_contacts_ordered_last_non_nil
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
    (hordered_last_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg k).Nil) :
    GMIX24Split.LeftTripodResidualSourceFacts P hno_cross :=
  GMIX24Split.LeftTripodContactSourceFacts.to_residual_source_facts
    P hno_cross
    (GMIX24Split.LeftTripodContactSourceFacts.of_path_contacts_ordered_last_non_nil
      P hno_cross hno_tripod hpath_contacts hordered_last_not_nil)

/-- Left side-tripods are impossible from path-contact normalization and the
last-leg source common-end construction.

This is the local source paragraph as an actual no-tripod statement: path
contacts put all three side-tripod feet on the induced cut path; the ordered
clean-tail classifier reduces the last step to the common-end or collapsed-arm
residuals; the sharpened residual constructor builds the forbidden ambient
tripod from only the last ordered nontrivial leg. -/
theorem canonicalOfNoCross_left_tripod_free_of_path_contacts_ordered_last_non_nil
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
    (hordered_last_not_nil :
      forall
        (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
        {i j k : Fin 3},
          i ≠ j -> i ≠ k -> j ≠ k ->
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ->
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) ->
            Not (T.leg k).Nil) :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :=
  GMIX24Split.LeftTripodResidualSourceFacts.left_tripod_free
    P hno_cross hno_tripod
    (GMIX24Split.LeftTripodResidualSourceFacts.of_path_contacts_ordered_last_non_nil
      P hno_cross hno_tripod hpath_contacts hordered_last_not_nil)

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
