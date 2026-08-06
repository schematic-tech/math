import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.BranchReplacement

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Source-shaped left all-path-foot side-tripod constructor.

This is the same constructor as
`..._replace_middle_branch_of_all_path_feet_path_contacts`, but with the
clean-tail hypothesis stated in the high-level source-wrapper form:
membership in some rim or leg. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_of_median_branch
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmedian :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j))
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun i : Fin 3 =>
          z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ->
        z = x) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_all_path_feet_path_contacts
    P hno_cross T holdAll q ha hq_path hq_outside hpath_contacts hmedian
    (by
      intro z hz hzT
      rcases hzT with hRim | hLeg
      · rcases hRim with ⟨i, hi⟩
        exact hq_clean z hz ⟨i, Or.inl hi⟩
      · rcases hLeg with ⟨i, hi⟩
        exact hq_clean z hz ⟨i, Or.inr hi⟩)

/-- Source-shaped right all-path-foot side-tripod constructor. -/
theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_of_median_branch
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmedian :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.reverse.path (T.boundary i) <
            Walk.supportIndex P.reverse.path (T.boundary j) ->
          Walk.supportIndex P.reverse.path (T.boundary j) <
            Walk.supportIndex P.reverse.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j))
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun i : Fin 3 =>
          z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ->
        z = x) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_all_path_feet_path_contacts
    P hno_cross T holdAll q ha hq_path hq_outside hpath_contacts hmedian
    (by
      intro z hz hzT
      rcases hzT with hRim | hLeg
      · rcases hRim with ⟨i, hi⟩
        exact hq_clean z hz ⟨i, Or.inl hi⟩
      · rcases hLeg with ⟨i, hi⟩
        exact hq_clean z hz ⟨i, Or.inr hi⟩)

theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmedian :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j))
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun i : Fin 3 =>
          z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ->
        z = x) :
    False :=
  hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_of_median_branch
      P hno_cross T holdAll q ha hq_path hq_outside hpath_contacts
      hmedian hq_clean)

/-- Under the ordered all-path-foot normalization, a clean tail cannot start
on either non-median leg in an ambient tripod-free society. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_leg_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg i).support ∨ x ∈ (T.leg k).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    False := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_ordered_leg_or_median_branch_path_contacts
      P hno_cross T hij hik hjk q
      (by
        rcases hx with hfirst | hlast
        · exact Or.inl hfirst
        · exact Or.inr (Or.inr hlast))
      ha hold hq_path hij_order hjk_order hq_outside hpath_contacts
      hq_clean_vertex)

/-- Under the ordered all-path-foot normalization, a clean tail cannot start
on either non-median rim in the nondegenerate case where that old foot is not
itself on a rim.  The remaining degenerate rim-foot case is the only local
case not covered by these direct first/last rim constructors. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_rim_nondegenerate_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      (x ∈ Walk.InternalVertices (T.rim i) ∧
        forall r : Fin 3, T.boundary i ∉ (T.rim r).support) ∨
      (x ∈ Walk.InternalVertices (T.rim k) ∧
        forall r : Fin 3, T.boundary k ∉ (T.rim r).support))
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    False := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  exact hno_tripod
    (by
      rcases hx with hfirst | hlast
      · exact
          GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_first_rim_of_ordered_indices_path_contacts
            P hno_cross T hij hik hjk q hfirst.1 hfirst.2 ha hold
            hq_path hij_order hjk_order hq_outside hpath_contacts
            hq_clean_vertex
      · exact
          GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_last_rim_of_ordered_indices_path_contacts
            P hno_cross T hij hik hjk q hlast.1 hlast.2 ha hold
            hq_path hij_order hjk_order hq_outside hpath_contacts
            hq_clean_vertex)

/-- Classification of an all-path-foot clean-tail start after the completed
non-median leg and nondegenerate-rim eliminators.

What remains, before the final source common-end argument is formalized, is
precisely endpoint contact or a degenerate non-median rim contact where the
old non-median foot is itself on a rim. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              Exists fun s : Fin 3 => T.boundary r ∈ (T.rim s).support := by
  classical
  rcases hxT with ⟨r, hxRim | hxLeg⟩
  · rcases T.rim_support_internal_or_endpoint hxRim with hxInt | hxEnd
    · rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
      · subst r
        by_cases hboundary_not_rim :
            forall s : Fin 3, T.boundary i ∉ (T.rim s).support
        · exact False.elim
            (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_rim_nondegenerate_impossible
              P hno_cross hno_tripod T hij hik hjk q
              (Or.inl ⟨hxInt, hboundary_not_rim⟩) ha hold hq_path
              hij_order hjk_order hq_outside hpath_contacts hq_clean)
        · have hdeg :
              Exists fun s : Fin 3 => T.boundary i ∈ (T.rim s).support := by
            push Not at hboundary_not_rim
            exact hboundary_not_rim
          exact Or.inr (Or.inr ⟨i, Or.inl rfl, hxInt, hdeg⟩)
      · rcases hrjk with hrj | hrk
        · subst r
          exact Or.inl (Or.inr hxInt)
        · subst r
          by_cases hboundary_not_rim :
              forall s : Fin 3, T.boundary k ∉ (T.rim s).support
          · exact False.elim
              (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_rim_nondegenerate_impossible
                P hno_cross hno_tripod T hij hik hjk q
                (Or.inr ⟨hxInt, hboundary_not_rim⟩) ha hold hq_path
                hij_order hjk_order hq_outside hpath_contacts hq_clean)
          · have hdeg :
                Exists fun s : Fin 3 => T.boundary k ∈ (T.rim s).support := by
              push Not at hboundary_not_rim
              exact hboundary_not_rim
            exact Or.inr (Or.inr ⟨k, Or.inr rfl, hxInt, hdeg⟩)
    · exact Or.inr (Or.inl hxEnd)
  · rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
    · subst r
      exact False.elim
        (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_leg_impossible
          P hno_cross hno_tripod T hij hik hjk q (Or.inl hxLeg) ha
          hold hq_path hij_order hjk_order hq_outside hpath_contacts
          hq_clean)
    · rcases hrjk with hrj | hrk
      · subst r
        exact Or.inl (Or.inl hxLeg)
      · subst r
        exact False.elim
          (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_leg_impossible
            P hno_cross hno_tripod T hij hik hjk q (Or.inr hxLeg) ha
            hold hq_path hij_order hjk_order hq_outside hpath_contacts
            hq_clean)

/-- The residual alternatives in
`canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_residual`
are genuinely disjoint from the median-branch conclusion.

This is the checked bookkeeping behind the source phrase "the paths have a
common end": once the start of the clean tail is on the middle branch, it is
neither a common rim endpoint nor an internal point of either non-median rim. -/
theorem tripod_median_branch_not_residual
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (_hik : i ≠ k) (hjk : j ≠ k)
    {x : V}
    (hmedian :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) :
    Not
      ((x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              Exists fun s : Fin 3 =>
                T.boundary r ∈ (T.rim s).support) := by
  intro hres
  rcases hres with hend | hrim
  · rcases hend with hleft | hright
    · rcases hmedian with hleg | hrimj
      · exact T.left_not_mem_leg j (by simpa [hleft] using hleg)
      · exact hrimj.2.1 hleft
    · rcases hmedian with hleg | hrimj
      · exact T.right_not_mem_leg j (by simpa [hright] using hleg)
      · exact hrimj.2.2 hright
  · rcases hrim with ⟨r, hri_or_rk, hxrim, _hdegenerate⟩
    have hrj : r ≠ j := by
      rcases hri_or_rk with hri | hrk
      · subst r
        exact hij
      · subst r
        exact fun h => hjk h.symm
    rcases hmedian with hleg | hrimj
    · have hx_attach : x = T.attach j :=
        T.legs_meet_rims_only_at_attach j r x hleg hxrim.1
      have hxrimj : x ∈ Walk.InternalVertices (T.rim j) := by
        simpa [hx_attach] using T.attach_mem_rim j
      exact Set.disjoint_left.mp (T.rim_internals_disjoint r j hrj)
        hxrim hxrimj
    · exact Set.disjoint_left.mp (T.rim_internals_disjoint r j hrj)
        hxrim hrimj

/-- Normalize the degenerate-rim residual left by
`...median_branch_or_residual`.

The residual stores an existential witness that an old non-median boundary foot
lies on some rim.  The general tripod structure forces that witness to be the
same branch and the foot to be exactly the corresponding attachment; this
lemma packages the form needed by the final common-end construction. -/
theorem tripod_degenerate_rim_residual_eq_attach
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i k : Fin 3} {x : V}
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            Exists fun s : Fin 3 =>
              T.boundary r ∈ (T.rim s).support) :
    Exists fun r : Fin 3 =>
      (r = i ∨ r = k) ∧
        x ∈ Walk.InternalVertices (T.rim r) ∧
          T.boundary r = T.attach r := by
  rcases hres with ⟨r, hr, hxrim, s, hs⟩
  exact ⟨r, hr, hxrim, T.boundary_mem_rim_eq_attach hs⟩

/-- The degenerate-rim residual is equivalently a non-median rim contact
whose old leg is trivial.

This is the form used by the source common-end proof: after the old boundary
foot is identified with its attachment, the corresponding `Q_i` contributes
no extra vertices and the residual becomes part of the common-end
configuration. -/
theorem tripod_degenerate_rim_residual_leg_nil
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i k : Fin 3} {x : V}
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            Exists fun s : Fin 3 =>
              T.boundary r ∈ (T.rim s).support) :
    Exists fun r : Fin 3 =>
      (r = i ∨ r = k) ∧
        x ∈ Walk.InternalVertices (T.rim r) ∧
          (T.leg r).Nil := by
  rcases GMIX24Split.tripod_degenerate_rim_residual_eq_attach T hres with
    ⟨r, hr, hxrim, hboundary_attach⟩
  exact ⟨r, hr, hxrim,
    (T.boundary_eq_attach_iff_leg_nil r).mp hboundary_attach⟩

/-- Convert the normalized attachment-equality residual back to the raw
residual shape emitted by the classifier. -/
theorem tripod_refined_residual_to_residual
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i k : Fin 3} {x : V}
    (hres :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              T.boundary r = T.attach r) :
    (x = T.left ∨ x = T.right) ∨
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            Exists fun s : Fin 3 =>
              T.boundary r ∈ (T.rim s).support := by
  rcases hres with hend | hrim
  · exact Or.inl hend
  · rcases hrim with ⟨r, hr, hxrim, hboundary_attach⟩
    have hboundary_rim : T.boundary r ∈ (T.rim r).support := by
      simpa [hboundary_attach] using (T.attach_mem_rim r).1
    exact Or.inr ⟨r, hr, hxrim, r, hboundary_rim⟩

/-- Convert the explicit trivial-leg residual back to the raw residual shape
emitted by the classifier. -/
theorem tripod_leg_nil_residual_to_residual
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i k : Fin 3} {x : V}
    (hres :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              (T.leg r).Nil) :
    (x = T.left ∨ x = T.right) ∨
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            Exists fun s : Fin 3 =>
              T.boundary r ∈ (T.rim s).support := by
  rcases hres with hend | hrim
  · exact Or.inl hend
  · rcases hrim with ⟨r, hr, hxrim, hleg_nil⟩
    exact
      GMIX24Split.tripod_refined_residual_to_residual T
        (i := i) (k := k) (x := x)
        (Or.inr ⟨r, hr, hxrim,
          (T.leg_nil_iff_boundary_eq_attach r).mp hleg_nil⟩)

/-- A zero-leg residual clean tail cannot start at the collapsed attachment
when that old foot lies on the cut path.

The source common-end argument treats the zero-leg branch as a degenerate
side-tripod contact.  This lemma removes the subcase where the clean tail
actually starts at the collapsed foot: the start of the tail is outside the
cut path, while the collapsed foot is on it. -/
theorem tripod_leg_nil_clean_tail_start_ne_attach_of_path_foot
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    {r : Fin 3}
    (hboundary_path : T.boundary r ∈ P.pathSet)
    (hleg_nil : (T.leg r).Nil)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside) :
    x ≠ T.attach r := by
  intro hx_attach
  have hboundary_attach : T.boundary r = T.attach r :=
    (T.leg_nil_iff_boundary_eq_attach r).mp hleg_nil
  have hx_path : x ∈ P.pathSet := by
    simpa [hx_attach, hboundary_attach] using hboundary_path
  exact (hq_outside x q.start_mem_support).2
    (by simpa [GMIX24CutPath.pathSet] using hx_path)

/-- Sharpen a zero-leg residual using the outside-clean-tail hypothesis: the
tail start is not the collapsed attachment of the zero-length old leg. -/
theorem tripod_leg_nil_residual_not_attach_of_outside
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i k : Fin 3} {x a : V} (q : S.graph.Walk x a)
    (hold : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            (T.leg r).Nil) :
    Exists fun r : Fin 3 =>
      (r = i ∨ r = k) ∧
        x ∈ Walk.InternalVertices (T.rim r) ∧
          (T.leg r).Nil ∧ x ≠ T.attach r := by
  rcases hres with ⟨r, hr, hxrim, hleg_nil⟩
  exact ⟨r, hr, hxrim, hleg_nil,
    GMIX24Split.tripod_leg_nil_clean_tail_start_ne_attach_of_path_foot
      P T q (hold r) hleg_nil hq_outside⟩

/-- The zero-leg residual is a genuine open-rim hit: after the cut-path foot has
collapsed to its attachment, the clean outside tail starts strictly on one side
or the other of that attachment along the old rim.

This is the next local datum needed for the source construction in GM IX `(2.4)`:
the residual is not merely "somewhere on the same rim"; it lies on a definite
old rim arm, so the subsequent tripod lift can split the rim at `x` and at the
collapsed foot without ambiguity. -/
theorem tripod_leg_nil_residual_rim_order_of_outside
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i k : Fin 3} {x a : V} (q : S.graph.Walk x a)
    (hold : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            (T.leg r).Nil) :
    Exists fun r : Fin 3 =>
      (r = i ∨ r = k) ∧
        x ∈ Walk.InternalVertices (T.rim r) ∧
          (T.leg r).Nil ∧
            (Walk.supportIndex (T.rim r) x <
                Walk.supportIndex (T.rim r) (T.attach r) ∨
              Walk.supportIndex (T.rim r) (T.attach r) <
                Walk.supportIndex (T.rim r) x) := by
  rcases
      GMIX24Split.tripod_leg_nil_residual_not_attach_of_outside
        P T q hold hq_outside hres with
    ⟨r, hr, hxrim, hleg_nil, hx_ne_attach⟩
  have hidx_ne :
      Walk.supportIndex (T.rim r) x ≠
        Walk.supportIndex (T.rim r) (T.attach r) := by
    intro hidx
    apply hx_ne_attach
    have hidx' :
        (T.rim r).support.idxOf x =
          (T.rim r).support.idxOf (T.attach r) := by
      simpa [Walk.supportIndex] using hidx
    exact (List.idxOf_inj hxrim.1).mp hidx'
  exact ⟨r, hr, hxrim, hleg_nil, lt_or_gt_of_ne hidx_ne⟩

/-- Arm form of the zero-leg residual.  The residual tail starts strictly on
one of the two split arms of the old rim, relative to the collapsed attachment.

The two cases are precisely the two geometric subcases that the direct GM IX
`(2.4)` construction has to handle next. -/
theorem tripod_leg_nil_residual_arm_of_outside
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i k : Fin 3} {x a : V} (q : S.graph.Walk x a)
    (hold : forall r : Fin 3, T.boundary r ∈ P.pathSet)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            (T.leg r).Nil) :
    Exists fun r : Fin 3 =>
      (r = i ∨ r = k) ∧
        x ∈ Walk.InternalVertices (T.rim r) ∧
          (T.leg r).Nil ∧ x ≠ T.attach r ∧
            ((x ∈ (T.leftToAttach r).support ∧
                x ≠ T.attach r) ∨
              (x ∈ (T.attachToRight r).support ∧
                x ≠ T.attach r)) := by
  rcases
      GMIX24Split.tripod_leg_nil_residual_not_attach_of_outside
        P T q hold hq_outside hres with
    ⟨r, hr, hxrim, hleg_nil, hx_ne_attach⟩
  have horder :
      Walk.supportIndex (T.rim r) x <
          Walk.supportIndex (T.rim r) (T.attach r) ∨
        Walk.supportIndex (T.rim r) (T.attach r) <
          Walk.supportIndex (T.rim r) x := by
    have hidx_ne :
        Walk.supportIndex (T.rim r) x ≠
          Walk.supportIndex (T.rim r) (T.attach r) := by
      intro hidx
      apply hx_ne_attach
      have hidx' :
          (T.rim r).support.idxOf x =
            (T.rim r).support.idxOf (T.attach r) := by
        simpa [Walk.supportIndex] using hidx
      exact (List.idxOf_inj hxrim.1).mp hidx'
    exact lt_or_gt_of_ne hidx_ne
  refine ⟨r, hr, hxrim, hleg_nil, hx_ne_attach, ?_⟩
  rcases horder with hbefore | hafter
  · exact Or.inl
      ⟨T.mem_leftToAttach_of_rim_supportIndex_le_attach hxrim.1
        (le_of_lt hbefore), hx_ne_attach⟩
  · exact Or.inr
      ⟨T.mem_attachToRight_of_attach_supportIndex_le_rim hxrim.1
        (le_of_lt hafter), hx_ne_attach⟩

/-- A zero-leg rim residual point is not any tripod attachment.

For its own branch this is the outside/cut-path argument; for the other two
branches it follows from internal disjointness of the old rim paths.  This is
the attachment-normalization needed before the residual case can be treated by
the literal source construction rather than by a nondegenerate shortcut. -/
theorem tripod_leg_nil_residual_not_attach_any
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i k : Fin 3} {x : V}
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            (T.leg r).Nil ∧ x ≠ T.attach r) :
    forall j : Fin 3, x ≠ T.attach j := by
  classical
  rcases hres with ⟨r, _hr, hxrim, _hnil, hx_ne_attach⟩
  intro j hx_attach
  by_cases hjr : j = r
  · exact hx_ne_attach (by simpa [hjr] using hx_attach)
  · have hxrim_j : x ∈ Walk.InternalVertices (T.rim j) := by
      simpa [hx_attach] using T.attach_mem_rim j
    exact
      Set.disjoint_left.mp (T.rim_internals_disjoint r j (fun h => hjr h.symm))
        hxrim hxrim_j

/-- A zero-leg rim residual point is on no old leg.

Any old-leg contact with a rim is forced to be the corresponding attachment, and
the previous lemma rules out all attachments. -/
theorem tripod_leg_nil_residual_not_mem_leg
    {S : GeneralSociety V}
    (T : S.Tripod)
    {i k : Fin 3} {x : V}
    (hres :
      Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            (T.leg r).Nil ∧ x ≠ T.attach r) :
    forall j : Fin 3, x ∉ (T.leg j).support := by
  classical
  rcases hres with ⟨r, hr, hxrim, hnil, hx_ne_attach⟩
  have hnot_attach :
      forall j : Fin 3, x ≠ T.attach j :=
    GMIX24Split.tripod_leg_nil_residual_not_attach_any T
      (i := i) (k := k) (x := x)
      ⟨r, hr, hxrim, hnil, hx_ne_attach⟩
  intro j hxleg
  exact hnot_attach j
    (T.legs_meet_rims_only_at_attach j r x hxleg hxrim.1)

/-- Path-contact normalization for the left arm of a nil residual.

If the residual hit `x` lies strictly on the old left-to-attachment arm of a
left side-tripod branch, then the prefix from the old left common end to `x`
stays in the ambient outside of the cut path.  The only possible cut-path
contacts of a side-tripod rim are named feet; the two other feet cannot lie on
this rim, and the own foot is the collapsed attachment, which is after the
strict prefix. -/
theorem canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} {x : V}
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r) :
    forall z : V,
      z ∈ ((T.leftToAttach r).takeUntil x hx_arm).support ->
        z ∈ P.outside := by
  classical
  have hattach_not_prefix :
      T.attach r ∉ ((T.leftToAttach r).takeUntil x hx_arm).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.leftToAttach_isPath r) hx_arm
      (by simpa [ne_eq] using hx_ne_attach.symm)
  intro z hzPrefix
  have hzArm : z ∈ (T.leftToAttach r).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach r) hx_arm
      hzPrefix
  have hzRim : z ∈ (T.rim r).support :=
    T.leftToAttach_support_subset_rim r hzArm
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_rim_support_subset_side_or_path
        P hno_cross T r hzRim with hzSide | hzPath
  · exact P.leftSide_subset_outside hzSide
  · exfalso
    rcases hpath_contacts z hzPath (T.rim_mem_vertexSet (i := r) hzRim) with
      ⟨m, hm⟩
    by_cases hmr : m = r
    · subst m
      have hboundary_rim : T.boundary r ∈ (T.rim r).support := by
        simpa [hm] using hzRim
      have hboundary_attach : T.boundary r = T.attach r :=
        T.boundary_mem_rim_eq_attach hboundary_rim
      exact hattach_not_prefix (by simpa [hm, hboundary_attach] using hzPrefix)
    · exact
        T.boundary_not_mem_rim_of_ne_index hmr
          (by simpa [hm] using hzRim)

/-- Path-contact normalization for the right arm of a nil residual.

This is the right-end analogue of
`canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts`:
the prefix from the old right common end to a strict hit on the
attachment-to-right arm is outside the cut path. -/
theorem canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} {x : V}
    (hx_arm : x ∈ (T.rightToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r) :
    forall z : V,
      z ∈ ((T.rightToAttach r).takeUntil x hx_arm).support ->
        z ∈ P.outside := by
  classical
  have hattach_not_prefix :
      T.attach r ∉ ((T.rightToAttach r).takeUntil x hx_arm).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.rightToAttach_isPath r) hx_arm
      (by simpa [ne_eq] using hx_ne_attach.symm)
  intro z hzPrefix
  have hzArm : z ∈ (T.rightToAttach r).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach r) hx_arm
      hzPrefix
  have hzRim : z ∈ (T.rim r).support :=
    T.rightToAttach_support_subset_rim r hzArm
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_rim_support_subset_side_or_path
        P hno_cross T r hzRim with hzSide | hzPath
  · exact P.leftSide_subset_outside hzSide
  · exfalso
    rcases hpath_contacts z hzPath (T.rim_mem_vertexSet (i := r) hzRim) with
      ⟨m, hm⟩
    by_cases hmr : m = r
    · subst m
      have hboundary_rim : T.boundary r ∈ (T.rim r).support := by
        simpa [hm] using hzRim
      have hboundary_attach : T.boundary r = T.attach r :=
        T.boundary_mem_rim_eq_attach hboundary_rim
      exact hattach_not_prefix (by simpa [hm, hboundary_attach] using hzPrefix)
    · exact
        T.boundary_not_mem_rim_of_ne_index hmr
          (by simpa [hm] using hzRim)

/-- The whole left-arm-prefix-plus-clean-tail walk stays outside the cut path. -/
theorem canonicalOfNoCross_left_tripod_leftArmPrefixTail_subset_outside_of_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} {x a : V}
    (hx_arm : x ∈ (T.leftToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (q : S.graph.Walk x a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside) :
    forall z : V,
      z ∈
        (T.leftArmPrefixTail
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
          hx_arm q).support ->
        z ∈ P.outside := by
  intro z hz
  have hzCases :
      z ∈
          (((T.leftToAttach r).takeUntil x hx_arm).mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).support ∨
        z ∈ q.support := by
    simpa [Tripod.leftArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
      using hz
  rcases hzCases with hzPrefixMap | hzq
  · have hzPrefix :
        z ∈ ((T.leftToAttach r).takeUntil x hx_arm).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_leftToAttach_takeUntil_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach z hzPrefix
  · exact hq_outside z hzq

/-- The whole right-arm-prefix-plus-clean-tail walk stays outside the cut path. -/
theorem canonicalOfNoCross_left_tripod_rightArmPrefixTail_subset_outside_of_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {r : Fin 3} {x a : V}
    (hx_arm : x ∈ (T.rightToAttach r).support)
    (hx_ne_attach : x ≠ T.attach r)
    (q : S.graph.Walk x a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside) :
    forall z : V,
      z ∈
        (T.rightArmPrefixTail
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
          hx_arm q).support ->
        z ∈ P.outside := by
  intro z hz
  have hzCases :
      z ∈
          (((T.rightToAttach r).takeUntil x hx_arm).mapLe
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le).support ∨
        z ∈ q.support := by
    simpa [Tripod.rightArmPrefixTail, SimpleGraph.Walk.mem_support_append_iff]
      using hz
  rcases hzCases with hzPrefixMap | hzq
  · have hzPrefix :
        z ∈ ((T.rightToAttach r).takeUntil x hx_arm).support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzPrefixMap
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_rightToAttach_takeUntil_subset_outside_of_path_contacts
        P hno_cross T hpath_contacts hx_arm hx_ne_attach z hzPrefix
  · exact hq_outside z hzq

/-- Boundary-clean side tripods have no zero-leg residual at all.

This is the formal version of the source proof's hidden cleanliness
condition: a nil leg identifies a boundary foot with its rim attachment, so
the boundary foot would be an internal rim vertex. -/
theorem tripod_leg_nil_residual_impossible_of_boundaryClean
    {S : GeneralSociety V}
    (T : S.Tripod)
    (hclean : T.BoundaryClean)
    {i k : Fin 3} {x : V} :
    Not
      (Exists fun r : Fin 3 =>
        (r = i ∨ r = k) ∧
          x ∈ Walk.InternalVertices (T.rim r) ∧
            (T.leg r).Nil) := by
  rintro ⟨r, _hr, _hxrim, hleg_nil⟩
  exact T.boundaryClean_leg_not_nil hclean r hleg_nil

/-- Normalized version of
`canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_residual`.

The raw classifier emits an existential rim contact for the degenerate
non-median branch.  This theorem immediately converts that branch to the
trivial-leg form, leaving only the median branch, the common-end branch, and
the explicit zero-leg non-median branch. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              (T.leg r).Nil := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact Or.inl hmedian
  · rcases hresidual with hend | hrim
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr
        (GMIX24Split.tripod_degenerate_rim_residual_leg_nil T hrim))

/-- Arm-normalized form of the all-path-foot side-tripod classifier.

The source proof's remaining side-tripod case is not just a nil old leg: the
clean outside path starts strictly on one of the two old rim arms adjacent to
the collapsed boundary foot.  This form is the one used by the direct residual
constructor. -/
theorem canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_arm_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              (T.leg r).Nil ∧ x ≠ T.attach r ∧
                ((x ∈ (T.leftToAttach r).support ∧
                    x ≠ T.attach r) ∨
                  (x ∈ (T.attachToRight r).support ∧
                    x ≠ T.attach r)) := by
  rcases
      GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact Or.inl hmedian
  · rcases hresidual with hend | hnil
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr
        (GMIX24Split.tripod_leg_nil_residual_arm_of_outside
          P T q
          (fun r : Fin 3 => by
            rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
            · simpa [hri, fin3Order] using hold 0
            · rcases hrjk with hrj | hrk
              · simpa [hrj, fin3Order] using hold 1
              · simpa [hrk, fin3Order] using hold 2)
          hq_outside hnil))

theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_median_branch_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmedian :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.reverse.path (T.boundary i) <
            Walk.supportIndex P.reverse.path (T.boundary j) ->
          Walk.supportIndex P.reverse.path (T.boundary j) <
            Walk.supportIndex P.reverse.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j))
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun i : Fin 3 =>
          z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ->
        z = x) :
    False :=
  hno_tripod
    (GMIX24Split.canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_of_median_branch
      P hno_cross T holdAll q ha hq_path hq_outside hpath_contacts
      hmedian hq_clean)

/-- Right-side version of the non-median-leg clean-tail contradiction, obtained
by reversing the canonical cut path. -/
theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_nonmedian_leg_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg i).support ∨ x ∈ (T.leg k).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.reverse.path (T.boundary i) <
        Walk.supportIndex P.reverse.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.reverse.path (T.boundary j) <
        Walk.supportIndex P.reverse.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
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
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_leg_impossible
      P.reverse hno_cross hno_tripod Trev hij hik hjk q
      (by simpa [Trev] using hx)
      (by simpa [Trev] using ha)
      (by
        intro r
        simpa [Trev] using hold r)
      hq_path
      (by simpa [Trev] using hij_order)
      (by simpa [Trev] using hjk_order)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro z hzPath hzT
        have hzPathP : z ∈ P.pathSet := by
          simpa using hzPath
        have hzTorig : z ∈ T.vertexSet := by
          simpa [Trev] using hzT
        simpa [Trev] using hpath_contacts z hzPathP hzTorig)
      (by
        intro z hz hzT
        exact hq_clean z hz (by simpa [Trev] using hzT))

/-- Right-side version of the nondegenerate non-median-rim clean-tail
contradiction, obtained by reversing the canonical cut path. -/
theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_nonmedian_rim_nondegenerate_impossible
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      (x ∈ Walk.InternalVertices (T.rim i) ∧
        forall r : Fin 3, T.boundary i ∉ (T.rim r).support) ∨
      (x ∈ Walk.InternalVertices (T.rim k) ∧
        forall r : Fin 3, T.boundary k ∉ (T.rim r).support))
    (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.reverse.path (T.boundary i) <
        Walk.supportIndex P.reverse.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.reverse.path (T.boundary j) <
        Walk.supportIndex P.reverse.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
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
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_nonmedian_rim_nondegenerate_impossible
      P.reverse hno_cross hno_tripod Trev hij hik hjk q
      (by
        rcases hx with hfirst | hlast
        · exact Or.inl
            ⟨by simpa [Trev] using hfirst.1,
              by
                intro r hr
                exact hfirst.2 r (by simpa [Trev] using hr)⟩
        · exact Or.inr
            ⟨by simpa [Trev] using hlast.1,
              by
                intro r hr
                exact hlast.2 r (by simpa [Trev] using hr)⟩)
      (by simpa [Trev] using ha)
      (by
        intro r
        simpa [Trev] using hold r)
      hq_path
      (by simpa [Trev] using hij_order)
      (by simpa [Trev] using hjk_order)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro z hzPath hzT
        have hzPathP : z ∈ P.pathSet := by
          simpa using hzPath
        have hzTorig : z ∈ T.vertexSet := by
          simpa [Trev] using hzT
        simpa [Trev] using hpath_contacts z hzPathP hzTorig)
      (by
        intro z hz hzT
        exact hq_clean z hz (by simpa [Trev] using hzT))

/-- Right-side version of the median-branch-or-residual classification,
obtained from the left-side theorem for `P.reverse`. -/
theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_median_branch_or_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.reverse.path (T.boundary i) <
        Walk.supportIndex P.reverse.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.reverse.path (T.boundary j) <
        Walk.supportIndex P.reverse.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              Exists fun s : Fin 3 => T.boundary r ∈ (T.rim s).support := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  simpa [Trev] using
    (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_residual
      P.reverse hno_cross hno_tripod Trev hij hik hjk q
      (by simpa [Trev] using hxT)
      (by simpa [Trev] using ha)
      (by
        intro r
        simpa [Trev] using hold r)
      hq_path
      (by simpa [Trev] using hij_order)
      (by simpa [Trev] using hjk_order)
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro z hzPath hzT
        have hzPathP : z ∈ P.pathSet := by
          simpa using hzPath
        have hzTorig : z ∈ T.vertexSet := by
          simpa [Trev] using hzT
        simpa [Trev] using hpath_contacts z hzPathP hzTorig)
      (by
        intro z hz hzT
        exact hq_clean z hz (by simpa [Trev] using hzT)))

/-- Right-side normalized median/common-end/zero-leg classifier. -/
theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.reverse.path (T.boundary i) <
        Walk.supportIndex P.reverse.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.reverse.path (T.boundary j) <
        Walk.supportIndex P.reverse.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              (T.leg r).Nil := by
  rcases
      GMIX24Split.canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_median_branch_or_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact Or.inl hmedian
  · rcases hresidual with hend | hrim
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr
        (GMIX24Split.tripod_degenerate_rim_residual_leg_nil T hrim))

/-- Right-side arm-normalized form of the all-path-foot side-tripod classifier. -/
theorem canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_median_branch_or_arm_residual
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hxT :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.reverse.path (T.boundary i) <
        Walk.supportIndex P.reverse.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.reverse.path (T.boundary j) <
        Walk.supportIndex P.reverse.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x) :
    (x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) ∨
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧
              (T.leg r).Nil ∧ x ≠ T.attach r ∧
                ((x ∈ (T.leftToAttach r).support ∧
                    x ≠ T.attach r) ∨
                  (x ∈ (T.attachToRight r).support ∧
                    x ≠ T.attach r)) := by
  rcases
      GMIX24Split.canonicalOfNoCross_right_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
        P hno_cross hno_tripod T hij hik hjk q hxT ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean with
    hmedian | hresidual
  · exact Or.inl hmedian
  · rcases hresidual with hend | hnil
    · exact Or.inr (Or.inl hend)
    · exact Or.inr (Or.inr
        (GMIX24Split.tripod_leg_nil_residual_arm_of_outside
          P T q
          (fun r : Fin 3 => by
            rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hri | hrjk
            · simpa [hri, fin3Order] using hold 0
            · rcases hrjk with hrj | hrk
              · simpa [hrj, fin3Order] using hold 1
              · simpa [hrk, fin3Order] using hold 2)
          hq_outside hnil))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
