import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.ResidualContradiction

/-!
Collapse of source-clean side-tripod legs.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}


/-- With path contacts normalized, a nontrivial ordered middle leg closes the
last double-outer-collapsed branch, so the clean outside tail must start on
the middle branch. -/
theorem left_side_tripod_clean_tail_median_branch_of_middle_non_nil
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    {x a : V}
    (q : S.graph.Walk x a)
    (hxT : Exists fun r : Fin 3 =>
      x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) -> z = x) :
    x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j) := by
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_outer_nil_obstruction
      P hno_cross hno_tripod T hij hik hjk q hxT ha hi hj hk hq_path
      hij_order hjk_order hq_outside hpath_contacts hq_clean ?_
  intro hresidual hleg_i_nil hleg_k_nil
  exact False.elim
    (outerNilMiddleNonNil_residual_impossible
      P hno_cross hno_tripod T hij hik hjk hleg_i_nil hleg_j_not_nil
      hleg_k_nil hi hj hk hij_order hjk_order hpath_contacts q ha
      hq_path hq_outside hq_clean hresidual)

/-- A source-clean side tripod with no hidden cut-path contact can survive
the ambient no-tripod hypothesis only if all three of its linkage legs have
collapsed.

This is the direct, order-independent conclusion of the checked side-tripod
constructors.  After the three feet are forced onto the induced cut path and
ordered as `i,j,k`, a nontrivial first or last leg is eliminated by the
corresponding ordered residual constructor.  A nontrivial middle leg is
eliminated by `outerNilMiddleNonNil_residual_impossible`, including both old
common ends and both internal outer-rim starts. -/
theorem left_side_tripod_all_legs_nil_of_source_clean_no_hidden_contact
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (hno_hidden :
      forall z : V,
        z ∈ P.pathSet ->
          (Exists fun r : Fin 3 => z ∈ (T.rim r).support) ->
            (forall m : Fin 3, z ≠ T.boundary m) -> False) :
    forall r : Fin 3, (T.leg r).Nil := by
  classical
  let hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_no_hidden_rim_contact
      P hno_cross T hsource_clean hno_hidden
  have hall : forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  obtain ⟨_z0, x, a, q, _hz0T, _hz0Left, hxT, ha, hq_path,
      _hq_side, hq_outside, hq_clean⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_clean_tail_to_boundary_at
      P hno_cross T j (hall j)
  have hq_clean_vertex :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x := by
    intro z hz hzT
    exact hq_clean z hz (by
      rcases hzT with hzRim | hzLeg
      · rcases hzRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases hzLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩)
  have hfalse_of_median
      (hmedian :
        x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j)) :
      False :=
    hno_tripod
      (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
        P hno_cross T hij hik hjk q hmedian ha
        (fun r : Fin 3 => hall (fin3Order i j k r))
        hq_path hij_order hjk_order hq_outside hpath_contacts
        hq_clean_vertex)
  have hi_nil : (T.leg i).Nil := by
    by_contra hi_not_nil
    exact hfalse_of_median
      (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_first_non_nil
        P hno_cross hno_tripod T hij hik hjk hi_not_nil q hxT ha
        (fun r : Fin 3 => hall (fin3Order i j k r)) hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean)
  have hk_nil : (T.leg k).Nil := by
    by_contra hk_not_nil
    exact hfalse_of_median
      (GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_of_ordered_last_non_nil
        P hno_cross hno_tripod T hij hik hjk hk_not_nil q hxT ha
        (fun r : Fin 3 => hall (fin3Order i j k r)) hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean)
  have hj_nil : (T.leg j).Nil := by
    by_contra hj_not_nil
    exact hfalse_of_median
      (left_side_tripod_clean_tail_median_branch_of_middle_non_nil
        P hno_cross hno_tripod T hij hik hjk hj_not_nil q hxT ha
        (hall i) (hall j) (hall k) hq_path hij_order hjk_order
        hq_outside hpath_contacts hq_clean)
  intro r
  rcases fin3_eq_of_pairwise (m := r) hij hik hjk with hr | hr
  · subst r
    exact hi_nil
  · rcases hr with hr | hr
    · subst r
      exact hj_nil
    · subst r
      exact hk_nil

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
