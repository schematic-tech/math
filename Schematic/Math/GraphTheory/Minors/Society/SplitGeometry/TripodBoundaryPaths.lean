import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.CrossCleanBranches

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
theorem canonicalOfNoCross_left_tripod_rim_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3) :
    {z : V | z ∈ (T.rim i).support} ⊆ P.leftSide ∪ P.pathSet := by
  intro z hz
  have hzSupport :
      z ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.support :=
    T.rim_support_subset_graph_support i hz
  exact
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices
      hzSupport

theorem canonicalOfNoCross_left_tripod_leg_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3) :
    {z : V | z ∈ (T.leg i).support} ⊆ P.leftSide ∪ P.pathSet := by
  intro z hz
  have hzSupport :
      z ∈
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.support :=
    T.leg_support_subset_graph_support i hz
  exact
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices
      hzSupport

theorem canonicalOfNoCross_right_tripod_rim_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    {z : V | z ∈ (T.rim i).support} ⊆ P.rightSide ∪ P.pathSet := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    GMIX24Split.canonicalOfNoCross_left_tripod_rim_support_subset_side_or_path
      P.reverse hno_cross Trev i

theorem canonicalOfNoCross_right_tripod_leg_support_subset_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    {z : V | z ∈ (T.leg i).support} ⊆ P.rightSide ∪ P.pathSet := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    GMIX24Split.canonicalOfNoCross_left_tripod_leg_support_subset_side_or_path
      P.reverse hno_cross Trev i

theorem canonicalOfNoCross_left_tripod_boundary_path_meets_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3)
    (hboundary : T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      (z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
        z ∈ P.leftSide := by
  classical
  by_cases hleg_nil : (T.leg i).Nil
  · have hattach_path : T.attach i ∈ P.pathSet := by
      simpa [SimpleGraph.Walk.Nil.eq hleg_nil] using hboundary
    have hrim_nontrivial : (T.rim i).length ≠ 0 := by
      intro hlen
      exact T.left_ne_right (SimpleGraph.Walk.eq_of_length_eq_zero hlen)
    obtain ⟨z, hzrim, hzLeft⟩ := by
      simpa [GMIX24Split.canonicalOfNoCross,
        GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
        GMIX24Split.ofCanonical] using
        P.leftGraph_walk_touching_path_meets_leftSide
          (T.rim i) (T.attach_mem_rim i).1 hattach_path hrim_nontrivial
          (GMIX24Split.canonicalOfNoCross_left_tripod_rim_support_subset_side_or_path
            P hno_cross T i)
    exact ⟨z, Or.inl hzrim, hzLeft⟩
  · have hleg_nontrivial : (T.leg i).length ≠ 0 := by
      intro hlen
      exact hleg_nil ((SimpleGraph.Walk.nil_iff_length_eq).mpr hlen)
    obtain ⟨z, hzleg, hzLeft⟩ := by
      simpa [GMIX24Split.canonicalOfNoCross,
        GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
        GMIX24Split.ofCanonical] using
        P.leftGraph_walk_to_path_meets_leftSide
          (T.leg i) hboundary hleg_nontrivial
          (GMIX24Split.canonicalOfNoCross_left_tripod_leg_support_subset_side_or_path
            P hno_cross T i)
    exact ⟨z, Or.inr hzleg, hzLeft⟩

theorem canonicalOfNoCross_right_tripod_boundary_path_meets_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3)
    (hboundary : T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      (z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
        z ∈ P.rightSide := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    (GMIX24Split.canonicalOfNoCross_left_tripod_boundary_path_meets_leftSide
      P.reverse hno_cross Trev i (by simpa [Trev] using hboundary))

theorem canonicalOfNoCross_left_tripod_with_path_foot_meets_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      (Exists fun i : Fin 3 =>
        z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
        z ∈ P.leftSide := by
  rcases hpath with ⟨i, hi⟩
  obtain ⟨z, hz, hzLeft⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_boundary_path_meets_leftSide
      P hno_cross T i hi
  exact ⟨z, ⟨i, hz⟩, hzLeft⟩

theorem canonicalOfNoCross_right_tripod_with_path_foot_meets_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      (Exists fun i : Fin 3 =>
        z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
        z ∈ P.rightSide := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    (GMIX24Split.canonicalOfNoCross_left_tripod_with_path_foot_meets_leftSide
      P.reverse hno_cross Trev (by simpa [Trev] using hpath))

theorem canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk z a =>
          (Exists fun i : Fin 3 =>
            z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
            z ∈ P.leftSide ∧ a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                forall w : V, w ∈ q.support -> w ∈ P.outside := by
  obtain ⟨z, hzT, hzLeft⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_with_path_foot_meets_leftSide
      P hno_cross T hpath
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside hzLeft
  exact ⟨z, a, q, hzT, hzLeft, ha, hqPath, hqLeft, hqOutside⟩

/-- Source-preserving version of
`canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path`.

The source proof starts the auxiliary path from a specified foot of the side
tripod.  The older existential form immediately forgot that index, which is
too coarse for the final common-end residual analysis. -/
theorem canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path_at
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (i : Fin 3)
    (hi : T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk z a =>
          (z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
            z ∈ P.leftSide ∧ a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.leftSide) ∧
                forall w : V, w ∈ q.support -> w ∈ P.outside := by
  obtain ⟨z, hzT, hzLeft⟩ :=
    GMIX24Split.canonicalOfNoCross_left_tripod_boundary_path_meets_leftSide
      P hno_cross T i hi
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside hzLeft
  exact ⟨z, a, q, hzT, hzLeft, ha, hqPath, hqLeft, hqOutside⟩

theorem canonicalOfNoCross_right_tripod_path_foot_side_to_boundary_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath : Exists fun i : Fin 3 => T.boundary i ∈ P.pathSet) :
    Exists fun z : V =>
      Exists fun a : V =>
        Exists fun q : S.graph.Walk z a =>
          (Exists fun i : Fin 3 =>
            z ∈ (T.rim i).support ∨ z ∈ (T.leg i).support) ∧
            z ∈ P.rightSide ∧ a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
              (forall w : V, w ∈ q.support -> w ∈ P.rightSide) ∧
                forall w : V, w ∈ q.support -> w ∈ P.outside := by
  let Trev := GMIX24Split.canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  simpa [Trev] using
    (GMIX24Split.canonicalOfNoCross_left_tripod_path_foot_side_to_boundary_path
      P.reverse hno_cross Trev (by simpa [Trev] using hpath))

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
