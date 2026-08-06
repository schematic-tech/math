import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountCases

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

def CrossPathEndpointAdjacentCases
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    Prop :=
  (X.endpoints.endpoint 0 ∈ P.pathSet ∧
      X.endpoints.endpoint 1 ∈ P.pathSet ∧
      X.endpoints.endpoint 2 ∉ P.pathSet ∧
      X.endpoints.endpoint 3 ∉ P.pathSet) ∨
    (X.endpoints.endpoint 1 ∈ P.pathSet ∧
      X.endpoints.endpoint 2 ∈ P.pathSet ∧
      X.endpoints.endpoint 0 ∉ P.pathSet ∧
      X.endpoints.endpoint 3 ∉ P.pathSet) ∨
    (X.endpoints.endpoint 2 ∈ P.pathSet ∧
      X.endpoints.endpoint 3 ∈ P.pathSet ∧
      X.endpoints.endpoint 0 ∉ P.pathSet ∧
      X.endpoints.endpoint 1 ∉ P.pathSet) ∨
    (X.endpoints.endpoint 3 ∈ P.pathSet ∧
      X.endpoints.endpoint 0 ∈ P.pathSet ∧
      X.endpoints.endpoint 1 ∉ P.pathSet ∧
      X.endpoints.endpoint 2 ∉ P.pathSet)

theorem canonicalOfNoCross_left_cross_count_two_not_path_endpoint02
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hothers_off :
      forall i : Fin 4, i ≠ 0 -> i ≠ 2 ->
        X.endpoints.endpoint i ∉ P.pathSet) :
    False := by
  classical
  let Ω := P.leftOrderedCutBoundary
  let e := X.endpoints.endpoint
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h1_arc : e 1 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 1).mp (hothers_off 1 (by decide) (by decide))
  have h3_arc : e 3 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 3).mp (hothers_off 3 (by decide) (by decide))
  have h10 :
      Ω.indexOf (e 1) < Ω.indexOf (e 0) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h1_arc h0_path
  have h12 :
      Ω.indexOf (e 1) < Ω.indexOf (e 2) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h1_arc h2_path
  have h30 :
      Ω.indexOf (e 3) < Ω.indexOf (e 0) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h3_arc h0_path
  have h32 :
      Ω.indexOf (e 3) < Ω.indexOf (e 2) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h3_arc h2_path
  exact
    CrossEndpointAlternating.not_opposite_02_of_13_before
      hside h10 h12 h30 h32

theorem canonicalOfNoCross_right_cross_count_two_not_path_endpoint02
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hothers_off :
      forall i : Fin 4, i ≠ 0 -> i ≠ 2 ->
        X.endpoints.endpoint i ∉ P.pathSet) :
    False := by
  classical
  let Xrev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Cross :=
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm ▸ X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_count_two_not_path_endpoint02
      P.reverse hno_cross Xrev
      (by simpa [Xrev] using h0_path)
      (by simpa [Xrev] using h2_path)
      (by
        intro i hi0 hi2
        simpa [Xrev] using hothers_off i hi0 hi2)

theorem canonicalOfNoCross_left_cross_count_two_not_path_endpoint13
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hothers_off :
      forall i : Fin 4, i ≠ 1 -> i ≠ 3 ->
        X.endpoints.endpoint i ∉ P.pathSet) :
    False := by
  classical
  let Ω := P.leftOrderedCutBoundary
  let e := X.endpoints.endpoint
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h0_arc : e 0 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp (hothers_off 0 (by decide) (by decide))
  have h2_arc : e 2 ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp (hothers_off 2 (by decide) (by decide))
  have h01 :
      Ω.indexOf (e 0) < Ω.indexOf (e 1) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h0_arc h1_path
  have h03 :
      Ω.indexOf (e 0) < Ω.indexOf (e 3) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h0_arc h3_path
  have h21 :
      Ω.indexOf (e 2) < Ω.indexOf (e 1) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h2_arc h1_path
  have h23 :
      Ω.indexOf (e 2) < Ω.indexOf (e 3) := by
    simpa [Ω, e] using
      P.leftOrderedCutBoundary_index_arc_lt_path h2_arc h3_path
  exact
    CrossEndpointAlternating.not_opposite_13_of_02_before
      hside h01 h03 h21 h23

theorem canonicalOfNoCross_right_cross_count_two_not_path_endpoint13
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hothers_off :
      forall i : Fin 4, i ≠ 1 -> i ≠ 3 ->
        X.endpoints.endpoint i ∉ P.pathSet) :
    False := by
  classical
  let Xrev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Cross :=
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm ▸ X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_count_two_not_path_endpoint13
      P.reverse hno_cross Xrev
      (by simpa [Xrev] using h1_path)
      (by simpa [Xrev] using h3_path)
      (by
        intro i hi1 hi3
        simpa [Xrev] using hothers_off i hi1 hi3)

theorem canonicalOfNoCross_left_cross_count_two_path_adjacent_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 2) :
    CrossPathEndpointAdjacentCases P X := by
  classical
  obtain ⟨k, l, hkl, hk_path, hl_path, hothers_off⟩ :=
    GMIX24Split.cross_exists_two_old_on_path_of_count_two P X hcount
  fin_cases k <;> fin_cases l
  · exact False.elim (hkl rfl)
  · exact Or.inl
      ⟨hk_path, hl_path, hothers_off 2 (by decide) (by decide),
        hothers_off 3 (by decide) (by decide)⟩
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_count_two_not_path_endpoint02
        P hno_cross X hk_path hl_path hothers_off)
  · exact Or.inr (Or.inr (Or.inr
      ⟨hl_path, hk_path, hothers_off 1 (by decide) (by decide),
        hothers_off 2 (by decide) (by decide)⟩))
  · exact Or.inl
      ⟨hl_path, hk_path, hothers_off 2 (by decide) (by decide),
        hothers_off 3 (by decide) (by decide)⟩
  · exact False.elim (hkl rfl)
  · exact Or.inr (Or.inl
      ⟨hk_path, hl_path, hothers_off 0 (by decide) (by decide),
        hothers_off 3 (by decide) (by decide)⟩)
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_count_two_not_path_endpoint13
        P hno_cross X hk_path hl_path hothers_off)
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_count_two_not_path_endpoint02
        P hno_cross X hl_path hk_path (by
          intro i hi0 hi2
          exact hothers_off i hi2 hi0))
  · exact Or.inr (Or.inl
      ⟨hl_path, hk_path, hothers_off 0 (by decide) (by decide),
        hothers_off 3 (by decide) (by decide)⟩)
  · exact False.elim (hkl rfl)
  · exact Or.inr (Or.inr (Or.inl
      ⟨hk_path, hl_path, hothers_off 0 (by decide) (by decide),
        hothers_off 1 (by decide) (by decide)⟩))
  · exact Or.inr (Or.inr (Or.inr
      ⟨hk_path, hl_path, hothers_off 1 (by decide) (by decide),
        hothers_off 2 (by decide) (by decide)⟩))
  · exact False.elim
      (GMIX24Split.canonicalOfNoCross_left_cross_count_two_not_path_endpoint13
        P hno_cross X hl_path hk_path (by
          intro i hi1 hi3
          exact hothers_off i hi3 hi1))
  · exact Or.inr (Or.inr (Or.inl
      ⟨hl_path, hk_path, hothers_off 0 (by decide) (by decide),
        hothers_off 1 (by decide) (by decide)⟩))
  · exact False.elim (hkl rfl)

theorem canonicalOfNoCross_right_cross_count_two_path_adjacent_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 2) :
    CrossPathEndpointAdjacentCases P X := by
  classical
  let Xrev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Cross :=
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm ▸ X
  have hrev :=
    GMIX24Split.canonicalOfNoCross_left_cross_count_two_path_adjacent_cases
      P.reverse hno_cross Xrev
      (by
        simpa [Xrev, crossOffPathEndpointCount,
          crossOffPathEndpointFinset] using hcount)
  simpa [CrossPathEndpointAdjacentCases, Xrev] using hrev

theorem canonicalOfNoCross_right_cross_adjacent01_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 0) <
      Walk.supportIndex P.path (X.endpoints.endpoint 1) := by
  classical
  let e := X.endpoints.endpoint
  have h2_arc : e 2 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp h2_off
  have h3_arc : e 3 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 3).mp h3_off
  have hidx :
      P.rightOrderedCutBoundary.indexOf (e 0) <=
        P.rightOrderedCutBoundary.indexOf (e 1) :=
    CrossEndpointAlternating.index_le_01_of_23_before
      (GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h2_arc h0_path)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h2_arc h1_path)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h3_arc h0_path)
  have hne : e 0 ≠ e 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1)
      (X.endpoints.endpoint_injective h)
  exact P.rightOrderedCutBoundary_supportIndex_lt_of_index_le
    h0_path h1_path (by simpa [e] using hidx) hne

theorem canonicalOfNoCross_left_cross_adjacent01_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 1) <
      Walk.supportIndex P.path (X.endpoints.endpoint 0) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  apply (P.supportIndex_reverse_lt_iff h0_path h1_path).mp
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_adjacent01_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off))


theorem canonicalOfNoCross_right_cross_adjacent12_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 1) <
      Walk.supportIndex P.path (X.endpoints.endpoint 2) := by
  classical
  let e := X.endpoints.endpoint
  have h0_arc : e 0 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp h0_off
  have hidx :
      P.rightOrderedCutBoundary.indexOf (e 1) <=
        P.rightOrderedCutBoundary.indexOf (e 2) :=
    CrossEndpointAlternating.index_le_12_of_03_before
      (GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h0_arc h2_path)
  have hne : e 1 ≠ e 2 := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 2)
      (X.endpoints.endpoint_injective h)
  exact P.rightOrderedCutBoundary_supportIndex_lt_of_index_le
    h1_path h2_path (by simpa [e] using hidx) hne

theorem canonicalOfNoCross_left_cross_adjacent12_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 2) <
      Walk.supportIndex P.path (X.endpoints.endpoint 1) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  apply (P.supportIndex_reverse_lt_iff h1_path h2_path).mp
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_adjacent12_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off))


theorem canonicalOfNoCross_right_cross_adjacent23_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 2) <
      Walk.supportIndex P.path (X.endpoints.endpoint 3) := by
  classical
  let e := X.endpoints.endpoint
  have h0_arc : e 0 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp h0_off
  have hidx :
      P.rightOrderedCutBoundary.indexOf (e 2) <=
        P.rightOrderedCutBoundary.indexOf (e 3) :=
    CrossEndpointAlternating.index_le_23_of_01_before
      (GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h0_arc h2_path)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h0_arc h3_path)
  have hne : e 2 ≠ e 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3)
      (X.endpoints.endpoint_injective h)
  exact P.rightOrderedCutBoundary_supportIndex_lt_of_index_le
    h2_path h3_path (by simpa [e] using hidx) hne

theorem canonicalOfNoCross_left_cross_adjacent23_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 3) <
      Walk.supportIndex P.path (X.endpoints.endpoint 2) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  apply (P.supportIndex_reverse_lt_iff h2_path h3_path).mp
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_adjacent23_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off))


theorem canonicalOfNoCross_right_cross_adjacent30_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 3) <
      Walk.supportIndex P.path (X.endpoints.endpoint 0) := by
  classical
  let e := X.endpoints.endpoint
  have h2_arc : e 2 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp h2_off
  have hidx :
      P.rightOrderedCutBoundary.indexOf (e 3) <=
        P.rightOrderedCutBoundary.indexOf (e 0) :=
    CrossEndpointAlternating.index_le_30_of_12_before
      (GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X)
      (by simpa [e] using
        P.rightOrderedCutBoundary_index_arc_lt_path h2_arc h0_path)
  have hne : e 3 ≠ e 0 := by
    intro h
    exact (by decide : (3 : Fin 4) ≠ 0)
      (X.endpoints.endpoint_injective h)
  exact P.rightOrderedCutBoundary_supportIndex_lt_of_index_le
    h3_path h0_path (by simpa [e] using hidx) hne

theorem canonicalOfNoCross_left_cross_adjacent30_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 0) <
      Walk.supportIndex P.path (X.endpoints.endpoint 3) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  apply (P.supportIndex_reverse_lt_iff h3_path h0_path).mp
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_adjacent30_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off))



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
