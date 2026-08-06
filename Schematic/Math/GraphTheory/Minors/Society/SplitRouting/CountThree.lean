import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem cross_exists_single_old_on_path_of_count_three
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross)
    (hcount : crossOffPathEndpointCount X P = 3) :
    Exists fun k : Fin 4 =>
      X.endpoints.endpoint k ∈ P.pathSet ∧
        forall i : Fin 4, i ≠ k -> X.endpoints.endpoint i ∉ P.pathSet :=
  (crossOffPathEndpointCount_eq_three_iff_exists_single_on_path P X).mp
    hcount

theorem canonicalOfNoCross_left_cross_replaceEndpointAt_end_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {k : Fin 4}
    (hpath : X.endpoints.endpoint k ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ k ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (replaceEndpointAt X.endpoints.endpoint k P.t) := by
  classical
  let Ω := P.leftOrderedCutBoundary
  let e := X.endpoints.endpoint
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have ht_mem : P.t ∈ Ω.vertexSet := by
    exact P.pathSet_subset_leftOrderedCutBoundary P.t_mem_pathSet
  have hbefore :
      forall i : Fin 4, i ≠ k ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e i) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t := by
    intro i hi
    have harc :
        e i ∈ P.leftBoundaryArc :=
      (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
        P hno_cross X i).mp (hoff i hi)
    have hlt :=
      P.leftOrderedCutBoundary_index_arc_lt_path harc P.t_mem_pathSet
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have ht_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e k) := by
    have hsupport :
        Walk.supportIndex P.path (e k) <= Walk.supportIndex P.path P.t :=
      Walk.IsPath.supportIndex_le_end P.path_isPath
        (by simpa [GMIX24CutPath.pathSet, e] using hpath)
    have hidx :=
      (P.leftOrderedCutBoundary_index_path_le_iff
        P.t_mem_pathSet (by simpa [e] using hpath)).mpr hsupport
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hidx
  have hside_repl :
      CrossEndpointAlternating Ω (replaceEndpointAt e k P.t) := by
    fin_cases k
    · exact
        crossEndpointAlternating_replaceEndpoint0_of_after_other_endpoints
          Ω (by
            intro i hi
            exact hbefore i (by simpa using hi)) ht_le hside
    · exact
        crossEndpointAlternating_replaceEndpoint1_of_after_other_endpoints
          Ω ht_mem (by
            intro i hi
            exact hbefore i (by simpa using hi)) ht_le hside
    · exact
        crossEndpointAlternating_replaceEndpoint2_of_after_other_endpoints
          Ω (by
            intro i hi
            exact hbefore i (by simpa using hi)) ht_le hside
    · exact
        crossEndpointAlternating_replaceEndpoint3_of_after_other_endpoints
          Ω ht_mem (by
            intro i hi
            exact hbefore i (by simpa using hi)) ht_le hside
  have hmem_repl :
      forall i : Fin 4,
        replaceEndpointAt e k P.t i ∈ P.leftBoundaryArc ∨
          replaceEndpointAt e k P.t i = P.t := by
    intro i
    by_cases hi : i = k
    · subst i
      simp [replaceEndpointAt]
    · have harc :
          e i ∈ P.leftBoundaryArc :=
        (GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
          P hno_cross X i).mp (hoff i hi)
      exact Or.inl (by simpa [replaceEndpointAt, hi] using harc)
  dsimp [CrossEndpointAlternating] at hside_repl ⊢
  exact ⟨
    P.leftOrdered_clockwiseOpenBetween_original_of_arc_or_end
      (hmem_repl 0) (hmem_repl 2) (hmem_repl 1) hside_repl.1,
    P.leftOrdered_clockwiseOpenBetween_original_of_arc_or_end
      (hmem_repl 2) (hmem_repl 0) (hmem_repl 3) hside_repl.2⟩

theorem canonicalOfNoCross_right_cross_replaceEndpointAt_start_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {k : Fin 4}
    (hpath : X.endpoints.endpoint k ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ k ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (replaceEndpointAt X.endpoints.endpoint k P.s) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have hs_mem : P.s ∈ Ω.vertexSet := by
    exact P.pathSet_subset_rightOrderedCutBoundary P.s_mem_pathSet
  have hbefore :
      forall i : Fin 4, i ≠ k ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e i) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s := by
    intro i hi
    have harc :
        e i ∈ P.rightBoundaryArc :=
      (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
        P hno_cross X i).mp (hoff i hi)
    have hlt :=
      P.rightOrderedCutBoundary_index_arc_lt_path harc P.s_mem_pathSet
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have hs_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e k) := by
    have hsupport :
        Walk.supportIndex P.path P.s <= Walk.supportIndex P.path (e k) :=
      Walk.supportIndex_start_le (p := P.path)
    have hidx :=
      (P.rightOrderedCutBoundary_index_path_le_iff
        P.s_mem_pathSet (by simpa [e] using hpath)).mpr hsupport
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hidx
  have hside_repl :
      CrossEndpointAlternating Ω (replaceEndpointAt e k P.s) := by
    fin_cases k
    · exact
        crossEndpointAlternating_replaceEndpoint0_of_after_other_endpoints
          Ω (by
            intro i hi
            exact hbefore i (by simpa using hi)) hs_le hside
    · exact
        crossEndpointAlternating_replaceEndpoint1_of_after_other_endpoints
          Ω hs_mem (by
            intro i hi
            exact hbefore i (by simpa using hi)) hs_le hside
    · exact
        crossEndpointAlternating_replaceEndpoint2_of_after_other_endpoints
          Ω (by
            intro i hi
            exact hbefore i (by simpa using hi)) hs_le hside
    · exact
        crossEndpointAlternating_replaceEndpoint3_of_after_other_endpoints
          Ω hs_mem (by
            intro i hi
            exact hbefore i (by simpa using hi)) hs_le hside
  have hmem_repl :
      forall i : Fin 4,
        replaceEndpointAt e k P.s i ∈ P.rightBoundaryArc ∨
          replaceEndpointAt e k P.s i = P.s := by
    intro i
    by_cases hi : i = k
    · subst i
      simp [replaceEndpointAt]
    · have harc :
          e i ∈ P.rightBoundaryArc :=
        (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
          P hno_cross X i).mp (hoff i hi)
      exact Or.inl (by simpa [replaceEndpointAt, hi] using harc)
  dsimp [CrossEndpointAlternating] at hside_repl ⊢
  exact ⟨
    P.rightOrdered_clockwiseOpenBetween_original_of_arc_or_start
      (hmem_repl 0) (hmem_repl 2) (hmem_repl 1) hside_repl.1,
    P.rightOrdered_clockwiseOpenBetween_original_of_arc_or_start
      (hmem_repl 2) (hmem_repl 0) (hmem_repl 3) hside_repl.2⟩

theorem canonicalOfNoCross_left_cross_replaceEndpoint0_end_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 0 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 0 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.t) := by
  simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpointAt_end_original_alternating_of_single_path
      P hno_cross X (k := 0) hpath hoff

theorem canonicalOfNoCross_left_cross_replaceEndpoint1_end_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 1 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 1 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.t) := by
  simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpointAt_end_original_alternating_of_single_path
      P hno_cross X (k := 1) hpath hoff

theorem canonicalOfNoCross_left_cross_replaceEndpoint2_end_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 2 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.t) := by
  simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpointAt_end_original_alternating_of_single_path
      P hno_cross X (k := 2) hpath hoff

theorem canonicalOfNoCross_left_cross_replaceEndpoint3_end_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hpath : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 3 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.t) := by
  simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpointAt_end_original_alternating_of_single_path
      P hno_cross X (k := 3) hpath hoff

theorem canonicalOfNoCross_right_cross_replaceEndpoint0_start_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 0 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 0 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.s) := by
  simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpointAt_start_original_alternating_of_single_path
      P hno_cross X (k := 0) hpath hoff

theorem canonicalOfNoCross_right_cross_replaceEndpoint1_start_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 1 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 1 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.s) := by
  simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpointAt_start_original_alternating_of_single_path
      P hno_cross X (k := 1) hpath hoff

theorem canonicalOfNoCross_right_cross_replaceEndpoint2_start_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 2 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.s) := by
  simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpointAt_start_original_alternating_of_single_path
      P hno_cross X (k := 2) hpath hoff

theorem canonicalOfNoCross_right_cross_replaceEndpoint3_start_original_alternating_of_single_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hpath : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 3 ->
      X.endpoints.endpoint i ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.s) := by
  simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpointAt_start_original_alternating_of_single_path
      P hno_cross X (k := 3) hpath hoff

theorem canonicalOfNoCross_left_cross_original_alternating_of_single_path_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {k : Fin 4}
    (hpath : X.endpoints.endpoint k ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ k ->
      X.endpoints.endpoint i ∉ P.pathSet)
    (hb : X.endpoints.endpoint k ∈ S.boundarySet) :
    CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
  classical
  let e := X.endpoints.endpoint
  have hside :
      CrossEndpointAlternating P.leftOrderedCutBoundary e := by
    simpa [e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h02 : e 0 ≠ e 2 := by
    intro h
    have hfin : (0 : Fin 4) = 2 := X.endpoints.endpoint_injective h
    exact (by decide : (0 : Fin 4) ≠ 2) hfin
  have h20 : e 2 ≠ e 0 := h02.symm
  rcases P.boundary_mem_pathSet_eq_s_or_t hb hpath with hks | hkt
  · have hmem :
        forall i : Fin 4, e i ∈ P.leftBoundaryArc ∨ e i = P.s := by
      intro i
      by_cases hi : i = k
      · subst i
        exact Or.inr hks
      · exact Or.inl
          ((GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
            P hno_cross X i).mp (hoff i hi))
    dsimp [CrossEndpointAlternating] at hside ⊢
    exact ⟨
      GMIX24CutPath.leftOrdered_clockwiseOpenBetween_original_of_arc_or_start
        P
        (hmem 0) (hmem 2) (hmem 1) h02 hside.1,
      GMIX24CutPath.leftOrdered_clockwiseOpenBetween_original_of_arc_or_start
        P
        (hmem 2) (hmem 0) (hmem 3) h20 hside.2⟩
  · have hmem :
        forall i : Fin 4, e i ∈ P.leftBoundaryArc ∨ e i = P.t := by
      intro i
      by_cases hi : i = k
      · subst i
        exact Or.inr hkt
      · exact Or.inl
          ((GMIX24Split.canonicalOfNoCross_left_cross_endpoint_not_path_iff_arc
            P hno_cross X i).mp (hoff i hi))
    dsimp [CrossEndpointAlternating] at hside ⊢
    exact ⟨
      P.leftOrdered_clockwiseOpenBetween_original_of_arc_or_end
        (hmem 0) (hmem 2) (hmem 1) hside.1,
      P.leftOrdered_clockwiseOpenBetween_original_of_arc_or_end
        (hmem 2) (hmem 0) (hmem 3) hside.2⟩

theorem canonicalOfNoCross_right_cross_original_alternating_of_single_path_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {k : Fin 4}
    (hpath : X.endpoints.endpoint k ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ k ->
      X.endpoints.endpoint i ∉ P.pathSet)
    (hb : X.endpoints.endpoint k ∈ S.boundarySet) :
    CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_single_path_boundary
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hpath)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
          hoff i hi)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hb))


theorem canonicalOfNoCross_left_cross_lift_of_count_three_from_endpoint_alternations
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (halt0 :
      X.endpoints.endpoint 0 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 0 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 0 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.t)))
    (halt1 :
      X.endpoints.endpoint 1 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 1 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 1 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.t)))
    (halt2 :
      X.endpoints.endpoint 2 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 2 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 2 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.t)))
    (halt3 :
      X.endpoints.endpoint 3 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 3 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 3 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.t)))
    (hcount : crossOffPathEndpointCount X P = 3) :
    Nonempty S.Cross := by
  classical
  obtain ⟨k, hpath, hoff⟩ :=
    GMIX24Split.cross_exists_single_old_on_path_of_count_three P X hcount
  fin_cases k
  · rcases halt0 hpath hoff with ⟨horiginal, htail⟩
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_lift_of_only_endpoint0_on_path_or_to_end
        P hno_cross X hpath hoff horiginal htail
  · rcases halt1 hpath hoff with ⟨horiginal, htail⟩
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_lift_of_only_endpoint1_on_path_or_to_end
        P hno_cross X hpath hoff horiginal htail
  · rcases halt2 hpath hoff with ⟨horiginal, htail⟩
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_lift_of_only_endpoint2_on_path_or_to_end
        P hno_cross X hpath hoff horiginal htail
  · rcases halt3 hpath hoff with ⟨horiginal, htail⟩
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_lift_of_only_endpoint3_on_path_or_to_end
        P hno_cross X hpath hoff horiginal htail

theorem canonicalOfNoCross_right_cross_lift_of_count_three_from_endpoint_alternations
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (halt0 :
      X.endpoints.endpoint 0 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 0 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 0 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.s)))
    (halt1 :
      X.endpoints.endpoint 1 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 1 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 1 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.s)))
    (halt2 :
      X.endpoints.endpoint 2 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 2 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 2 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.s)))
    (halt3 :
      X.endpoints.endpoint 3 ∈ P.pathSet ->
        (forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) ->
          (X.endpoints.endpoint 3 ∈ S.boundarySet ->
            CrossEndpointAlternating S.boundary X.endpoints.endpoint) ∧
            (X.endpoints.endpoint 3 ∉ S.boundarySet ->
              CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.s)))
    (hcount : crossOffPathEndpointCount X P = 3) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  apply
    GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_three_from_endpoint_alternations
      P.reverse hno_cross Xrev
  · intro hpath hoff
    simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
      halt0
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hpath)
        (by
          intro i hi
          simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
            hoff i hi)
  · intro hpath hoff
    simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
      halt1
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hpath)
        (by
          intro i hi
          simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
            hoff i hi)
  · intro hpath hoff
    simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
      halt2
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hpath)
        (by
          intro i hi
          simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
            hoff i hi)
  · intro hpath hoff
    simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
      halt3
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using hpath)
        (by
          intro i hi
          simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
            hoff i hi)
  · simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross,
      crossOffPathEndpointCount, crossOffPathEndpointFinset] using hcount


theorem canonicalOfNoCross_left_cross_lift_of_count_three_from_side_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 3) :
    Nonempty S.Cross :=
  GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_three_from_endpoint_alternations
    P hno_cross X
    (fun hpath hoff =>
      ⟨fun hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_single_path_boundary
          P hno_cross X (k := 0) hpath hoff hb,
       fun _hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint0_end_original_alternating_of_single_path
          P hno_cross X hpath hoff⟩)
    (fun hpath hoff =>
      ⟨fun hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_single_path_boundary
          P hno_cross X (k := 1) hpath hoff hb,
       fun _hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint1_end_original_alternating_of_single_path
          P hno_cross X hpath hoff⟩)
    (fun hpath hoff =>
      ⟨fun hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_single_path_boundary
          P hno_cross X (k := 2) hpath hoff hb,
       fun _hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint2_end_original_alternating_of_single_path
          P hno_cross X hpath hoff⟩)
    (fun hpath hoff =>
      ⟨fun hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_original_alternating_of_single_path_boundary
          P hno_cross X (k := 3) hpath hoff hb,
       fun _hb =>
        GMIX24Split.canonicalOfNoCross_left_cross_replaceEndpoint3_end_original_alternating_of_single_path
          P hno_cross X hpath hoff⟩)
    hcount

theorem canonicalOfNoCross_right_cross_lift_of_count_three_from_side_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 3) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_three_from_side_order
      P.reverse hno_cross Xrev (by
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross,
          crossOffPathEndpointCount, crossOffPathEndpointFinset] using hcount)



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
