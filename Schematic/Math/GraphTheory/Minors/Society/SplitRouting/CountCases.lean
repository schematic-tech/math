import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_count_ne_four
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    crossOffPathEndpointCount X P ≠ 4 := by
  intro hcount
  exact hno_cross
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_four
      P hno_cross X hcount)

theorem canonicalOfNoCross_right_cross_count_ne_four
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    crossOffPathEndpointCount X P ≠ 4 := by
  intro hcount
  exact hno_cross
    (GMIX24Split.canonicalOfNoCross_right_cross_lift_of_count_four
      P hno_cross X hcount)

theorem canonicalOfNoCross_left_cross_count_le_three
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    crossOffPathEndpointCount X P <= 3 := by
  have hle4 := crossOffPathEndpointCount_le_four P X
  have hne4 :=
    GMIX24Split.canonicalOfNoCross_left_cross_count_ne_four
      P hno_cross X
  omega

theorem canonicalOfNoCross_right_cross_count_le_three
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    crossOffPathEndpointCount X P <= 3 := by
  have hle4 := crossOffPathEndpointCount_le_four P X
  have hne4 :=
    GMIX24Split.canonicalOfNoCross_right_cross_count_ne_four
      P hno_cross X
  omega

theorem nat_eq_zero_or_one_or_two_or_three_of_le_three
    {n : Nat} (hn : n <= 3) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  omega

theorem canonicalOfNoCross_left_cross_count_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    crossOffPathEndpointCount X P = 0 ∨
      crossOffPathEndpointCount X P = 1 ∨
        crossOffPathEndpointCount X P = 2 ∨
          crossOffPathEndpointCount X P = 3 :=
  nat_eq_zero_or_one_or_two_or_three_of_le_three
    (GMIX24Split.canonicalOfNoCross_left_cross_count_le_three
      P hno_cross X)

theorem canonicalOfNoCross_right_cross_count_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    crossOffPathEndpointCount X P = 0 ∨
      crossOffPathEndpointCount X P = 1 ∨
        crossOffPathEndpointCount X P = 2 ∨
          crossOffPathEndpointCount X P = 3 :=
  nat_eq_zero_or_one_or_two_or_three_of_le_three
    (GMIX24Split.canonicalOfNoCross_right_cross_count_le_three
      P hno_cross X)

theorem exists_left_crossOffPathCountMaximal_with_count_cases_of_nonempty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hcross :
      Nonempty
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Exists fun X :
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross =>
        CrossOffPathCountMaximal P X ∧
          (crossOffPathEndpointCount X P = 0 ∨
            crossOffPathEndpointCount X P = 1 ∨
              crossOffPathEndpointCount X P = 2 ∨
                crossOffPathEndpointCount X P = 3) := by
  obtain ⟨X, hmax⟩ :=
    exists_crossOffPathCountMaximal_of_nonempty P hcross
  exact ⟨X, hmax,
    GMIX24Split.canonicalOfNoCross_left_cross_count_cases P hno_cross X⟩

theorem exists_right_crossOffPathCountMaximal_with_count_cases_of_nonempty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hcross :
      Nonempty
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    Exists fun X :
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross =>
        CrossOffPathCountMaximal P X ∧
          (crossOffPathEndpointCount X P = 0 ∨
            crossOffPathEndpointCount X P = 1 ∨
              crossOffPathEndpointCount X P = 2 ∨
                crossOffPathEndpointCount X P = 3) := by
  obtain ⟨X, hmax⟩ :=
    exists_crossOffPathCountMaximal_of_nonempty P hcross
  exact ⟨X, hmax,
    GMIX24Split.canonicalOfNoCross_right_cross_count_cases P hno_cross X⟩

def LeftMaximalCrossSourceCases [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Prop :=
  (forall {l : Fin 4},
      l = 1 ∨ l = 3 ->
      X.endpoints.endpoint l ∉ P.pathSet ->
      (forall i : Fin 4, i ≠ l ->
        X.endpoints.endpoint i ∈ P.pathSet) ->
    forall {x y : V} (r : S.graph.Walk x y),
      x ∈ X.firstPath.support ->
        y ∈ X.secondPath.support ->
          r.IsPath ->
            (forall w : V, w ∈ r.support ->
              w ∈ X.firstPath.support -> w = x) ->
            (forall w : V, w ∈ r.support ->
              w ∈ X.secondPath.support -> w = y) ->
            (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ->
              (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                Nonempty S.Tripod) ∧
      (forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod)

def RightMaximalCrossSourceCases [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    Prop :=
  (forall {l : Fin 4},
      l = 1 ∨ l = 3 ->
      X.endpoints.endpoint l ∉ P.pathSet ->
      (forall i : Fin 4, i ≠ l ->
        X.endpoints.endpoint i ∈ P.pathSet) ->
    forall {x y : V} (r : S.graph.Walk x y),
      x ∈ X.firstPath.support ->
        y ∈ X.secondPath.support ->
          r.IsPath ->
            (forall w : V, w ∈ r.support ->
              w ∈ X.firstPath.support -> w = x) ->
            (forall w : V, w ∈ r.support ->
              w ∈ X.secondPath.support -> w = y) ->
            (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ->
              (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                Nonempty S.Tripod) ∧
      (forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod)

theorem cross_all_endpoints_on_path_of_count_zero
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross)
    (hcount : crossOffPathEndpointCount X P = 0) :
    forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet :=
  (crossOffPathEndpointCount_eq_zero_iff_all_on_path P X).mp hcount

theorem cross_exists_single_old_off_path_of_count_one
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross)
    (hcount : crossOffPathEndpointCount X P = 1) :
    Exists fun l : Fin 4 =>
      X.endpoints.endpoint l ∉ P.pathSet ∧
        forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet :=
  (crossOffPathEndpointCount_eq_one_iff_exists_single_old_off_path P X).mp
    hcount

theorem cross_exists_two_old_off_path_of_count_two
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross)
    (hcount : crossOffPathEndpointCount X P = 2) :
    Exists fun k : Fin 4 =>
      Exists fun l : Fin 4 =>
        k ≠ l ∧ X.endpoints.endpoint k ∉ P.pathSet ∧
          X.endpoints.endpoint l ∉ P.pathSet ∧
            forall i : Fin 4, i ≠ k -> i ≠ l ->
              X.endpoints.endpoint i ∈ P.pathSet :=
  (crossOffPathEndpointCount_eq_two_iff_exists_two_old_off_path P X).mp
    hcount

theorem cross_exists_two_old_on_path_of_count_two
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross)
    (hcount : crossOffPathEndpointCount X P = 2) :
    Exists fun k : Fin 4 =>
      Exists fun l : Fin 4 =>
        k ≠ l ∧ X.endpoints.endpoint k ∈ P.pathSet ∧
          X.endpoints.endpoint l ∈ P.pathSet ∧
            forall i : Fin 4, i ≠ k -> i ≠ l ->
              X.endpoints.endpoint i ∉ P.pathSet := by
  classical
  obtain ⟨k, l, hkl, hk_off, hl_off, hothers_path⟩ :=
    GMIX24Split.cross_exists_two_old_off_path_of_count_two P X hcount
  fin_cases k <;> fin_cases l
  · exact False.elim (hkl rfl)
  · refine ⟨2, 3, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 2 (by decide) (by decide)
    · exact hothers_path 3 (by decide) (by decide)
    · intro i hi2 hi3
      fin_cases i
      · exact hk_off
      · exact hl_off
      · exact False.elim (hi2 rfl)
      · exact False.elim (hi3 rfl)
  · refine ⟨1, 3, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 1 (by decide) (by decide)
    · exact hothers_path 3 (by decide) (by decide)
    · intro i hi1 hi3
      fin_cases i
      · exact hk_off
      · exact False.elim (hi1 rfl)
      · exact hl_off
      · exact False.elim (hi3 rfl)
  · refine ⟨1, 2, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 1 (by decide) (by decide)
    · exact hothers_path 2 (by decide) (by decide)
    · intro i hi1 hi2
      fin_cases i
      · exact hk_off
      · exact False.elim (hi1 rfl)
      · exact False.elim (hi2 rfl)
      · exact hl_off
  · refine ⟨2, 3, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 2 (by decide) (by decide)
    · exact hothers_path 3 (by decide) (by decide)
    · intro i hi2 hi3
      fin_cases i
      · exact hl_off
      · exact hk_off
      · exact False.elim (hi2 rfl)
      · exact False.elim (hi3 rfl)
  · exact False.elim (hkl rfl)
  · refine ⟨0, 3, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 0 (by decide) (by decide)
    · exact hothers_path 3 (by decide) (by decide)
    · intro i hi0 hi3
      fin_cases i
      · exact False.elim (hi0 rfl)
      · exact hk_off
      · exact hl_off
      · exact False.elim (hi3 rfl)
  · refine ⟨0, 2, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 0 (by decide) (by decide)
    · exact hothers_path 2 (by decide) (by decide)
    · intro i hi0 hi2
      fin_cases i
      · exact False.elim (hi0 rfl)
      · exact hk_off
      · exact False.elim (hi2 rfl)
      · exact hl_off
  · refine ⟨1, 3, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 1 (by decide) (by decide)
    · exact hothers_path 3 (by decide) (by decide)
    · intro i hi1 hi3
      fin_cases i
      · exact hl_off
      · exact False.elim (hi1 rfl)
      · exact hk_off
      · exact False.elim (hi3 rfl)
  · refine ⟨0, 3, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 0 (by decide) (by decide)
    · exact hothers_path 3 (by decide) (by decide)
    · intro i hi0 hi3
      fin_cases i
      · exact False.elim (hi0 rfl)
      · exact hl_off
      · exact hk_off
      · exact False.elim (hi3 rfl)
  · exact False.elim (hkl rfl)
  · refine ⟨0, 1, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 0 (by decide) (by decide)
    · exact hothers_path 1 (by decide) (by decide)
    · intro i hi0 hi1
      fin_cases i
      · exact False.elim (hi0 rfl)
      · exact False.elim (hi1 rfl)
      · exact hk_off
      · exact hl_off
  · refine ⟨1, 2, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 1 (by decide) (by decide)
    · exact hothers_path 2 (by decide) (by decide)
    · intro i hi1 hi2
      fin_cases i
      · exact hl_off
      · exact False.elim (hi1 rfl)
      · exact False.elim (hi2 rfl)
      · exact hk_off
  · refine ⟨0, 2, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 0 (by decide) (by decide)
    · exact hothers_path 2 (by decide) (by decide)
    · intro i hi0 hi2
      fin_cases i
      · exact False.elim (hi0 rfl)
      · exact hl_off
      · exact False.elim (hi2 rfl)
      · exact hk_off
  · refine ⟨0, 1, by decide, ?_, ?_, ?_⟩
    · exact hothers_path 0 (by decide) (by decide)
    · exact hothers_path 1 (by decide) (by decide)
    · intro i hi0 hi1
      fin_cases i
      · exact False.elim (hi0 rfl)
      · exact False.elim (hi1 rfl)
      · exact hl_off
      · exact hk_off
  · exact False.elim (hkl rfl)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

