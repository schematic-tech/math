import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.CrossTransport

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

def replaceEndpointAt (endpoint : Fin 4 -> V) (k : Fin 4) (a : V) :
    Fin 4 -> V := fun i => if i = k then a else endpoint i

theorem CyclicBoundary.clockwiseOpenBetween_of_index_between_classical
    (Ω : CyclicBoundary V) {x y z : V}
    (hz : z ∈ Ω.vertexSet)
    (hxy :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω x <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω y)
    (hxz :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω x <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω z)
    (hzy :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω z <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω y)
    (hzx : z ≠ x) (hzy_ne : z ≠ y) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V) Ω x y z := by
  classical
  refine ⟨⟨hz, ?_⟩, hzx, hzy_ne⟩
  simpa [CyclicBoundary.ClockwiseBetween, hxy] using And.intro hxz hzy

theorem CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
    (Ω : CyclicBoundary V) {x y z : V}
    (hz : z ∈ Ω.vertexSet)
    (hxy :
      ¬ @CyclicBoundary.indexOf V (Classical.decEq V) Ω x <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω y)
    (hwrap :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω x <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω z ∨
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω z <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω y)
    (hzx : z ≠ x) (hzy_ne : z ≠ y) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V) Ω x y z := by
  classical
  refine ⟨⟨hz, ?_⟩, hzx, hzy_ne⟩
  simpa [CyclicBoundary.ClockwiseBetween, hxy] using hwrap

theorem CyclicBoundary.clockwiseOpenBetween_rotate_left
    {Ω : CyclicBoundary V} {x y z : V}
    (hx : x ∈ Ω.vertexSet) (hy : y ∈ Ω.vertexSet)
    (h : @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      Ω x y z) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      Ω y z x := by
  classical
  have hz : z ∈ Ω.vertexSet := h.1.1
  have hxy : x ≠ y := CyclicBoundary.ne_of_clockwiseOpenBetween_left_right h
  have hxz : x ≠ z := by
    intro hxz
    exact h.2.1 hxz.symm
  have hidx_xz : Ω.indexOf x ≠ Ω.indexOf z :=
    CyclicBoundary.indexOf_ne_of_ne hx hxz
  have hidx_zy : Ω.indexOf z ≠ Ω.indexOf y :=
    CyclicBoundary.indexOf_ne_of_ne hz h.2.2
  by_cases hxy_idx : Ω.indexOf x <= Ω.indexOf y
  · have horder := h.1.2
    change
      (if Ω.indexOf x <= Ω.indexOf y then
        Ω.indexOf x <= Ω.indexOf z ∧ Ω.indexOf z <= Ω.indexOf y
      else
        Ω.indexOf x <= Ω.indexOf z ∨ Ω.indexOf z <= Ω.indexOf y) at horder
    rw [if_pos hxy_idx] at horder
    have hx_lt_z : Ω.indexOf x < Ω.indexOf z :=
      lt_of_le_of_ne horder.1 hidx_xz
    have hz_lt_y : Ω.indexOf z < Ω.indexOf y :=
      lt_of_le_of_ne horder.2 hidx_zy
    refine
      CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
        Ω hx ?_ ?_ hxy hxz
    · intro hyz
      omega
    · exact Or.inr (Nat.le_of_lt hx_lt_z)
  · have horder := h.1.2
    change
      (if Ω.indexOf x <= Ω.indexOf y then
        Ω.indexOf x <= Ω.indexOf z ∧ Ω.indexOf z <= Ω.indexOf y
      else
        Ω.indexOf x <= Ω.indexOf z ∨ Ω.indexOf z <= Ω.indexOf y) at horder
    rw [if_neg hxy_idx] at horder
    by_cases hyz_idx : Ω.indexOf y <= Ω.indexOf z
    · refine
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical
          Ω hx hyz_idx ?_ ?_ hxy hxz
      · omega
      · rcases horder with hxz_le | hzy_le
        · exact hxz_le
        · have hy_ne_z : Ω.indexOf y ≠ Ω.indexOf z :=
            CyclicBoundary.indexOf_ne_of_ne hy h.2.2.symm
          omega
    · refine
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
          Ω hx hyz_idx ?_ hxy hxz
      exact Or.inl (by omega)

theorem CyclicBoundary.clockwiseOpenBetween_rotate_right
    {Ω : CyclicBoundary V} {x y z : V}
    (hx : x ∈ Ω.vertexSet) (hy : y ∈ Ω.vertexSet)
    (h : @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      Ω x y z) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      Ω z x y := by
  exact
    CyclicBoundary.clockwiseOpenBetween_rotate_left hy h.1.1
      (CyclicBoundary.clockwiseOpenBetween_rotate_left hx hy h)

theorem GMIX24CutPath.leftBoundaryArc_clockwiseOpenBetween_end_arc_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {a : V}
    (ha : a ∈ P.leftBoundaryArc) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary P.t a P.s := by
  classical
  have h0 : S.boundary.ClockwiseOpenBetween P.s P.t a := by
    simpa [GMIX24CutPath.leftBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using ha
  have h :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s P.t a := by
    simpa [CyclicBoundary.ClockwiseOpenBetween,
      CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using h0
  exact
    CyclicBoundary.clockwiseOpenBetween_rotate_left
      P.s_mem_boundary P.t_mem_boundary h

theorem GMIX24CutPath.leftBoundaryArc_clockwiseOpenBetween_arc_start_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {a : V}
    (ha : a ∈ P.leftBoundaryArc) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary a P.s P.t := by
  classical
  have h0 : S.boundary.ClockwiseOpenBetween P.s P.t a := by
    simpa [GMIX24CutPath.leftBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using ha
  have h :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s P.t a := by
    simpa [CyclicBoundary.ClockwiseOpenBetween,
      CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using h0
  exact
    CyclicBoundary.clockwiseOpenBetween_rotate_right
      P.s_mem_boundary P.t_mem_boundary h

theorem GMIX24CutPath.rightBoundaryArc_clockwiseOpenBetween_start_arc_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {a : V}
    (ha : a ∈ P.rightBoundaryArc) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary P.s a P.t := by
  classical
  have h0 : S.boundary.ClockwiseOpenBetween P.t P.s a := by
    simpa [GMIX24CutPath.rightBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using ha
  have h :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.t P.s a := by
    simpa [CyclicBoundary.ClockwiseOpenBetween,
      CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using h0
  exact
    CyclicBoundary.clockwiseOpenBetween_rotate_left
      P.t_mem_boundary P.s_mem_boundary h

theorem GMIX24CutPath.rightBoundaryArc_clockwiseOpenBetween_arc_end_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {a : V}
    (ha : a ∈ P.rightBoundaryArc) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary a P.t P.s := by
  classical
  have h0 : S.boundary.ClockwiseOpenBetween P.t P.s a := by
    simpa [GMIX24CutPath.rightBoundaryArc, CyclicBoundary.clockwiseArcSet]
      using ha
  have h :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.t P.s a := by
    simpa [CyclicBoundary.ClockwiseOpenBetween,
      CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using h0
  exact
    CyclicBoundary.clockwiseOpenBetween_rotate_right
      P.t_mem_boundary P.s_mem_boundary h

theorem CyclicBoundary.clockwiseOpenBetween_append_middle_singleton_iff_of_ne
    [DecidableEq V]
    {pref mid : List V} {last x y z : V}
    (hshort : (pref ++ [last]).Nodup)
    (hfull : (pref ++ mid ++ [last]).Nodup)
    (hx : x ∈ pref ∨ x = last)
    (hy : y ∈ pref ∨ y = last)
    (hz : z ∈ pref ∨ z = last)
    (hxy : x ≠ y) :
    @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ mid ++ [last], nodup := hfull } :
          CyclicBoundary V) x y z ↔
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ [last], nodup := hshort } :
          CyclicBoundary V) x y z := by
  classical
  letI := Classical.decEq V
  let Ωfull : CyclicBoundary V :=
    { vertices := pref ++ mid ++ [last], nodup := hfull }
  let Ωshort : CyclicBoundary V :=
    { vertices := pref ++ [last], nodup := hshort }
  have hpref : pref.Nodup := hshort.of_append_left
  have hfull_assoc : (pref ++ (mid ++ [last])).Nodup := by
    simpa [List.append_assoc] using hfull
  have hlast_not_short : last ∉ pref := by
    have hdisj :=
      List.disjoint_of_nodup_append (l₁ := pref) (l₂ := [last]) hshort
    intro hlast
    exact (List.disjoint_left.mp hdisj) hlast (by simp)
  have hlast_not_full : last ∉ pref ++ mid := by
    have hdisj :=
      List.disjoint_of_nodup_append (l₁ := pref ++ mid) (l₂ := [last])
        (by simpa [List.append_assoc] using hfull)
    intro hlast
    exact (List.disjoint_left.mp hdisj) hlast (by simp)
  have hidx_full_pref :
      forall {v : V}, v ∈ pref -> Ωfull.indexOf v = pref.idxOf v := by
    intro v hv
    simp [Ωfull, CyclicBoundary.indexOf, List.append_assoc,
      List.idxOf_append_of_mem hv]
  have hidx_short_pref :
      forall {v : V}, v ∈ pref -> Ωshort.indexOf v = pref.idxOf v := by
    intro v hv
    simp [Ωshort, CyclicBoundary.indexOf, List.idxOf_append_of_mem hv]
  have hidx_full_last : Ωfull.indexOf last = pref.length + mid.length := by
    change (pref ++ mid ++ [last]).idxOf last =
      pref.length + mid.length
    calc
      (pref ++ mid ++ [last]).idxOf last =
          ((pref ++ mid) ++ [last]).idxOf last := by
            rw [List.append_assoc]
      _ = (pref ++ mid).length + ([last] : List V).idxOf last :=
            List.idxOf_append_of_notMem hlast_not_full
      _ = pref.length + mid.length := by simp
  have hidx_short_last : Ωshort.indexOf last = pref.length := by
    change (pref ++ [last]).idxOf last = pref.length
    calc
      (pref ++ [last]).idxOf last =
          pref.length + ([last] : List V).idxOf last :=
            List.idxOf_append_of_notMem hlast_not_short
      _ = pref.length := by simp
  have hidx_pref_lt_len :
      forall {v : V}, v ∈ pref -> pref.idxOf v < pref.length := by
    intro v hv
    exact List.idxOf_lt_length_of_mem hv
  rcases hx with hxPref | hxLast
  · rcases hy with hyPref | hyLast
    · rcases hz with hzPref | hzLast
      · have hfull_pref :
            ({ vertices := pref ++ (mid ++ [last]), nodup := hfull_assoc } :
                CyclicBoundary V).ClockwiseOpenBetween x y z ↔
              ({ vertices := pref, nodup := hpref } :
                CyclicBoundary V).ClockwiseOpenBetween x y z :=
          CyclicBoundary.clockwiseOpenBetween_append_tail_iff
            hpref hfull_assoc hxPref hyPref hzPref
        have hshort_pref :
            ({ vertices := pref ++ [last], nodup := hshort } :
                CyclicBoundary V).ClockwiseOpenBetween x y z ↔
              ({ vertices := pref, nodup := hpref } :
                CyclicBoundary V).ClockwiseOpenBetween x y z :=
          CyclicBoundary.clockwiseOpenBetween_append_tail_iff
            hpref hshort hxPref hyPref hzPref
        simpa [Ωfull, Ωshort, List.append_assoc] using
          hfull_pref.trans hshort_pref.symm
      · subst z
        constructor
        · intro hclock
          have hnot_xy : ¬ Ωshort.indexOf x <= Ωshort.indexOf y := by
            intro hxy_le
            have hxy_full : Ωfull.indexOf x <= Ωfull.indexOf y := by
              simpa [hidx_full_pref hxPref, hidx_full_pref hyPref,
                hidx_short_pref hxPref, hidx_short_pref hyPref] using hxy_le
            have horder := hclock.1.2
            change
              (if Ωfull.indexOf x <= Ωfull.indexOf y then
                Ωfull.indexOf x <= Ωfull.indexOf last ∧
                  Ωfull.indexOf last <= Ωfull.indexOf y
              else
                Ωfull.indexOf x <= Ωfull.indexOf last ∨
                  Ωfull.indexOf last <= Ωfull.indexOf y) at horder
            rw [if_pos hxy_full] at horder
            have hy_lt : Ωfull.indexOf y < Ωfull.indexOf last := by
              rw [hidx_full_pref hyPref, hidx_full_last]
              have hy_idx := hidx_pref_lt_len hyPref
              omega
            omega
          exact
            CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
              Ωshort
              (by
                change last ∈ pref ++ [last]
                simp)
              hnot_xy
              (Or.inl (by
                rw [hidx_short_pref hxPref, hidx_short_last]
                exact Nat.le_of_lt (hidx_pref_lt_len hxPref)))
              hclock.2.1 hclock.2.2
        · intro hclock
          have hnot_xy : ¬ Ωfull.indexOf x <= Ωfull.indexOf y := by
            intro hxy_le
            have hxy_short : Ωshort.indexOf x <= Ωshort.indexOf y := by
              simpa [hidx_full_pref hxPref, hidx_full_pref hyPref,
                hidx_short_pref hxPref, hidx_short_pref hyPref] using hxy_le
            have horder := hclock.1.2
            change
              (if Ωshort.indexOf x <= Ωshort.indexOf y then
                Ωshort.indexOf x <= Ωshort.indexOf last ∧
                  Ωshort.indexOf last <= Ωshort.indexOf y
              else
                Ωshort.indexOf x <= Ωshort.indexOf last ∨
                  Ωshort.indexOf last <= Ωshort.indexOf y) at horder
            rw [if_pos hxy_short] at horder
            have hy_lt : Ωshort.indexOf y < Ωshort.indexOf last := by
              rw [hidx_short_pref hyPref, hidx_short_last]
              exact hidx_pref_lt_len hyPref
            omega
          exact
            CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
              Ωfull
              (by
                change last ∈ pref ++ mid ++ [last]
                simp)
              hnot_xy
              (Or.inl (by
                rw [hidx_full_pref hxPref, hidx_full_last]
                have hx_idx := hidx_pref_lt_len hxPref
                omega))
              hclock.2.1 hclock.2.2
    · subst y
      rcases hz with hzPref | hzLast
      · constructor
        · intro hclock
          have hx_last_short :
              Ωshort.indexOf x <= Ωshort.indexOf last := by
            rw [hidx_short_pref hxPref, hidx_short_last]
            exact Nat.le_of_lt (hidx_pref_lt_len hxPref)
          have hxz_short : Ωshort.indexOf x <= Ωshort.indexOf z := by
            have hx_last_full :
                Ωfull.indexOf x <= Ωfull.indexOf last := by
              rw [hidx_full_pref hxPref, hidx_full_last]
              have hx_idx := hidx_pref_lt_len hxPref
              omega
            have horder := hclock.1.2
            change
              (if Ωfull.indexOf x <= Ωfull.indexOf last then
                Ωfull.indexOf x <= Ωfull.indexOf z ∧
                  Ωfull.indexOf z <= Ωfull.indexOf last
              else
                Ωfull.indexOf x <= Ωfull.indexOf z ∨
                  Ωfull.indexOf z <= Ωfull.indexOf last) at horder
            rw [if_pos hx_last_full] at horder
            simpa [hidx_full_pref hxPref, hidx_full_pref hzPref,
              hidx_short_pref hxPref, hidx_short_pref hzPref] using horder.1
          have hz_last_short :
              Ωshort.indexOf z <= Ωshort.indexOf last := by
            rw [hidx_short_pref hzPref, hidx_short_last]
            exact Nat.le_of_lt (hidx_pref_lt_len hzPref)
          exact
            CyclicBoundary.clockwiseOpenBetween_of_index_between_classical
              Ωshort
              (by
                change z ∈ pref ++ [last]
                exact List.mem_append_left [last] hzPref)
              hx_last_short hxz_short hz_last_short
              hclock.2.1 hclock.2.2
        · intro hclock
          have hx_last_full :
              Ωfull.indexOf x <= Ωfull.indexOf last := by
            rw [hidx_full_pref hxPref, hidx_full_last]
            have hx_idx := hidx_pref_lt_len hxPref
            omega
          have hxz_full : Ωfull.indexOf x <= Ωfull.indexOf z := by
            have hx_last_short :
                Ωshort.indexOf x <= Ωshort.indexOf last := by
              rw [hidx_short_pref hxPref, hidx_short_last]
              exact Nat.le_of_lt (hidx_pref_lt_len hxPref)
            have horder := hclock.1.2
            change
              (if Ωshort.indexOf x <= Ωshort.indexOf last then
                Ωshort.indexOf x <= Ωshort.indexOf z ∧
                  Ωshort.indexOf z <= Ωshort.indexOf last
              else
                Ωshort.indexOf x <= Ωshort.indexOf z ∨
                  Ωshort.indexOf z <= Ωshort.indexOf last) at horder
            rw [if_pos hx_last_short] at horder
            simpa [hidx_full_pref hxPref, hidx_full_pref hzPref,
              hidx_short_pref hxPref, hidx_short_pref hzPref] using horder.1
          have hz_last_full :
              Ωfull.indexOf z <= Ωfull.indexOf last := by
            rw [hidx_full_pref hzPref, hidx_full_last]
            have hz_idx := hidx_pref_lt_len hzPref
            omega
          exact
            CyclicBoundary.clockwiseOpenBetween_of_index_between_classical
              Ωfull
              (by
                change z ∈ pref ++ mid ++ [last]
                simpa [List.append_assoc] using
                  (List.mem_append_left (mid ++ [last]) hzPref))
              hx_last_full hxz_full hz_last_full
              hclock.2.1 hclock.2.2
      · subst z
        constructor
        · intro hclock
          exact False.elim (hclock.2.2 rfl)
        · intro hclock
          exact False.elim (hclock.2.2 rfl)
  · subst x
    rcases hy with hyPref | hyLast
    · rcases hz with hzPref | hzLast
      · constructor
        · intro hclock
          have hnot_last_y :
              ¬ Ωshort.indexOf last <= Ωshort.indexOf y := by
            intro hle
            have hy_lt : Ωshort.indexOf y < Ωshort.indexOf last := by
              rw [hidx_short_pref hyPref, hidx_short_last]
              exact hidx_pref_lt_len hyPref
            omega
          have hzy_short : Ωshort.indexOf z <= Ωshort.indexOf y := by
            have hnot_last_y_full :
                ¬ Ωfull.indexOf last <= Ωfull.indexOf y := by
              intro hle
              have hy_lt : Ωfull.indexOf y < Ωfull.indexOf last := by
                rw [hidx_full_pref hyPref, hidx_full_last]
                have hy_idx := hidx_pref_lt_len hyPref
                omega
              omega
            have horder := hclock.1.2
            change
              (if Ωfull.indexOf last <= Ωfull.indexOf y then
                Ωfull.indexOf last <= Ωfull.indexOf z ∧
                  Ωfull.indexOf z <= Ωfull.indexOf y
              else
                Ωfull.indexOf last <= Ωfull.indexOf z ∨
                  Ωfull.indexOf z <= Ωfull.indexOf y) at horder
            rw [if_neg hnot_last_y_full] at horder
            rcases horder with hlast_z | hz_y
            · have hz_lt : Ωfull.indexOf z < Ωfull.indexOf last := by
                rw [hidx_full_pref hzPref, hidx_full_last]
                have hz_idx := hidx_pref_lt_len hzPref
                omega
              omega
            · simpa [hidx_full_pref hzPref, hidx_full_pref hyPref,
                hidx_short_pref hzPref, hidx_short_pref hyPref] using hz_y
          exact
            CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
              Ωshort
              (by
                change z ∈ pref ++ [last]
                exact List.mem_append_left [last] hzPref)
              hnot_last_y (Or.inr hzy_short)
              hclock.2.1 hclock.2.2
        · intro hclock
          have hnot_last_y :
              ¬ Ωfull.indexOf last <= Ωfull.indexOf y := by
            intro hle
            have hy_lt : Ωfull.indexOf y < Ωfull.indexOf last := by
              rw [hidx_full_pref hyPref, hidx_full_last]
              have hy_idx := hidx_pref_lt_len hyPref
              omega
            omega
          have hzy_full : Ωfull.indexOf z <= Ωfull.indexOf y := by
            have hnot_last_y_short :
                ¬ Ωshort.indexOf last <= Ωshort.indexOf y := by
              intro hle
              have hy_lt : Ωshort.indexOf y < Ωshort.indexOf last := by
                rw [hidx_short_pref hyPref, hidx_short_last]
                exact hidx_pref_lt_len hyPref
              omega
            have horder := hclock.1.2
            change
              (if Ωshort.indexOf last <= Ωshort.indexOf y then
                Ωshort.indexOf last <= Ωshort.indexOf z ∧
                  Ωshort.indexOf z <= Ωshort.indexOf y
              else
                Ωshort.indexOf last <= Ωshort.indexOf z ∨
                  Ωshort.indexOf z <= Ωshort.indexOf y) at horder
            rw [if_neg hnot_last_y_short] at horder
            rcases horder with hlast_z | hz_y
            · have hz_lt : Ωshort.indexOf z < Ωshort.indexOf last := by
                rw [hidx_short_pref hzPref, hidx_short_last]
                exact hidx_pref_lt_len hzPref
              omega
            · simpa [hidx_full_pref hzPref, hidx_full_pref hyPref,
                hidx_short_pref hzPref, hidx_short_pref hyPref] using hz_y
          exact
            CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
              Ωfull
              (by
                change z ∈ pref ++ mid ++ [last]
                simpa [List.append_assoc] using
                  (List.mem_append_left (mid ++ [last]) hzPref))
              hnot_last_y (Or.inr hzy_full)
              hclock.2.1 hclock.2.2
      · subst z
        constructor
        · intro hclock
          exact False.elim (hclock.2.1 rfl)
        · intro hclock
          exact False.elim (hclock.2.1 rfl)
    · subst y
      exact False.elim (hxy rfl)

theorem GMIX24CutPath.leftOrdered_clockwiseOpenBetween_original_of_arc_or_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.leftBoundaryArc ∨ x = P.s)
    (hy : y ∈ P.leftBoundaryArc ∨ y = P.s)
    (hz : z ∈ P.leftBoundaryArc ∨ z = P.s)
    (hxy : x ≠ y)
    (hclock :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        P.leftOrderedCutBoundary x y z) :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary x y z := by
  classical
  let pref : List V := P.leftBoundaryArcList
  let sideMid : List V := P.path.support.reverse.dropLast
  have hrev_snoc :
      P.path.support.reverse = sideMid ++ [P.s] := by
    have h :=
      (List.dropLast_append_getLast
        (SimpleGraph.Walk.support_ne_nil P.path.reverse)).symm
    simp [sideMid, SimpleGraph.Walk.support_reverse] at h ⊢
  have hside_vertices :
      P.leftOrderedCutBoundary.vertices = pref ++ sideMid ++ [P.s] := by
    dsimp [GMIX24CutPath.leftOrderedCutBoundary,
      GMIX24CutPath.leftOrderedCutBoundaryVertices]
    rw [hrev_snoc]
    simp [pref, sideMid, List.append_assoc]
  have hsideNodup : (pref ++ sideMid ++ [P.s]).Nodup := by
    simpa [← hside_vertices] using P.leftOrderedCutBoundary.nodup
  have hshort : (pref ++ [P.s]).Nodup := by
    simpa [pref] using P.leftBoundaryArcList_append_start_nodup
  have hxShort : x ∈ pref ∨ x = P.s := by
    rcases hx with hxArc | hxs
    · exact Or.inl (by
        simpa [pref] using (GMIX24CutPath.mem_leftBoundaryArcList P).mpr hxArc)
    · exact Or.inr hxs
  have hyShort : y ∈ pref ∨ y = P.s := by
    rcases hy with hyArc | hys
    · exact Or.inl (by
        simpa [pref] using (GMIX24CutPath.mem_leftBoundaryArcList P).mpr hyArc)
    · exact Or.inr hys
  have hzShort : z ∈ pref ∨ z = P.s := by
    rcases hz with hzArc | hzs
    · exact Or.inl (by
        simpa [pref] using (GMIX24CutPath.mem_leftBoundaryArcList P).mpr hzArc)
    · exact Or.inr hzs
  have hclockSideFull :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ sideMid ++ [P.s], nodup := hsideNodup } :
          CyclicBoundary V) x y z := by
    rcases hclock with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ pref ++ sideMid ++ [P.s]
      simpa [CyclicBoundary.vertexSet, hside_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hside_vertices, List.append_assoc] using horder
  have hclockShort :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ [P.s], nodup := hshort } :
          CyclicBoundary V) x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_middle_singleton_iff_of_ne
      hshort hsideNodup hxShort hyShort hzShort hxy).mp hclockSideFull
  let Ωrot : CyclicBoundary V :=
    { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1),
      nodup := List.nodup_rotate.mpr S.boundary.nodup }
  let origBeforeStart : List V :=
    S.boundary.vertices.drop (S.boundary.indexOf P.s + 1) ++
      S.boundary.vertices.take (S.boundary.indexOf P.s)
  let origMid : List V := origBeforeStart.drop pref.length
  have hs_mem : P.s ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.s_mem_boundary
  have hn :
      S.boundary.indexOf P.s + 1 <= S.boundary.vertices.length := by
    have hs_idx : S.boundary.indexOf P.s < S.boundary.vertices.length := by
      simpa [CyclicBoundary.indexOf] using
        (List.idxOf_lt_length_iff.mpr hs_mem)
    omega
  have hs_idx_lt : S.boundary.indexOf P.s < S.boundary.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr hs_mem)
  have hs_get :
      S.boundary.vertices[S.boundary.indexOf P.s] = P.s := by
    simp [CyclicBoundary.indexOf]
  have htake_succ :
      S.boundary.vertices.take (S.boundary.indexOf P.s + 1) =
        S.boundary.vertices.take (S.boundary.indexOf P.s) ++ [P.s] := by
    calc
      S.boundary.vertices.take (S.boundary.indexOf P.s + 1)
          = S.boundary.vertices.take (S.boundary.indexOf P.s) ++
              [S.boundary.vertices[S.boundary.indexOf P.s]] := by
            exact (List.take_concat_get' S.boundary.vertices
              (S.boundary.indexOf P.s) hs_idx_lt).symm
      _ = S.boundary.vertices.take (S.boundary.indexOf P.s) ++ [P.s] := by
            simp [hs_get]
  have hrot_snoc :
      Ωrot.vertices = origBeforeStart ++ [P.s] := by
    dsimp [Ωrot]
    rw [List.rotate_eq_drop_append_take hn, htake_succ]
    simp [origBeforeStart, List.append_assoc]
  have htake_idx :
      pref = Ωrot.vertices.take (Ωrot.indexOf P.t) := by
    simpa [pref, Ωrot] using
      (GMIX24CutPath.leftBoundaryArcList_eq_rotate_take_to_end P)
  have htRot : P.t ∈ Ωrot.vertices := by
    exact (List.mem_rotate).mpr (by
      simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
        P.t_mem_boundary)
  have htIdx_lt : Ωrot.indexOf P.t < Ωrot.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr htRot)
  have hlen_pref : pref.length = Ωrot.indexOf P.t := by
    have hlen := congrArg List.length htake_idx
    have hle : Ωrot.indexOf P.t <= Ωrot.vertices.length :=
      Nat.le_of_lt htIdx_lt
    simpa [List.length_take, Nat.min_eq_left hle] using hlen
  have hprefix : Ωrot.vertices.take pref.length = pref := by
    rw [hlen_pref]
    exact htake_idx.symm
  have htake_before :
      origBeforeStart.take pref.length = pref := by
    have htake_rot :
        Ωrot.vertices.take pref.length =
          (origBeforeStart ++ [P.s]).take pref.length := by
      rw [hrot_snoc]
    have hle_before : pref.length <= origBeforeStart.length := by
      have ht_ne_s : P.t ≠ P.s := P.s_ne_t.symm
      have htBefore : P.t ∈ origBeforeStart := by
        have htAppend : P.t ∈ origBeforeStart ++ [P.s] := by
          simpa [← hrot_snoc] using htRot
        rcases List.mem_append.mp htAppend with htBefore | htLast
        · exact htBefore
        · simp at htLast
          exact False.elim (ht_ne_s htLast)
      have htIdxBefore : origBeforeStart.idxOf P.t < origBeforeStart.length :=
        List.idxOf_lt_length_of_mem htBefore
      have hidx_rot_before :
          Ωrot.indexOf P.t = origBeforeStart.idxOf P.t := by
        change Ωrot.vertices.idxOf P.t = origBeforeStart.idxOf P.t
        rw [hrot_snoc]
        exact List.idxOf_append_of_mem (l₂ := [P.s]) htBefore
      rw [hlen_pref, hidx_rot_before]
      exact Nat.le_of_lt htIdxBefore
    have htake_append :
        (origBeforeStart ++ [P.s]).take pref.length =
          origBeforeStart.take pref.length := by
      exact List.take_append_of_le_length hle_before
    simpa [hprefix, htake_append] using htake_rot.symm
  have hbefore_split : origBeforeStart = pref ++ origMid := by
    calc
      origBeforeStart =
          origBeforeStart.take pref.length ++
            origBeforeStart.drop pref.length := by
            exact (List.take_append_drop pref.length origBeforeStart).symm
      _ = pref ++ origMid := by
            simp [htake_before, origMid]
  have hrot_vertices : Ωrot.vertices = pref ++ origMid ++ [P.s] := by
    rw [hrot_snoc, hbefore_split, List.append_assoc]
  have hrotNodup : (pref ++ origMid ++ [P.s]).Nodup := by
    simpa [← hrot_vertices] using Ωrot.nodup
  have hclockRotFull :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ origMid ++ [P.s], nodup := hrotNodup } :
          CyclicBoundary V) x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_middle_singleton_iff_of_ne
      hshort hrotNodup hxShort hyShort hzShort hxy).mpr hclockShort
  have hrot :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ωrot x y z := by
    rcases hclockRotFull with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ Ωrot.vertices
      change z ∈ pref ++ origMid ++ [P.s] at hzMem
      simpa [hrot_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hrot_vertices, List.append_assoc] using horder
  have hxOrig : x ∈ S.boundary.vertexSet := by
    rcases hx with hxArc | hxs
    · simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hxArc
    · subst x
      simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have hyOrig : y ∈ S.boundary.vertexSet := by
    rcases hy with hyArc | hys
    · simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hyArc
    · subst y
      simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have hzOrig : z ∈ S.boundary.vertexSet := by
    rcases hz with hzArc | hzs
    · simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hzArc
    · subst z
      simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have hlocal : S.boundary.ClockwiseOpenBetween x y z :=
    CyclicBoundary.clockwiseOpenBetween_of_rotate
      S.boundary hn hxOrig hyOrig hzOrig
      (by
        have hrotCurrent : Ωrot.ClockwiseOpenBetween x y z := by
          simpa [CyclicBoundary.ClockwiseOpenBetween,
            CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using hrot
        simpa [Ωrot] using hrotCurrent)
  simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
    CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
    hlocal

theorem GMIX24CutPath.rightOrdered_clockwiseOpenBetween_original_of_arc_or_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.rightBoundaryArc ∨ x = P.t)
    (hy : y ∈ P.rightBoundaryArc ∨ y = P.t)
    (hz : z ∈ P.rightBoundaryArc ∨ z = P.t)
    (hxy : x ≠ y)
    (hclock :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        P.rightOrderedCutBoundary x y z) :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary x y z := by
  classical
  let pref : List V := P.rightBoundaryArcList
  let sideMid : List V := P.path.support.dropLast
  have hpath_snoc :
      P.path.support = sideMid ++ [P.t] := by
    have h :=
      (List.dropLast_append_getLast
        (SimpleGraph.Walk.support_ne_nil P.path)).symm
    simp [sideMid] at h ⊢
  have hside_vertices :
      P.rightOrderedCutBoundary.vertices = pref ++ sideMid ++ [P.t] := by
    dsimp [GMIX24CutPath.rightOrderedCutBoundary,
      GMIX24CutPath.rightOrderedCutBoundaryVertices]
    rw [hpath_snoc]
    simp [pref, sideMid, List.append_assoc]
  have hsideNodup : (pref ++ sideMid ++ [P.t]).Nodup := by
    simpa [← hside_vertices] using P.rightOrderedCutBoundary.nodup
  have hshort : (pref ++ [P.t]).Nodup := by
    simpa [pref] using P.rightBoundaryArcList_append_end_nodup
  have hxShort : x ∈ pref ∨ x = P.t := by
    rcases hx with hxArc | hxt
    · exact Or.inl (by
        simpa [pref] using (GMIX24CutPath.mem_rightBoundaryArcList P).mpr hxArc)
    · exact Or.inr hxt
  have hyShort : y ∈ pref ∨ y = P.t := by
    rcases hy with hyArc | hyt
    · exact Or.inl (by
        simpa [pref] using (GMIX24CutPath.mem_rightBoundaryArcList P).mpr hyArc)
    · exact Or.inr hyt
  have hzShort : z ∈ pref ∨ z = P.t := by
    rcases hz with hzArc | hzt
    · exact Or.inl (by
        simpa [pref] using (GMIX24CutPath.mem_rightBoundaryArcList P).mpr hzArc)
    · exact Or.inr hzt
  have hclockSideFull :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ sideMid ++ [P.t], nodup := hsideNodup } :
          CyclicBoundary V) x y z := by
    rcases hclock with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ pref ++ sideMid ++ [P.t]
      simpa [CyclicBoundary.vertexSet, hside_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hside_vertices, List.append_assoc] using horder
  have hclockShort :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ [P.t], nodup := hshort } :
          CyclicBoundary V) x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_middle_singleton_iff_of_ne
      hshort hsideNodup hxShort hyShort hzShort hxy).mp hclockSideFull
  let Ωrot : CyclicBoundary V :=
    { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.t + 1),
      nodup := List.nodup_rotate.mpr S.boundary.nodup }
  let origBeforeEnd : List V :=
    S.boundary.vertices.drop (S.boundary.indexOf P.t + 1) ++
      S.boundary.vertices.take (S.boundary.indexOf P.t)
  let origMid : List V := origBeforeEnd.drop pref.length
  have ht_mem : P.t ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.t_mem_boundary
  have hn :
      S.boundary.indexOf P.t + 1 <= S.boundary.vertices.length := by
    have ht_idx : S.boundary.indexOf P.t < S.boundary.vertices.length := by
      simpa [CyclicBoundary.indexOf] using
        (List.idxOf_lt_length_iff.mpr ht_mem)
    omega
  have ht_idx_lt : S.boundary.indexOf P.t < S.boundary.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr ht_mem)
  have ht_get :
      S.boundary.vertices[S.boundary.indexOf P.t] = P.t := by
    simp [CyclicBoundary.indexOf]
  have htake_succ :
      S.boundary.vertices.take (S.boundary.indexOf P.t + 1) =
        S.boundary.vertices.take (S.boundary.indexOf P.t) ++ [P.t] := by
    calc
      S.boundary.vertices.take (S.boundary.indexOf P.t + 1)
          = S.boundary.vertices.take (S.boundary.indexOf P.t) ++
              [S.boundary.vertices[S.boundary.indexOf P.t]] := by
            exact (List.take_concat_get' S.boundary.vertices
              (S.boundary.indexOf P.t) ht_idx_lt).symm
      _ = S.boundary.vertices.take (S.boundary.indexOf P.t) ++ [P.t] := by
            simp [ht_get]
  have hrot_snoc :
      Ωrot.vertices = origBeforeEnd ++ [P.t] := by
    dsimp [Ωrot]
    rw [List.rotate_eq_drop_append_take hn, htake_succ]
    simp [origBeforeEnd, List.append_assoc]
  have htake_idx :
      pref = Ωrot.vertices.take (Ωrot.indexOf P.s) := by
    simpa [pref, Ωrot] using
      (GMIX24CutPath.rightBoundaryArcList_eq_rotate_take_to_start P)
  have hsRot : P.s ∈ Ωrot.vertices := by
    exact (List.mem_rotate).mpr (by
      simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
        P.s_mem_boundary)
  have hsIdx_lt : Ωrot.indexOf P.s < Ωrot.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr hsRot)
  have hlen_pref : pref.length = Ωrot.indexOf P.s := by
    have hlen := congrArg List.length htake_idx
    have hle : Ωrot.indexOf P.s <= Ωrot.vertices.length :=
      Nat.le_of_lt hsIdx_lt
    simpa [List.length_take, Nat.min_eq_left hle] using hlen
  have hprefix : Ωrot.vertices.take pref.length = pref := by
    rw [hlen_pref]
    exact htake_idx.symm
  have htake_before :
      origBeforeEnd.take pref.length = pref := by
    have htake_rot :
        Ωrot.vertices.take pref.length =
          (origBeforeEnd ++ [P.t]).take pref.length := by
      rw [hrot_snoc]
    have hle_before : pref.length <= origBeforeEnd.length := by
      have hs_ne_t : P.s ≠ P.t := P.s_ne_t
      have hsBefore : P.s ∈ origBeforeEnd := by
        have hsAppend : P.s ∈ origBeforeEnd ++ [P.t] := by
          simpa [← hrot_snoc] using hsRot
        rcases List.mem_append.mp hsAppend with hsBefore | hsLast
        · exact hsBefore
        · simp at hsLast
          exact False.elim (hs_ne_t hsLast)
      have hsIdxBefore : origBeforeEnd.idxOf P.s < origBeforeEnd.length :=
        List.idxOf_lt_length_of_mem hsBefore
      have hidx_rot_before :
          Ωrot.indexOf P.s = origBeforeEnd.idxOf P.s := by
        change Ωrot.vertices.idxOf P.s = origBeforeEnd.idxOf P.s
        rw [hrot_snoc]
        exact List.idxOf_append_of_mem (l₂ := [P.t]) hsBefore
      rw [hlen_pref, hidx_rot_before]
      exact Nat.le_of_lt hsIdxBefore
    have htake_append :
        (origBeforeEnd ++ [P.t]).take pref.length =
          origBeforeEnd.take pref.length := by
      exact List.take_append_of_le_length hle_before
    simpa [hprefix, htake_append] using htake_rot.symm
  have hbefore_split : origBeforeEnd = pref ++ origMid := by
    calc
      origBeforeEnd =
          origBeforeEnd.take pref.length ++
            origBeforeEnd.drop pref.length := by
            exact (List.take_append_drop pref.length origBeforeEnd).symm
      _ = pref ++ origMid := by
            simp [htake_before, origMid]
  have hrot_vertices : Ωrot.vertices = pref ++ origMid ++ [P.t] := by
    rw [hrot_snoc, hbefore_split, List.append_assoc]
  have hrotNodup : (pref ++ origMid ++ [P.t]).Nodup := by
    simpa [← hrot_vertices] using Ωrot.nodup
  have hclockRotFull :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        ({ vertices := pref ++ origMid ++ [P.t], nodup := hrotNodup } :
          CyclicBoundary V) x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_middle_singleton_iff_of_ne
      hshort hrotNodup hxShort hyShort hzShort hxy).mpr hclockShort
  have hrot :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ωrot x y z := by
    rcases hclockRotFull with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ Ωrot.vertices
      change z ∈ pref ++ origMid ++ [P.t] at hzMem
      simpa [hrot_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hrot_vertices, List.append_assoc] using horder
  have hxOrig : x ∈ S.boundary.vertexSet := by
    rcases hx with hxArc | hxt
    · simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset hxArc
    · subst x
      simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hyOrig : y ∈ S.boundary.vertexSet := by
    rcases hy with hyArc | hyt
    · simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset hyArc
    · subst y
      simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hzOrig : z ∈ S.boundary.vertexSet := by
    rcases hz with hzArc | hzt
    · simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset hzArc
    · subst z
      simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hlocal : S.boundary.ClockwiseOpenBetween x y z :=
    CyclicBoundary.clockwiseOpenBetween_of_rotate
      S.boundary hn hxOrig hyOrig hzOrig
      (by
        have hrotCurrent : Ωrot.ClockwiseOpenBetween x y z := by
          simpa [CyclicBoundary.ClockwiseOpenBetween,
            CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using hrot
        simpa [Ωrot] using hrotCurrent)
  simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
    CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
    hlocal

theorem crossEndpointAlternating_replaceEndpoint0_or_2_of_before_all
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (hmem : forall i : Fin 4, endpoint i ∈ Ω.vertexSet)
    (hinj : Function.Injective endpoint)
    (_ha_mem : a ∈ Ω.vertexSet)
    (ha_lt :
      forall i : Fin 4,
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 0 a) ∨
      CrossEndpointAlternating Ω (replaceEndpointAt endpoint 2 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have hidx02_ne : idx (endpoint 0) ≠ idx (endpoint 2) := by
    intro hidx
    have h02 : endpoint 0 = endpoint 2 := by
      simpa [idx, CyclicBoundary.indexOf] using
        (List.idxOf_inj (hmem 0)).mp (by
          simpa [idx, CyclicBoundary.indexOf] using hidx)
    have hfin : (0 : Fin 4) = 2 := hinj h02
    have hval : ((0 : Fin 4).val : Nat) = (2 : Fin 4).val :=
      congrArg Fin.val hfin
    omega
  have h1_ne_a : endpoint 1 ≠ a := by
    intro h
    have hlt := ha_lt 1
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  have h3_ne_a : endpoint 3 ≠ a := by
    intro h
    have hlt := ha_lt 3
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  have ha_le0 : idx a <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 0)
  have ha_le1 : idx a <= idx (endpoint 1) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 1)
  have ha_le2 : idx a <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 2)
  have ha_le3 : idx a <= idx (endpoint 3) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 3)
  have h0a_not : ¬ idx (endpoint 0) <= idx a := by
    have hlt : idx a < idx (endpoint 0) := by
      simpa [idx] using ha_lt 0
    omega
  have h2a_not : ¬ idx (endpoint 2) <= idx a := by
    have hlt : idx a < idx (endpoint 2) := by
      simpa [idx] using ha_lt 2
    omega
  rcases halt with ⟨h012, h203⟩
  by_cases h02 : idx (endpoint 0) <= idx (endpoint 2)
  · have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by
      intro h20
      exact hidx02_ne (by omega)
    have h012_order :
        idx (endpoint 0) <= idx (endpoint 1) ∧
          idx (endpoint 1) <= idx (endpoint 2) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
    have h203_wrap :
        idx (endpoint 2) <= idx (endpoint 3) ∨
          idx (endpoint 3) <= idx (endpoint 0) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h20_not] using h203.1.2
    by_cases h23 : idx (endpoint 2) <= idx (endpoint 3)
    · left
      dsimp [CrossEndpointAlternating, replaceEndpointAt]
      constructor
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
            h012.1.1 ha_le2 ha_le1 h012_order.2 h1_ne_a h012.2.2
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
            h203.1.1 h2a_not (Or.inl h23) h203.2.1 h3_ne_a
    · have h30 : idx (endpoint 3) <= idx (endpoint 0) := by
        rcases h203_wrap with h23' | h30
        · exact False.elim (h23 h23')
        · exact h30
      right
      dsimp [CrossEndpointAlternating, replaceEndpointAt]
      constructor
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
            h012.1.1 h0a_not (Or.inl h012_order.1)
            h012.2.1 h1_ne_a
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
            h203.1.1 ha_le0 ha_le3 h30 h3_ne_a h203.2.2
  · have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
    have h012_wrap :
        idx (endpoint 0) <= idx (endpoint 1) ∨
          idx (endpoint 1) <= idx (endpoint 2) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
    have h203_order :
        idx (endpoint 2) <= idx (endpoint 3) ∧
          idx (endpoint 3) <= idx (endpoint 0) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h20] using h203.1.2
    by_cases h01 : idx (endpoint 0) <= idx (endpoint 1)
    · right
      dsimp [CrossEndpointAlternating, replaceEndpointAt]
      constructor
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
            h012.1.1 h0a_not (Or.inl h01)
            h012.2.1 h1_ne_a
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
            h203.1.1 ha_le0 ha_le3 h203_order.2 h3_ne_a h203.2.2
    · have h12 : idx (endpoint 1) <= idx (endpoint 2) := by
        rcases h012_wrap with h01' | h12
        · exact False.elim (h01 h01')
        · exact h12
      left
      dsimp [CrossEndpointAlternating, replaceEndpointAt]
      constructor
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
            h012.1.1 ha_le2 ha_le1 h12 h1_ne_a h012.2.2
      · exact
          CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
            h203.1.1 h2a_not (Or.inl h203_order.1)
            h203.2.1 h3_ne_a

theorem crossEndpointAlternating_replaceEndpoint1_or_3_of_before_all
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (hmem : forall i : Fin 4, endpoint i ∈ Ω.vertexSet)
    (hinj : Function.Injective endpoint)
    (ha_mem : a ∈ Ω.vertexSet)
    (ha_lt :
      forall i : Fin 4,
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 1 a) ∨
      CrossEndpointAlternating Ω (replaceEndpointAt endpoint 3 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have hidx02_ne : idx (endpoint 0) ≠ idx (endpoint 2) := by
    intro hidx
    have h02 : endpoint 0 = endpoint 2 := by
      simpa [idx, CyclicBoundary.indexOf] using
        (List.idxOf_inj (hmem 0)).mp (by
          simpa [idx, CyclicBoundary.indexOf] using hidx)
    have hfin : (0 : Fin 4) = 2 := hinj h02
    have hval : ((0 : Fin 4).val : Nat) = (2 : Fin 4).val :=
      congrArg Fin.val hfin
    omega
  have ha_ne0 : a ≠ endpoint 0 := by
    intro h
    have hlt := ha_lt 0
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  have ha_ne2 : a ≠ endpoint 2 := by
    intro h
    have hlt := ha_lt 2
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  have ha_le0 : idx a <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 0)
  have ha_le2 : idx a <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 2)
  rcases halt with ⟨h012, h203⟩
  by_cases h02 : idx (endpoint 0) <= idx (endpoint 2)
  · have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by
      intro h20
      exact hidx02_ne (by omega)
    right
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact h012
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          ha_mem h20_not (Or.inr ha_le0) ha_ne2 ha_ne0
  · have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
    left
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          ha_mem h02 (Or.inr ha_le2) ha_ne0 ha_ne2
    · exact h203

theorem crossEndpointAlternating_replaceEndpoint0_or_2_of_endpoint3_before_path
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (hmem : forall i : Fin 4, endpoint i ∈ Ω.vertexSet)
    (hinj : Function.Injective endpoint)
    (ha_lt :
      forall i : Fin 4, i ≠ 3 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (h3_lt :
      forall i : Fin 4, i ≠ 3 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 3) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (ha_ne3 : a ≠ endpoint 3)
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 0 a) ∨
      CrossEndpointAlternating Ω (replaceEndpointAt endpoint 2 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have hidx02_ne : idx (endpoint 0) ≠ idx (endpoint 2) := by
    intro hidx
    have h02 : endpoint 0 = endpoint 2 := by
      simpa [idx, CyclicBoundary.indexOf] using
        (List.idxOf_inj (hmem 0)).mp (by
          simpa [idx, CyclicBoundary.indexOf] using hidx)
    have hfin : (0 : Fin 4) = 2 := hinj h02
    have hval : ((0 : Fin 4).val : Nat) = (2 : Fin 4).val :=
      congrArg Fin.val hfin
    omega
  have ha_le0 : idx a <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 0 (by decide))
  have ha_le1 : idx a <= idx (endpoint 1) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 1 (by decide))
  have ha_le2 : idx a <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 2 (by decide))
  have h3_le0 : idx (endpoint 3) <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (h3_lt 0 (by decide))
  have h3_le2 : idx (endpoint 3) <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (h3_lt 2 (by decide))
  have h0a_not : ¬ idx (endpoint 0) <= idx a := by
    have hlt : idx a < idx (endpoint 0) := by
      simpa [idx] using (ha_lt 0 (by decide))
    omega
  have h2a_not : ¬ idx (endpoint 2) <= idx a := by
    have hlt : idx a < idx (endpoint 2) := by
      simpa [idx] using (ha_lt 2 (by decide))
    omega
  have h1_ne_a : endpoint 1 ≠ a := by
    intro h
    have hlt := ha_lt 1 (by decide)
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  have h3_ne_a : endpoint 3 ≠ a := fun h => ha_ne3 h.symm
  rcases halt with ⟨h012, h203⟩
  have h02 : idx (endpoint 0) <= idx (endpoint 2) := by
    by_contra h02
    have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
    have h203_order :
        idx (endpoint 2) <= idx (endpoint 3) ∧
          idx (endpoint 3) <= idx (endpoint 0) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h20] using h203.1.2
    have h3lt2 : idx (endpoint 3) < idx (endpoint 2) := by
      simpa [idx] using h3_lt 2 (by decide)
    omega
  have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by
    intro h20
    exact hidx02_ne (by omega)
  have h012_order :
      idx (endpoint 0) <= idx (endpoint 1) ∧
        idx (endpoint 1) <= idx (endpoint 2) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
  by_cases h3a : idx (endpoint 3) <= idx a
  · left
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
          h012.1.1 ha_le2 ha_le1 h012_order.2 h1_ne_a h012.2.2
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          h203.1.1 h2a_not (Or.inr h3a) h203.2.1 h3_ne_a
  · have ha3 : idx a <= idx (endpoint 3) := by omega
    right
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          h012.1.1 h0a_not (Or.inl h012_order.1) h012.2.1 h1_ne_a
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
          h203.1.1 ha_le0 ha3 h3_le0 h3_ne_a h203.2.2

theorem crossEndpointAlternating_replaceEndpoint0_or_2_of_endpoint1_before_path
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (hmem : forall i : Fin 4, endpoint i ∈ Ω.vertexSet)
    (hinj : Function.Injective endpoint)
    (ha_lt :
      forall i : Fin 4, i ≠ 1 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (h1_lt :
      forall i : Fin 4, i ≠ 1 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 1) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (ha_ne1 : a ≠ endpoint 1)
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 0 a) ∨
      CrossEndpointAlternating Ω (replaceEndpointAt endpoint 2 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have hidx02_ne : idx (endpoint 0) ≠ idx (endpoint 2) := by
    intro hidx
    have h02 : endpoint 0 = endpoint 2 := by
      simpa [idx, CyclicBoundary.indexOf] using
        (List.idxOf_inj (hmem 0)).mp (by
          simpa [idx, CyclicBoundary.indexOf] using hidx)
    have hfin : (0 : Fin 4) = 2 := hinj h02
    have hval : ((0 : Fin 4).val : Nat) = (2 : Fin 4).val :=
      congrArg Fin.val hfin
    omega
  have ha_le0 : idx a <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 0 (by decide))
  have ha_le2 : idx a <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 2 (by decide))
  have ha_le3 : idx a <= idx (endpoint 3) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 3 (by decide))
  have h1_le0 : idx (endpoint 1) <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (h1_lt 0 (by decide))
  have h1_le2 : idx (endpoint 1) <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (h1_lt 2 (by decide))
  have h0a_not : ¬ idx (endpoint 0) <= idx a := by
    have hlt : idx a < idx (endpoint 0) := by
      simpa [idx] using (ha_lt 0 (by decide))
    omega
  have h2a_not : ¬ idx (endpoint 2) <= idx a := by
    have hlt : idx a < idx (endpoint 2) := by
      simpa [idx] using (ha_lt 2 (by decide))
    omega
  have h1_ne_a : endpoint 1 ≠ a := fun h => ha_ne1 h.symm
  have h3_ne_a : endpoint 3 ≠ a := by
    intro h
    have hlt := ha_lt 3 (by decide)
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  rcases halt with ⟨h012, h203⟩
  have h02_not : ¬ idx (endpoint 0) <= idx (endpoint 2) := by
    intro h02
    have h012_order :
        idx (endpoint 0) <= idx (endpoint 1) ∧
          idx (endpoint 1) <= idx (endpoint 2) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
    have h1lt0 : idx (endpoint 1) < idx (endpoint 0) := by
      simpa [idx] using h1_lt 0 (by decide)
    omega
  have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
  have h203_order :
      idx (endpoint 2) <= idx (endpoint 3) ∧
        idx (endpoint 3) <= idx (endpoint 0) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h20] using h203.1.2
  by_cases ha1 : idx a <= idx (endpoint 1)
  · left
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
          h012.1.1 ha_le2 ha1 h1_le2 h1_ne_a h012.2.2
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          h203.1.1 h2a_not (Or.inl h203_order.1) h203.2.1 h3_ne_a
  · have h1a : idx (endpoint 1) <= idx a := by omega
    right
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          h012.1.1 h0a_not (Or.inr h1a) h012.2.1 h1_ne_a
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
          h203.1.1 ha_le0 ha_le3 h203_order.2 h3_ne_a h203.2.2

theorem crossEndpointAlternating_replaceEndpoint1_or_3_of_endpoint0_before_path
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (ha_mem : a ∈ Ω.vertexSet)
    (ha_lt :
      forall i : Fin 4, i ≠ 0 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (h0_lt :
      forall i : Fin 4, i ≠ 0 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 0) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (ha_ne0 : a ≠ endpoint 0)
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 1 a) ∨
      CrossEndpointAlternating Ω (replaceEndpointAt endpoint 3 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h02 : idx (endpoint 0) <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (h0_lt 2 (by decide))
  have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by
    have hlt : idx (endpoint 0) < idx (endpoint 2) := by
      simpa [idx] using h0_lt 2 (by decide)
    omega
  have ha_le2 : idx a <= idx (endpoint 2) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 2 (by decide))
  have ha_ne2 : a ≠ endpoint 2 := by
    intro h
    have hlt := ha_lt 2 (by decide)
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  rcases halt with ⟨h012, h203⟩
  have h012_order :
      idx (endpoint 0) <= idx (endpoint 1) ∧
        idx (endpoint 1) <= idx (endpoint 2) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
  have h203_wrap :
      idx (endpoint 2) <= idx (endpoint 3) ∨
        idx (endpoint 3) <= idx (endpoint 0) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h20_not] using h203.1.2
  have h23 : idx (endpoint 2) <= idx (endpoint 3) := by
    rcases h203_wrap with h23 | h30
    · exact h23
    · have h0lt3 : idx (endpoint 0) < idx (endpoint 3) := by
        simpa [idx] using h0_lt 3 (by decide)
      omega
  by_cases h0a : idx (endpoint 0) <= idx a
  · left
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
          ha_mem h02 h0a ha_le2 ha_ne0 ha_ne2
    · exact h203
  · have ha0 : idx a <= idx (endpoint 0) := by omega
    right
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact h012
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          ha_mem h20_not (Or.inr ha0) ha_ne2 ha_ne0

theorem crossEndpointAlternating_replaceEndpoint1_or_3_of_endpoint2_before_path
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (ha_mem : a ∈ Ω.vertexSet)
    (ha_lt :
      forall i : Fin 4, i ≠ 2 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (h2_lt :
      forall i : Fin 4, i ≠ 2 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 2) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i))
    (ha_ne2 : a ≠ endpoint 2)
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 1 a) ∨
      CrossEndpointAlternating Ω (replaceEndpointAt endpoint 3 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h20 : idx (endpoint 2) <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (h2_lt 0 (by decide))
  have h02_not : ¬ idx (endpoint 0) <= idx (endpoint 2) := by
    have hlt : idx (endpoint 2) < idx (endpoint 0) := by
      simpa [idx] using h2_lt 0 (by decide)
    omega
  have ha_le0 : idx a <= idx (endpoint 0) := by
    simpa [idx] using Nat.le_of_lt (ha_lt 0 (by decide))
  have ha_ne0 : a ≠ endpoint 0 := by
    intro h
    have hlt := ha_lt 0 (by decide)
    rw [h] at hlt
    exact Nat.lt_irrefl _ hlt
  rcases halt with ⟨h012, h203⟩
  have h203_order :
      idx (endpoint 2) <= idx (endpoint 3) ∧
        idx (endpoint 3) <= idx (endpoint 0) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h20] using h203.1.2
  have h012_wrap :
      idx (endpoint 0) <= idx (endpoint 1) ∨
        idx (endpoint 1) <= idx (endpoint 2) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h02_not] using h012.1.2
  have h01 : idx (endpoint 0) <= idx (endpoint 1) := by
    rcases h012_wrap with h01 | h12
    · exact h01
    · have h2lt1 : idx (endpoint 2) < idx (endpoint 1) := by
        simpa [idx] using h2_lt 1 (by decide)
      omega
  by_cases h2a : idx (endpoint 2) <= idx a
  · right
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact h012
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
          ha_mem h20 h2a ha_le0 ha_ne2 ha_ne0
  · have ha2 : idx a <= idx (endpoint 2) := by omega
    left
    dsimp [CrossEndpointAlternating, replaceEndpointAt]
    constructor
    · exact
        CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
          ha_mem h02_not (Or.inr ha2) ha_ne0 ha_ne2
    · exact h203

theorem crossEndpointAlternating_replaceEndpoint0_of_after_other_endpoints
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (hbefore :
      forall i : Fin 4, i ≠ 0 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω a)
    (ha_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 0))
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 0 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  rcases halt with ⟨h012, h203⟩
  have h1_lt_a : idx (endpoint 1) < idx a := by
    simpa [idx] using hbefore 1 (by decide)
  have h2_lt_a : idx (endpoint 2) < idx a := by
    simpa [idx] using hbefore 2 (by decide)
  have h3_lt_a : idx (endpoint 3) < idx a := by
    simpa [idx] using hbefore 3 (by decide)
  have ha_le0 : idx a <= idx (endpoint 0) := by
    simpa [idx] using ha_le
  have h02_not : ¬ idx (endpoint 0) <= idx (endpoint 2) := by
    intro h02
    omega
  have h20 : idx (endpoint 2) <= idx (endpoint 0) := by omega
  have h012_wrap :
      idx (endpoint 0) <= idx (endpoint 1) ∨
        idx (endpoint 1) <= idx (endpoint 2) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h02_not] using h012.1.2
  have h12 : idx (endpoint 1) <= idx (endpoint 2) := by
    rcases h012_wrap with h01 | h12
    · omega
    · exact h12
  have h203_order :
      idx (endpoint 2) <= idx (endpoint 3) ∧
        idx (endpoint 3) <= idx (endpoint 0) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h20] using h203.1.2
  have ha2_not : ¬ idx a <= idx (endpoint 2) := by omega
  have h2_le_a : idx (endpoint 2) <= idx a := by omega
  have h3_le_a : idx (endpoint 3) <= idx a := by omega
  have h1_ne_a : endpoint 1 ≠ a := by
    intro h
    rw [h] at h1_lt_a
    exact Nat.lt_irrefl _ h1_lt_a
  have h3_ne_a : endpoint 3 ≠ a := by
    intro h
    rw [h] at h3_lt_a
    exact Nat.lt_irrefl _ h3_lt_a
  dsimp [CrossEndpointAlternating, replaceEndpointAt]
  exact ⟨
    CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
      h012.1.1 ha2_not (Or.inr h12) h1_ne_a h012.2.2,
    CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
      h203.1.1 h2_le_a h203_order.1 h3_le_a h203.2.1 h3_ne_a⟩

theorem crossEndpointAlternating_replaceEndpoint2_of_after_other_endpoints
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (hbefore :
      forall i : Fin 4, i ≠ 2 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω a)
    (ha_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 2))
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 2 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  rcases halt with ⟨h012, h203⟩
  have h0_lt_a : idx (endpoint 0) < idx a := by
    simpa [idx] using hbefore 0 (by decide)
  have h1_lt_a : idx (endpoint 1) < idx a := by
    simpa [idx] using hbefore 1 (by decide)
  have h3_lt_a : idx (endpoint 3) < idx a := by
    simpa [idx] using hbefore 3 (by decide)
  have ha_le2 : idx a <= idx (endpoint 2) := by
    simpa [idx] using ha_le
  have h02 : idx (endpoint 0) <= idx (endpoint 2) := by omega
  have h012_order :
      idx (endpoint 0) <= idx (endpoint 1) ∧
        idx (endpoint 1) <= idx (endpoint 2) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
  have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by
    intro h20
    omega
  have h203_wrap :
      idx (endpoint 2) <= idx (endpoint 3) ∨
        idx (endpoint 3) <= idx (endpoint 0) := by
    simpa [CyclicBoundary.ClockwiseBetween, idx, h20_not] using h203.1.2
  have h30 : idx (endpoint 3) <= idx (endpoint 0) := by
    rcases h203_wrap with h23 | h30
    · omega
    · exact h30
  have h0_le_a : idx (endpoint 0) <= idx a := by omega
  have h1_le_a : idx (endpoint 1) <= idx a := by omega
  have ha0_not : ¬ idx a <= idx (endpoint 0) := by omega
  have h1_ne_a : endpoint 1 ≠ a := by
    intro h
    rw [h] at h1_lt_a
    exact Nat.lt_irrefl _ h1_lt_a
  have h3_ne_a : endpoint 3 ≠ a := by
    intro h
    rw [h] at h3_lt_a
    exact Nat.lt_irrefl _ h3_lt_a
  dsimp [CrossEndpointAlternating, replaceEndpointAt]
  exact ⟨
    CyclicBoundary.clockwiseOpenBetween_of_index_between_classical Ω
      h012.1.1 h0_le_a h012_order.1 h1_le_a h012.2.1 h1_ne_a,
    CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
      h203.1.1 ha0_not (Or.inr h30) h3_ne_a h203.2.2⟩

theorem crossEndpointAlternating_replaceEndpoint1_of_after_other_endpoints
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (ha_mem : a ∈ Ω.vertexSet)
    (hbefore :
      forall i : Fin 4, i ≠ 1 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω a)
    (ha_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 1))
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 1 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  rcases halt with ⟨h012, h203⟩
  have h0_lt_a : idx (endpoint 0) < idx a := by
    simpa [idx] using hbefore 0 (by decide)
  have h2_lt_a : idx (endpoint 2) < idx a := by
    simpa [idx] using hbefore 2 (by decide)
  have h3_lt_a : idx (endpoint 3) < idx a := by
    simpa [idx] using hbefore 3 (by decide)
  have ha_le1 : idx a <= idx (endpoint 1) := by
    simpa [idx] using ha_le
  have h02_not : ¬ idx (endpoint 0) <= idx (endpoint 2) := by
    intro h02
    have h012_order :
        idx (endpoint 0) <= idx (endpoint 1) ∧
          idx (endpoint 1) <= idx (endpoint 2) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h02] using h012.1.2
    omega
  have h0_le_a : idx (endpoint 0) <= idx a := by omega
  have ha_ne0 : a ≠ endpoint 0 := by
    intro h
    rw [← h] at h0_lt_a
    exact Nat.lt_irrefl _ h0_lt_a
  have ha_ne2 : a ≠ endpoint 2 := by
    intro h
    rw [← h] at h2_lt_a
    exact Nat.lt_irrefl _ h2_lt_a
  dsimp [CrossEndpointAlternating, replaceEndpointAt]
  exact ⟨
    CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
      ha_mem h02_not (Or.inl h0_le_a) ha_ne0 ha_ne2,
    h203⟩

theorem crossEndpointAlternating_replaceEndpoint3_of_after_other_endpoints
    (Ω : CyclicBoundary V) {endpoint : Fin 4 -> V} {a : V}
    (ha_mem : a ∈ Ω.vertexSet)
    (hbefore :
      forall i : Fin 4, i ≠ 3 ->
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint i) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω a)
    (ha_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω a <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (endpoint 3))
    (halt : CrossEndpointAlternating Ω endpoint) :
    CrossEndpointAlternating Ω (replaceEndpointAt endpoint 3 a) := by
  classical
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  rcases halt with ⟨h012, h203⟩
  have h0_lt_a : idx (endpoint 0) < idx a := by
    simpa [idx] using hbefore 0 (by decide)
  have h1_lt_a : idx (endpoint 1) < idx a := by
    simpa [idx] using hbefore 1 (by decide)
  have h2_lt_a : idx (endpoint 2) < idx a := by
    simpa [idx] using hbefore 2 (by decide)
  have ha_le3 : idx a <= idx (endpoint 3) := by
    simpa [idx] using ha_le
  have h20_not : ¬ idx (endpoint 2) <= idx (endpoint 0) := by
    intro h20
    have h203_order :
        idx (endpoint 2) <= idx (endpoint 3) ∧
          idx (endpoint 3) <= idx (endpoint 0) := by
      simpa [CyclicBoundary.ClockwiseBetween, idx, h20] using h203.1.2
    omega
  have h2_le_a : idx (endpoint 2) <= idx a := by omega
  have ha_ne2 : a ≠ endpoint 2 := by
    intro h
    rw [← h] at h2_lt_a
    exact Nat.lt_irrefl _ h2_lt_a
  have ha_ne0 : a ≠ endpoint 0 := by
    intro h
    rw [← h] at h0_lt_a
    exact Nat.lt_irrefl _ h0_lt_a
  dsimp [CrossEndpointAlternating, replaceEndpointAt]
  exact ⟨
    h012,
    CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical Ω
      ha_mem h20_not (Or.inl h2_le_a) ha_ne2 ha_ne0⟩


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
