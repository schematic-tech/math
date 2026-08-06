import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
General finite societies for the literal Graph Minors IX (2.4) induction.

The existing `Schematic.Math.GraphTheory.Minors.Society.ThreeBoundary` file contains the
three-boundary
specialization needed by the dominating-four-colour/RST bridge. The proof of
GM IX (2.4) itself
does not stay in that specialization: after choosing the induced `s`--`t`
path `P`, the smaller societies have boundary `Ω(s,t) ∪ V(P)` and
`Ω(t,s) ∪ V(P)`.  This file records the general finite-boundary objects
needed for that source-proof route.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

/-- The ordered triple map on `Fin 3`.  This is deliberately local to the
general-society development; the older three-boundary specialization has its
own historical helper. -/
def fin3Order (i j k : Fin 3) : Fin 3 -> Fin 3
  | 0 => i
  | 1 => j
  | 2 => k

theorem fin3Order_injective
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    Function.Injective (fin3Order i j k) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [fin3Order] at hab ⊢
  · exact False.elim (hij hab)
  · exact False.elim (hik hab)
  · exact False.elim (hij hab.symm)
  · exact False.elim (hjk hab)
  · exact False.elim (hik hab.symm)
  · exact False.elim (hjk hab.symm)

theorem fin3_eq_of_pairwise
    {i j k m : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    m = i ∨ m = j ∨ m = k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;>
    simp at hij hik hjk ⊢

/-- A symmetric relation on `Fin 3` follows at every distinct pair from its
three increasing-index cases. -/
theorem fin3_of_pairwise_of_symmetric
    {p : Fin 3 -> Fin 3 -> Prop}
    (hsymm : forall {i j : Fin 3}, p i j -> p j i)
    (h01 : p 0 1)
    (h02 : p 0 2)
    (h12 : p 1 2)
    {i j : Fin 3}
    (hij : i ≠ j) :
    p i j := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact h01
  · exact h02
  · exact hsymm h01
  · exact False.elim (hij rfl)
  · exact h12
  · exact hsymm h02
  · exact hsymm h12
  · exact False.elim (hij rfl)

/-- Three pairwise-disjoint sets are disjoint at every pair of distinct
`Fin 3` indices. -/
theorem fin3_pairwise_disjoint
    {α : Type u} {s : Fin 3 -> Set α}
    (h01 : Disjoint (s 0) (s 1))
    (h02 : Disjoint (s 0) (s 2))
    (h12 : Disjoint (s 1) (s 2))
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (s i) (s j) :=
  fin3_of_pairwise_of_symmetric
    (p := fun i j => Disjoint (s i) (s j))
    (fun h => h.symm) h01 h02 h12 hij

/-- Filtering a nodup list preserves the relative `idxOf` order of retained
elements.  The GM IX `(2.4)` split boundaries are built by filtering the
original society boundary down to one clockwise arc. -/
theorem list_idxOf_filter_le_iff_of_mem
    {α : Type u} [DecidableEq α]
    {l : List α} (hnd : l.Nodup)
    {p : α -> Bool} {x y : α}
    (hx : x ∈ l.filter p) (hy : y ∈ l.filter p) :
    (l.filter p).idxOf x <= (l.filter p).idxOf y ↔
      l.idxOf x <= l.idxOf y := by
  induction l with
  | nil =>
      simp at hx
  | cons a tl ih =>
      have hnd_tail : tl.Nodup := hnd.tail
      have ha_not_tail : a ∉ tl := hnd.notMem
      by_cases hpa : p a = true
      · by_cases hxa : x = a
        · subst x
          simp [hpa]
        · by_cases hya : y = a
          · subst y
            have hax : a ≠ x := fun h => hxa h.symm
            simp [hpa, hax]
          · have hx_tail : x ∈ tl.filter p := by
              simpa [hpa, hxa] using hx
            have hy_tail : y ∈ tl.filter p := by
              simpa [hpa, hya] using hy
            have hax : a ≠ x := fun h => hxa h.symm
            have hay : a ≠ y := fun h => hya h.symm
            simpa [hpa, hax, hay] using ih hnd_tail hx_tail hy_tail
      · have hx_tail : x ∈ tl.filter p := by
          simpa [hpa] using hx
        have hy_tail : y ∈ tl.filter p := by
          simpa [hpa] using hy
        have hax : a ≠ x := by
          intro h
          exact ha_not_tail (by
            rw [h]
            exact List.mem_of_mem_filter hx_tail)
        have hay : a ≠ y := by
          intro h
          exact ha_not_tail (by
            rw [h]
            exact List.mem_of_mem_filter hy_tail)
        simpa [hpa, hax, hay] using ih hnd_tail hx_tail hy_tail

/-- A strict-order version of `list_idxOf_filter_le_iff_of_mem`. -/
theorem list_idxOf_filter_lt_iff_of_mem
    {α : Type u} [DecidableEq α]
    {l : List α} (hnd : l.Nodup)
    {p : α -> Bool} {x y : α}
    (hx : x ∈ l.filter p) (hy : y ∈ l.filter p) :
    (l.filter p).idxOf x < (l.filter p).idxOf y ↔
      l.idxOf x < l.idxOf y := by
  constructor
  · intro hlt
    have hle :=
      (list_idxOf_filter_le_iff_of_mem hnd hx hy).mp
        (Nat.le_of_lt hlt)
    have hne : l.idxOf x ≠ l.idxOf y := by
      intro hidx
      have hxy : x = y := (List.idxOf_inj (List.mem_of_mem_filter hx)).mp hidx
      subst y
      exact Nat.lt_irrefl _ hlt
    omega
  · intro hlt
    have hle :=
      (list_idxOf_filter_le_iff_of_mem hnd hx hy).mpr
        (Nat.le_of_lt hlt)
    have hne : (l.filter p).idxOf x ≠ (l.filter p).idxOf y := by
      intro hidx
      have hxy : x = y := (List.idxOf_inj hx).mp hidx
      subst y
      exact Nat.lt_irrefl _ hlt
    omega

theorem list_idxOf_take_eq_of_idx_lt
    {α : Type u} [DecidableEq α]
    {l : List α} {x : α} {n : Nat}
    (hx : x ∈ l) (hidx : l.idxOf x < n) :
    (l.take n).idxOf x = l.idxOf x := by
  have hx_take : x ∈ l.take n :=
    (List.mem_take_iff_idxOf_lt hx).mpr hidx
  have hidx_append :
      (l.take n ++ l.drop n).idxOf x = (l.take n).idxOf x :=
    List.idxOf_append_of_mem hx_take
  simpa [List.take_append_drop] using hidx_append.symm

theorem list_idxOf_drop_eq_sub_of_idx_le
    {α : Type u} [DecidableEq α]
    {l : List α} {x : α} {n : Nat}
    (hx : x ∈ l) (hidx : n <= l.idxOf x) :
    (l.drop n).idxOf x = l.idxOf x - n := by
  have hnot_take : x ∉ l.take n := by
    intro hx_take
    have hxlt := (List.mem_take_iff_idxOf_lt hx).mp hx_take
    omega
  have hidx_append :
      (l.take n ++ l.drop n).idxOf x =
        (l.take n).length + (l.drop n).idxOf x :=
    List.idxOf_append_of_notMem hnot_take
  have hn_len : n <= l.length := by
    have hx_len : l.idxOf x < l.length := by
      rwa [List.idxOf_lt_length_iff]
    omega
  have htake_len : (l.take n).length = n := by
    simp [List.length_take, Nat.min_eq_left hn_len]
  have hmain : l.idxOf x = n + (l.drop n).idxOf x := by
    simpa [List.take_append_drop, htake_len] using hidx_append
  omega

theorem list_idxOf_rotate_eq_of_mem
    {α : Type u} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {x : α} {n : Nat}
    (hn : n <= l.length) (hx : x ∈ l) :
    (l.rotate n).idxOf x =
      if l.idxOf x < n then l.length - n + l.idxOf x else l.idxOf x - n := by
  rw [List.rotate_eq_drop_append_take hn]
  by_cases hidx : l.idxOf x < n
  · have hx_take : x ∈ l.take n :=
      (List.mem_take_iff_idxOf_lt hx).mpr hidx
    have hnot_drop : x ∉ l.drop n := by
      intro hx_drop
      exact (List.disjoint_take_drop hnd (le_refl n)) hx_take hx_drop
    have hidx_append :
        (l.drop n ++ l.take n).idxOf x =
          (l.drop n).length + (l.take n).idxOf x :=
      List.idxOf_append_of_notMem hnot_drop
    have hdrop_len : (l.drop n).length = l.length - n := by
      simp [List.length_drop]
    have htake_idx :=
      list_idxOf_take_eq_of_idx_lt (l := l) (x := x) (n := n) hx hidx
    simp [hidx, hidx_append, hdrop_len, htake_idx]
  · have hnidx : n <= l.idxOf x := by omega
    have hnot_take : x ∉ l.take n := by
      intro hx_take
      exact hidx ((List.mem_take_iff_idxOf_lt hx).mp hx_take)
    have hidx_append :
        (l.drop n ++ l.take n).idxOf x = (l.drop n).idxOf x := by
      have hx_append : x ∈ l.take n ++ l.drop n := by
        simpa [List.take_append_drop] using hx
      have hx_drop : x ∈ l.drop n := by
        rcases List.mem_append.mp hx_append with hx_take | hx_drop
        · exact False.elim (hnot_take hx_take)
        · exact hx_drop
      exact List.idxOf_append_of_mem hx_drop
    have hdrop_idx :=
      list_idxOf_drop_eq_sub_of_idx_le (l := l) (x := x) (n := n) hx hnidx
    simp [hidx, hidx_append, hdrop_idx]

theorem cyclic_between_of_rotated_indices_aux
    {L n m ix iy iz : Nat}
    (hm : m + n = L) (hix : ix < L) (hiy : iy < L) (hiz : iz < L)
    (hrot :
      (if (if ix < n then m + ix else ix - n) <=
            (if iy < n then m + iy else iy - n) then
        (if ix < n then m + ix else ix - n) <=
            (if iz < n then m + iz else iz - n) ∧
          (if iz < n then m + iz else iz - n) <=
            (if iy < n then m + iy else iy - n)
      else
        (if ix < n then m + ix else ix - n) <=
            (if iz < n then m + iz else iz - n) ∨
          (if iz < n then m + iz else iz - n) <=
            (if iy < n then m + iy else iy - n))) :
    (if ix <= iy then ix <= iz ∧ iz <= iy else ix <= iz ∨ iz <= iy) := by
  by_cases hx : ix < n <;> by_cases hy : iy < n <;>
    by_cases hz : iz < n <;>
      (simp [hx, hy, hz] at hrot ⊢
       split at hrot <;> split <;> omega)

theorem cyclic_open_between_rotate_after_start_iff_aux
    {L n m is it iv : Nat}
    (hn : n = is + 1) (hm : m + n = L)
    (hit : it < L) (hiv : iv < L)
    (hst : is ≠ it) :
    ((if is <= it then is <= iv ∧ iv <= it else is <= iv ∨ iv <= it) ∧
        iv ≠ is ∧ iv ≠ it) ↔
      (if iv < n then m + iv else iv - n) <
        (if it < n then m + it else it - n) := by
  subst n
  by_cases ht : it < is + 1 <;> by_cases hv : iv < is + 1 <;>
    by_cases hst_le : is <= it <;>
      simp [ht, hv, hst_le] <;> omega

theorem list_reverse_idxOf_add_idxOf_add_one
    {α : Type u} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {x : α} (hx : x ∈ l) :
    l.reverse.idxOf x + l.idxOf x + 1 = l.length := by
  induction l with
  | nil =>
      simp at hx
  | cons a tl ih =>
      have hnd_tail : tl.Nodup := hnd.tail
      by_cases hxa : x = a
      · subst x
        have ha_not_rev : a ∉ tl.reverse := by
          intro ha
          exact hnd.notMem (List.mem_reverse.mp ha)
        have hidx_rev :
            (tl.reverse ++ [a]).idxOf a = tl.reverse.length := by
          rw [List.idxOf_append_of_notMem ha_not_rev]
          simp
        simp [hidx_rev]
      · have hx_tail : x ∈ tl := by
          simpa [hxa] using hx
        have hx_rev : x ∈ tl.reverse := List.mem_reverse.mpr hx_tail
        have hidx_rev :
            (tl.reverse ++ [a]).idxOf x = tl.reverse.idxOf x :=
          List.idxOf_append_of_mem hx_rev
        have hih :
            tl.reverse.idxOf x + tl.idxOf x + 1 = tl.length :=
          ih hnd_tail hx_tail
        have hax : a ≠ x := fun h => hxa h.symm
        simp [hax, hidx_rev]
        omega

theorem list_reverse_idxOf_le_iff
    {α : Type u} [DecidableEq α]
    {l : List α} (hnd : l.Nodup) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) :
    l.reverse.idxOf x <= l.reverse.idxOf y ↔
      l.idxOf y <= l.idxOf x := by
  have hxidx := list_reverse_idxOf_add_idxOf_add_one hnd hx
  have hyidx := list_reverse_idxOf_add_idxOf_add_one hnd hy
  constructor <;> intro h <;> omega


end Schematic.Math.GraphTheory
