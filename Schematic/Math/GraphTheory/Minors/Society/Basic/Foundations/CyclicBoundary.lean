import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.ListOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

/-- A finite boundary order for a society, represented by a cyclic list.

The list representation is deliberately concrete: GM IX (2.4) cuts the cycle
at two boundary vertices and then appends a path in one of two directions. -/
structure CyclicBoundary (V : Type u) where
  vertices : List V
  nodup : vertices.Nodup

namespace CyclicBoundary

@[ext]
theorem ext {Ω Ω' : CyclicBoundary V} (hvertices : Ω.vertices = Ω'.vertices) :
    Ω = Ω' := by
  cases Ω
  cases Ω'
  simp at hvertices ⊢
  exact hvertices

def length (Ω : CyclicBoundary V) : Nat :=
  Ω.vertices.length

def vertexSet (Ω : CyclicBoundary V) : Set V :=
  {v | v ∈ Ω.vertices}

theorem mem_vertexSet_iff {Ω : CyclicBoundary V} {v : V} :
    v ∈ Ω.vertexSet ↔ v ∈ Ω.vertices :=
  Iff.rfl

theorem finite_vertexSet (Ω : CyclicBoundary V) :
    Ω.vertexSet.Finite := by
  classical
  simp [vertexSet]

theorem ncard_vertexSet_eq_length (Ω : CyclicBoundary V) :
    Ω.vertexSet.ncard = Ω.vertices.length := by
  classical
  have hset : Ω.vertexSet = (Ω.vertices.toFinset : Set V) := by
    ext v
    simp [vertexSet]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup Ω.nodup]

theorem ncard_vertexSet_eq_length' (Ω : CyclicBoundary V) :
    Ω.vertexSet.ncard = Ω.length := by
  simpa [length] using Ω.ncard_vertexSet_eq_length

theorem mem_vertices_of_mem_vertexSet {Ω : CyclicBoundary V} {v : V}
    (hv : v ∈ Ω.vertexSet) :
    v ∈ Ω.vertices :=
  hv

theorem mem_vertexSet_of_mem_vertices {Ω : CyclicBoundary V} {v : V}
    (hv : v ∈ Ω.vertices) :
    v ∈ Ω.vertexSet :=
  hv

/-- The position of a vertex in the chosen cyclic list.  For vertices outside
the boundary this is `length`, so interval predicates below always carry a
membership conjunct. -/
def indexOf [DecidableEq V] (Ω : CyclicBoundary V) (v : V) : Nat :=
  Ω.vertices.idxOf v

theorem list_idxOf_eq_classical [DecidableEq V] (l : List V) (v : V) :
    @List.idxOf V (@instBEqOfDecidableEq V ‹DecidableEq V›) v l =
      @List.idxOf V (@instBEqOfDecidableEq V (Classical.decEq V)) v l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : x = v
      · simp [hx]
      · simp [List.idxOf_cons_ne, hx, ih]

/-- Inclusive clockwise interval from `s` to `t` in the list model of a
cyclic boundary. -/
def ClockwiseBetween [DecidableEq V] (Ω : CyclicBoundary V) (s t v : V) :
    Prop :=
  v ∈ Ω.vertexSet ∧
    if Ω.indexOf s <= Ω.indexOf t then
      Ω.indexOf s <= Ω.indexOf v ∧ Ω.indexOf v <= Ω.indexOf t
    else
      Ω.indexOf s <= Ω.indexOf v ∨ Ω.indexOf v <= Ω.indexOf t

/-- Open clockwise interval from `s` to `t`, excluding the two endpoints. -/
def ClockwiseOpenBetween [DecidableEq V] (Ω : CyclicBoundary V) (s t v : V) :
    Prop :=
  Ω.ClockwiseBetween s t v ∧ v ≠ s ∧ v ≠ t

def clockwiseArcSet [DecidableEq V] (Ω : CyclicBoundary V) (s t : V) :
    Set V :=
  {v | Ω.ClockwiseOpenBetween s t v}

theorem clockwiseOpenBetween_of_rotate [DecidableEq V]
    (Ω : CyclicBoundary V) {n : Nat} (hn : n <= Ω.vertices.length)
    {x y z : V}
    (hx : x ∈ Ω.vertexSet) (hy : y ∈ Ω.vertexSet) (hz : z ∈ Ω.vertexSet)
    (hclock :
      ({ vertices := Ω.vertices.rotate n,
          nodup := (List.nodup_rotate.mpr Ω.nodup) } :
        CyclicBoundary V).ClockwiseOpenBetween x y z) :
    Ω.ClockwiseOpenBetween x y z := by
  classical
  let Ωr : CyclicBoundary V :=
    { vertices := Ω.vertices.rotate n,
      nodup := (List.nodup_rotate.mpr Ω.nodup) }
  let m := Ω.vertices.length - n
  have hm : m + n = Ω.vertices.length := by
    dsimp [m]
    omega
  have hix : Ω.indexOf x < Ω.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr hx)
  have hiy : Ω.indexOf y < Ω.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr hy)
  have hiz : Ω.indexOf z < Ω.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr hz)
  have hidx_x :
      Ωr.indexOf x =
        if Ω.indexOf x < n then m + Ω.indexOf x else Ω.indexOf x - n := by
    dsimp [Ωr, m, CyclicBoundary.indexOf]
    simpa [CyclicBoundary.indexOf] using
      list_idxOf_rotate_eq_of_mem Ω.nodup hn hx
  have hidx_y :
      Ωr.indexOf y =
        if Ω.indexOf y < n then m + Ω.indexOf y else Ω.indexOf y - n := by
    dsimp [Ωr, m, CyclicBoundary.indexOf]
    simpa [CyclicBoundary.indexOf] using
      list_idxOf_rotate_eq_of_mem Ω.nodup hn hy
  have hidx_z :
      Ωr.indexOf z =
        if Ω.indexOf z < n then m + Ω.indexOf z else Ω.indexOf z - n := by
    dsimp [Ωr, m, CyclicBoundary.indexOf]
    simpa [CyclicBoundary.indexOf] using
      list_idxOf_rotate_eq_of_mem Ω.nodup hn hz
  rcases hclock with ⟨hbetween, hzx, hzy⟩
  rcases hbetween with ⟨_hzmem, horder⟩
  refine ⟨⟨hz, ?_⟩, hzx, hzy⟩
  have hrot :
      (if (if Ω.indexOf x < n then m + Ω.indexOf x else Ω.indexOf x - n) <=
            (if Ω.indexOf y < n then m + Ω.indexOf y else Ω.indexOf y - n) then
        (if Ω.indexOf x < n then m + Ω.indexOf x else Ω.indexOf x - n) <=
            (if Ω.indexOf z < n then m + Ω.indexOf z else Ω.indexOf z - n) ∧
          (if Ω.indexOf z < n then m + Ω.indexOf z else Ω.indexOf z - n) <=
            (if Ω.indexOf y < n then m + Ω.indexOf y else Ω.indexOf y - n)
      else
        (if Ω.indexOf x < n then m + Ω.indexOf x else Ω.indexOf x - n) <=
            (if Ω.indexOf z < n then m + Ω.indexOf z else Ω.indexOf z - n) ∨
          (if Ω.indexOf z < n then m + Ω.indexOf z else Ω.indexOf z - n) <=
            (if Ω.indexOf y < n then m + Ω.indexOf y else Ω.indexOf y - n)) := by
    simpa [Ωr, CyclicBoundary.ClockwiseBetween, hidx_x, hidx_y, hidx_z]
      using horder
  simpa [CyclicBoundary.ClockwiseBetween] using
    cyclic_between_of_rotated_indices_aux
      (L := Ω.vertices.length) (n := n) (m := m)
      (ix := Ω.indexOf x) (iy := Ω.indexOf y) (iz := Ω.indexOf z)
      hm hix hiy hiz hrot

theorem clockwiseOpenBetween_rotate_after_start_iff_index_lt
    [DecidableEq V] (Ω : CyclicBoundary V) {s t v : V}
    (hs : s ∈ Ω.vertexSet) (ht : t ∈ Ω.vertexSet) (hst : s ≠ t)
    (hv : v ∈ Ω.vertexSet) :
    let n := Ω.indexOf s + 1
    let Ωr : CyclicBoundary V :=
      { vertices := Ω.vertices.rotate n,
        nodup := (List.nodup_rotate.mpr Ω.nodup) }
    Ω.ClockwiseOpenBetween s t v ↔ Ωr.indexOf v < Ωr.indexOf t := by
  classical
  intro n Ωr
  have hn_le : n <= Ω.vertices.length := by
    have hs_idx : Ω.indexOf s < Ω.vertices.length := by
      simpa [CyclicBoundary.indexOf] using
        (List.idxOf_lt_length_iff.mpr hs)
    dsimp [n]
    omega
  let m := Ω.vertices.length - n
  have hm : m + n = Ω.vertices.length := by
    dsimp [m]
    omega
  have hidx_v :
      Ωr.indexOf v =
        if Ω.indexOf v < n then m + Ω.indexOf v else Ω.indexOf v - n := by
    dsimp [Ωr, m, CyclicBoundary.indexOf]
    simpa [CyclicBoundary.indexOf] using
      list_idxOf_rotate_eq_of_mem Ω.nodup hn_le hv
  have hidx_t :
      Ωr.indexOf t =
        if Ω.indexOf t < n then m + Ω.indexOf t else Ω.indexOf t - n := by
    dsimp [Ωr, m, CyclicBoundary.indexOf]
    simpa [CyclicBoundary.indexOf] using
      list_idxOf_rotate_eq_of_mem Ω.nodup hn_le ht
  have hs_ne_t_idx : Ω.indexOf s ≠ Ω.indexOf t := by
    intro hidx
    exact hst ((List.idxOf_inj hs).mp (by
      simpa [CyclicBoundary.indexOf] using hidx))
  have hiff :=
    cyclic_open_between_rotate_after_start_iff_aux
      (L := Ω.vertices.length) (n := n) (m := m)
      (is := Ω.indexOf s) (it := Ω.indexOf t) (iv := Ω.indexOf v)
      (by dsimp [n]) hm
      (by
        simpa [CyclicBoundary.indexOf] using
          (List.idxOf_lt_length_iff.mpr ht))
      (by
        simpa [CyclicBoundary.indexOf] using
          (List.idxOf_lt_length_iff.mpr hv))
      hs_ne_t_idx
  constructor
  · intro hclock
    rcases hclock with ⟨hbetween, hvs, hvt⟩
    rcases hbetween with ⟨_hv, horder⟩
    have hraw :
        ((if Ω.indexOf s <= Ω.indexOf t then
            Ω.indexOf s <= Ω.indexOf v ∧ Ω.indexOf v <= Ω.indexOf t
          else
            Ω.indexOf s <= Ω.indexOf v ∨ Ω.indexOf v <= Ω.indexOf t) ∧
          Ω.indexOf v ≠ Ω.indexOf s ∧
            Ω.indexOf v ≠ Ω.indexOf t) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [CyclicBoundary.ClockwiseBetween] using horder
      · intro hidx
        exact hvs ((List.idxOf_inj hv).mp (by
          simpa [CyclicBoundary.indexOf] using hidx))
      · intro hidx
        exact hvt ((List.idxOf_inj hv).mp (by
          simpa [CyclicBoundary.indexOf] using hidx))
    simpa [hidx_v, hidx_t] using hiff.mp hraw
  · intro hlt
    have hraw :
        ((if Ω.indexOf s <= Ω.indexOf t then
            Ω.indexOf s <= Ω.indexOf v ∧ Ω.indexOf v <= Ω.indexOf t
          else
            Ω.indexOf s <= Ω.indexOf v ∨ Ω.indexOf v <= Ω.indexOf t) ∧
          Ω.indexOf v ≠ Ω.indexOf s ∧
            Ω.indexOf v ≠ Ω.indexOf t) := by
      exact hiff.mpr (by simpa [hidx_v, hidx_t] using hlt)
    refine ⟨⟨hv, ?_⟩, ?_, ?_⟩
    · simpa [CyclicBoundary.ClockwiseBetween] using hraw.1
    · intro hvs
      exact hraw.2.1 (by
        subst v
        rfl)
    · intro hvt
      exact hraw.2.2 (by
        subst v
        rfl)

theorem clockwiseOpenBetween_append_tail_iff [DecidableEq V]
    {pref tail : List V}
    (hpref : pref.Nodup)
    (happend : (pref ++ tail).Nodup)
    {x y z : V}
    (hx : x ∈ pref) (hy : y ∈ pref) (hz : z ∈ pref) :
    ({ vertices := pref ++ tail, nodup := happend } :
        CyclicBoundary V).ClockwiseOpenBetween x y z ↔
      ({ vertices := pref, nodup := hpref } :
        CyclicBoundary V).ClockwiseOpenBetween x y z := by
  classical
  let Ωfull : CyclicBoundary V := { vertices := pref ++ tail, nodup := happend }
  let Ωprefix : CyclicBoundary V := { vertices := pref, nodup := hpref }
  have hidx_x : Ωfull.indexOf x = Ωprefix.indexOf x := by
    simp [Ωfull, Ωprefix, CyclicBoundary.indexOf,
      List.idxOf_append_of_mem hx]
  have hidx_y : Ωfull.indexOf y = Ωprefix.indexOf y := by
    simp [Ωfull, Ωprefix, CyclicBoundary.indexOf,
      List.idxOf_append_of_mem hy]
  have hidx_z : Ωfull.indexOf z = Ωprefix.indexOf z := by
    simp [Ωfull, Ωprefix, CyclicBoundary.indexOf,
      List.idxOf_append_of_mem hz]
  constructor
  · intro hclock
    rcases hclock with ⟨hbetween, hzx, hzy⟩
    rcases hbetween with ⟨_hzmem, horder⟩
    refine ⟨⟨hz, ?_⟩, hzx, hzy⟩
    simpa [Ωfull, Ωprefix, CyclicBoundary.ClockwiseBetween,
      hidx_x, hidx_y, hidx_z] using horder
  · intro hclock
    rcases hclock with ⟨hbetween, hzx, hzy⟩
    rcases hbetween with ⟨_hzmem, horder⟩
    refine ⟨⟨by exact List.mem_append_left tail hz, ?_⟩,
      hzx, hzy⟩
    simpa [Ωfull, Ωprefix, CyclicBoundary.ClockwiseBetween,
      hidx_x, hidx_y, hidx_z] using horder

theorem clockwiseOpenBetween_filter_iff [DecidableEq V]
    (Ω : CyclicBoundary V) {p : V -> Bool}
    {x y z : V}
    (hx : x ∈ Ω.vertices.filter p)
    (hy : y ∈ Ω.vertices.filter p)
    (hz : z ∈ Ω.vertices.filter p) :
    ({ vertices := Ω.vertices.filter p,
        nodup := Ω.nodup.filter p } :
      CyclicBoundary V).ClockwiseOpenBetween x y z ↔
      Ω.ClockwiseOpenBetween x y z := by
  classical
  let Ωf : CyclicBoundary V :=
    { vertices := Ω.vertices.filter p, nodup := Ω.nodup.filter p }
  have hidx_x : Ωf.indexOf x = (Ω.vertices.filter p).idxOf x := rfl
  have hidx_y : Ωf.indexOf y = (Ω.vertices.filter p).idxOf y := rfl
  have hidx_z : Ωf.indexOf z = (Ω.vertices.filter p).idxOf z := rfl
  have hle_xy :
      Ωf.indexOf x <= Ωf.indexOf y ↔ Ω.indexOf x <= Ω.indexOf y := by
    rw [hidx_x, hidx_y]
    simpa [CyclicBoundary.indexOf] using
      (list_idxOf_filter_le_iff_of_mem Ω.nodup hx hy)
  have hle_xz :
      Ωf.indexOf x <= Ωf.indexOf z ↔ Ω.indexOf x <= Ω.indexOf z := by
    rw [hidx_x, hidx_z]
    simpa [CyclicBoundary.indexOf] using
      (list_idxOf_filter_le_iff_of_mem Ω.nodup hx hz)
  have hle_zy :
      Ωf.indexOf z <= Ωf.indexOf y ↔ Ω.indexOf z <= Ω.indexOf y := by
    rw [hidx_z, hidx_y]
    simpa [CyclicBoundary.indexOf] using
      (list_idxOf_filter_le_iff_of_mem Ω.nodup hz hy)
  constructor
  · intro hclock
    rcases hclock with ⟨hbetween, hzx, hzy⟩
    rcases hbetween with ⟨_hzmem, horder⟩
    refine ⟨⟨List.mem_of_mem_filter hz, ?_⟩, hzx, hzy⟩
    by_cases hf_xy : Ωf.indexOf x <= Ωf.indexOf y
    · have hΩ_xy : Ω.indexOf x <= Ω.indexOf y := hle_xy.mp hf_xy
      have hside :
          Ωf.indexOf x <= Ωf.indexOf z ∧
            Ωf.indexOf z <= Ωf.indexOf y := by
        simpa [Ωf, CyclicBoundary.ClockwiseBetween, hf_xy] using horder
      have hΩ :
          Ω.indexOf x <= Ω.indexOf z ∧ Ω.indexOf z <= Ω.indexOf y :=
        ⟨hle_xz.mp hside.1, hle_zy.mp hside.2⟩
      simpa [CyclicBoundary.ClockwiseBetween, hΩ_xy] using hΩ
    · have hΩ_not_xy : ¬ Ω.indexOf x <= Ω.indexOf y := by
        intro hΩ_xy
        exact hf_xy (hle_xy.mpr hΩ_xy)
      have hside :
          Ωf.indexOf x <= Ωf.indexOf z ∨
            Ωf.indexOf z <= Ωf.indexOf y := by
        simpa [Ωf, CyclicBoundary.ClockwiseBetween, hf_xy] using horder
      have hΩ :
          Ω.indexOf x <= Ω.indexOf z ∨ Ω.indexOf z <= Ω.indexOf y :=
        hside.elim
          (fun h => Or.inl (hle_xz.mp h))
          (fun h => Or.inr (hle_zy.mp h))
      simpa [CyclicBoundary.ClockwiseBetween, hΩ_not_xy] using hΩ
  · intro hclock
    rcases hclock with ⟨hbetween, hzx, hzy⟩
    rcases hbetween with ⟨_hzmem, horder⟩
    refine ⟨⟨hz, ?_⟩, hzx, hzy⟩
    by_cases hΩ_xy : Ω.indexOf x <= Ω.indexOf y
    · have hf_xy : Ωf.indexOf x <= Ωf.indexOf y := hle_xy.mpr hΩ_xy
      have hΩ :
          Ω.indexOf x <= Ω.indexOf z ∧ Ω.indexOf z <= Ω.indexOf y := by
        simpa [CyclicBoundary.ClockwiseBetween, hΩ_xy] using horder
      have hf :
          Ωf.indexOf x <= Ωf.indexOf z ∧
            Ωf.indexOf z <= Ωf.indexOf y :=
        ⟨hle_xz.mpr hΩ.1, hle_zy.mpr hΩ.2⟩
      simpa [Ωf, CyclicBoundary.ClockwiseBetween, hf_xy] using hf
    · have hf_not_xy : ¬ Ωf.indexOf x <= Ωf.indexOf y := by
        intro hf_xy
        exact hΩ_xy (hle_xy.mp hf_xy)
      have hΩ :
          Ω.indexOf x <= Ω.indexOf z ∨ Ω.indexOf z <= Ω.indexOf y := by
        simpa [CyclicBoundary.ClockwiseBetween, hΩ_xy] using horder
      have hf :
          Ωf.indexOf x <= Ωf.indexOf z ∨
            Ωf.indexOf z <= Ωf.indexOf y :=
        hΩ.elim
          (fun h => Or.inl (hle_xz.mpr h))
          (fun h => Or.inr (hle_zy.mpr h))
      simpa [Ωf, CyclicBoundary.ClockwiseBetween, hf_not_xy] using hf

theorem clockwiseOpenBetween_of_filter_append [DecidableEq V]
    (Ω : CyclicBoundary V) {p : V -> Bool} {tail : List V}
    {hnd : (Ω.vertices.filter p ++ tail).Nodup}
    {x y z : V}
    (hx : x ∈ Ω.vertices.filter p)
    (hy : y ∈ Ω.vertices.filter p)
    (hz : z ∈ Ω.vertices.filter p)
    (hclock :
      ({ vertices := Ω.vertices.filter p ++ tail, nodup := hnd } :
        CyclicBoundary V).ClockwiseOpenBetween x y z) :
    Ω.ClockwiseOpenBetween x y z := by
  classical
  let Ω' : CyclicBoundary V :=
    { vertices := Ω.vertices.filter p ++ tail, nodup := hnd }
  have hidx_x : Ω'.indexOf x = (Ω.vertices.filter p).idxOf x := by
    simp [Ω', CyclicBoundary.indexOf, List.idxOf_append_of_mem hx]
  have hidx_y : Ω'.indexOf y = (Ω.vertices.filter p).idxOf y := by
    simp [Ω', CyclicBoundary.indexOf, List.idxOf_append_of_mem hy]
  have hidx_z : Ω'.indexOf z = (Ω.vertices.filter p).idxOf z := by
    simp [Ω', CyclicBoundary.indexOf, List.idxOf_append_of_mem hz]
  have hle_xy :
      Ω'.indexOf x <= Ω'.indexOf y ↔ Ω.indexOf x <= Ω.indexOf y := by
    rw [hidx_x, hidx_y]
    simpa [CyclicBoundary.indexOf] using
      (list_idxOf_filter_le_iff_of_mem Ω.nodup hx hy)
  have hle_xz :
      Ω'.indexOf x <= Ω'.indexOf z ↔ Ω.indexOf x <= Ω.indexOf z := by
    rw [hidx_x, hidx_z]
    simpa [CyclicBoundary.indexOf] using
      (list_idxOf_filter_le_iff_of_mem Ω.nodup hx hz)
  have hle_zy :
      Ω'.indexOf z <= Ω'.indexOf y ↔ Ω.indexOf z <= Ω.indexOf y := by
    rw [hidx_z, hidx_y]
    simpa [CyclicBoundary.indexOf] using
      (list_idxOf_filter_le_iff_of_mem Ω.nodup hz hy)
  rcases hclock with ⟨hbetween, hzx, hzy⟩
  rcases hbetween with ⟨_hzmem, horder⟩
  refine ⟨⟨List.mem_of_mem_filter hz, ?_⟩, hzx, hzy⟩
  by_cases hside_xy : Ω'.indexOf x <= Ω'.indexOf y
  · have horig_xy : Ω.indexOf x <= Ω.indexOf y := hle_xy.mp hside_xy
    have hside_order :
        Ω'.indexOf x <= Ω'.indexOf z ∧ Ω'.indexOf z <= Ω'.indexOf y := by
      simpa [Ω', CyclicBoundary.ClockwiseBetween, hside_xy] using horder
    have horig_order :
        Ω.indexOf x <= Ω.indexOf z ∧ Ω.indexOf z <= Ω.indexOf y :=
      ⟨hle_xz.mp hside_order.1, hle_zy.mp hside_order.2⟩
    simpa [CyclicBoundary.ClockwiseBetween, horig_xy] using horig_order
  · have horig_not_xy : ¬ Ω.indexOf x <= Ω.indexOf y := by
      intro horig_xy
      exact hside_xy (hle_xy.mpr horig_xy)
    have hside_order :
        Ω'.indexOf x <= Ω'.indexOf z ∨ Ω'.indexOf z <= Ω'.indexOf y := by
      simpa [Ω', CyclicBoundary.ClockwiseBetween, hside_xy] using horder
    have horig_order :
        Ω.indexOf x <= Ω.indexOf z ∨ Ω.indexOf z <= Ω.indexOf y :=
      hside_order.elim
        (fun h => Or.inl (hle_xz.mp h))
        (fun h => Or.inr (hle_zy.mp h))
    simpa [CyclicBoundary.ClockwiseBetween, horig_not_xy] using horig_order

theorem clockwiseArcSet_subset [DecidableEq V] (Ω : CyclicBoundary V)
    (s t : V) :
    Ω.clockwiseArcSet s t ⊆ Ω.vertexSet := by
  intro v hv
  exact hv.1.1

theorem clockwiseBetween_left_mem [DecidableEq V] {Ω : CyclicBoundary V}
    {s t : V} (hs : s ∈ Ω.vertexSet) :
    Ω.ClockwiseBetween s t s := by
  classical
  constructor
  · exact hs
  · by_cases hst : Ω.indexOf s <= Ω.indexOf t
    · change
        if Ω.indexOf s <= Ω.indexOf t then
          Ω.indexOf s <= Ω.indexOf s ∧ Ω.indexOf s <= Ω.indexOf t
        else
          Ω.indexOf s <= Ω.indexOf s ∨ Ω.indexOf s <= Ω.indexOf t
      simp [hst]
    · change
        if Ω.indexOf s <= Ω.indexOf t then
          Ω.indexOf s <= Ω.indexOf s ∧ Ω.indexOf s <= Ω.indexOf t
        else
          Ω.indexOf s <= Ω.indexOf s ∨ Ω.indexOf s <= Ω.indexOf t
      simp [hst]

theorem clockwiseBetween_right_mem [DecidableEq V] {Ω : CyclicBoundary V}
    {s t : V} (ht : t ∈ Ω.vertexSet) :
    Ω.ClockwiseBetween s t t := by
  classical
  constructor
  · exact ht
  · by_cases hst : Ω.indexOf s <= Ω.indexOf t
    · change
        if Ω.indexOf s <= Ω.indexOf t then
          Ω.indexOf s <= Ω.indexOf t ∧ Ω.indexOf t <= Ω.indexOf t
        else
          Ω.indexOf s <= Ω.indexOf t ∨ Ω.indexOf t <= Ω.indexOf t
      simp [hst]
    · change
        if Ω.indexOf s <= Ω.indexOf t then
          Ω.indexOf s <= Ω.indexOf t ∧ Ω.indexOf t <= Ω.indexOf t
        else
          Ω.indexOf s <= Ω.indexOf t ∨ Ω.indexOf t <= Ω.indexOf t
      simp [hst]

theorem indexOf_ne_of_ne [DecidableEq V] {Ω : CyclicBoundary V}
    {x y : V} (hx : x ∈ Ω.vertexSet)
    (hxy : x ≠ y) :
    Ω.indexOf x ≠ Ω.indexOf y := by
  intro hidx
  exact hxy ((List.idxOf_inj hx).mp (by
    simpa [CyclicBoundary.indexOf] using hidx))

theorem ne_of_clockwiseOpenBetween_left_right [DecidableEq V]
    {Ω : CyclicBoundary V} {x y z : V}
    (h : Ω.ClockwiseOpenBetween x y z) :
    x ≠ y := by
  classical
  intro hxy
  subst y
  have hidx_eq : Ω.indexOf z = Ω.indexOf x := by
    have horder := h.1.2
    change
      (if Ω.indexOf x <= Ω.indexOf x then
        Ω.indexOf x <= Ω.indexOf z ∧ Ω.indexOf z <= Ω.indexOf x
      else
        Ω.indexOf x <= Ω.indexOf z ∨ Ω.indexOf z <= Ω.indexOf x) at horder
    rw [if_pos (le_rfl : Ω.indexOf x <= Ω.indexOf x)] at horder
    exact le_antisymm horder.2 horder.1
  have hz_eq_x : z = x :=
    (List.idxOf_inj h.1.1).mp (by
      simpa [CyclicBoundary.indexOf] using hidx_eq)
  exact h.2.1 hz_eq_x

theorem clockwiseOpen_or_reverse_of_mem_ne [DecidableEq V]
    {Ω : CyclicBoundary V} {s t v : V}
    (hs : s ∈ Ω.vertexSet)
    (hv : v ∈ Ω.vertexSet) (hvs : v ≠ s) (hvt : v ≠ t)
    (hst_ne : s ≠ t) :
    Ω.ClockwiseOpenBetween s t v ∨ Ω.ClockwiseOpenBetween t s v := by
  classical
  let a := Ω.indexOf s
  let b := Ω.indexOf t
  let c := Ω.indexOf v
  have hcv_ne_a : c ≠ a := by
    intro h
    have hidx : Ω.vertices.idxOf v = Ω.vertices.idxOf s := by
      simpa [a, c, indexOf] using h
    exact hvs ((List.idxOf_inj hv).mp hidx)
  have hcv_ne_b : c ≠ b := by
    intro h
    have hidx : Ω.vertices.idxOf v = Ω.vertices.idxOf t := by
      simpa [b, c, indexOf] using h
    exact hvt ((List.idxOf_inj hv).mp hidx)
  have hab_ne : a ≠ b := by
    intro h
    have hidx : Ω.vertices.idxOf s = Ω.vertices.idxOf t := by
      simpa [a, b, indexOf] using h
    exact hst_ne ((List.idxOf_inj hs).mp hidx)
  by_cases hab : a <= b
  · by_cases hleft : a <= c ∧ c <= b
    · left
      refine ⟨⟨hv, ?_⟩, hvs, hvt⟩
      change if a <= b then a <= c ∧ c <= b else a <= c ∨ c <= b
      simpa [hab] using hleft
    · right
      have hb_not_le_a : ¬ b <= a := by
        intro hba
        exact hab_ne (le_antisymm hab hba)
      have hright : b <= c ∨ c <= a := by
        by_cases hac : a <= c
        · have hnot_cb : ¬ c <= b := by
            intro hcb
            exact hleft ⟨hac, hcb⟩
          left
          omega
        · right
          omega
      refine ⟨⟨hv, ?_⟩, hvt, hvs⟩
      change if b <= a then b <= c ∧ c <= a else b <= c ∨ c <= a
      simpa [hb_not_le_a] using hright
  · by_cases hleft : a <= c ∨ c <= b
    · left
      refine ⟨⟨hv, ?_⟩, hvs, hvt⟩
      change if a <= b then a <= c ∧ c <= b else a <= c ∨ c <= b
      simpa [hab] using hleft
    · right
      have hba : b <= a := by omega
      have hright : b <= c ∧ c <= a := by
        constructor <;> omega
      refine ⟨⟨hv, ?_⟩, hvt, hvs⟩
      change if b <= a then b <= c ∧ c <= a else b <= c ∨ c <= a
      simpa [hba] using hright

theorem clockwiseArcSet_disjoint_reverse [DecidableEq V]
    {Ω : CyclicBoundary V} {s t : V}
    (hs : s ∈ Ω.vertexSet) (hst_ne : s ≠ t) :
    Disjoint (Ω.clockwiseArcSet s t) (Ω.clockwiseArcSet t s) := by
  classical
  rw [Set.disjoint_left]
  intro v hvst hvts
  let a := Ω.indexOf s
  let b := Ω.indexOf t
  let c := Ω.indexOf v
  have hvs : v ≠ s := hvst.2.1
  have hvt : v ≠ t := hvst.2.2
  have hcv_ne_a : c ≠ a := by
    intro h
    have hidx : Ω.vertices.idxOf v = Ω.vertices.idxOf s := by
      simpa [a, c, indexOf] using h
    exact hvs ((List.idxOf_inj hvst.1.1).mp hidx)
  have hcv_ne_b : c ≠ b := by
    intro h
    have hidx : Ω.vertices.idxOf v = Ω.vertices.idxOf t := by
      simpa [b, c, indexOf] using h
    exact hvt ((List.idxOf_inj hvst.1.1).mp hidx)
  have hab_ne : a ≠ b := by
    intro h
    have hidx : Ω.vertices.idxOf s = Ω.vertices.idxOf t := by
      simpa [a, b, indexOf] using h
    exact hst_ne ((List.idxOf_inj hs).mp hidx)
  by_cases hab : a <= b
  · have hleft : a <= c ∧ c <= b := by
      have hraw :
          if a <= b then a <= c ∧ c <= b else a <= c ∨ c <= b := by
        simpa [indexOf, a, b, c] using hvst.1.2
      simpa [hab] using hraw
    have hb_not_le_a : ¬ b <= a := by
      intro hba
      exact hab_ne (le_antisymm hab hba)
    have hright : b <= c ∨ c <= a := by
      have hraw :
          if b <= a then b <= c ∧ c <= a else b <= c ∨ c <= a := by
        simpa [indexOf, a, b, c] using hvts.1.2
      simpa [hb_not_le_a] using hraw
    rcases hright with hbc | hca
    · exact hcv_ne_b (le_antisymm hbc hleft.2).symm
    · exact hcv_ne_a (le_antisymm hca hleft.1)
  · have hleft : a <= c ∨ c <= b := by
      have hraw :
          if a <= b then a <= c ∧ c <= b else a <= c ∨ c <= b := by
        simpa [indexOf, a, b, c] using hvst.1.2
      simpa [hab] using hraw
    have hba : b <= a := by omega
    have hright : b <= c ∧ c <= a := by
      have hraw :
          if b <= a then b <= c ∧ c <= a else b <= c ∨ c <= a := by
        simpa [indexOf, a, b, c] using hvts.1.2
      simpa [hba] using hraw
    rcases hleft with hac | hcb
    · exact hcv_ne_a (le_antisymm hright.2 hac)
    · exact hcv_ne_b (le_antisymm hcb hright.1)

theorem clockwiseArcSet_union_reverse [DecidableEq V]
    {Ω : CyclicBoundary V} {s t : V}
    (hs : s ∈ Ω.vertexSet) (ht : t ∈ Ω.vertexSet)
    (hst_ne : s ≠ t) :
    Ω.clockwiseArcSet s t ∪ Ω.clockwiseArcSet t s =
      Ω.vertexSet \ ({s, t} : Set V) := by
  ext v
  constructor
  · intro hv
    rcases hv with hv | hv
    · exact ⟨hv.1.1, by
        intro h
        rcases h with rfl | rfl
        · exact hv.2.1 rfl
        · exact hv.2.2 rfl⟩
    · exact ⟨hv.1.1, by
        intro h
        rcases h with rfl | rfl
        · exact hv.2.2 rfl
        · exact hv.2.1 rfl⟩
  · intro hv
    have hvs : v ≠ s := by
      intro h
      exact hv.2 (Or.inl h)
    have hvt : v ≠ t := by
      intro h
      exact hv.2 (Or.inr h)
    exact clockwiseOpen_or_reverse_of_mem_ne hs hv.1 hvs hvt hst_ne

/-- A boundary obtained from an injective `Fin n` indexing. -/
def ofFin {n : Nat} (boundary : Fin n -> V)
    (hinj : Function.Injective boundary) : CyclicBoundary V where
  vertices := List.ofFn boundary
  nodup := by
    classical
    exact List.nodup_ofFn.mpr hinj

@[simp]
theorem mem_ofFin_vertices {n : Nat} {boundary : Fin n -> V}
    {hinj : Function.Injective boundary} {v : V} :
    v ∈ (ofFin boundary hinj).vertices ↔ v ∈ Set.range boundary := by
  classical
  simp [ofFin, List.mem_ofFn]

@[simp]
theorem ofFin_vertexSet {n : Nat} {boundary : Fin n -> V}
    {hinj : Function.Injective boundary} :
    (ofFin boundary hinj).vertexSet = Set.range boundary := by
  ext v
  simp [vertexSet]

noncomputable def ofFiniteSet (s : Set V) (hs : s.Finite) :
    CyclicBoundary V where
  vertices := hs.toFinset.toList
  nodup := by
    exact Finset.nodup_toList hs.toFinset

@[simp]
theorem mem_ofFiniteSet_vertices {s : Set V} {hs : s.Finite} {v : V} :
    v ∈ (ofFiniteSet s hs).vertices ↔ v ∈ s := by
  classical
  simp [ofFiniteSet, Set.Finite.mem_toFinset]

@[simp]
theorem ofFiniteSet_vertexSet {s : Set V} {hs : s.Finite} :
    (ofFiniteSet s hs).vertexSet = s := by
  ext v
  simp [vertexSet]


end CyclicBoundary

end Schematic.Math.GraphTheory
