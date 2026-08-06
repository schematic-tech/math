import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Sides.BoundaryCycles

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

/-- After the one closing polygon edge, the canonical left boundary cycle
traverses the cut path from `s` to `t`. -/
theorem leftOrderedCutBoundary_cycle_segment_support
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (n : Nat)
    (h : P.leftOrderedCutBoundary.length = n + 3) :
    ((((P.leftOrderedCutBoundary.cycleWalkOfLength n h).drop 1).take
      P.path.length).support) = P.path.support := by
  have hcycleLength :
      (P.leftOrderedCutBoundary.cycleWalkOfLength n h).length = n + 3 := by
    change
      ((SimpleGraph.cycleGraph.cycle n).map
        (SimpleGraph.Embedding.map
          (P.leftOrderedCutBoundary.embeddingOfLength (n + 3) h)
          (SimpleGraph.cycleGraph (n + 3))).toHom).length = n + 3
    rw [SimpleGraph.Walk.length_map,
      SimpleGraph.cycleGraph.length_cycle]
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left (by omega),
    P.leftOrderedCutBoundary.cycleWalkOfLength_support n h]
  rw [show P.leftOrderedCutBoundary.vertices.reverse =
      P.path.support ++ P.leftBoundaryArcList.reverse by
    simp [leftOrderedCutBoundary, leftOrderedCutBoundaryVertices]]
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [← SimpleGraph.Walk.length_support]
  rw [List.take_left]

/-- After the one closing polygon edge, the canonical right boundary cycle
traverses the cut path from `t` to `s`. -/
theorem rightOrderedCutBoundary_cycle_segment_support
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (n : Nat)
    (h : P.rightOrderedCutBoundary.length = n + 3) :
    ((((P.rightOrderedCutBoundary.cycleWalkOfLength n h).drop 1).take
      P.path.reverse.length).support) = P.path.reverse.support := by
  have hcycleLength :
      (P.rightOrderedCutBoundary.cycleWalkOfLength n h).length = n + 3 := by
    change
      ((SimpleGraph.cycleGraph.cycle n).map
        (SimpleGraph.Embedding.map
          (P.rightOrderedCutBoundary.embeddingOfLength (n + 3) h)
          (SimpleGraph.cycleGraph (n + 3))).toHom).length = n + 3
    rw [SimpleGraph.Walk.length_map,
      SimpleGraph.cycleGraph.length_cycle]
  rw [SimpleGraph.Walk.take_support_eq_support_take_succ,
    SimpleGraph.Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left (by omega),
    P.rightOrderedCutBoundary.cycleWalkOfLength_support n h]
  rw [show P.rightOrderedCutBoundary.vertices.reverse =
      P.path.reverse.support ++ P.rightBoundaryArcList.reverse by
    simp [rightOrderedCutBoundary, rightOrderedCutBoundaryVertices]]
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [← SimpleGraph.Walk.length_support]
  rw [List.take_left]

theorem leftBoundaryArc_subset_leftOrderedCutBoundary
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.leftBoundaryArc ⊆ P.leftOrderedCutBoundary.vertexSet := by
  intro v hv
  rw [P.leftOrderedCutBoundary_vertexSet]
  exact Or.inl hv

theorem rightBoundaryArc_subset_rightOrderedCutBoundary
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.rightBoundaryArc ⊆ P.rightOrderedCutBoundary.vertexSet := by
  simpa using P.reverse.leftBoundaryArc_subset_leftOrderedCutBoundary

theorem pathSet_subset_leftOrderedCutBoundary
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.pathSet ⊆ P.leftOrderedCutBoundary.vertexSet := by
  intro v hv
  rw [P.leftOrderedCutBoundary_vertexSet]
  exact Or.inr hv

theorem pathSet_subset_rightOrderedCutBoundary
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.pathSet ⊆ P.rightOrderedCutBoundary.vertexSet := by
  simpa using P.reverse.pathSet_subset_leftOrderedCutBoundary

theorem leftOrderedCutBoundary_index_path_eq
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x : V} (hx : x ∈ P.pathSet) :
    P.leftOrderedCutBoundary.indexOf x =
      P.leftBoundaryArcList.length + P.path.support.reverse.idxOf x := by
  classical
  have hxNotArcList : x ∉ P.leftBoundaryArcList := by
    intro hxArcList
    have hxArc : x ∈ P.leftBoundaryArc := by
      simpa using (GMIX24CutPath.mem_leftBoundaryArcList P).mp hxArcList
    exact (P.leftBoundaryArc_subset_outside hxArc).2
      (by simpa [GMIX24CutPath.pathSet] using hx)
  simp [GMIX24CutPath.leftOrderedCutBoundary,
    GMIX24CutPath.leftOrderedCutBoundaryVertices,
    CyclicBoundary.indexOf, List.idxOf_append_of_notMem hxNotArcList]

theorem rightOrderedCutBoundary_index_path_eq
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x : V} (hx : x ∈ P.pathSet) :
    P.rightOrderedCutBoundary.indexOf x =
      P.rightBoundaryArcList.length + P.path.support.idxOf x := by
  have h :=
    P.reverse.leftOrderedCutBoundary_index_path_eq (by simpa using hx)
  have hsupport : P.path.reverse.support.reverse = P.path.support :=
    calc
      P.path.reverse.support.reverse = P.path.support.reverse.reverse :=
        congrArg List.reverse P.path.support_reverse
      _ = P.path.support := List.reverse_reverse P.path.support
  simp only [reverse_path] at h
  have h' :
      P.rightOrderedCutBoundary.indexOf x =
        P.rightBoundaryArcList.length +
          P.path.reverse.support.reverse.idxOf x := by
    simpa only [reverse_leftOrderedCutBoundary,
      reverse_leftBoundaryArcList] using h
  exact h'.trans (congrArg (P.rightBoundaryArcList.length + ·)
    (congrArg (List.idxOf x) hsupport))

theorem rightOrderedCutBoundary_index_path_le_iff
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) :
    P.rightOrderedCutBoundary.indexOf x <=
        P.rightOrderedCutBoundary.indexOf y ↔
      Walk.supportIndex P.path x <= Walk.supportIndex P.path y := by
  rw [P.rightOrderedCutBoundary_index_path_eq hx,
    P.rightOrderedCutBoundary_index_path_eq hy]
  simp [Walk.supportIndex]

theorem leftOrderedCutBoundary_index_path_le_iff
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) :
    P.leftOrderedCutBoundary.indexOf x <=
        P.leftOrderedCutBoundary.indexOf y ↔
      Walk.supportIndex P.path y <= Walk.supportIndex P.path x := by
  have hxSupport : x ∈ P.path.support := by
    simpa [GMIX24CutPath.pathSet] using hx
  have hySupport : y ∈ P.path.support := by
    simpa [GMIX24CutPath.pathSet] using hy
  rw [P.leftOrderedCutBoundary_index_path_eq hx,
    P.leftOrderedCutBoundary_index_path_eq hy]
  simpa [Walk.supportIndex] using
    (list_reverse_idxOf_le_iff P.path_isPath.support_nodup
      hxSupport hySupport)

theorem rightOrderedCutBoundary_supportIndex_lt_of_index_le
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hidx :
      P.rightOrderedCutBoundary.indexOf x <=
        P.rightOrderedCutBoundary.indexOf y)
    (hxy : x ≠ y) :
    Walk.supportIndex P.path x < Walk.supportIndex P.path y := by
  have hle :=
    (P.rightOrderedCutBoundary_index_path_le_iff hx hy).mp hidx
  exact
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using hx)
      hle hxy

theorem leftOrderedCutBoundary_supportIndex_gt_of_index_le
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hidx :
      P.leftOrderedCutBoundary.indexOf x <=
        P.leftOrderedCutBoundary.indexOf y)
    (hxy : y ≠ x) :
    Walk.supportIndex P.path y < Walk.supportIndex P.path x := by
  have hle :=
    (P.leftOrderedCutBoundary_index_path_le_iff hx hy).mp hidx
  exact
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using hy)
      hle hxy

theorem rightOrdered_clockwiseOpenBetween_of_path_index_between
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) (hz : z ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hxz : Walk.supportIndex P.path x < Walk.supportIndex P.path z)
    (hzy : Walk.supportIndex P.path z < Walk.supportIndex P.path y) :
    P.rightOrderedCutBoundary.ClockwiseOpenBetween x y z := by
  have hidx_xy :
      P.rightOrderedCutBoundary.indexOf x <=
        P.rightOrderedCutBoundary.indexOf y :=
    (P.rightOrderedCutBoundary_index_path_le_iff hx hy).mpr hxy
  have hidx_xz :
      P.rightOrderedCutBoundary.indexOf x <=
        P.rightOrderedCutBoundary.indexOf z :=
    (P.rightOrderedCutBoundary_index_path_le_iff hx hz).mpr
      (Nat.le_of_lt hxz)
  have hidx_zy :
      P.rightOrderedCutBoundary.indexOf z <=
        P.rightOrderedCutBoundary.indexOf y :=
    (P.rightOrderedCutBoundary_index_path_le_iff hz hy).mpr
      (Nat.le_of_lt hzy)
  refine ⟨⟨P.pathSet_subset_rightOrderedCutBoundary hz, ?_⟩, ?_, ?_⟩
  · simpa [CyclicBoundary.ClockwiseBetween, hidx_xy] using
      And.intro hidx_xz hidx_zy
  · intro hzx
    subst z
    omega
  · intro hzy_eq
    subst z
    omega

theorem leftOrdered_clockwiseOpenBetween_of_path_index_between
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) (hz : z ∈ P.pathSet)
    (hyx : Walk.supportIndex P.path y <= Walk.supportIndex P.path x)
    (hyz : Walk.supportIndex P.path y < Walk.supportIndex P.path z)
    (hzx : Walk.supportIndex P.path z < Walk.supportIndex P.path x) :
    P.leftOrderedCutBoundary.ClockwiseOpenBetween x y z := by
  have hidx_xy :
      P.leftOrderedCutBoundary.indexOf x <=
        P.leftOrderedCutBoundary.indexOf y :=
    (P.leftOrderedCutBoundary_index_path_le_iff hx hy).mpr hyx
  have hidx_xz :
      P.leftOrderedCutBoundary.indexOf x <=
        P.leftOrderedCutBoundary.indexOf z :=
    (P.leftOrderedCutBoundary_index_path_le_iff hx hz).mpr
      (Nat.le_of_lt hzx)
  have hidx_zy :
      P.leftOrderedCutBoundary.indexOf z <=
        P.leftOrderedCutBoundary.indexOf y :=
    (P.leftOrderedCutBoundary_index_path_le_iff hz hy).mpr
      (Nat.le_of_lt hyz)
  refine ⟨⟨P.pathSet_subset_leftOrderedCutBoundary hz, ?_⟩, ?_, ?_⟩
  · simpa [CyclicBoundary.ClockwiseBetween, hidx_xy] using
      And.intro hidx_xz hidx_zy
  · intro hzx_eq
    subst z
    omega
  · intro hzy_eq
    subst z
    omega

theorem leftOrderedCutBoundary_index_arc_lt_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {a x : V}
    (ha : a ∈ P.leftBoundaryArc) (hx : x ∈ P.pathSet) :
    P.leftOrderedCutBoundary.indexOf a <
      P.leftOrderedCutBoundary.indexOf x := by
  classical
  have haList : a ∈ P.leftBoundaryArcList := by
    simpa using (GMIX24CutPath.mem_leftBoundaryArcList P).mpr ha
  have hxTail : x ∈ P.path.support.reverse := by
    exact List.mem_reverse.mpr (by simpa [GMIX24CutPath.pathSet] using hx)
  have hxNotArcList : x ∉ P.leftBoundaryArcList := by
    intro hxArcList
    have hxArc : x ∈ P.leftBoundaryArc := by
      simpa using (GMIX24CutPath.mem_leftBoundaryArcList P).mp hxArcList
    exact (P.leftBoundaryArc_subset_outside hxArc).2
      (by simpa [GMIX24CutPath.pathSet] using hx)
  have hidx_a :
      P.leftOrderedCutBoundary.indexOf a =
        P.leftBoundaryArcList.idxOf a := by
    simp [GMIX24CutPath.leftOrderedCutBoundary,
      GMIX24CutPath.leftOrderedCutBoundaryVertices,
      CyclicBoundary.indexOf, List.idxOf_append_of_mem haList]
  have hidx_x :
      P.leftOrderedCutBoundary.indexOf x =
        P.leftBoundaryArcList.length + P.path.support.reverse.idxOf x := by
    simp [GMIX24CutPath.leftOrderedCutBoundary,
      GMIX24CutPath.leftOrderedCutBoundaryVertices,
      CyclicBoundary.indexOf, List.idxOf_append_of_notMem hxNotArcList]
  have ha_lt : P.leftBoundaryArcList.idxOf a < P.leftBoundaryArcList.length :=
    List.idxOf_lt_length_of_mem haList
  omega

theorem rightOrderedCutBoundary_index_arc_lt_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {a x : V}
    (ha : a ∈ P.rightBoundaryArc) (hx : x ∈ P.pathSet) :
    P.rightOrderedCutBoundary.indexOf a <
      P.rightOrderedCutBoundary.indexOf x := by
  simpa using
    P.reverse.leftOrderedCutBoundary_index_arc_lt_path
      (by simpa using ha) (by simpa using hx)

theorem leftOrdered_clockwiseOpenBetween_original_of_arc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.leftBoundaryArc)
    (hy : y ∈ P.leftBoundaryArc)
    (hz : z ∈ P.leftBoundaryArc)
    (hclock :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        P.leftOrderedCutBoundary x y z) :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary x y z := by
  classical
  let Ωrot : CyclicBoundary V :=
    { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1),
      nodup := List.nodup_rotate.mpr S.boundary.nodup }
  have hs_mem : P.s ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.s_mem_boundary
  have hn :
      S.boundary.indexOf P.s + 1 <= S.boundary.vertices.length := by
    have hs_idx : S.boundary.indexOf P.s < S.boundary.vertices.length := by
      simpa [CyclicBoundary.indexOf] using
        (List.idxOf_lt_length_iff.mpr hs_mem)
    omega
  have hxFilter :
      x ∈ (S.boundary.vertices.rotate
        (S.boundary.indexOf P.s + 1)).filter P.leftBoundaryArcBool := by
    have hxList : x ∈ P.leftBoundaryArcList := by simpa using
      (GMIX24CutPath.mem_leftBoundaryArcList P).mpr hx
    simpa [GMIX24CutPath.leftBoundaryArcList] using hxList
  have hyFilter :
      y ∈ (S.boundary.vertices.rotate
        (S.boundary.indexOf P.s + 1)).filter P.leftBoundaryArcBool := by
    have hyList : y ∈ P.leftBoundaryArcList := by simpa using
      (GMIX24CutPath.mem_leftBoundaryArcList P).mpr hy
    simpa [GMIX24CutPath.leftBoundaryArcList] using hyList
  have hzFilter :
      z ∈ (S.boundary.vertices.rotate
        (S.boundary.indexOf P.s + 1)).filter P.leftBoundaryArcBool := by
    have hzList : z ∈ P.leftBoundaryArcList := by simpa using
      (GMIX24CutPath.mem_leftBoundaryArcList P).mpr hz
    simpa [GMIX24CutPath.leftBoundaryArcList] using hzList
  have hclockLocal :
      P.leftOrderedCutBoundary.ClockwiseOpenBetween x y z := by
    simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
      CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
      hclock
  have hrot : Ωrot.ClockwiseOpenBetween x y z :=
    CyclicBoundary.clockwiseOpenBetween_of_filter_append
      (Ω := Ωrot) (p := P.leftBoundaryArcBool)
      (tail := P.path.support.reverse)
      hxFilter hyFilter hzFilter
      (by
        simpa [Ωrot, GMIX24CutPath.leftOrderedCutBoundary,
          GMIX24CutPath.leftOrderedCutBoundaryVertices,
          GMIX24CutPath.leftBoundaryArcList] using hclockLocal)
  have hlocal : S.boundary.ClockwiseOpenBetween x y z :=
    CyclicBoundary.clockwiseOpenBetween_of_rotate
      S.boundary hn
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hx)
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hy)
      (by simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hz)
      (by simpa [Ωrot] using hrot)
  simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
    CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
    hlocal

theorem rightOrdered_clockwiseOpenBetween_original_of_arc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.rightBoundaryArc)
    (hy : y ∈ P.rightBoundaryArc)
    (hz : z ∈ P.rightBoundaryArc)
    (hclock :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        P.rightOrderedCutBoundary x y z) :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary x y z := by
  simpa using
    P.reverse.leftOrdered_clockwiseOpenBetween_original_of_arc
      (by simpa using hx) (by simpa using hy) (by simpa using hz)
      (by simpa using hclock)

theorem leftOrdered_clockwiseOpenBetween_original_of_arc_or_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.leftBoundaryArc ∨ x = P.t)
    (hy : y ∈ P.leftBoundaryArc ∨ y = P.t)
    (hz : z ∈ P.leftBoundaryArc ∨ z = P.t)
    (hclock :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        P.leftOrderedCutBoundary x y z) :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary x y z := by
  classical
  let pref : List V := P.leftBoundaryArcList ++ [P.t]
  have hpref : pref.Nodup := by
    simpa [pref] using P.leftBoundaryArcList_append_end_nodup
  have hxPref : x ∈ pref := by
    rcases hx with hxArc | hxt
    · exact List.mem_append_left [P.t]
        ((GMIX24CutPath.mem_leftBoundaryArcList P).mpr hxArc)
    · subst x
      exact List.mem_append_right P.leftBoundaryArcList (by simp)
  have hyPref : y ∈ pref := by
    rcases hy with hyArc | hyt
    · exact List.mem_append_left [P.t]
        ((GMIX24CutPath.mem_leftBoundaryArcList P).mpr hyArc)
    · subst y
      exact List.mem_append_right P.leftBoundaryArcList (by simp)
  have hzPref : z ∈ pref := by
    rcases hz with hzArc | hzt
    · exact List.mem_append_left [P.t]
        ((GMIX24CutPath.mem_leftBoundaryArcList P).mpr hzArc)
    · subst z
      exact List.mem_append_right P.leftBoundaryArcList (by simp)
  let sideTail : List V := P.path.support.reverse.tail
  have hrev_cons :
      P.path.support.reverse = P.t :: P.path.support.reverse.tail := by
    have h := (P.path.reverse.cons_tail_support).symm
    rw [SimpleGraph.Walk.support_reverse] at h
    exact h
  have hside_vertices :
      P.leftOrderedCutBoundary.vertices = pref ++ sideTail := by
    dsimp [GMIX24CutPath.leftOrderedCutBoundary,
      GMIX24CutPath.leftOrderedCutBoundaryVertices]
    change P.leftBoundaryArcList ++ P.path.support.reverse = pref ++ sideTail
    rw [hrev_cons]
    simp [pref, sideTail, List.append_assoc]
  have hsideNodup : (pref ++ sideTail).Nodup := by
    simpa [← hside_vertices] using P.leftOrderedCutBoundary.nodup
  have hclockLocal :
      P.leftOrderedCutBoundary.ClockwiseOpenBetween x y z := by
    simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
      CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
      hclock
  have hclockSideFull :
      ({ vertices := pref ++ sideTail, nodup := hsideNodup } :
        CyclicBoundary V).ClockwiseOpenBetween x y z := by
    rcases hclockLocal with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ pref ++ sideTail
      change z ∈ P.leftOrderedCutBoundary.vertices at hzMem
      simpa [hside_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hside_vertices] using horder
  have hclockPref :
      ({ vertices := pref, nodup := hpref } :
        CyclicBoundary V).ClockwiseOpenBetween x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_tail_iff
      hpref hsideNodup hxPref hyPref hzPref).mp hclockSideFull
  let Ωrot : CyclicBoundary V :=
    { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.s + 1),
      nodup := List.nodup_rotate.mpr S.boundary.nodup }
  let origTail : List V := Ωrot.vertices.drop (Ωrot.indexOf P.t + 1)
  have hs_mem : P.s ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.s_mem_boundary
  have hn :
      S.boundary.indexOf P.s + 1 <= S.boundary.vertices.length := by
    have hs_idx : S.boundary.indexOf P.s < S.boundary.vertices.length := by
      simpa [CyclicBoundary.indexOf] using
        (List.idxOf_lt_length_iff.mpr hs_mem)
    omega
  have htRot : P.t ∈ Ωrot.vertices := by
    exact (List.mem_rotate).mpr (by
      simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
        P.t_mem_boundary)
  have htIdx : Ωrot.indexOf P.t < Ωrot.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr htRot)
  have hget :
      Ωrot.vertices[Ωrot.indexOf P.t] = P.t := by
    simp [CyclicBoundary.indexOf]
  have htake :
      Ωrot.vertices.take (Ωrot.indexOf P.t) = P.leftBoundaryArcList := by
    simpa [Ωrot] using
      (GMIX24CutPath.leftBoundaryArcList_eq_rotate_take_to_end P).symm
  have htake_succ :
      Ωrot.vertices.take (Ωrot.indexOf P.t + 1) = pref := by
    calc
      Ωrot.vertices.take (Ωrot.indexOf P.t + 1)
          = Ωrot.vertices.take (Ωrot.indexOf P.t) ++
              [Ωrot.vertices[Ωrot.indexOf P.t]] := by
            exact (List.take_concat_get' Ωrot.vertices
              (Ωrot.indexOf P.t) htIdx).symm
      _ = pref := by
            simp [pref, htake, hget]
  have hrot_vertices : Ωrot.vertices = pref ++ origTail := by
    calc
      Ωrot.vertices =
          Ωrot.vertices.take (Ωrot.indexOf P.t + 1) ++
            Ωrot.vertices.drop (Ωrot.indexOf P.t + 1) := by
            exact (List.take_append_drop
              (Ωrot.indexOf P.t + 1) Ωrot.vertices).symm
      _ = pref ++ origTail := by
            simp [origTail, htake_succ]
  have hrotNodup : (pref ++ origTail).Nodup := by
    simpa [← hrot_vertices] using Ωrot.nodup
  have hclockRotFull :
      ({ vertices := pref ++ origTail, nodup := hrotNodup } :
        CyclicBoundary V).ClockwiseOpenBetween x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_tail_iff
      hpref hrotNodup hxPref hyPref hzPref).mpr hclockPref
  have hrot : Ωrot.ClockwiseOpenBetween x y z := by
    rcases hclockRotFull with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ Ωrot.vertices
      change z ∈ pref ++ origTail at hzMem
      simpa [hrot_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hrot_vertices] using horder
  have hxOrig : x ∈ S.boundary.vertexSet := by
    rcases hx with hxArc | hxt
    · simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hxArc
    · subst x
      simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hyOrig : y ∈ S.boundary.vertexSet := by
    rcases hy with hyArc | hyt
    · simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hyArc
    · subst y
      simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hzOrig : z ∈ S.boundary.vertexSet := by
    rcases hz with hzArc | hzt
    · simpa [GeneralSociety.boundarySet] using P.leftBoundaryArc_subset hzArc
    · subst z
      simpa [GeneralSociety.boundarySet] using P.t_mem_boundary
  have hlocal : S.boundary.ClockwiseOpenBetween x y z :=
    CyclicBoundary.clockwiseOpenBetween_of_rotate
      S.boundary hn hxOrig hyOrig hzOrig
      (by simpa [Ωrot] using hrot)
  simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
    CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
    hlocal

theorem rightOrdered_clockwiseOpenBetween_original_of_arc_or_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {x y z : V}
    (hx : x ∈ P.rightBoundaryArc ∨ x = P.s)
    (hy : y ∈ P.rightBoundaryArc ∨ y = P.s)
    (hz : z ∈ P.rightBoundaryArc ∨ z = P.s)
    (hclock :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        P.rightOrderedCutBoundary x y z) :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
      S.boundary x y z := by
  classical
  let pref : List V := P.rightBoundaryArcList ++ [P.s]
  have hpref : pref.Nodup := by
    simpa [pref] using P.rightBoundaryArcList_append_start_nodup
  have hxPref : x ∈ pref := by
    rcases hx with hxArc | hxs
    · exact List.mem_append_left [P.s]
        ((GMIX24CutPath.mem_rightBoundaryArcList P).mpr hxArc)
    · subst x
      exact List.mem_append_right P.rightBoundaryArcList (by simp)
  have hyPref : y ∈ pref := by
    rcases hy with hyArc | hys
    · exact List.mem_append_left [P.s]
        ((GMIX24CutPath.mem_rightBoundaryArcList P).mpr hyArc)
    · subst y
      exact List.mem_append_right P.rightBoundaryArcList (by simp)
  have hzPref : z ∈ pref := by
    rcases hz with hzArc | hzs
    · exact List.mem_append_left [P.s]
        ((GMIX24CutPath.mem_rightBoundaryArcList P).mpr hzArc)
    · subst z
      exact List.mem_append_right P.rightBoundaryArcList (by simp)
  let sideTail : List V := P.path.support.tail
  have hsupport_cons :
      P.path.support = P.s :: P.path.support.tail :=
    P.path.cons_tail_support.symm
  have hside_vertices :
      P.rightOrderedCutBoundary.vertices = pref ++ sideTail := by
    dsimp [GMIX24CutPath.rightOrderedCutBoundary,
      GMIX24CutPath.rightOrderedCutBoundaryVertices]
    change P.rightBoundaryArcList ++ P.path.support = pref ++ sideTail
    rw [hsupport_cons]
    simp [pref, sideTail, List.append_assoc]
  have hsideNodup : (pref ++ sideTail).Nodup := by
    simpa [← hside_vertices] using P.rightOrderedCutBoundary.nodup
  have hclockLocal :
      P.rightOrderedCutBoundary.ClockwiseOpenBetween x y z := by
    simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
      CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
      hclock
  have hclockSideFull :
      ({ vertices := pref ++ sideTail, nodup := hsideNodup } :
        CyclicBoundary V).ClockwiseOpenBetween x y z := by
    rcases hclockLocal with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ pref ++ sideTail
      change z ∈ P.rightOrderedCutBoundary.vertices at hzMem
      simpa [hside_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hside_vertices] using horder
  have hclockPref :
      ({ vertices := pref, nodup := hpref } :
        CyclicBoundary V).ClockwiseOpenBetween x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_tail_iff
      hpref hsideNodup hxPref hyPref hzPref).mp hclockSideFull
  let Ωrot : CyclicBoundary V :=
    { vertices := S.boundary.vertices.rotate (S.boundary.indexOf P.t + 1),
      nodup := List.nodup_rotate.mpr S.boundary.nodup }
  let origTail : List V := Ωrot.vertices.drop (Ωrot.indexOf P.s + 1)
  have ht_mem : P.t ∈ S.boundary.vertices := by
    simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
      P.t_mem_boundary
  have hn :
      S.boundary.indexOf P.t + 1 <= S.boundary.vertices.length := by
    have ht_idx : S.boundary.indexOf P.t < S.boundary.vertices.length := by
      simpa [CyclicBoundary.indexOf] using
        (List.idxOf_lt_length_iff.mpr ht_mem)
    omega
  have hsRot : P.s ∈ Ωrot.vertices := by
    exact (List.mem_rotate).mpr (by
      simpa [GeneralSociety.boundarySet, CyclicBoundary.vertexSet] using
        P.s_mem_boundary)
  have hsIdx : Ωrot.indexOf P.s < Ωrot.vertices.length := by
    simpa [CyclicBoundary.indexOf] using
      (List.idxOf_lt_length_iff.mpr hsRot)
  have hget :
      Ωrot.vertices[Ωrot.indexOf P.s] = P.s := by
    simp [CyclicBoundary.indexOf]
  have htake :
      Ωrot.vertices.take (Ωrot.indexOf P.s) = P.rightBoundaryArcList := by
    simpa [Ωrot] using
      (GMIX24CutPath.rightBoundaryArcList_eq_rotate_take_to_start P).symm
  have htake_succ :
      Ωrot.vertices.take (Ωrot.indexOf P.s + 1) = pref := by
    calc
      Ωrot.vertices.take (Ωrot.indexOf P.s + 1)
          = Ωrot.vertices.take (Ωrot.indexOf P.s) ++
              [Ωrot.vertices[Ωrot.indexOf P.s]] := by
            exact (List.take_concat_get' Ωrot.vertices
              (Ωrot.indexOf P.s) hsIdx).symm
      _ = pref := by
            simp [pref, htake, hget]
  have hrot_vertices : Ωrot.vertices = pref ++ origTail := by
    calc
      Ωrot.vertices =
          Ωrot.vertices.take (Ωrot.indexOf P.s + 1) ++
            Ωrot.vertices.drop (Ωrot.indexOf P.s + 1) := by
            exact (List.take_append_drop
              (Ωrot.indexOf P.s + 1) Ωrot.vertices).symm
      _ = pref ++ origTail := by
            simp [origTail, htake_succ]
  have hrotNodup : (pref ++ origTail).Nodup := by
    simpa [← hrot_vertices] using Ωrot.nodup
  have hclockRotFull :
      ({ vertices := pref ++ origTail, nodup := hrotNodup } :
        CyclicBoundary V).ClockwiseOpenBetween x y z :=
    (CyclicBoundary.clockwiseOpenBetween_append_tail_iff
      hpref hrotNodup hxPref hyPref hzPref).mpr hclockPref
  have hrot : Ωrot.ClockwiseOpenBetween x y z := by
    rcases hclockRotFull with ⟨⟨hzMem, horder⟩, hzx, hzy⟩
    refine ⟨⟨?_, ?_⟩, hzx, hzy⟩
    · change z ∈ Ωrot.vertices
      change z ∈ pref ++ origTail at hzMem
      simpa [hrot_vertices] using hzMem
    · simpa [CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
        hrot_vertices] using horder
  have hxOrig : x ∈ S.boundary.vertexSet := by
    rcases hx with hxArc | hxs
    · simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset hxArc
    · subst x
      simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have hyOrig : y ∈ S.boundary.vertexSet := by
    rcases hy with hyArc | hys
    · simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset hyArc
    · subst y
      simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have hzOrig : z ∈ S.boundary.vertexSet := by
    rcases hz with hzArc | hzs
    · simpa [GeneralSociety.boundarySet] using P.rightBoundaryArc_subset hzArc
    · subst z
      simpa [GeneralSociety.boundarySet] using P.s_mem_boundary
  have hlocal : S.boundary.ClockwiseOpenBetween x y z :=
    CyclicBoundary.clockwiseOpenBetween_of_rotate
      S.boundary hn hxOrig hyOrig hzOrig
      (by simpa [Ωrot] using hrot)
  simpa [CyclicBoundary.ClockwiseOpenBetween, CyclicBoundary.ClockwiseBetween,
    CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
    hlocal

theorem leftCutBoundarySet_inter_rightCutBoundarySet_eq_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftCutBoundarySet ∩ P.rightCutBoundarySet = P.pathSet := by
  ext v
  constructor
  · intro hv
    rcases hv.1 with hvLeft | hvPath
    · rcases hv.2 with hvRight | hvPath
      · exact False.elim
          (Set.disjoint_left.mp P.leftBoundaryArc_disjoint_right
            hvLeft hvRight)
      · exact hvPath
    · exact hvPath
  · intro hvPath
    exact ⟨Or.inr hvPath, Or.inr hvPath⟩

theorem leftCutBoundarySet_union_rightCutBoundarySet_eq_boundary_union_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftCutBoundarySet ∪ P.rightCutBoundarySet =
      S.boundarySet ∪ P.pathSet := by
  ext v
  constructor
  · intro hv
    rcases hv with hvLeftCut | hvRightCut
    · rcases hvLeftCut with hvLeft | hvPath
      · exact Or.inl (P.leftBoundaryArc_subset hvLeft)
      · exact Or.inr hvPath
    · rcases hvRightCut with hvRight | hvPath
      · exact Or.inl (P.rightBoundaryArc_subset hvRight)
      · exact Or.inr hvPath
  · intro hv
    rcases hv with hvBoundary | hvPath
    · by_cases hvs : v = P.s
      · exact Or.inl (Or.inr (by
          simp [pathSet, hvs]))
      · by_cases hvt : v = P.t
        · exact Or.inl (Or.inr (by
            simp [pathSet, hvt]))
        · have hvArc :
              v ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
            rw [P.leftBoundaryArc_union_right]
            exact ⟨hvBoundary, by
              intro hvst
              rcases hvst with hvs' | hvt'
              · exact hvs hvs'
              · exact hvt hvt'⟩
          rcases hvArc with hvLeft | hvRight
          · exact Or.inl (Or.inl hvLeft)
          · exact Or.inr (Or.inl hvRight)
    · exact Or.inl (Or.inr hvPath)

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
