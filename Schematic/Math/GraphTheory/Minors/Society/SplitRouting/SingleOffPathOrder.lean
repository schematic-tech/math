import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem cross_endpoint_index_ne_of_on_path_of_off_path
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    {k l : Fin 4}
    (hk_path : X.endpoints.endpoint k ∈ P.pathSet)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet) :
    k ≠ l := by
  intro hkl
  subst k
  exact hl_off hk_path

theorem cross_clean_branch_endpoint_not_path
    {S : GeneralSociety V} {P : GMIX24CutPath S}
    {x y : V} (r : S.graph.Walk x y)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    x ∉ P.pathSet ∧ y ∉ P.pathSet := by
  exact ⟨
    (hr_outside x r.start_mem_support).2,
    (hr_outside y r.end_mem_support).2⟩

theorem cross_clean_branch_endpoints_ne_on_path_endpoint
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    {l : Fin 4}
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V} (r : S.graph.Walk x y)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    forall i : Fin 4, i ≠ l ->
      x ≠ X.endpoints.endpoint i ∧ y ≠ X.endpoints.endpoint i := by
  intro i hi
  have hnot_path :=
    cross_clean_branch_endpoint_not_path (P := P) r hr_outside
  exact ⟨
    (fun hxi => hnot_path.1 (by simpa [hxi] using hothers_path i hi)),
    (fun hyi => hnot_path.2 (by simpa [hyi] using hothers_path i hi))⟩

theorem cross_clean_branch_endpoints_ne
    {H : GeneralSociety V} {X : H.Cross}
    {x y : V}
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support) :
    x ≠ y := by
  intro hxy
  exact
    Set.disjoint_left.mp X.paths_disjoint hx_first (by simpa [hxy] using hy_second)

theorem cross_clean_branch_endpoints_ne_symm
    {H : GeneralSociety V} {X : H.Cross}
    {x y : V}
    (hx_second : x ∈ X.secondPath.support)
    (hy_first : y ∈ X.firstPath.support) :
    x ≠ y := by
  intro hxy
  exact
    Set.disjoint_left.mp X.paths_disjoint (by simpa [hxy] using hy_first) hx_second

theorem canonicalOfNoCross_right_cross_endpoint3_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 0) <
        Walk.supportIndex P.path (X.endpoints.endpoint 1) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 1) <
        Walk.supportIndex P.path (X.endpoints.endpoint 2) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h0P : e 0 ∈ P.pathSet := hothers_path 0 (by decide)
  have h1P : e 1 ∈ P.pathSet := hothers_path 1 (by decide)
  have h2P : e 2 ∈ P.pathSet := hothers_path 2 (by decide)
  have h3Arc : e 3 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 3).mp h3_off
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h3_lt0 : idx (e 3) < idx (e 0) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h3Arc h0P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h3_lt2 : idx (e 3) < idx (e 2) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h3Arc h2P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h20_not : ¬ idx (e 2) <= idx (e 0) := by
    intro h20
    have hbetween := hside.2.1.2
    change
      (if idx (e 2) <= idx (e 0) then
        idx (e 2) <= idx (e 3) ∧ idx (e 3) <= idx (e 0)
      else
        idx (e 2) <= idx (e 3) ∨ idx (e 3) <= idx (e 0)) at hbetween
    rw [if_pos h20] at hbetween
    have h23 : idx (e 2) <= idx (e 3) := hbetween.1
    omega
  have h02 : idx (e 0) < idx (e 2) := by omega
  have h012_le :
      idx (e 0) <= idx (e 1) ∧ idx (e 1) <= idx (e 2) := by
    have hbetween := hside.1.1.2
    change
      (if idx (e 0) <= idx (e 2) then
        idx (e 0) <= idx (e 1) ∧ idx (e 1) <= idx (e 2)
      else
        idx (e 0) <= idx (e 1) ∨ idx (e 1) <= idx (e 2)) at hbetween
    rw [if_pos (Nat.le_of_lt h02)] at hbetween
    exact hbetween
  have h01_le :
      Walk.supportIndex P.path (e 0) <= Walk.supportIndex P.path (e 1) := by
    exact
      (P.rightOrderedCutBoundary_index_path_le_iff h0P h1P).mp
        (by
          simpa [idx, Ω, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using h012_le.1)
  have h12_le :
      Walk.supportIndex P.path (e 1) <= Walk.supportIndex P.path (e 2) := by
    exact
      (P.rightOrderedCutBoundary_index_path_le_iff h1P h2P).mp
        (by
          simpa [idx, Ω, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using h012_le.2)
  have h01_ne : e 0 ≠ e 1 := by
    intro h
    have hfin : (0 : Fin 4) = 1 := X.endpoints.endpoint_injective h
    exact (by decide : (0 : Fin 4) ≠ 1) hfin
  have h12_ne : e 1 ≠ e 2 := by
    intro h
    have hfin : (1 : Fin 4) = 2 := X.endpoints.endpoint_injective h
    exact (by decide : (1 : Fin 4) ≠ 2) hfin
  exact ⟨
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h0P)
      h01_le h01_ne,
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h1P)
      h12_le h12_ne⟩

theorem canonicalOfNoCross_left_cross_endpoint3_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 2) <
        Walk.supportIndex P.path (X.endpoints.endpoint 1) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 1) <
        Walk.supportIndex P.path (X.endpoints.endpoint 0) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  have hrev :=
    GMIX24Split.canonicalOfNoCross_right_cross_endpoint3_off_path_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
          hothers_path i hi)
  exact
    ⟨(P.supportIndex_reverse_lt_iff
        (hothers_path 1 (by decide)) (hothers_path 2 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.2),
      (P.supportIndex_reverse_lt_iff
        (hothers_path 0 (by decide)) (hothers_path 1 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.1)⟩


theorem canonicalOfNoCross_right_cross_endpoint1_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 2) <
        Walk.supportIndex P.path (X.endpoints.endpoint 3) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 3) <
        Walk.supportIndex P.path (X.endpoints.endpoint 0) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h0P : e 0 ∈ P.pathSet := hothers_path 0 (by decide)
  have h2P : e 2 ∈ P.pathSet := hothers_path 2 (by decide)
  have h3P : e 3 ∈ P.pathSet := hothers_path 3 (by decide)
  have h1Arc : e 1 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 1).mp h1_off
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h1_lt0 : idx (e 1) < idx (e 0) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h1Arc h0P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h1_lt2 : idx (e 1) < idx (e 2) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h1Arc h2P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h02_not : ¬ idx (e 0) <= idx (e 2) := by
    intro h02
    have hbetween := hside.1.1.2
    change
      (if idx (e 0) <= idx (e 2) then
        idx (e 0) <= idx (e 1) ∧ idx (e 1) <= idx (e 2)
      else
        idx (e 0) <= idx (e 1) ∨ idx (e 1) <= idx (e 2)) at hbetween
    rw [if_pos h02] at hbetween
    have h01 : idx (e 0) <= idx (e 1) := hbetween.1
    omega
  have h20 : idx (e 2) < idx (e 0) := by omega
  have h230_le :
      idx (e 2) <= idx (e 3) ∧ idx (e 3) <= idx (e 0) := by
    have hbetween := hside.2.1.2
    change
      (if idx (e 2) <= idx (e 0) then
        idx (e 2) <= idx (e 3) ∧ idx (e 3) <= idx (e 0)
      else
        idx (e 2) <= idx (e 3) ∨ idx (e 3) <= idx (e 0)) at hbetween
    rw [if_pos (Nat.le_of_lt h20)] at hbetween
    exact hbetween
  have h23_le :
      Walk.supportIndex P.path (e 2) <= Walk.supportIndex P.path (e 3) := by
    exact
      (P.rightOrderedCutBoundary_index_path_le_iff h2P h3P).mp
        (by
          simpa [idx, Ω, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using h230_le.1)
  have h30_le :
      Walk.supportIndex P.path (e 3) <= Walk.supportIndex P.path (e 0) := by
    exact
      (P.rightOrderedCutBoundary_index_path_le_iff h3P h0P).mp
        (by
          simpa [idx, Ω, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using h230_le.2)
  have h23_ne : e 2 ≠ e 3 := by
    intro h
    have hfin : (2 : Fin 4) = 3 := X.endpoints.endpoint_injective h
    exact (by decide : (2 : Fin 4) ≠ 3) hfin
  have h30_ne : e 3 ≠ e 0 := by
    intro h
    have hfin : (3 : Fin 4) = 0 := X.endpoints.endpoint_injective h
    exact (by decide : (3 : Fin 4) ≠ 0) hfin
  exact ⟨
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h2P)
      h23_le h23_ne,
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h3P)
      h30_le h30_ne⟩

theorem canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 0) <
        Walk.supportIndex P.path (X.endpoints.endpoint 3) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 3) <
        Walk.supportIndex P.path (X.endpoints.endpoint 2) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  have hrev :=
    GMIX24Split.canonicalOfNoCross_right_cross_endpoint1_off_path_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
          hothers_path i hi)
  exact
    ⟨(P.supportIndex_reverse_lt_iff
        (hothers_path 3 (by decide)) (hothers_path 0 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.2),
      (P.supportIndex_reverse_lt_iff
        (hothers_path 2 (by decide)) (hothers_path 3 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.1)⟩


theorem canonicalOfNoCross_right_cross_endpoint0_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 1) <
        Walk.supportIndex P.path (X.endpoints.endpoint 2) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 2) <
        Walk.supportIndex P.path (X.endpoints.endpoint 3) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h1P : e 1 ∈ P.pathSet := hothers_path 1 (by decide)
  have h2P : e 2 ∈ P.pathSet := hothers_path 2 (by decide)
  have h3P : e 3 ∈ P.pathSet := hothers_path 3 (by decide)
  have h0Arc : e 0 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp h0_off
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h0_lt2 : idx (e 0) < idx (e 2) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h0Arc h2P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h0_lt3 : idx (e 0) < idx (e 3) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h0Arc h3P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h012_le :
      idx (e 0) <= idx (e 1) ∧ idx (e 1) <= idx (e 2) := by
    have hbetween := hside.1.1.2
    change
      (if idx (e 0) <= idx (e 2) then
        idx (e 0) <= idx (e 1) ∧ idx (e 1) <= idx (e 2)
      else
        idx (e 0) <= idx (e 1) ∨ idx (e 1) <= idx (e 2)) at hbetween
    rw [if_pos (Nat.le_of_lt h0_lt2)] at hbetween
    exact hbetween
  have h23_le_idx : idx (e 2) <= idx (e 3) := by
    have hbetween := hside.2.1.2
    have h20_not : ¬ idx (e 2) <= idx (e 0) := by omega
    change
      (if idx (e 2) <= idx (e 0) then
        idx (e 2) <= idx (e 3) ∧ idx (e 3) <= idx (e 0)
      else
        idx (e 2) <= idx (e 3) ∨ idx (e 3) <= idx (e 0)) at hbetween
    rw [if_neg h20_not] at hbetween
    rcases hbetween with h23 | h30
    · exact h23
    · omega
  have h12_le :
      Walk.supportIndex P.path (e 1) <= Walk.supportIndex P.path (e 2) :=
    (P.rightOrderedCutBoundary_index_path_le_iff h1P h2P).mp
      (by simpa [idx, Ω, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using h012_le.2)
  have h23_le :
      Walk.supportIndex P.path (e 2) <= Walk.supportIndex P.path (e 3) :=
    (P.rightOrderedCutBoundary_index_path_le_iff h2P h3P).mp
      (by simpa [idx, Ω, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using h23_le_idx)
  have h12_ne : e 1 ≠ e 2 := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 2) (X.endpoints.endpoint_injective h)
  have h23_ne : e 2 ≠ e 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (X.endpoints.endpoint_injective h)
  exact ⟨
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h1P)
      h12_le h12_ne,
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h2P)
      h23_le h23_ne⟩

theorem canonicalOfNoCross_left_cross_endpoint0_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 3) <
        Walk.supportIndex P.path (X.endpoints.endpoint 2) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 2) <
        Walk.supportIndex P.path (X.endpoints.endpoint 1) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  have hrev :=
    GMIX24Split.canonicalOfNoCross_right_cross_endpoint0_off_path_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
          hothers_path i hi)
  exact
    ⟨(P.supportIndex_reverse_lt_iff
        (hothers_path 2 (by decide)) (hothers_path 3 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.2),
      (P.supportIndex_reverse_lt_iff
        (hothers_path 1 (by decide)) (hothers_path 2 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.1)⟩


theorem canonicalOfNoCross_right_cross_endpoint2_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 3) <
        Walk.supportIndex P.path (X.endpoints.endpoint 0) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 0) <
        Walk.supportIndex P.path (X.endpoints.endpoint 1) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  let idx : V -> Nat :=
    fun v => @CyclicBoundary.indexOf V (Classical.decEq V) Ω v
  have h0P : e 0 ∈ P.pathSet := hothers_path 0 (by decide)
  have h1P : e 1 ∈ P.pathSet := hothers_path 1 (by decide)
  have h3P : e 3 ∈ P.pathSet := hothers_path 3 (by decide)
  have h2Arc : e 2 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp h2_off
  have hside : CrossEndpointAlternating Ω e := by
    simpa [Ω, e, GMIX24Split.canonicalOfNoCross,
      GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
      GMIX24Split.ofCanonical] using X.endpoints.cyclic_alternating
  have h2_lt0 : idx (e 2) < idx (e 0) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h2Arc h0P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h2_lt1 : idx (e 2) < idx (e 1) := by
    have hlt := P.rightOrderedCutBoundary_index_arc_lt_path h2Arc h1P
    simpa [idx, Ω, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hlt
  have h203_le :
      idx (e 2) <= idx (e 3) ∧ idx (e 3) <= idx (e 0) := by
    have hbetween := hside.2.1.2
    change
      (if idx (e 2) <= idx (e 0) then
        idx (e 2) <= idx (e 3) ∧ idx (e 3) <= idx (e 0)
      else
        idx (e 2) <= idx (e 3) ∨ idx (e 3) <= idx (e 0)) at hbetween
    rw [if_pos (Nat.le_of_lt h2_lt0)] at hbetween
    exact hbetween
  have h01_le_idx : idx (e 0) <= idx (e 1) := by
    have hbetween := hside.1.1.2
    have h02_not : ¬ idx (e 0) <= idx (e 2) := by omega
    change
      (if idx (e 0) <= idx (e 2) then
        idx (e 0) <= idx (e 1) ∧ idx (e 1) <= idx (e 2)
      else
        idx (e 0) <= idx (e 1) ∨ idx (e 1) <= idx (e 2)) at hbetween
    rw [if_neg h02_not] at hbetween
    rcases hbetween with h01 | h12
    · exact h01
    · omega
  have h30_le :
      Walk.supportIndex P.path (e 3) <= Walk.supportIndex P.path (e 0) :=
    (P.rightOrderedCutBoundary_index_path_le_iff h3P h0P).mp
      (by simpa [idx, Ω, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using h203_le.2)
  have h01_le :
      Walk.supportIndex P.path (e 0) <= Walk.supportIndex P.path (e 1) :=
    (P.rightOrderedCutBoundary_index_path_le_iff h0P h1P).mp
      (by simpa [idx, Ω, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using h01_le_idx)
  have h30_ne : e 3 ≠ e 0 := by
    intro h
    exact (by decide : (3 : Fin 4) ≠ 0) (X.endpoints.endpoint_injective h)
  have h01_ne : e 0 ≠ e 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (X.endpoints.endpoint_injective h)
  exact ⟨
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h3P)
      h30_le h30_ne,
    Walk.supportIndex_lt_of_le_of_mem_of_ne
      (by simpa [GMIX24CutPath.pathSet] using h0P)
      h01_le h01_ne⟩

theorem canonicalOfNoCross_left_cross_endpoint2_off_path_path_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet) :
    Walk.supportIndex P.path (X.endpoints.endpoint 1) <
        Walk.supportIndex P.path (X.endpoints.endpoint 0) ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 0) <
        Walk.supportIndex P.path (X.endpoints.endpoint 3) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  have hrev :=
    GMIX24Split.canonicalOfNoCross_right_cross_endpoint2_off_path_path_order
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)
      (by
        intro i hi
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
          hothers_path i hi)
  exact
    ⟨(P.supportIndex_reverse_lt_iff
        (hothers_path 0 (by decide)) (hothers_path 1 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.2),
      (P.supportIndex_reverse_lt_iff
        (hothers_path 3 (by decide)) (hothers_path 0 (by decide))).mp
        (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using hrev.1)⟩


theorem canonicalOfNoCross_left_cross_first_to_second_single_off_path_order_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {l : Fin 4}
    (hl : l = 1 ∨ l = 3)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet) :
    (l = 1 ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 0) <
          Walk.supportIndex P.path (X.endpoints.endpoint 3) ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 3) <
          Walk.supportIndex P.path (X.endpoints.endpoint 2)) ∨
      (l = 3 ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 2) <
            Walk.supportIndex P.path (X.endpoints.endpoint 1) ∧
          Walk.supportIndex P.path (X.endpoints.endpoint 1) <
            Walk.supportIndex P.path (X.endpoints.endpoint 0)) := by
  rcases hl with rfl | rfl
  · left
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
        P hno_cross X hl_off hothers_path⟩
  · right
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint3_off_path_path_order
        P hno_cross X hl_off hothers_path⟩

theorem canonicalOfNoCross_right_cross_first_to_second_single_off_path_order_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {l : Fin 4}
    (hl : l = 1 ∨ l = 3)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet) :
    (l = 1 ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 2) <
          Walk.supportIndex P.path (X.endpoints.endpoint 3) ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 3) <
          Walk.supportIndex P.path (X.endpoints.endpoint 0)) ∨
      (l = 3 ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 0) <
            Walk.supportIndex P.path (X.endpoints.endpoint 1) ∧
          Walk.supportIndex P.path (X.endpoints.endpoint 1) <
            Walk.supportIndex P.path (X.endpoints.endpoint 2)) := by
  rcases hl with rfl | rfl
  · left
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_right_cross_endpoint1_off_path_path_order
        P hno_cross X hl_off hothers_path⟩
  · right
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_right_cross_endpoint3_off_path_path_order
        P hno_cross X hl_off hothers_path⟩

theorem canonicalOfNoCross_left_cross_second_to_first_single_off_path_order_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    {l : Fin 4}
    (hl : l = 0 ∨ l = 2)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet) :
    (l = 0 ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 3) <
          Walk.supportIndex P.path (X.endpoints.endpoint 2) ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 2) <
          Walk.supportIndex P.path (X.endpoints.endpoint 1)) ∨
      (l = 2 ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 1) <
            Walk.supportIndex P.path (X.endpoints.endpoint 0) ∧
          Walk.supportIndex P.path (X.endpoints.endpoint 0) <
            Walk.supportIndex P.path (X.endpoints.endpoint 3)) := by
  rcases hl with rfl | rfl
  · left
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint0_off_path_path_order
        P hno_cross X hl_off hothers_path⟩
  · right
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint2_off_path_path_order
        P hno_cross X hl_off hothers_path⟩

theorem canonicalOfNoCross_right_cross_second_to_first_single_off_path_order_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    {l : Fin 4}
    (hl : l = 0 ∨ l = 2)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet) :
    (l = 0 ∧
      Walk.supportIndex P.path (X.endpoints.endpoint 1) <
          Walk.supportIndex P.path (X.endpoints.endpoint 2) ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 2) <
          Walk.supportIndex P.path (X.endpoints.endpoint 3)) ∨
      (l = 2 ∧
        Walk.supportIndex P.path (X.endpoints.endpoint 3) <
            Walk.supportIndex P.path (X.endpoints.endpoint 0) ∧
          Walk.supportIndex P.path (X.endpoints.endpoint 0) <
            Walk.supportIndex P.path (X.endpoints.endpoint 1)) := by
  rcases hl with rfl | rfl
  · left
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_right_cross_endpoint0_off_path_path_order
        P hno_cross X hl_off hothers_path⟩
  · right
    exact ⟨rfl,
      GMIX24Split.canonicalOfNoCross_right_cross_endpoint2_off_path_path_order
        P hno_cross X hl_off hothers_path⟩


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
