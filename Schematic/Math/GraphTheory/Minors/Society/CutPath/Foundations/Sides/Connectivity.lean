import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Sides.BoundaryOrder

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

theorem leftSide_subset_outside [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftSide ⊆ P.outside := by
  simpa [leftSide] using
    ComponentUnionMeeting_subset S.graph P.leftBoundaryArc P.outside

theorem rightSide_subset_outside [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightSide ⊆ P.outside := by
  simpa [rightSide] using
    ComponentUnionMeeting_subset S.graph P.rightBoundaryArc P.outside

theorem leftBoundaryArc_subset_leftSide [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArc ⊆ P.leftSide := by
  simpa [leftSide] using
    subset_ComponentUnionMeeting_of_subset S.graph
      P.leftBoundaryArc_subset_outside

theorem rightBoundaryArc_subset_rightSide [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightBoundaryArc ⊆ P.rightSide := by
  simpa [rightSide] using
    subset_ComponentUnionMeeting_of_subset S.graph
      P.rightBoundaryArc_subset_outside

theorem leftSide_caught [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    Catches S.graph P.leftBoundaryArc P.leftSide := by
  simpa [leftSide] using
    ComponentUnionMeeting_catches S.graph
      P.leftBoundaryArc_subset_outside

theorem rightSide_caught [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    Catches S.graph P.rightBoundaryArc P.rightSide := by
  simpa [rightSide] using
    ComponentUnionMeeting_catches S.graph
      P.rightBoundaryArc_subset_outside

theorem outside_subset_leftSide_union_rightSide [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.outside ⊆ P.leftSide ∪ P.rightSide := by
  intro v hv
  let C : (S.graph.induce P.outside).ConnectedComponent :=
    (S.graph.induce P.outside).connectedComponentMk ⟨v, hv⟩
  obtain ⟨a, haX, haBoundary, haC⟩ := P.caught_outside.2 C
  have haArc : a ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
    rw [P.leftBoundaryArc_union_right]
    exact haBoundary
  rcases haArc with haLeft | haRight
  · left
    refine ⟨hv, C, SimpleGraph.ConnectedComponent.connectedComponentMk_mem,
      a, ?_, haLeft, haC⟩
    simpa [outside] using haX
  · right
    refine ⟨hv, C, SimpleGraph.ConnectedComponent.connectedComponentMk_mem,
      a, ?_, haRight, haC⟩
    simpa [outside] using haX

theorem leftSide_union_rightSide_eq_outside [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.leftSide ∪ P.rightSide = P.outside := by
  apply Set.Subset.antisymm
  · intro v hv
    rcases hv with hvLeft | hvRight
    · exact P.leftSide_subset_outside hvLeft
    · exact P.rightSide_subset_outside hvRight
  · exact P.outside_subset_leftSide_union_rightSide

theorem exists_outside_path_of_leftSide_rightSide [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {v : V}
    (hvLeft : v ∈ P.leftSide) (hvRight : v ∈ P.rightSide) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun q : S.graph.Walk a b =>
          a ∈ P.leftBoundaryArc ∧ b ∈ P.rightBoundaryArc ∧
            q.IsPath ∧
              forall z : V, z ∈ q.support -> z ∈ P.outside := by
  simpa [leftSide, rightSide] using
    exists_path_between_component_unions
      (G := S.graph) (A := P.leftBoundaryArc)
      (B := P.rightBoundaryArc) (X := P.outside)
      hvLeft hvRight

theorem exists_boundary_clean_outside_arc_path [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a b : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.rightBoundaryArc)
    {q : S.graph.Walk a b}
    (hq_path : q.IsPath)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside) :
    Exists fun a' : V =>
      Exists fun b' : V =>
        Exists fun r : S.graph.Walk a' b' =>
          a' ∈ P.leftBoundaryArc ∧ b' ∈ P.rightBoundaryArc ∧
            r.IsPath ∧
              (forall z : V, z ∈ r.support -> z ∈ P.outside) ∧
                Walk.InternalVertices r ∩ S.boundarySet = ∅ := by
  classical
  let Q : Nat -> Prop := fun n =>
    forall {a b : V}
      (ha : a ∈ P.leftBoundaryArc)
      (hb : b ∈ P.rightBoundaryArc)
      {q : S.graph.Walk a b},
        q.IsPath ->
          (forall z : V, z ∈ q.support -> z ∈ P.outside) ->
            q.length = n ->
              Exists fun a' : V =>
                Exists fun b' : V =>
                  Exists fun r : S.graph.Walk a' b' =>
                    a' ∈ P.leftBoundaryArc ∧ b' ∈ P.rightBoundaryArc ∧
                      r.IsPath ∧
                        (forall z : V, z ∈ r.support -> z ∈ P.outside) ∧
                          Walk.InternalVertices r ∩ S.boundarySet = ∅
  have hQ : forall n : Nat, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b ha hb q hq_path hq_outside hlen
      by_cases hclean :
          Walk.InternalVertices q ∩ S.boundarySet = ∅
      · exact ⟨a, b, q, ha, hb, hq_path, hq_outside, hclean⟩
      · have hnonempty :
            (Walk.InternalVertices q ∩ S.boundarySet).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          exact hclean
        rcases hnonempty with ⟨x, hx⟩
        have hx_internal : x ∈ Walk.InternalVertices q := hx.1
        have hx_boundary : x ∈ S.boundarySet := hx.2
        have hx_support : x ∈ q.support := hx_internal.1
        have hxa : x ≠ a := hx_internal.2.1
        have hxb : x ≠ b := hx_internal.2.2
        have hx_outside : x ∈ P.outside := hq_outside x hx_support
        have hx_not_endpoints : x ∉ ({P.s, P.t} : Set V) := by
          intro hxst
          rcases hxst with hxs | hxt
          · subst x
            exact P.s_not_mem_outside hx_outside
          · subst x
            exact P.t_not_mem_outside hx_outside
        have hx_arc : x ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
          rw [P.leftBoundaryArc_union_right]
          exact ⟨hx_boundary, hx_not_endpoints⟩
        rcases hx_arc with hx_left | hx_right
        · let q' : S.graph.Walk x b := q.dropUntil x hx_support
          have hq'_path : q'.IsPath := by
            simpa [q'] using hq_path.dropUntil hx_support
          have hq'_outside :
              forall z : V, z ∈ q'.support -> z ∈ P.outside := by
            intro z hz
            exact hq_outside z
              (SimpleGraph.Walk.support_dropUntil_subset q hx_support hz)
          have hlt : q'.length < n := by
            have hdrop :
                q'.length < q.length := by
              simpa [q'] using
                Walk.length_dropUntil_lt_of_mem_support_ne_start
                  hx_support hxa
            omega
          exact ih q'.length hlt hx_left hb hq'_path hq'_outside rfl
        · let q' : S.graph.Walk a x := q.takeUntil x hx_support
          have hq'_path : q'.IsPath := by
            simpa [q'] using hq_path.takeUntil hx_support
          have hq'_outside :
              forall z : V, z ∈ q'.support -> z ∈ P.outside := by
            intro z hz
            exact hq_outside z
              (SimpleGraph.Walk.support_takeUntil_subset q hx_support hz)
          have hlt : q'.length < n := by
            have htake :
                q'.length < q.length := by
              simpa [q'] using
                SimpleGraph.Walk.length_takeUntil_lt hx_support hxb
            omega
          exact ih q'.length hlt ha hx_right hq'_path hq'_outside rfl
  exact hQ q.length ha hb hq_path hq_outside rfl

theorem exists_path_from_leftSide_to_leftBoundaryArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.leftSide) :
    Exists fun a : V =>
      Exists fun q : S.graph.Walk v a =>
        a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
          forall z : V, z ∈ q.support -> z ∈ P.outside := by
  simpa [leftSide] using
    exists_path_to_component_union_witness
      (G := S.graph) (A := P.leftBoundaryArc)
      (X := P.outside) hv

theorem exists_path_from_leftSide_to_leftBoundaryArc_inside [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.leftSide) :
    Exists fun a : V =>
      Exists fun q : S.graph.Walk v a =>
        a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
            forall z : V, z ∈ q.support -> z ∈ P.outside := by
  simpa [leftSide] using
    exists_path_to_component_union_witness_inside
      (G := S.graph) (A := P.leftBoundaryArc)
      (X := P.outside) hv

/-- Component-preserving form of the left-side escape path.

Besides the boundary witness and path, this exposes the actual connected
component of `G - V(P)` containing the starting vertex.  Consequently two
such paths obtained from unequal components are disjoint without any further
uncrossing. -/
theorem exists_path_from_leftSide_to_leftBoundaryArc_in_outsideComponent
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.leftSide) :
    Exists fun hvOutside : v ∈ P.outside =>
      Exists fun C : (S.graph.induce P.outside).ConnectedComponent =>
        (⟨v, hvOutside⟩ : P.outside) ∈ C.supp ∧
          Exists fun a : V =>
            Exists fun q : S.graph.Walk v a =>
              a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
                forall z : V, z ∈ q.support ->
                  z ∈ induceComponentSupport (G := S.graph) C := by
  classical
  change v ∈
    ComponentUnionMeeting S.graph P.leftBoundaryArc P.outside at hv
  rcases hv with ⟨hvOutside, C, hvC, a, haOutside, haArc, haC⟩
  obtain ⟨q, hqPath, hqComponent⟩ :=
    exists_path_in_induceComponentSupport S.graph C
      hvOutside haOutside hvC haC
  exact ⟨hvOutside, C, hvC, a, q, haArc, hqPath, hqComponent⟩

theorem exists_path_from_rightSide_to_rightBoundaryArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.rightSide) :
    Exists fun a : V =>
      Exists fun q : S.graph.Walk v a =>
        a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
          forall z : V, z ∈ q.support -> z ∈ P.outside := by
  simpa using
    P.reverse.exists_path_from_leftSide_to_leftBoundaryArc (by simpa using hv)

theorem exists_path_from_rightSide_to_rightBoundaryArc_inside [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.rightSide) :
    Exists fun a : V =>
      Exists fun q : S.graph.Walk v a =>
        a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support -> z ∈ P.rightSide) ∧
            forall z : V, z ∈ q.support -> z ∈ P.outside := by
  simpa using
    P.reverse.exists_path_from_leftSide_to_leftBoundaryArc_inside
      (by simpa using hv)

theorem cross_of_outside_arc_path [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a b : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.rightBoundaryArc)
    {q : S.graph.Walk a b}
    (hq_path : q.IsPath)
    (hq_outside : forall v : V, v ∈ q.support -> v ∈ P.outside)
    (hq_internal_boundary :
      Walk.InternalVertices q ∩ S.boundarySet = ∅) :
    Nonempty S.Cross := by
  classical
  have ha_open : S.boundary.ClockwiseOpenBetween P.s P.t a := by
    simpa [leftBoundaryArc] using ha
  have hb_open : S.boundary.ClockwiseOpenBetween P.t P.s b := by
    simpa [rightBoundaryArc] using hb
  have hs_ne_a : P.s ≠ a := by
    intro h
    exact ha_open.2.1 h.symm
  have hs_ne_b : P.s ≠ b := by
    intro h
    exact hb_open.2.2 h.symm
  have ht_ne_a : P.t ≠ a := by
    intro h
    exact ha_open.2.2 h.symm
  have ht_ne_b : P.t ≠ b := by
    intro h
    exact hb_open.2.1 h.symm
  have ha_ne_b : a ≠ b := by
    intro h
    have hb_left : b ∈ P.leftBoundaryArc := by
      simpa [h] using ha
    exact Set.disjoint_left.mp P.leftBoundaryArc_disjoint_right
      hb_left hb
  let endpoint : Fin 4 -> V
    | 0 => P.s
    | 1 => a
    | 2 => P.t
    | 3 => b
  have endpoint_mem : forall i : Fin 4, endpoint i ∈ S.boundary.vertexSet := by
    intro i
    fin_cases i
    · exact P.s_mem_boundary
    · exact P.leftBoundaryArc_subset ha
    · exact P.t_mem_boundary
    · exact P.rightBoundaryArc_subset hb
  have endpoint_injective : Function.Injective endpoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [endpoint] at hij ⊢ <;>
      first
      | rfl
      | exact False.elim (hs_ne_a hij)
      | exact False.elim (hs_ne_a hij.symm)
      | exact False.elim (hs_ne_b hij)
      | exact False.elim (hs_ne_b hij.symm)
      | exact False.elim (P.s_ne_t hij)
      | exact False.elim (P.s_ne_t hij.symm)
      | exact False.elim (ht_ne_a hij)
      | exact False.elim (ht_ne_a hij.symm)
      | exact False.elim (ht_ne_b hij)
      | exact False.elim (ht_ne_b hij.symm)
      | exact False.elim (ha_ne_b hij)
      | exact False.elim (ha_ne_b hij.symm)
  refine ⟨{
    endpoints := {
      endpoint := endpoint
      endpoint_mem := endpoint_mem
      endpoint_injective := endpoint_injective
      cyclic_alternating := by
        have ha_open' :
            @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
              S.boundary P.s P.t a := by
          simpa [CyclicBoundary.ClockwiseOpenBetween,
            CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using
            ha_open
        have hb_open' :
            @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
              S.boundary P.t P.s b := by
          simpa [CyclicBoundary.ClockwiseOpenBetween,
            CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using
            hb_open
        dsimp [CrossEndpointAlternating, endpoint]
        exact ⟨ha_open', hb_open'⟩
    }
    firstPath := P.path
    secondPath := q
    firstPath_isPath := P.path_isPath
    secondPath_isPath := hq_path
    firstPath_nontrivial := ?_
    secondPath_nontrivial := ?_
    paths_disjoint := ?_
    first_internal_boundary := P.internal_disjoint_boundary
    second_internal_boundary := hq_internal_boundary
  }⟩
  · intro hlen
    exact P.s_ne_t (SimpleGraph.Walk.eq_of_length_eq_zero hlen)
  · intro hlen
    exact ha_ne_b (SimpleGraph.Walk.eq_of_length_eq_zero hlen)
  · rw [Set.disjoint_left]
    intro v hvP hvq
    exact (hq_outside v hvq).2 hvP

theorem no_cross_forbids_outside_arc_path [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {a b : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.rightBoundaryArc)
    {q : S.graph.Walk a b}
    (hq_path : q.IsPath)
    (hq_outside : forall v : V, v ∈ q.support -> v ∈ P.outside)
    (hq_internal_boundary :
      Walk.InternalVertices q ∩ S.boundarySet = ∅) :
    False :=
  hno_cross
    (P.cross_of_outside_arc_path ha hb hq_path hq_outside
      hq_internal_boundary)

theorem leftSide_disjoint_rightSide_of_no_cross [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    Disjoint P.leftSide P.rightSide := by
  rw [Set.disjoint_left]
  intro v hvLeft hvRight
  obtain ⟨a, b, q, ha, hb, hq_path, hq_outside⟩ :=
    P.exists_outside_path_of_leftSide_rightSide hvLeft hvRight
  obtain ⟨a', b', r, ha', hb', hr_path, hr_outside,
      hr_internal_boundary⟩ :=
    P.exists_boundary_clean_outside_arc_path ha hb hq_path hq_outside
  exact
    P.no_cross_forbids_outside_arc_path hno_cross ha' hb'
      hr_path hr_outside hr_internal_boundary

theorem boundary_mem_leftSide_of_no_cross [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {v : V}
    (hvBoundary : v ∈ S.boundarySet)
    (hvLeft : v ∈ P.leftSide) :
    v ∈ P.leftBoundaryArc := by
  have hvOutside : v ∈ P.outside := P.leftSide_subset_outside hvLeft
  have hvNotPath : v ∉ P.pathSet := by
    simpa [GMIX24CutPath.pathSet] using hvOutside.2
  have hvs : v ≠ P.s := by
    intro h
    exact hvNotPath (by simp [GMIX24CutPath.pathSet, h])
  have hvt : v ≠ P.t := by
    intro h
    exact hvNotPath (by simp [GMIX24CutPath.pathSet, h])
  have hvArc : v ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
    rw [P.leftBoundaryArc_union_right]
    exact ⟨hvBoundary, by
      intro hvst
      rcases hvst with hvs' | hvt'
      · exact hvs hvs'
      · exact hvt hvt'⟩
  rcases hvArc with hvLeftArc | hvRightArc
  · exact hvLeftArc
  · exact False.elim
      (Set.disjoint_left.mp
        (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
        hvLeft (P.rightBoundaryArc_subset_rightSide hvRightArc))

theorem boundary_mem_rightSide_of_no_cross [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {v : V}
    (hvBoundary : v ∈ S.boundarySet)
    (hvRight : v ∈ P.rightSide) :
    v ∈ P.rightBoundaryArc := by
  simpa using
    P.reverse.boundary_mem_leftSide_of_no_cross hno_cross hvBoundary
      (by simpa using hvRight)

theorem exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) {v : V}
    (hv : v ∈ P.leftSide) :
    Exists fun a : V =>
      Exists fun q : S.graph.Walk v a =>
        a ∈ P.leftBoundaryArc ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support -> z ∈ P.leftSide) ∧
            (forall z : V, z ∈ q.support -> z ∈ P.outside) ∧
              Walk.InternalVertices q ∩ S.boundarySet = ∅ := by
  classical
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside hv
  obtain ⟨x, hxq, hxBoundary, hfirstBoundary⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) hqPath S.boundarySet (P.leftBoundaryArc_subset ha)
  let pref : S.graph.Walk v x := q.takeUntil x hxq
  have hxLeft : x ∈ P.leftSide := hqLeft x hxq
  have hxArc : x ∈ P.leftBoundaryArc :=
    P.boundary_mem_leftSide_of_no_cross hno_cross hxBoundary hxLeft
  refine ⟨x, pref, hxArc, ?_, ?_, ?_, ?_⟩
  · simpa [pref] using hqPath.takeUntil hxq
  · intro z hz
    exact hqLeft z (SimpleGraph.Walk.support_takeUntil_subset q hxq
      (by simpa [pref] using hz))
  · intro z hz
    exact hqOutside z (SimpleGraph.Walk.support_takeUntil_subset q hxq
      (by simpa [pref] using hz))
  · rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzInternal : z ∈ Walk.InternalVertices pref := hz.1
    have hzBoundary : z ∈ S.boundarySet := hz.2
    have hz_eq_x : z = x :=
      hfirstBoundary z (by simpa [pref] using hzInternal.1)
        hzBoundary
    exact hzInternal.2.2 hz_eq_x

theorem exists_path_from_rightSide_to_rightBoundaryArc_inside_boundary_clean
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) {v : V}
    (hv : v ∈ P.rightSide) :
    Exists fun a : V =>
      Exists fun q : S.graph.Walk v a =>
        a ∈ P.rightBoundaryArc ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support -> z ∈ P.rightSide) ∧
            (forall z : V, z ∈ q.support -> z ∈ P.outside) ∧
              Walk.InternalVertices q ∩ S.boundarySet = ∅ := by
  simpa using
    P.reverse.exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
      hno_cross (by simpa using hv)

/-- Clean last-contact tail from the end of an arbitrary path to the left
boundary arc.

Starting with a path-like object whose endpoint lies on the left side, choose a
boundary-clean path from that endpoint to the left boundary arc, then drop it
at the last vertex where it meets the original object's support.  This is the
source proof's reusable "clean tail" move in the left side. -/
theorem exists_clean_tail_from_path_target_to_leftBoundaryArc
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {z v : V} (r : S.graph.Walk z v)
    (hv : v ∈ P.leftSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ r.support ∧
            a ∈ P.leftBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.leftSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ r.support -> w = x := by
  classical
  obtain ⟨a, q, ha, hqPath, hqLeft, hqOutside, hqBoundaryClean⟩ :=
    P.exists_path_from_leftSide_to_leftBoundaryArc_inside_boundary_clean
      hno_cross hv
  let A : Set V := {w : V | w ∈ r.support}
  have hvA : v ∈ A := by
    simp [A]
  obtain ⟨x, hxq, hxA, htail_path, htail_clean, htail_subset,
      _htail_covers, _htail_index⟩ :=
    Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
      (G := S.graph) hqPath A hvA
  let tail : S.graph.Walk x a := q.dropUntil x hxq
  have htail_boundary_clean :
      Walk.InternalVertices tail ∩ S.boundarySet = ∅ := by
    simpa [tail] using
      Walk.IsPath.dropUntil_internalVertices_disjoint_of_internalVertices_disjoint
        hqPath hxq S.boundarySet hqBoundaryClean
  refine ⟨x, a, tail, ?_, ha, ?_, ?_, ?_, htail_boundary_clean, ?_⟩
  · simpa [A] using hxA
  · simpa [tail] using htail_path
  · intro w hw
    exact hqLeft w (htail_subset w (by simpa [tail] using hw))
  · intro w hw
    exact hqOutside w (htail_subset w (by simpa [tail] using hw))
  · intro w hw hwr
    exact htail_clean w (by simpa [tail] using hw) (by simpa [A] using hwr)

/-- Clean last-contact tail from the end of an arbitrary path to the right
boundary arc. -/
theorem exists_clean_tail_from_path_target_to_rightBoundaryArc
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {z v : V} (r : S.graph.Walk z v)
    (hv : v ∈ P.rightSide) :
    Exists fun x : V =>
      Exists fun a : V =>
        Exists fun tail : S.graph.Walk x a =>
          x ∈ r.support ∧
            a ∈ P.rightBoundaryArc ∧ tail.IsPath ∧
              (forall w : V, w ∈ tail.support -> w ∈ P.rightSide) ∧
                (forall w : V, w ∈ tail.support -> w ∈ P.outside) ∧
                  Walk.InternalVertices tail ∩ S.boundarySet = ∅ ∧
                    forall w : V,
                      w ∈ tail.support -> w ∈ r.support -> w = x := by
  simpa using
    P.reverse.exists_clean_tail_from_path_target_to_leftBoundaryArc
      hno_cross r (by simpa using hv)

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
