import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.SourceFacts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
private theorem canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_aux
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3} {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg i).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff : ∀ j : Fin 3, j ≠ i → T.boundary j ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      ∀ w : V, w ∈ q.support →
        (Exists fun j : Fin 3 =>
          w ∈ (T.rim j).support ∨ w ∈ (T.leg j).support) →
          w = x) :
    Nonempty S.Tripod := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  have ha_ne_other : ∀ j : Fin 3, j ≠ i → a ≠ T.boundary j := by
    intro j hij
    exact T.clean_tail_from_leg_hit_ne_other_boundary (fun h => hij h.symm)
      hx q hq_clean_vertex
  refine ⟨T.liftReplaceBoundaryOnLegWithTail
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    hx ?_ (P.leftBoundaryArc_subset ha) ha_ne_other q hq_path
    hq_clean_vertex⟩
  intro j hji
  exact P.leftBoundaryArc_subset
    ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T j).mp (hoff j hji))

theorem canonicalOfNoCross_left_tripod_lift_of_leg0_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg 0).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff1 : T.boundary 1 ∉ P.pathSet)
    (hoff2 : T.boundary 2 ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  apply canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hx ha _ hq_path hq_clean
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · exact hoff1
  · exact hoff2

theorem canonicalOfNoCross_left_tripod_lift_of_leg1_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg 1).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff0 : T.boundary 0 ∉ P.pathSet)
    (hoff2 : T.boundary 2 ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  apply canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hx ha _ hq_path hq_clean
  intro j hj
  fin_cases j
  · exact hoff0
  · exact (hj rfl).elim
  · exact hoff2

theorem canonicalOfNoCross_left_tripod_lift_of_leg2_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg 2).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hoff0 : T.boundary 0 ∉ P.pathSet)
    (hoff1 : T.boundary 1 ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  apply canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hx ha _ hq_path hq_clean
  intro j hj
  fin_cases j
  · exact hoff0
  · exact hoff1
  · exact (hj rfl).elim

private theorem canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_aux
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3} {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg i).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff : ∀ j : Fin 3, j ≠ i → T.boundary j ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      ∀ w : V, w ∈ q.support →
        (Exists fun j : Fin 3 =>
          w ∈ (T.rim j).support ∨ w ∈ (T.leg j).support) →
          w = x) :
    Nonempty S.Tripod := by
  classical
  let Trev := canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  exact canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_aux
    P.reverse hno_cross Trev q
    (by simpa [Trev] using hx)
    (by simpa using ha)
    (by
      intro j hji
      simpa [Trev] using hoff j hji)
    hq_path
    (by
      intro w hw hwT
      exact hq_clean w hw (by simpa [Trev] using hwT))

theorem canonicalOfNoCross_right_tripod_lift_of_leg0_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg 0).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff1 : T.boundary 1 ∉ P.pathSet)
    (hoff2 : T.boundary 2 ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  apply canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hx ha _ hq_path hq_clean
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · exact hoff1
  · exact hoff2

theorem canonicalOfNoCross_right_tripod_lift_of_leg1_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg 1).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff0 : T.boundary 0 ∉ P.pathSet)
    (hoff2 : T.boundary 2 ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  apply canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hx ha _ hq_path hq_clean
  intro j hj
  fin_cases j
  · exact hoff0
  · exact (hj rfl).elim
  · exact hoff2

theorem canonicalOfNoCross_right_tripod_lift_of_leg2_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg 2).support)
    (ha : a ∈ P.rightBoundaryArc)
    (hoff0 : T.boundary 0 ∉ P.pathSet)
    (hoff1 : T.boundary 1 ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  apply canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hx ha _ hq_path hq_clean
  intro j hj
  fin_cases j
  · exact hoff0
  · exact hoff1
  · exact (hj rfl).elim

theorem canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ (T.leg i).support ∧
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  rcases hx with ⟨i, hxi, hoff⟩
  exact canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hxi ha hoff hq_path hq_clean

theorem canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ (T.leg i).support ∧
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  rcases hx with ⟨i, hxi, hoff⟩
  exact canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_aux
    P hno_cross T q hxi ha hoff hq_path hq_clean

theorem canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {x y : V} (q : S.graph.Walk x y)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ (T.leg i).support ∧
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  rcases hx with ⟨i, hxi, hoff⟩
  have hy_ne_other :
      forall j : Fin 3, j ≠ i -> y ≠ T.boundary j := by
    intro j hij
    exact T.clean_tail_from_leg_hit_ne_other_boundary (fun h => hij h.symm) hxi q
      hq_clean_vertex
  refine ⟨T.liftReplaceBoundaryOnLegWithTail
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    hxi ?_ hy_boundary hy_ne_other q hq_path hq_clean_vertex⟩
  intro j hji
  exact P.leftBoundaryArc_subset
    ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T j).mp (hoff j hji))

theorem canonicalOfNoCross_right_tripod_lift_of_leg_clean_tail_to_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {x y : V} (q : S.graph.Walk x y)
    (hx :
      Exists fun i : Fin 3 =>
        x ∈ (T.leg i).support ∧
          forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hy_boundary : y ∈ S.boundarySet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
          w = x) :
    Nonempty S.Tripod := by
  classical
  let Trev := canonicalOfNoCross.rightTripodOnReverse P hno_cross T
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_leg_clean_tail_to_boundary
      P.reverse hno_cross Trev q
      (by simpa [Trev] using hx)
      hy_boundary hq_path
      (by
        intro w hw hwT
        exact hq_clean w hw
          (by simpa [Trev] using hwT))

theorem canonicalOfNoCross_left_tripod_lift_replace_boundary_foot_with_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3} {y : V}
    (q : S.graph.Walk (T.boundary i) y)
    (hy_boundary : y ∈ S.boundarySet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  have hy_ne_other :
      forall j : Fin 3, j ≠ i -> y ≠ T.boundary j := by
    intro j hij
    exact T.clean_tail_from_leg_hit_ne_other_boundary (fun h => hij h.symm)
      (T.leg i).end_mem_support q hq_clean_vertex
  refine ⟨T.liftReplaceBoundaryOnLegWithTail
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (T.leg i).end_mem_support ?_ hy_boundary hy_ne_other
    q hq_path hq_clean_vertex⟩
  intro j hji
  exact P.leftBoundaryArc_subset
    ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T j).mp (hoff j hji))

theorem canonicalOfNoCross_right_tripod_lift_replace_boundary_foot_with_clean_tail
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3} {y : V}
    (q : S.graph.Walk (T.boundary i) y)
    (hy_boundary : y ∈ S.boundarySet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hq_path : q.IsPath)
    (hq_clean :
      forall w : V, w ∈ q.support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod := by
  have hq_clean_vertex := T.clean_vertex_of_branch_clean q hq_clean
  have hy_ne_other :
      forall j : Fin 3, j ≠ i -> y ≠ T.boundary j := by
    intro j hij
    exact T.clean_tail_from_leg_hit_ne_other_boundary (fun h => hij h.symm)
      (T.leg i).end_mem_support q hq_clean_vertex
  refine ⟨T.liftReplaceBoundaryOnLegWithTail
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le
    (T.leg i).end_mem_support ?_ hy_boundary hy_ne_other
    q hq_path hq_clean_vertex⟩
  intro j hji
  exact P.rightBoundaryArc_subset
    ((GMIX24Split.canonicalOfNoCross_right_tripod_boundary_not_path_iff_arc
      P hno_cross T j).mp (hoff j hji))

theorem canonicalOfNoCross_left_tripod_lift_replace_path_foot_to_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hclean :
      forall w : V, w ∈ (P.pathTailToStart hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_boundary_foot_with_clean_tail
    P hno_cross T (P.pathTailToStart hpath) P.s_mem_boundary hoff
    (P.pathTailToStart_isPath hpath) hclean

theorem canonicalOfNoCross_left_tripod_lift_replace_path_foot_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hclean :
      forall w : V, w ∈ (P.pathTailToEnd hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_boundary_foot_with_clean_tail
    P hno_cross T (P.pathTailToEnd hpath) P.t_mem_boundary hoff
    (P.pathTailToEnd_isPath hpath) hclean

theorem canonicalOfNoCross_right_tripod_lift_replace_path_foot_to_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hclean :
      forall w : V, w ∈ (P.pathTailToStart hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_boundary_foot_with_clean_tail
    P hno_cross T (P.pathTailToStart hpath) P.s_mem_boundary hoff
    (P.pathTailToStart_isPath hpath) hclean

theorem canonicalOfNoCross_right_tripod_lift_replace_path_foot_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hclean :
      forall w : V, w ∈ (P.pathTailToEnd hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_boundary_foot_with_clean_tail
    P hno_cross T (P.pathTailToEnd hpath) P.t_mem_boundary hoff
    (P.pathTailToEnd_isPath hpath) hclean

theorem canonicalOfNoCross_left_tripod_lift_replace_isolated_path_foot_to_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hpath_clean :
      forall w : V, w ∈ P.pathSet ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_path_foot_to_start
    P hno_cross T hpath hoff (by
      intro w hw hT
      exact hpath_clean w (P.pathTailToStart_support_subset_pathSet hpath w hw) hT)

theorem canonicalOfNoCross_left_tripod_lift_replace_isolated_path_foot_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hpath_clean :
      forall w : V, w ∈ P.pathSet ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_path_foot_to_end
    P hno_cross T hpath hoff (by
      intro w hw hT
      exact hpath_clean w (P.pathTailToEnd_support_subset_pathSet hpath w hw) hT)

theorem canonicalOfNoCross_right_tripod_lift_replace_isolated_path_foot_to_start
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hpath_clean :
      forall w : V, w ∈ P.pathSet ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_path_foot_to_start
    P hno_cross T hpath hoff (by
      intro w hw hT
      exact hpath_clean w (P.pathTailToStart_support_subset_pathSet hpath w hw) hT)

theorem canonicalOfNoCross_right_tripod_lift_replace_isolated_path_foot_to_end
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet)
    (hpath_clean :
      forall w : V, w ∈ P.pathSet ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_path_foot_to_end
    P hno_cross T hpath hoff (by
      intro w hw hT
      exact hpath_clean w (P.pathTailToEnd_support_subset_pathSet hpath w hw) hT)

theorem canonicalOfNoCross_left_tripod_nonisolated_path_contact_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun w : V =>
      w ∈ P.pathSet ∧
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ∧
        w ≠ T.boundary i := by
  by_contra hnone
  push Not at hnone
  have hpath_clean :
      forall w : V, w ∈ P.pathSet ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i := by
    intro w hw hT
    by_contra hne
    exact hne (hnone w hw hT)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_isolated_path_foot_to_start
      P hno_cross T hpath hoff hpath_clean)

theorem canonicalOfNoCross_right_tripod_nonisolated_path_contact_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun w : V =>
      w ∈ P.pathSet ∧
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ∧
        w ≠ T.boundary i := by
  by_contra hnone
  push Not at hnone
  have hpath_clean :
      forall w : V, w ∈ P.pathSet ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i := by
    intro w hw hT
    by_contra hne
    exact hne (hnone w hw hT)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_isolated_path_foot_to_start
      P hno_cross T hpath hoff hpath_clean)

theorem canonicalOfNoCross_left_tripod_pathTailToStart_has_other_contact_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun w : V =>
      w ∈ (P.pathTailToStart hpath).support ∧
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ∧
        w ≠ T.boundary i := by
  by_contra hnone
  push Not at hnone
  have hclean :
      forall w : V, w ∈ (P.pathTailToStart hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i := by
    intro w hw hT
    by_contra hne
    exact hne (hnone w hw hT)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_path_foot_to_start
      P hno_cross T hpath hoff hclean)

theorem canonicalOfNoCross_left_tripod_pathTailToEnd_has_other_contact_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun w : V =>
      w ∈ (P.pathTailToEnd hpath).support ∧
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ∧
        w ≠ T.boundary i := by
  by_contra hnone
  push Not at hnone
  have hclean :
      forall w : V, w ∈ (P.pathTailToEnd hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i := by
    intro w hw hT
    by_contra hne
    exact hne (hnone w hw hT)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_left_tripod_lift_replace_path_foot_to_end
      P hno_cross T hpath hoff hclean)

theorem canonicalOfNoCross_right_tripod_pathTailToStart_has_other_contact_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun w : V =>
      w ∈ (P.pathTailToStart hpath).support ∧
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ∧
        w ≠ T.boundary i := by
  by_contra hnone
  push Not at hnone
  have hclean :
      forall w : V, w ∈ (P.pathTailToStart hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i := by
    intro w hw hT
    by_contra hne
    exact hne (hnone w hw hT)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_path_foot_to_start
      P hno_cross T hpath hoff hclean)

theorem canonicalOfNoCross_right_tripod_pathTailToEnd_has_other_contact_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i : Fin 3}
    (hpath : T.boundary i ∈ P.pathSet)
    (hoff : forall j : Fin 3, j ≠ i -> T.boundary j ∉ P.pathSet) :
    Exists fun w : V =>
      w ∈ (P.pathTailToEnd hpath).support ∧
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ∧
        w ≠ T.boundary i := by
  by_contra hnone
  push Not at hnone
  have hclean :
      forall w : V, w ∈ (P.pathTailToEnd hpath).support ->
        (Exists fun k : Fin 3 =>
          w ∈ (T.rim k).support ∨ w ∈ (T.leg k).support) ->
          w = T.boundary i := by
    intro w hw hT
    by_contra hne
    exact hne (hnone w hw hT)
  exact hno_tripod
    (GMIX24Split.canonicalOfNoCross_right_tripod_lift_replace_path_foot_to_end
      P hno_cross T hpath hoff hclean)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
