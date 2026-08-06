import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoCases

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_right_cross_replaceEndpoints01_start_end_original_alternating_of_adjacent01
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (_h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints01 P.s P.t) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  have h2_arc : e 2 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp (by simpa [e] using h2_off)
  have h3_arc : e 3 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 3).mp (by simpa [e] using h3_off)
  have hside :
      CrossEndpointAlternating Ω e := by
    simpa [Ω, e] using
      GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X
  have h20 :
      Ω.indexOf (e 2) < Ω.indexOf (e 0) := by
    simpa [Ω, e] using
      P.rightOrderedCutBoundary_index_arc_lt_path h2_arc h0_path
  have h20C :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using h20
  have h23_le :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
    have hbetween := hside.2.1.2
    change
      (if @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) then
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ∧
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0)
      else
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ∨
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0)) at hbetween
    rw [if_pos (Nat.le_of_lt h20C)] at hbetween
    exact hbetween.1
  have h23_ne_idx :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) ≠
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
    have h2_mem : e 2 ∈ Ω.vertexSet :=
      P.rightBoundaryArc_subset_rightOrderedCutBoundary h2_arc
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
      CyclicBoundary.indexOf_ne_of_ne h2_mem (by
      intro h23
      exact (by decide : (2 : Fin 4) ≠ 3)
        (X.endpoints.endpoint_injective (by simpa [e] using h23)))
  have h23 :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
    omega
  have h3s :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s := by
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using
      P.rightOrderedCutBoundary_index_arc_lt_path h3_arc P.s_mem_pathSet
  have h2s :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s := by
    exact lt_trans h23 h3s
  have h3_ne_2 : e 3 ≠ e 2 := by
    intro h
    have hidx :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) =
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
      simp [h]
    exact h23_ne_idx hidx
  have h3_ne_s : e 3 ≠ P.s := by
    intro h
    exact (P.rightBoundaryArc_subset_outside h3_arc).2
      (by simp [e, h])
  have hside_rot :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ω (e 2) P.s (e 3) := by
    refine ⟨⟨?_, ?_⟩, h3_ne_2, h3_ne_s⟩
    · exact P.rightBoundaryArc_subset_rightOrderedCutBoundary h3_arc
    · change
        (if @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s then
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ∧
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s
        else
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ∨
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s)
      rw [if_pos (Nat.le_of_lt h2s)]
      exact ⟨Nat.le_of_lt h23, Nat.le_of_lt h3s⟩
  have hfirst :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s (e 2) P.t :=
    GMIX24CutPath.rightBoundaryArc_clockwiseOpenBetween_start_arc_end
      P h2_arc
  have hsecond :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary (e 2) P.s (e 3) :=
    P.rightOrdered_clockwiseOpenBetween_original_of_arc_or_start
      (Or.inl h2_arc) (Or.inr rfl) (Or.inl h3_arc) hside_rot
  dsimp [CrossEndpointAlternating, Cross.replaceEndpoints01]
  exact ⟨hfirst, hsecond⟩

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoints01_to_start_end_of_adjacent01
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (h0_not_boundary : X.endpoints.endpoint 0 ∉ S.boundarySet)
    (h1_not_boundary : X.endpoints.endpoint 1 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.rightSociety_graph_le
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.rightSociety_graph_le
  let q0 : S.graph.Walk (X.endpoints.endpoint 0) P.s :=
    P.pathTailToStart h0_path
  let q1 : S.graph.Walk (X.endpoints.endpoint 1) P.t :=
    P.pathTailToEnd h1_path
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 0) <
        Walk.supportIndex P.path (X.endpoints.endpoint 1) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent01_path_order
      P hno_cross X h0_path h1_path h2_off h3_off
  have hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints01 P.s P.t i ∈ S.boundarySet := by
    intro i
    fin_cases i
    · simpa [Cross.replaceEndpoints01, GeneralSociety.boundarySet] using
        P.s_mem_boundary
    · simpa [Cross.replaceEndpoints01, GeneralSociety.boundarySet] using
        P.t_mem_boundary
    · simpa [Cross.replaceEndpoints01, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h2_off
    · simpa [Cross.replaceEndpoints01, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h3_off
  have hendpoint_injective :
      Function.Injective (X.replaceEndpoints01 P.s P.t) :=
    X.replaceEndpoints01_injective P.s_ne_t
      (endpoint_ne_start_of_off_path (P := P) h2_off)
      (endpoint_ne_start_of_off_path (P := P) h3_off)
      (endpoint_ne_end_of_off_path (P := P) h2_off)
      (endpoint_ne_end_of_off_path (P := P) h3_off)
  have halternating :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints01 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints01_start_end_original_alternating_of_adjacent01
      P hno_cross X h0_path h1_path h2_off h3_off
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.secondPath_isPath
  have hx0p : X.endpoints.endpoint 0 ∈ p.support := by
    simp [p]
  have hx1r : X.endpoints.endpoint 1 ∈ r.support := by
    simp [r]
  have hclean0 :
      forall z : V, z ∈ q0.support -> z ∈ p.support ->
        z = X.endpoints.endpoint 0 := by
    intro z hzq hzp
    have hzP : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet h0_path z (by
        simpa [q0] using hzq)
    have hzpX : z ∈ X.firstPath.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hzpX hzP with hz0 | hz2
    · exact hz0
    · exact False.elim (h2_off (by simpa [hz2] using hzP))
  have hclean1 :
      forall z : V, z ∈ q1.support -> z ∈ r.support ->
        z = X.endpoints.endpoint 1 := by
    intro z hzq hzr
    have hzP : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet h1_path z (by
        simpa [q1] using hzq)
    have hzrX : z ∈ X.secondPath.support := by
      simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hzrX hzP with hz1 | hz3
    · exact hz1
    · exact False.elim (h3_off (by simpa [hz3] using hzP))
  have hfirst_path : (q0.reverse.append p).IsPath := by
    have h :=
      Walk.IsPath.reverse_append_dropUntil_of_clean
        hp_path hx0p (P.pathTailToStart_isPath h0_path) hclean0
    simpa [p, q0, SimpleGraph.Walk.dropUntil_first] using h
  have hsecond_path : (q1.reverse.append r).IsPath := by
    have h :=
      Walk.IsPath.reverse_append_dropUntil_of_clean
        hr_path hx1r (P.pathTailToEnd_isPath h1_path) hclean1
    simpa [r, q1, SimpleGraph.Walk.dropUntil_first] using h
  have htail_disjoint :
      Disjoint {z : V | z ∈ q0.support} {z : V | z ∈ q1.support} := by
    simpa [q0, q1] using
      P.pathTailToStart_support_disjoint_pathTailToEnd
        h0_path h1_path horder
  have hq0_not_e1 :
      X.endpoints.endpoint 1 ∉ q0.support := by
    simpa [q0] using
      P.pathTailToStart_not_mem_of_supportIndex_lt
        h0_path horder
  have hq1_not_e0 :
      X.endpoints.endpoint 0 ∉ q1.support := by
    simpa [q1] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt
        h1_path horder
  have hpaths_disjoint :
      Disjoint {z : V | z ∈ (q0.reverse.append p).support}
        {z : V | z ∈ (q1.reverse.append r).support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_first' :
        z ∈ q0.reverse.support ∨ z ∈ p.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_first
    have hz_second' :
        z ∈ q1.reverse.support ∨ z ∈ r.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_second
    rcases hz_first' with hzq0_rev | hzp
    · have hzq0 : z ∈ q0.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzq0_rev
        exact List.mem_reverse.mp hzq0_rev
      rcases hz_second' with hzq1_rev | hzr
      · have hzq1 : z ∈ q1.support := by
          rw [SimpleGraph.Walk.support_reverse] at hzq1_rev
          exact List.mem_reverse.mp hzq1_rev
        exact Set.disjoint_left.mp htail_disjoint hzq0 hzq1
      · have hzP : z ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h0_path z (by
            simpa [q0] using hzq0)
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hzrX hzP with hz1 | hz3
        · exact hq0_not_e1 (by simpa [hz1] using hzq0)
        · exact h3_off (by simpa [hz3] using hzP)
    · rcases hz_second' with hzq1_rev | hzr
      · have hzq1 : z ∈ q1.support := by
          rw [SimpleGraph.Walk.support_reverse] at hzq1_rev
          exact List.mem_reverse.mp hzq1_rev
        have hzP : z ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h1_path z (by
            simpa [q1] using hzq1)
        have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hzpX hzP with hz0 | hz2
        · exact hq1_not_e0 (by simpa [hz0] using hzq1)
        · exact h2_off (by simpa [hz2] using hzP)
      · have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        exact Set.disjoint_left.mp X.paths_disjoint hzpX hzrX
  have hfirst_internal :
      Walk.InternalVertices (q0.reverse.append p) ∩ S.boundarySet = ∅ := by
    have hdrop :
        forall z : V,
          z ∈ (p.dropUntil (X.endpoints.endpoint 0) hx0p).support ->
          z ∈ S.boundarySet ->
            z = X.endpoints.endpoint 0 ∨ z = X.endpoints.endpoint 2 := by
      intro z hz hzB
      exact
        Walk.IsPath.dropUntil_boundary_subset_cut_or_end
          hp_path hx0p S.boundarySet
          (GMIX24Split.canonicalOfNoCross_right_cross_first_internal_boundary_original
            P hno_cross X)
          z hz hzB
    have h :=
      Walk.InternalVertices.reverse_append_dropUntil_boundary_clean
        hx0p hdrop (P.pathTailToStart_internal_boundary_empty h0_path)
        h0_not_boundary
    simpa [p, q0, SimpleGraph.Walk.dropUntil_first] using h
  have hsecond_internal :
      Walk.InternalVertices (q1.reverse.append r) ∩ S.boundarySet = ∅ := by
    have hdrop :
        forall z : V,
          z ∈ (r.dropUntil (X.endpoints.endpoint 1) hx1r).support ->
          z ∈ S.boundarySet ->
            z = X.endpoints.endpoint 1 ∨ z = X.endpoints.endpoint 3 := by
      intro z hz hzB
      exact
        Walk.IsPath.dropUntil_boundary_subset_cut_or_end
          hr_path hx1r S.boundarySet
          (GMIX24Split.canonicalOfNoCross_right_cross_second_internal_boundary_original
            P hno_cross X)
          z hz hzB
    have h :=
      Walk.InternalVertices.reverse_append_dropUntil_boundary_clean
        hx1r hdrop (P.pathTailToEnd_internal_boundary_empty h1_path)
        h1_not_boundary
    simpa [r, q1, SimpleGraph.Walk.dropUntil_first] using h
  exact ⟨
    X.lift_replaceEndpoints01_with_tails
      D.rightSociety_graph_le
      (P.pathTailToStart h0_path) (P.pathTailToEnd h1_path)
      hendpoint_mem hendpoint_injective halternating
      (by simpa [p, q0] using hfirst_path)
      (by simpa [r, q1] using hsecond_path)
      (by simpa [p, r, q0, q1] using hpaths_disjoint)
      (by simpa [p, q0] using hfirst_internal)
      (by simpa [r, q1] using hsecond_internal)⟩

theorem canonicalOfNoCross_left_cross_replaceEndpoints01_end_start_original_alternating_of_adjacent01
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (_h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints01 P.t P.s) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints01_start_end_original_alternating_of_adjacent01
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using _h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off))


theorem canonicalOfNoCross_left_cross_lift_replaceEndpoints01_to_end_start_of_adjacent01
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (h0_not_boundary : X.endpoints.endpoint 0 ∉ S.boundarySet)
    (h1_not_boundary : X.endpoints.endpoint 1 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints01_to_start_end_of_adjacent01
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_not_boundary)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_not_boundary)


theorem canonicalOfNoCross_right_cross_lift_of_adjacent01
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 0) <
        Walk.supportIndex P.path (X.endpoints.endpoint 1) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent01_path_order
      P hno_cross X h0_path h1_path h2_off h3_off
  have halt_pair :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints01 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints01_start_end_original_alternating_of_adjacent01
      P hno_cross X h0_path h1_path h2_off h3_off
  have h0_boundary_eq_start
      (hb0 : X.endpoints.endpoint 0 ∈ S.boundarySet) :
      X.endpoints.endpoint 0 = P.s := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb0 h0_path with h0s | h0t
    · exact h0s
    · exfalso
      have hle :
          Walk.supportIndex P.path (X.endpoints.endpoint 1) <=
            Walk.supportIndex P.path P.t :=
        Walk.IsPath.supportIndex_le_end P.path_isPath
          (by simpa [GMIX24CutPath.pathSet] using h1_path)
      have hbad :
          Walk.supportIndex P.path P.t <
            Walk.supportIndex P.path (X.endpoints.endpoint 1) := by
        simpa [h0t] using horder
      omega
  have h1_boundary_eq_end
      (hb1 : X.endpoints.endpoint 1 ∈ S.boundarySet) :
      X.endpoints.endpoint 1 = P.t := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb1 h1_path with h1s | h1t
    · exfalso
      have hle :
          Walk.supportIndex P.path P.s <=
            Walk.supportIndex P.path (X.endpoints.endpoint 0) :=
        Walk.supportIndex_start_le
          (p := P.path)
      have hbad :
          Walk.supportIndex P.path (X.endpoints.endpoint 0) <
            Walk.supportIndex P.path P.s := by
        simpa [h1s] using horder
      omega
    · exact h1t
  by_cases hb0 : X.endpoints.endpoint 0 ∈ S.boundarySet
  · have h0s := h0_boundary_eq_start hb0
    by_cases hb1 : X.endpoints.endpoint 1 ∈ S.boundarySet
    · have h1t := h1_boundary_eq_end hb1
      have hendpoint_mem :
          forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet := by
        intro i
        fin_cases i
        · simpa [GeneralSociety.boundarySet, h0s] using P.s_mem_boundary
        · simpa [GeneralSociety.boundarySet, h1t] using P.t_mem_boundary
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h2_off
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h3_off
      have halternating :
          CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
        have hfun :
            X.endpoints.endpoint = X.replaceEndpoints01 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoints01, h0s, h1t]
        simpa [hfun] using halt_pair
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_of_original_alternation
          P hno_cross X hendpoint_mem halternating
    · have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint1 P.t i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet, h0s]
            using P.s_mem_boundary
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet]
            using P.t_mem_boundary
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h2_off
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h3_off
      have hinj : Function.Injective (X.replaceEndpoint1 P.t) :=
        X.replaceEndpoint1_injective (by
          intro i hi
          fin_cases i
          · intro h
            exact P.s_ne_t (by simpa [h0s] using h.symm)
          · exact False.elim (hi rfl)
          · exact endpoint_ne_end_of_off_path (P := P) h2_off
          · exact endpoint_ne_end_of_off_path (P := P) h3_off)
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.t) := by
        have hfun :
            X.replaceEndpoint1 P.t = X.replaceEndpoints01 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint1,
            Cross.replaceEndpoints01, h0s]
        simpa [hfun] using halt_pair
      have hq_not_e0 :
          X.endpoints.endpoint 0 ∉ (P.pathTailToEnd h1_path).support := by
        simpa using
          P.pathTailToEnd_not_mem_of_supportIndex_lt h1_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToEnd h1_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 1 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h1_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact False.elim (hq_not_e0 (by simpa [hw0] using hw))
          · exact False.elim (h2_off (by simpa [hw2] using hwP))
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact hw1
          · exact False.elim (h3_off (by simpa [hw3] using hwP))
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail
          P hno_cross X X.secondPath.start_mem_support
          (P.pathTailToEnd h1_path) hendpoint_mem hinj halt
          (P.pathTailToEnd_isPath h1_path)
          (P.pathTailToEnd_internal_boundary_empty h1_path)
          hb1 hclean
  · by_cases hb1 : X.endpoints.endpoint 1 ∈ S.boundarySet
    · have h1t := h1_boundary_eq_end hb1
      have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint0 P.s i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet]
            using P.s_mem_boundary
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet, h1t]
            using P.t_mem_boundary
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h2_off
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h3_off
      have hinj : Function.Injective (X.replaceEndpoint0 P.s) :=
        X.replaceEndpoint0_injective (by
          intro i hi
          fin_cases i
          · exact False.elim (hi rfl)
          · intro h
            exact P.s_ne_t (by simpa [h1t] using h)
          · exact endpoint_ne_start_of_off_path (P := P) h2_off
          · exact endpoint_ne_start_of_off_path (P := P) h3_off)
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.s) := by
        have hfun :
            X.replaceEndpoint0 P.s = X.replaceEndpoints01 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint0,
            Cross.replaceEndpoints01, h1t]
        simpa [hfun] using halt_pair
      have hq_not_e1 :
          X.endpoints.endpoint 1 ∉ (P.pathTailToStart h0_path).support := by
        simpa using
          P.pathTailToStart_not_mem_of_supportIndex_lt h0_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToStart h0_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 0 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h0_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact hw0
          · exact False.elim (h2_off (by simpa [hw2] using hwP))
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact False.elim (hq_not_e1 (by simpa [hw1] using hw))
          · exact False.elim (h3_off (by simpa [hw3] using hwP))
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail
          P hno_cross X X.firstPath.start_mem_support
          (P.pathTailToStart h0_path) hendpoint_mem hinj halt
          (P.pathTailToStart_isPath h0_path)
          (P.pathTailToStart_internal_boundary_empty h0_path)
          hb0 hclean
    · exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints01_to_start_end_of_adjacent01
          P hno_cross X h0_path h1_path h2_off h3_off hb0 hb1

theorem canonicalOfNoCross_left_cross_lift_of_adjacent01
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_of_adjacent01
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off)



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
