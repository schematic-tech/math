import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoCases

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_right_cross_replaceEndpoints23_start_end_original_alternating_of_adjacent23
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (_h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints23 P.s P.t) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  have h0_arc : e 0 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp (by simpa [e] using h0_off)
  have h1_arc : e 1 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 1).mp (by simpa [e] using h1_off)
  have hside :
      CrossEndpointAlternating Ω e := by
    simpa [Ω, e] using
      GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X
  have h02 :
      Ω.indexOf (e 0) < Ω.indexOf (e 2) := by
    simpa [Ω, e] using
      P.rightOrderedCutBoundary_index_arc_lt_path h0_arc h2_path
  have h01 :
      Ω.indexOf (e 0) < Ω.indexOf (e 1) := by
    have h12 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      simpa [Ω, e, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using
        P.rightOrderedCutBoundary_index_arc_lt_path h1_arc h2_path
    have h02C :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
        using h02
    have hbetween := hside.1.1.2
    change
      (if @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) then
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ∧
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2)
      else
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ∨
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2)) at hbetween
    rw [if_pos (Nat.le_of_lt h02C)] at hbetween
    have hle01 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) :=
      hbetween.1
    have hne01 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) ≠
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) := by
      have h0_mem : e 0 ∈ Ω.vertexSet :=
        P.rightBoundaryArc_subset_rightOrderedCutBoundary h0_arc
      simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
        CyclicBoundary.indexOf_ne_of_ne h0_mem (by
        intro h01eq
        exact (by decide : (0 : Fin 4) ≠ 1)
          (X.endpoints.endpoint_injective (by simpa [e] using h01eq)))
    have hlt :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) := by
      omega
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hlt
  have h0s :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s := by
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using
      P.rightOrderedCutBoundary_index_arc_lt_path h0_arc P.s_mem_pathSet
  have h1s :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s := by
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using
      P.rightOrderedCutBoundary_index_arc_lt_path h1_arc P.s_mem_pathSet
  have h1_ne_0 : e 1 ≠ e 0 := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 0)
      (X.endpoints.endpoint_injective (by simpa [e] using h))
  have h1_ne_s : e 1 ≠ P.s := by
    intro h
    exact (P.rightBoundaryArc_subset_outside h1_arc).2
      (by simp [e, h])
  have hside_first :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ω (e 0) P.s (e 1) := by
    refine ⟨⟨?_, ?_⟩, h1_ne_0, h1_ne_s⟩
    · exact P.rightBoundaryArc_subset_rightOrderedCutBoundary h1_arc
    · change
        (if @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s then
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ∧
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s
        else
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ∨
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.s)
      rw [if_pos (Nat.le_of_lt h0s)]
      exact ⟨Nat.le_of_lt (by
        simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
          using h01), Nat.le_of_lt h1s⟩
  have hfirst :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary (e 0) P.s (e 1) :=
    P.rightOrdered_clockwiseOpenBetween_original_of_arc_or_start
      (Or.inl h0_arc) (Or.inr rfl) (Or.inl h1_arc) hside_first
  have hsecond :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s (e 0) P.t :=
    GMIX24CutPath.rightBoundaryArc_clockwiseOpenBetween_start_arc_end
      P h0_arc
  dsimp [CrossEndpointAlternating, Cross.replaceEndpoints23]
  exact ⟨hfirst, hsecond⟩

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoints23_to_start_end_of_adjacent23
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_not_boundary : X.endpoints.endpoint 2 ∉ S.boundarySet)
    (h3_not_boundary : X.endpoints.endpoint 3 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.rightSociety_graph_le
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.rightSociety_graph_le
  let q2 : S.graph.Walk (X.endpoints.endpoint 2) P.s :=
    P.pathTailToStart h2_path
  let q3 : S.graph.Walk (X.endpoints.endpoint 3) P.t :=
    P.pathTailToEnd h3_path
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 2) <
        Walk.supportIndex P.path (X.endpoints.endpoint 3) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent23_path_order
      P hno_cross X h2_path h3_path h0_off
  have hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints23 P.s P.t i ∈ S.boundarySet := by
    intro i
    fin_cases i
    · simpa [Cross.replaceEndpoints23, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h0_off
    · simpa [Cross.replaceEndpoints23, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h1_off
    · simpa [Cross.replaceEndpoints23, GeneralSociety.boundarySet] using
        P.s_mem_boundary
    · simpa [Cross.replaceEndpoints23, GeneralSociety.boundarySet] using
        P.t_mem_boundary
  have hendpoint_injective :
      Function.Injective (X.replaceEndpoints23 P.s P.t) :=
    X.replaceEndpoints23_injective P.s_ne_t
      (endpoint_ne_start_of_off_path (P := P) h0_off)
      (endpoint_ne_start_of_off_path (P := P) h1_off)
      (endpoint_ne_end_of_off_path (P := P) h0_off)
      (endpoint_ne_end_of_off_path (P := P) h1_off)
  have halternating :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints23 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints23_start_end_original_alternating_of_adjacent23
      P hno_cross X h2_path h3_path h0_off h1_off
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.secondPath_isPath
  have hclean2 :
      forall z : V, z ∈ q2.support -> z ∈ p.support ->
        z = X.endpoints.endpoint 2 := by
    intro z hzq hzp
    have hzP : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet h2_path z (by
        simpa [q2] using hzq)
    have hzpX : z ∈ X.firstPath.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hzpX hzP with hz0 | hz2
    · exact False.elim (h0_off (by simpa [hz0] using hzP))
    · exact hz2
  have hclean3 :
      forall z : V, z ∈ q3.support -> z ∈ r.support ->
        z = X.endpoints.endpoint 3 := by
    intro z hzq hzr
    have hzP : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet h3_path z (by
        simpa [q3] using hzq)
    have hzrX : z ∈ X.secondPath.support := by
      simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hzrX hzP with hz1 | hz3
    · exact False.elim (h1_off (by simpa [hz1] using hzP))
    · exact hz3
  have hfirst_path : (p.append q2).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hp_path (P.pathTailToStart_isPath h2_path) ?_
    intro z hzp hzq
    exact hclean2 z hzq hzp
  have hsecond_path : (r.append q3).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hr_path (P.pathTailToEnd_isPath h3_path) ?_
    intro z hzr hzq
    exact hclean3 z hzq hzr
  have htail_disjoint :
      Disjoint {z : V | z ∈ q2.support} {z : V | z ∈ q3.support} := by
    simpa [q2, q3] using
      P.pathTailToStart_support_disjoint_pathTailToEnd
        h2_path h3_path horder
  have hq2_not_e3 :
      X.endpoints.endpoint 3 ∉ q2.support := by
    simpa [q2] using
      P.pathTailToStart_not_mem_of_supportIndex_lt
        h2_path horder
  have hq3_not_e2 :
      X.endpoints.endpoint 2 ∉ q3.support := by
    simpa [q3] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt
        h3_path horder
  have hpaths_disjoint :
      Disjoint {z : V | z ∈ (p.append q2).support}
        {z : V | z ∈ (r.append q3).support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_first' :
        z ∈ p.support ∨ z ∈ q2.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_first
    have hz_second' :
        z ∈ r.support ∨ z ∈ q3.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_second
    rcases hz_first' with hzp | hzq2
    · rcases hz_second' with hzr | hzq3
      · have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        exact Set.disjoint_left.mp X.paths_disjoint hzpX hzrX
      · have hzP : z ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h3_path z (by
            simpa [q3] using hzq3)
        have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hzpX hzP with hz0 | hz2
        · exact h0_off (by simpa [hz0] using hzP)
        · exact hq3_not_e2 (by simpa [hz2] using hzq3)
    · rcases hz_second' with hzr | hzq3
      · have hzP : z ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h2_path z (by
            simpa [q2] using hzq2)
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hzrX hzP with hz1 | hz3
        · exact h1_off (by simpa [hz1] using hzP)
        · exact hq2_not_e3 (by simpa [hz3] using hzq2)
      · exact Set.disjoint_left.mp htail_disjoint (by
          simpa [q2] using hzq2) (by simpa [q3] using hzq3)
  have hfirst_internal :
      Walk.InternalVertices (p.append q2) ∩ S.boundarySet = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzInternal :
        z ∈ Walk.InternalVertices (p.append q2) := hz.1
    have hzB : z ∈ S.boundarySet := hz.2
    have hzSupport := hzInternal.1
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzSupport
    rcases hzSupport with hzp | hzq
    · by_cases hz0 : z = X.endpoints.endpoint 0
      · exact hzInternal.2.1 hz0
      · by_cases hz2 : z = X.endpoints.endpoint 2
        · exact h2_not_boundary (by simpa [hz2] using hzB)
        · have hzIntP : z ∈ Walk.InternalVertices p :=
            ⟨hzp, hz0, hz2⟩
          have hnot : z ∉ Walk.InternalVertices p ∩ S.boundarySet := by
            rw [GMIX24Split.canonicalOfNoCross_right_cross_first_internal_boundary_original
              P hno_cross X]
            simp
          exact hnot ⟨hzIntP, hzB⟩
    · by_cases hz2 : z = X.endpoints.endpoint 2
      · exact h2_not_boundary (by simpa [hz2] using hzB)
      · by_cases hzs : z = P.s
        · exact hzInternal.2.2 hzs
        · have hzIntQ : z ∈ Walk.InternalVertices q2 :=
            ⟨by simpa [q2] using hzq, hz2, hzs⟩
          have hnot : z ∉ Walk.InternalVertices q2 ∩ S.boundarySet := by
            rw [show Walk.InternalVertices q2 ∩ S.boundarySet = ∅ by
              simpa [q2] using P.pathTailToStart_internal_boundary_empty h2_path]
            simp
          exact hnot ⟨hzIntQ, hzB⟩
  have hsecond_internal :
      Walk.InternalVertices (r.append q3) ∩ S.boundarySet = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzInternal :
        z ∈ Walk.InternalVertices (r.append q3) := hz.1
    have hzB : z ∈ S.boundarySet := hz.2
    have hzSupport := hzInternal.1
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzSupport
    rcases hzSupport with hzr | hzq
    · by_cases hz1 : z = X.endpoints.endpoint 1
      · exact hzInternal.2.1 hz1
      · by_cases hz3 : z = X.endpoints.endpoint 3
        · exact h3_not_boundary (by simpa [hz3] using hzB)
        · have hzIntR : z ∈ Walk.InternalVertices r :=
            ⟨hzr, hz1, hz3⟩
          have hnot : z ∉ Walk.InternalVertices r ∩ S.boundarySet := by
            rw [GMIX24Split.canonicalOfNoCross_right_cross_second_internal_boundary_original
              P hno_cross X]
            simp
          exact hnot ⟨hzIntR, hzB⟩
    · by_cases hz3 : z = X.endpoints.endpoint 3
      · exact h3_not_boundary (by simpa [hz3] using hzB)
      · by_cases hzt : z = P.t
        · exact hzInternal.2.2 hzt
        · have hzIntQ : z ∈ Walk.InternalVertices q3 :=
            ⟨by simpa [q3] using hzq, hz3, hzt⟩
          have hnot : z ∉ Walk.InternalVertices q3 ∩ S.boundarySet := by
            rw [show Walk.InternalVertices q3 ∩ S.boundarySet = ∅ by
              simpa [q3] using P.pathTailToEnd_internal_boundary_empty h3_path]
            simp
          exact hnot ⟨hzIntQ, hzB⟩
  exact ⟨
    X.lift_replaceEndpoints23_with_tails
      D.rightSociety_graph_le
      (P.pathTailToStart h2_path) (P.pathTailToEnd h3_path)
      hendpoint_mem hendpoint_injective halternating
      (by simpa [p, q2] using hfirst_path)
      (by simpa [r, q3] using hsecond_path)
      (by simpa [p, r, q2, q3] using hpaths_disjoint)
      (by simpa [p, q2] using hfirst_internal)
      (by simpa [r, q3] using hsecond_internal)⟩

theorem canonicalOfNoCross_right_cross_lift_of_adjacent23
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 2) <
        Walk.supportIndex P.path (X.endpoints.endpoint 3) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent23_path_order
      P hno_cross X h2_path h3_path h0_off
  have halt_pair :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints23 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints23_start_end_original_alternating_of_adjacent23
      P hno_cross X h2_path h3_path h0_off h1_off
  have h2_boundary_eq_start
      (hb2 : X.endpoints.endpoint 2 ∈ S.boundarySet) :
      X.endpoints.endpoint 2 = P.s := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb2 h2_path with h2s | h2t
    · exact h2s
    · exfalso
      have hle :
          Walk.supportIndex P.path (X.endpoints.endpoint 3) <=
            Walk.supportIndex P.path P.t :=
        Walk.IsPath.supportIndex_le_end P.path_isPath
          (by simpa [GMIX24CutPath.pathSet] using h3_path)
      have hbad :
          Walk.supportIndex P.path P.t <
            Walk.supportIndex P.path (X.endpoints.endpoint 3) := by
        simpa [h2t] using horder
      omega
  have h3_boundary_eq_end
      (hb3 : X.endpoints.endpoint 3 ∈ S.boundarySet) :
      X.endpoints.endpoint 3 = P.t := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb3 h3_path with h3s | h3t
    · exfalso
      have hle :
          Walk.supportIndex P.path P.s <=
            Walk.supportIndex P.path (X.endpoints.endpoint 2) :=
        Walk.supportIndex_start_le
          (p := P.path)
      have hbad :
          Walk.supportIndex P.path (X.endpoints.endpoint 2) <
            Walk.supportIndex P.path P.s := by
        simpa [h3s] using horder
      omega
    · exact h3t
  by_cases hb2 : X.endpoints.endpoint 2 ∈ S.boundarySet
  · have h2s := h2_boundary_eq_start hb2
    by_cases hb3 : X.endpoints.endpoint 3 ∈ S.boundarySet
    · have h3t := h3_boundary_eq_end hb3
      have hendpoint_mem :
          forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet := by
        intro i
        fin_cases i
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h0_off
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h1_off
        · simpa [GeneralSociety.boundarySet, h2s] using P.s_mem_boundary
        · simpa [GeneralSociety.boundarySet, h3t] using P.t_mem_boundary
      have halternating :
          CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
        have hfun :
            X.endpoints.endpoint = X.replaceEndpoints23 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoints23, h2s, h3t]
        simpa [hfun] using halt_pair
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_of_original_alternation
          P hno_cross X hendpoint_mem halternating
    · have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint3 P.t i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h0_off
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h1_off
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet, h2s]
            using P.s_mem_boundary
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet] using
            P.t_mem_boundary
      have hinj : Function.Injective (X.replaceEndpoint3 P.t) :=
        X.replaceEndpoint3_injective (by
          intro i hi
          fin_cases i
          · exact endpoint_ne_end_of_off_path (P := P) h0_off
          · exact endpoint_ne_end_of_off_path (P := P) h1_off
          · intro h
            exact P.s_ne_t (by simpa [h2s] using h.symm)
          · exact False.elim (hi rfl))
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.t) := by
        have hfun :
            X.replaceEndpoint3 P.t = X.replaceEndpoints23 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint3,
            Cross.replaceEndpoints23, h2s]
        simpa [hfun] using halt_pair
      have hq_not_e2 :
          X.endpoints.endpoint 2 ∉ (P.pathTailToEnd h3_path).support := by
        simpa using
          P.pathTailToEnd_not_mem_of_supportIndex_lt h3_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToEnd h3_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 3 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h3_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact False.elim (h0_off (by simpa [hw0] using hwP))
          · exact False.elim (hq_not_e2 (by simpa [hw2] using hw))
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact False.elim (h1_off (by simpa [hw1] using hwP))
          · exact hw3
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail
          P hno_cross X X.secondPath.end_mem_support
          (P.pathTailToEnd h3_path) hendpoint_mem hinj halt
          (P.pathTailToEnd_isPath h3_path)
          (P.pathTailToEnd_internal_boundary_empty h3_path)
          hb3 hclean
  · by_cases hb3 : X.endpoints.endpoint 3 ∈ S.boundarySet
    · have h3t := h3_boundary_eq_end hb3
      have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint2 P.s i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h0_off
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h1_off
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet] using
            P.s_mem_boundary
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet, h3t]
            using P.t_mem_boundary
      have hinj : Function.Injective (X.replaceEndpoint2 P.s) :=
        X.replaceEndpoint2_injective (by
          intro i hi
          fin_cases i
          · exact endpoint_ne_start_of_off_path (P := P) h0_off
          · exact endpoint_ne_start_of_off_path (P := P) h1_off
          · exact False.elim (hi rfl)
          · intro h
            exact P.s_ne_t (by simpa [h3t] using h))
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.s) := by
        have hfun :
            X.replaceEndpoint2 P.s = X.replaceEndpoints23 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint2,
            Cross.replaceEndpoints23, h3t]
        simpa [hfun] using halt_pair
      have hq_not_e3 :
          X.endpoints.endpoint 3 ∉ (P.pathTailToStart h2_path).support := by
        simpa using
          P.pathTailToStart_not_mem_of_supportIndex_lt h2_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToStart h2_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 2 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h2_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact False.elim (h0_off (by simpa [hw0] using hwP))
          · exact hw2
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact False.elim (h1_off (by simpa [hw1] using hwP))
          · exact False.elim (hq_not_e3 (by simpa [hw3] using hw))
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail
          P hno_cross X X.firstPath.end_mem_support
          (P.pathTailToStart h2_path) hendpoint_mem hinj halt
          (P.pathTailToStart_isPath h2_path)
          (P.pathTailToStart_internal_boundary_empty h2_path)
          hb2 hclean
    · exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints23_to_start_end_of_adjacent23
          P hno_cross X h2_path h3_path h0_off h1_off hb2 hb3

theorem canonicalOfNoCross_left_cross_replaceEndpoints23_end_start_original_alternating_of_adjacent23
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (_h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints23 P.t P.s) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints23_start_end_original_alternating_of_adjacent23
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using _h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off))


theorem canonicalOfNoCross_left_cross_lift_replaceEndpoints23_to_end_start_of_adjacent23
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_not_boundary : X.endpoints.endpoint 2 ∉ S.boundarySet)
    (h3_not_boundary : X.endpoints.endpoint 3 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints23_to_start_end_of_adjacent23
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_not_boundary)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_not_boundary)


theorem canonicalOfNoCross_left_cross_lift_of_adjacent23
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_of_adjacent23
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off)



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
