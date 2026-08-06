import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoCases

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_right_cross_replaceEndpoints12_start_end_original_alternating_of_adjacent12
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (_h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints12 P.s P.t) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  have h0_arc : e 0 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 0).mp (by simpa [e] using h0_off)
  have h3_arc : e 3 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 3).mp (by simpa [e] using h3_off)
  have hside :
      CrossEndpointAlternating Ω e := by
    simpa [Ω, e] using
      GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X
  have h02 :
      Ω.indexOf (e 0) < Ω.indexOf (e 2) := by
    simpa [Ω, e] using
      P.rightOrderedCutBoundary_index_arc_lt_path h0_arc h2_path
  have h30 :
      Ω.indexOf (e 3) < Ω.indexOf (e 0) := by
    have h32 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      simpa [Ω, e, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using
        P.rightOrderedCutBoundary_index_arc_lt_path h3_arc h2_path
    have h02C :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
        using h02
    have hbetween := hside.2.1.2
    have hnot_le :
        ¬ @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
      omega
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
    rw [if_neg hnot_le] at hbetween
    have hle30 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
      rcases hbetween with hbad | hle
      · omega
      · exact hle
    have hne30 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ≠
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
      have h3_mem : e 3 ∈ Ω.vertexSet :=
        P.rightBoundaryArc_subset_rightOrderedCutBoundary h3_arc
      simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
        CyclicBoundary.indexOf_ne_of_ne h3_mem (by
        intro h30eq
        exact (by decide : (3 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective (by simpa [e] using h30eq)))
    have hltC :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
      omega
    simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
      using hltC
  have ht3 :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t >
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using
      P.rightOrderedCutBoundary_index_arc_lt_path h3_arc P.t_mem_pathSet
  have ht0_not :
      ¬ @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
    have h0t :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t := by
      simpa [Ω, e, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using
        P.rightOrderedCutBoundary_index_arc_lt_path h0_arc P.t_mem_pathSet
    omega
  have h3_ne_t : e 3 ≠ P.t := by
    intro h
    exact (P.rightBoundaryArc_subset_outside h3_arc).2
      (by simp [e, h])
  have h3_ne_0 : e 3 ≠ e 0 := by
    intro h
    have hidx : Ω.indexOf (e 3) = Ω.indexOf (e 0) := by simp [h]
    omega
  have hside_rot :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ω P.t (e 0) (e 3) := by
    refine ⟨⟨?_, ?_⟩, h3_ne_t, h3_ne_0⟩
    · exact P.rightBoundaryArc_subset_rightOrderedCutBoundary h3_arc
    · change
        (if @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) then
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ∧
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0)
        else
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ∨
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0))
      rw [if_neg ht0_not]
      exact Or.inr (by
        simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical]
          using Nat.le_of_lt h30)
  have hfirst :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary (e 0) P.t P.s :=
    GMIX24CutPath.rightBoundaryArc_clockwiseOpenBetween_arc_end_start
      P h0_arc
  have hpt_ne_e0 : P.t ≠ e 0 :=
    endpoint_ne_end_of_off_path (P := P) (X := X) h0_off
  have hsecond :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.t (e 0) (e 3) :=
    GMIX24CutPath.rightOrdered_clockwiseOpenBetween_original_of_arc_or_end
      P (Or.inr rfl) (Or.inl h0_arc) (Or.inl h3_arc)
      hpt_ne_e0 hside_rot
  dsimp [CrossEndpointAlternating, Cross.replaceEndpoints12]
  exact ⟨hfirst, hsecond⟩

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoints12_to_start_end_of_adjacent12
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (h1_not_boundary : X.endpoints.endpoint 1 ∉ S.boundarySet)
    (h2_not_boundary : X.endpoints.endpoint 2 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.rightSociety_graph_le
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.rightSociety_graph_le
  let q1 : S.graph.Walk (X.endpoints.endpoint 1) P.s :=
    P.pathTailToStart h1_path
  let q2 : S.graph.Walk (X.endpoints.endpoint 2) P.t :=
    P.pathTailToEnd h2_path
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 1) <
        Walk.supportIndex P.path (X.endpoints.endpoint 2) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent12_path_order
      P hno_cross X h1_path h2_path h0_off
  have hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints12 P.s P.t i ∈ S.boundarySet := by
    intro i
    fin_cases i
    · simpa [Cross.replaceEndpoints12, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h0_off
    · simpa [Cross.replaceEndpoints12, GeneralSociety.boundarySet] using
        P.s_mem_boundary
    · simpa [Cross.replaceEndpoints12, GeneralSociety.boundarySet] using
        P.t_mem_boundary
    · simpa [Cross.replaceEndpoints12, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h3_off
  have hendpoint_injective :
      Function.Injective (X.replaceEndpoints12 P.s P.t) :=
    X.replaceEndpoints12_injective P.s_ne_t
      (endpoint_ne_start_of_off_path (P := P) h0_off)
      (endpoint_ne_start_of_off_path (P := P) h3_off)
      (endpoint_ne_end_of_off_path (P := P) h0_off)
      (endpoint_ne_end_of_off_path (P := P) h3_off)
  have halternating :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints12 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints12_start_end_original_alternating_of_adjacent12
      P hno_cross X h1_path h2_path h0_off h3_off
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.secondPath_isPath
  have hx1r : X.endpoints.endpoint 1 ∈ r.support := by
    simp [r]
  have hclean2 :
      forall z : V, z ∈ q2.support -> z ∈ p.support ->
        z = X.endpoints.endpoint 2 := by
    intro z hzq hzp
    have hzP : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet h2_path z (by
        simpa [q2] using hzq)
    have hzpX : z ∈ X.firstPath.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hzpX hzP with hz0 | hz2
    · exact False.elim (h0_off (by simpa [hz0] using hzP))
    · exact hz2
  have hclean1 :
      forall z : V, z ∈ q1.support -> z ∈ r.support ->
        z = X.endpoints.endpoint 1 := by
    intro z hzq hzr
    have hzP : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet h1_path z (by
        simpa [q1] using hzq)
    have hzrX : z ∈ X.secondPath.support := by
      simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hzrX hzP with hz1 | hz3
    · exact hz1
    · exact False.elim (h3_off (by simpa [hz3] using hzP))
  have hfirst_path : (p.append q2).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hp_path (P.pathTailToEnd_isPath h2_path) ?_
    intro z hzp hzq
    exact hclean2 z hzq hzp
  have hsecond_path : (q1.reverse.append r).IsPath := by
    have h :=
      Walk.IsPath.reverse_append_dropUntil_of_clean
        hr_path hx1r (P.pathTailToStart_isPath h1_path) hclean1
    simpa [r, q1, SimpleGraph.Walk.dropUntil_first] using h
  have htail_disjoint :
      Disjoint {z : V | z ∈ q1.support} {z : V | z ∈ q2.support} := by
    simpa [q1, q2] using
      P.pathTailToStart_support_disjoint_pathTailToEnd
        h1_path h2_path horder
  have hq1_not_e2 :
      X.endpoints.endpoint 2 ∉ q1.support := by
    simpa [q1] using
      P.pathTailToStart_not_mem_of_supportIndex_lt
        h1_path horder
  have hq2_not_e1 :
      X.endpoints.endpoint 1 ∉ q2.support := by
    simpa [q2] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt
        h2_path horder
  have hpaths_disjoint :
      Disjoint {z : V | z ∈ (p.append q2).support}
        {z : V | z ∈ (q1.reverse.append r).support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_first' :
        z ∈ p.support ∨ z ∈ q2.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_first
    have hz_second' :
        z ∈ q1.reverse.support ∨ z ∈ r.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_second
    rcases hz_first' with hzp | hzq2
    · rcases hz_second' with hzq1_rev | hzr
      · have hzq1 : z ∈ q1.support := by
          rw [SimpleGraph.Walk.support_reverse] at hzq1_rev
          exact List.mem_reverse.mp hzq1_rev
        have hzP : z ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h1_path z (by
            simpa [q1] using hzq1)
        have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hzpX hzP with hz0 | hz2
        · exact h0_off (by simpa [hz0] using hzP)
        · exact hq1_not_e2 (by simpa [hz2] using hzq1)
      · have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        exact Set.disjoint_left.mp X.paths_disjoint hzpX hzrX
    · rcases hz_second' with hzq1_rev | hzr
      · have hzq1 : z ∈ q1.support := by
          rw [SimpleGraph.Walk.support_reverse] at hzq1_rev
          exact List.mem_reverse.mp hzq1_rev
        exact Set.disjoint_left.mp htail_disjoint hzq1 (by
          simpa [q2] using hzq2)
      · have hzP : z ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h2_path z (by
            simpa [q2] using hzq2)
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hzrX hzP with hz1 | hz3
        · exact hq2_not_e1 (by simpa [hz1] using hzq2)
        · exact h3_off (by simpa [hz3] using hzP)
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
      · by_cases hzt : z = P.t
        · exact hzInternal.2.2 hzt
        · have hzIntQ : z ∈ Walk.InternalVertices q2 :=
            ⟨by simpa [q2] using hzq, hz2, hzt⟩
          have hnot : z ∉ Walk.InternalVertices q2 ∩ S.boundarySet := by
            rw [show Walk.InternalVertices q2 ∩ S.boundarySet = ∅ by
              simpa [q2] using P.pathTailToEnd_internal_boundary_empty h2_path]
            simp
          exact hnot ⟨hzIntQ, hzB⟩
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
        hx1r hdrop (P.pathTailToStart_internal_boundary_empty h1_path)
        h1_not_boundary
    simpa [r, q1, SimpleGraph.Walk.dropUntil_first] using h
  exact ⟨
    X.lift_replaceEndpoints12_with_tails
      D.rightSociety_graph_le
      (P.pathTailToStart h1_path) (P.pathTailToEnd h2_path)
      hendpoint_mem hendpoint_injective halternating
      (by simpa [p, q2] using hfirst_path)
      (by simpa [r, q1] using hsecond_path)
      (by simpa [p, r, q1, q2] using hpaths_disjoint)
      (by simpa [p, q2] using hfirst_internal)
      (by simpa [r, q1] using hsecond_internal)⟩

theorem canonicalOfNoCross_right_cross_lift_of_adjacent12
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 1) <
        Walk.supportIndex P.path (X.endpoints.endpoint 2) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent12_path_order
      P hno_cross X h1_path h2_path h0_off
  have halt_pair :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints12 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints12_start_end_original_alternating_of_adjacent12
      P hno_cross X h1_path h2_path h0_off h3_off
  have h1_boundary_eq_start
      (hb1 : X.endpoints.endpoint 1 ∈ S.boundarySet) :
      X.endpoints.endpoint 1 = P.s := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb1 h1_path with h1s | h1t
    · exact h1s
    · exfalso
      have hle :
          Walk.supportIndex P.path (X.endpoints.endpoint 2) <=
            Walk.supportIndex P.path P.t :=
        Walk.IsPath.supportIndex_le_end P.path_isPath
          (by simpa [GMIX24CutPath.pathSet] using h2_path)
      have hbad :
          Walk.supportIndex P.path P.t <
            Walk.supportIndex P.path (X.endpoints.endpoint 2) := by
        simpa [h1t] using horder
      omega
  have h2_boundary_eq_end
      (hb2 : X.endpoints.endpoint 2 ∈ S.boundarySet) :
      X.endpoints.endpoint 2 = P.t := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb2 h2_path with h2s | h2t
    · exfalso
      have hle :
          Walk.supportIndex P.path P.s <=
            Walk.supportIndex P.path (X.endpoints.endpoint 1) :=
        Walk.supportIndex_start_le
          (p := P.path)
      have hbad :
          Walk.supportIndex P.path (X.endpoints.endpoint 1) <
            Walk.supportIndex P.path P.s := by
        simpa [h2s] using horder
      omega
    · exact h2t
  by_cases hb1 : X.endpoints.endpoint 1 ∈ S.boundarySet
  · have h1s := h1_boundary_eq_start hb1
    by_cases hb2 : X.endpoints.endpoint 2 ∈ S.boundarySet
    · have h2t := h2_boundary_eq_end hb2
      have hendpoint_mem :
          forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet := by
        intro i
        fin_cases i
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h0_off
        · simpa [GeneralSociety.boundarySet, h1s] using P.s_mem_boundary
        · simpa [GeneralSociety.boundarySet, h2t] using P.t_mem_boundary
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h3_off
      have halternating :
          CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
        have hfun :
            X.endpoints.endpoint = X.replaceEndpoints12 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoints12, h1s, h2t]
        simpa [hfun] using halt_pair
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_of_original_alternation
          P hno_cross X hendpoint_mem halternating
    · have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint2 P.t i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h0_off
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet, h1s]
            using P.s_mem_boundary
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet] using
            P.t_mem_boundary
        · simpa [Cross.replaceEndpoint2, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h3_off
      have hinj : Function.Injective (X.replaceEndpoint2 P.t) :=
        X.replaceEndpoint2_injective (by
          intro i hi
          fin_cases i
          · exact endpoint_ne_end_of_off_path (P := P) h0_off
          · intro h
            exact P.s_ne_t (by simpa [h1s] using h.symm)
          · exact False.elim (hi rfl)
          · exact endpoint_ne_end_of_off_path (P := P) h3_off)
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint2 P.t) := by
        have hfun :
            X.replaceEndpoint2 P.t = X.replaceEndpoints12 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint2,
            Cross.replaceEndpoints12, h1s]
        simpa [hfun] using halt_pair
      have hq_not_e1 :
          X.endpoints.endpoint 1 ∉ (P.pathTailToEnd h2_path).support := by
        simpa using
          P.pathTailToEnd_not_mem_of_supportIndex_lt h2_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToEnd h2_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 2 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h2_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact False.elim (h0_off (by simpa [hw0] using hwP))
          · exact hw2
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact False.elim (hq_not_e1 (by simpa [hw1] using hw))
          · exact False.elim (h3_off (by simpa [hw3] using hwP))
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint2_with_tail
          P hno_cross X X.firstPath.end_mem_support
          (P.pathTailToEnd h2_path) hendpoint_mem hinj halt
          (P.pathTailToEnd_isPath h2_path)
          (P.pathTailToEnd_internal_boundary_empty h2_path)
          hb2 hclean
  · by_cases hb2 : X.endpoints.endpoint 2 ∈ S.boundarySet
    · have h2t := h2_boundary_eq_end hb2
      have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint1 P.s i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h0_off
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet] using
            P.s_mem_boundary
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet, h2t]
            using P.t_mem_boundary
        · simpa [Cross.replaceEndpoint1, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h3_off
      have hinj : Function.Injective (X.replaceEndpoint1 P.s) :=
        X.replaceEndpoint1_injective (by
          intro i hi
          fin_cases i
          · exact endpoint_ne_start_of_off_path (P := P) h0_off
          · exact False.elim (hi rfl)
          · intro h
            exact P.s_ne_t (by simpa [h2t] using h)
          · exact endpoint_ne_start_of_off_path (P := P) h3_off)
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint1 P.s) := by
        have hfun :
            X.replaceEndpoint1 P.s = X.replaceEndpoints12 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint1,
            Cross.replaceEndpoints12, h2t]
        simpa [hfun] using halt_pair
      have hq_not_e2 :
          X.endpoints.endpoint 2 ∉ (P.pathTailToStart h1_path).support := by
        simpa using
          P.pathTailToStart_not_mem_of_supportIndex_lt h1_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToStart h1_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 1 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h1_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact False.elim (h0_off (by simpa [hw0] using hwP))
          · exact False.elim (hq_not_e2 (by simpa [hw2] using hw))
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact hw1
          · exact False.elim (h3_off (by simpa [hw3] using hwP))
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint1_with_tail
          P hno_cross X X.secondPath.start_mem_support
          (P.pathTailToStart h1_path) hendpoint_mem hinj halt
          (P.pathTailToStart_isPath h1_path)
          (P.pathTailToStart_internal_boundary_empty h1_path)
          hb1 hclean
    · exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints12_to_start_end_of_adjacent12
          P hno_cross X h1_path h2_path h0_off h3_off hb1 hb2

theorem canonicalOfNoCross_left_cross_replaceEndpoints12_end_start_original_alternating_of_adjacent12
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (_h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints12 P.t P.s) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints12_start_end_original_alternating_of_adjacent12
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using _h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off))


theorem canonicalOfNoCross_left_cross_lift_replaceEndpoints12_to_end_start_of_adjacent12
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (h1_not_boundary : X.endpoints.endpoint 1 ∉ S.boundarySet)
    (h2_not_boundary : X.endpoints.endpoint 2 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints12_to_start_end_of_adjacent12
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_not_boundary)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_not_boundary)


theorem canonicalOfNoCross_left_cross_lift_of_adjacent12
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_path : X.endpoints.endpoint 1 ∈ P.pathSet)
    (h2_path : X.endpoints.endpoint 2 ∈ P.pathSet)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_of_adjacent12
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_off)



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
