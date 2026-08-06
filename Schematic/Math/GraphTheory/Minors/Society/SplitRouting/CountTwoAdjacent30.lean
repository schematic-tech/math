import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoCases

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_right_cross_replaceEndpoints30_start_end_original_alternating_of_adjacent30
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints30 P.s P.t) := by
  classical
  let Ω := P.rightOrderedCutBoundary
  let e := X.endpoints.endpoint
  have h1_arc : e 1 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 1).mp (by simpa [e] using h1_off)
  have h2_arc : e 2 ∈ P.rightBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_right_cross_endpoint_not_path_iff_arc
      P hno_cross X 2).mp (by simpa [e] using h2_off)
  have hside :
      CrossEndpointAlternating Ω e := by
    simpa [Ω, e] using
      GMIX24Split.canonicalOfNoCross_right_cross_side_alternating
        P hno_cross X
  have h30_path :
      Walk.supportIndex P.path (e 3) <
        Walk.supportIndex P.path (e 0) := by
    simpa [e] using
      GMIX24Split.canonicalOfNoCross_right_cross_adjacent30_path_order
        P hno_cross X h3_path h0_path h2_off
  have h30 :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
    have hle :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
      simpa [Ω, e, CyclicBoundary.indexOf,
        CyclicBoundary.list_idxOf_eq_classical] using
        (P.rightOrderedCutBoundary_index_path_le_iff h3_path h0_path).mpr
          (Nat.le_of_lt h30_path)
    have hne :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) ≠
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) := by
      have h3_mem : e 3 ∈ Ω.vertexSet :=
        P.pathSet_subset_rightOrderedCutBoundary h3_path
      simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
        CyclicBoundary.indexOf_ne_of_ne h3_mem (by
        intro h30eq
        exact (by decide : (3 : Fin 4) ≠ 0)
          (X.endpoints.endpoint_injective (by simpa [e] using h30eq)))
    omega
  have h13 :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using
      P.rightOrderedCutBoundary_index_arc_lt_path h1_arc h3_path
  have h23 :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 3) := by
    simpa [Ω, e, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using
      P.rightOrderedCutBoundary_index_arc_lt_path h2_arc h3_path
  have h12 :
      @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
    have hfirst := hside.1.1.2
    have hnot02 :
        ¬ @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 0) <=
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      omega
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
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2)) at hfirst
    rw [if_neg hnot02] at hfirst
    have hle12 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      rcases hfirst with hbad | hle
      · omega
      · exact hle
    have hne12 :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ≠
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      have h1_mem : e 1 ∈ Ω.vertexSet :=
        P.rightBoundaryArc_subset_rightOrderedCutBoundary h1_arc
      simpa [CyclicBoundary.indexOf, CyclicBoundary.list_idxOf_eq_classical] using
        CyclicBoundary.indexOf_ne_of_ne h1_mem (by
        intro h12eq
        exact (by decide : (1 : Fin 4) ≠ 2)
          (X.endpoints.endpoint_injective (by simpa [e] using h12eq)))
    omega
  have h1_ne_t : e 1 ≠ P.t := by
    intro h
    exact (P.rightBoundaryArc_subset_outside h1_arc).2
      (by simp [e, h])
  have h1_ne_2 : e 1 ≠ e 2 := by
    intro h
    have hidx :
        @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) =
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
      simp [h]
    omega
  have hside_first :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        Ω P.t (e 2) (e 1) := by
    refine ⟨⟨?_, ?_⟩, h1_ne_t, h1_ne_2⟩
    · exact P.rightBoundaryArc_subset_rightOrderedCutBoundary h1_arc
    · have hnot_t2 :
          ¬ @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) := by
        have h2t :
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) <
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t := by
          simpa [Ω, e, CyclicBoundary.indexOf,
            CyclicBoundary.list_idxOf_eq_classical] using
            P.rightOrderedCutBoundary_index_arc_lt_path h2_arc P.t_mem_pathSet
        omega
      change
        (if @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2) then
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ∧
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2)
        else
          @CyclicBoundary.indexOf V (Classical.decEq V) Ω P.t <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) ∨
            @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 1) <=
              @CyclicBoundary.indexOf V (Classical.decEq V) Ω (e 2))
      rw [if_neg hnot_t2]
      exact Or.inr (Nat.le_of_lt h12)
  have hpt_ne_e2 : P.t ≠ e 2 :=
    endpoint_ne_end_of_off_path (P := P) (X := X) h2_off
  have hfirst :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.t (e 2) (e 1) :=
    GMIX24CutPath.rightOrdered_clockwiseOpenBetween_original_of_arc_or_end
      P (Or.inr rfl) (Or.inl h2_arc) (Or.inl h1_arc)
      hpt_ne_e2 hside_first
  have hsecond :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary (e 2) P.t P.s :=
    GMIX24CutPath.rightBoundaryArc_clockwiseOpenBetween_arc_end_start
      P h2_arc
  dsimp [CrossEndpointAlternating, Cross.replaceEndpoints30]
  exact ⟨hfirst, hsecond⟩

theorem canonicalOfNoCross_right_cross_lift_replaceEndpoints30_to_start_end_of_adjacent30
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_not_boundary : X.endpoints.endpoint 3 ∉ S.boundarySet)
    (h0_not_boundary : X.endpoints.endpoint 0 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let p : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.rightSociety_graph_le
  let r : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.rightSociety_graph_le
  let q3 : S.graph.Walk (X.endpoints.endpoint 3) P.s :=
    P.pathTailToStart h3_path
  let q0 : S.graph.Walk (X.endpoints.endpoint 0) P.t :=
    P.pathTailToEnd h0_path
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 3) <
        Walk.supportIndex P.path (X.endpoints.endpoint 0) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent30_path_order
      P hno_cross X h3_path h0_path h2_off
  have hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoints30 P.s P.t i ∈ S.boundarySet := by
    intro i
    fin_cases i
    · simpa [Cross.replaceEndpoints30, GeneralSociety.boundarySet] using
        P.t_mem_boundary
    · simpa [Cross.replaceEndpoints30, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h1_off
    · simpa [Cross.replaceEndpoints30, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
          P hno_cross X h2_off
    · simpa [Cross.replaceEndpoints30, GeneralSociety.boundarySet] using
        P.s_mem_boundary
  have hendpoint_injective :
      Function.Injective (X.replaceEndpoints30 P.s P.t) :=
    X.replaceEndpoints30_injective P.s_ne_t
      (endpoint_ne_start_of_off_path (P := P) h1_off)
      (endpoint_ne_start_of_off_path (P := P) h2_off)
      (endpoint_ne_end_of_off_path (P := P) h1_off)
      (endpoint_ne_end_of_off_path (P := P) h2_off)
  have halternating :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints30 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints30_start_end_original_alternating_of_adjacent30
      P hno_cross X h3_path h0_path h1_off h2_off
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.firstPath_isPath
  have hr_path : r.IsPath := by
    exact SimpleGraph.Walk.IsPath.mapLe
      D.rightSociety_graph_le X.secondPath_isPath
  have hx0p : X.endpoints.endpoint 0 ∈ p.support := by
    simp [p]
  have hclean0 :
      forall z : V, z ∈ q0.support -> z ∈ p.support ->
        z = X.endpoints.endpoint 0 := by
    intro z hzq hzp
    have hzP : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet h0_path z (by
        simpa [q0] using hzq)
    have hzpX : z ∈ X.firstPath.support := by
      simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
          P hno_cross X hzpX hzP with hz0 | hz2
    · exact hz0
    · exact False.elim (h2_off (by simpa [hz2] using hzP))
  have hclean3 :
      forall z : V, z ∈ q3.support -> z ∈ r.support ->
        z = X.endpoints.endpoint 3 := by
    intro z hzq hzr
    have hzP : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet h3_path z (by
        simpa [q3] using hzq)
    have hzrX : z ∈ X.secondPath.support := by
      simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
    rcases
        GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
          P hno_cross X hzrX hzP with hz1 | hz3
    · exact False.elim (h1_off (by simpa [hz1] using hzP))
    · exact hz3
  have hfirst_path : (q0.reverse.append p).IsPath := by
    have h :=
      Walk.IsPath.reverse_append_dropUntil_of_clean
        hp_path hx0p (P.pathTailToEnd_isPath h0_path) hclean0
    simpa [p, q0, SimpleGraph.Walk.dropUntil_first] using h
  have hsecond_path : (r.append q3).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hr_path (P.pathTailToStart_isPath h3_path) ?_
    intro z hzr hzq
    exact hclean3 z hzq hzr
  have htail_disjoint :
      Disjoint {z : V | z ∈ q3.support} {z : V | z ∈ q0.support} := by
    simpa [q3, q0] using
      P.pathTailToStart_support_disjoint_pathTailToEnd
        h3_path h0_path horder
  have hq3_not_e0 :
      X.endpoints.endpoint 0 ∉ q3.support := by
    simpa [q3] using
      P.pathTailToStart_not_mem_of_supportIndex_lt
        h3_path horder
  have hq0_not_e3 :
      X.endpoints.endpoint 3 ∉ q0.support := by
    simpa [q0] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt
        h0_path horder
  have hpaths_disjoint :
      Disjoint {z : V | z ∈ (q0.reverse.append p).support}
        {z : V | z ∈ (r.append q3).support} := by
    rw [Set.disjoint_left]
    intro z hz_first hz_second
    have hz_first' :
        z ∈ q0.reverse.support ∨ z ∈ p.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_first
    have hz_second' :
        z ∈ r.support ∨ z ∈ q3.support := by
      simpa [SimpleGraph.Walk.mem_support_append_iff] using hz_second
    rcases hz_first' with hzq0_rev | hzp
    · have hzq0 : z ∈ q0.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzq0_rev
        exact List.mem_reverse.mp hzq0_rev
      rcases hz_second' with hzr | hzq3
      · have hzP : z ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h0_path z (by
            simpa [q0] using hzq0)
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hzrX hzP with hz1 | hz3
        · exact h1_off (by simpa [hz1] using hzP)
        · exact hq0_not_e3 (by simpa [hz3] using hzq0)
      · exact Set.disjoint_left.mp htail_disjoint (by
          simpa [q3] using hzq3) (by simpa [q0] using hzq0)
    · rcases hz_second' with hzr | hzq3
      · have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        have hzrX : z ∈ X.secondPath.support := by
          simpa [r, SimpleGraph.Walk.support_mapLe_eq_support] using hzr
        exact Set.disjoint_left.mp X.paths_disjoint hzpX hzrX
      · have hzP : z ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h3_path z (by
            simpa [q3] using hzq3)
        have hzpX : z ∈ X.firstPath.support := by
          simpa [p, SimpleGraph.Walk.support_mapLe_eq_support] using hzp
        rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hzpX hzP with hz0 | hz2
        · exact hq3_not_e0 (by simpa [hz0] using hzq3)
        · exact h2_off (by simpa [hz2] using hzP)
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
        hx0p hdrop (P.pathTailToEnd_internal_boundary_empty h0_path)
        h0_not_boundary
    simpa [p, q0, SimpleGraph.Walk.dropUntil_first] using h
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
      · by_cases hzs : z = P.s
        · exact hzInternal.2.2 hzs
        · have hzIntQ : z ∈ Walk.InternalVertices q3 :=
            ⟨by simpa [q3] using hzq, hz3, hzs⟩
          have hnot : z ∉ Walk.InternalVertices q3 ∩ S.boundarySet := by
            rw [show Walk.InternalVertices q3 ∩ S.boundarySet = ∅ by
              simpa [q3] using P.pathTailToStart_internal_boundary_empty h3_path]
            simp
          exact hnot ⟨hzIntQ, hzB⟩
  exact ⟨
    X.lift_replaceEndpoints30_with_tails
      D.rightSociety_graph_le
      (P.pathTailToStart h3_path) (P.pathTailToEnd h0_path)
      hendpoint_mem hendpoint_injective halternating
      (by simpa [p, q0] using hfirst_path)
      (by simpa [r, q3] using hsecond_path)
      (by simpa [p, r, q3, q0] using hpaths_disjoint)
      (by simpa [p, q0] using hfirst_internal)
      (by simpa [r, q3] using hsecond_internal)⟩

theorem canonicalOfNoCross_right_cross_lift_of_adjacent30
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  have horder :
      Walk.supportIndex P.path (X.endpoints.endpoint 3) <
        Walk.supportIndex P.path (X.endpoints.endpoint 0) :=
    GMIX24Split.canonicalOfNoCross_right_cross_adjacent30_path_order
      P hno_cross X h3_path h0_path h2_off
  have halt_pair :
      CrossEndpointAlternating S.boundary
        (X.replaceEndpoints30 P.s P.t) :=
    GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints30_start_end_original_alternating_of_adjacent30
      P hno_cross X h3_path h0_path h1_off h2_off
  have h3_boundary_eq_start
      (hb3 : X.endpoints.endpoint 3 ∈ S.boundarySet) :
      X.endpoints.endpoint 3 = P.s := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb3 h3_path with h3s | h3t
    · exact h3s
    · exfalso
      have hle :
          Walk.supportIndex P.path (X.endpoints.endpoint 0) <=
            Walk.supportIndex P.path P.t :=
        Walk.IsPath.supportIndex_le_end P.path_isPath
          (by simpa [GMIX24CutPath.pathSet] using h0_path)
      have hbad :
          Walk.supportIndex P.path P.t <
            Walk.supportIndex P.path (X.endpoints.endpoint 0) := by
        simpa [h3t] using horder
      omega
  have h0_boundary_eq_end
      (hb0 : X.endpoints.endpoint 0 ∈ S.boundarySet) :
      X.endpoints.endpoint 0 = P.t := by
    rcases P.boundary_mem_pathSet_eq_s_or_t hb0 h0_path with h0s | h0t
    · exfalso
      have hle :
          Walk.supportIndex P.path P.s <=
            Walk.supportIndex P.path (X.endpoints.endpoint 3) :=
        Walk.supportIndex_start_le
          (p := P.path)
      have hbad :
          Walk.supportIndex P.path (X.endpoints.endpoint 3) <
            Walk.supportIndex P.path P.s := by
        simpa [h0s] using horder
      omega
    · exact h0t
  by_cases hb3 : X.endpoints.endpoint 3 ∈ S.boundarySet
  · have h3s := h3_boundary_eq_start hb3
    by_cases hb0 : X.endpoints.endpoint 0 ∈ S.boundarySet
    · have h0t := h0_boundary_eq_end hb0
      have hendpoint_mem :
          forall i : Fin 4, X.endpoints.endpoint i ∈ S.boundary.vertexSet := by
        intro i
        fin_cases i
        · simpa [GeneralSociety.boundarySet, h0t] using P.t_mem_boundary
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h1_off
        · exact
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h2_off
        · simpa [GeneralSociety.boundarySet, h3s] using P.s_mem_boundary
      have halternating :
          CrossEndpointAlternating S.boundary X.endpoints.endpoint := by
        have hfun :
            X.endpoints.endpoint = X.replaceEndpoints30 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoints30, h3s, h0t]
        simpa [hfun] using halt_pair
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_of_original_alternation
          P hno_cross X hendpoint_mem halternating
    · have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint0 P.t i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet] using
            P.t_mem_boundary
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h1_off
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h2_off
        · simpa [Cross.replaceEndpoint0, GeneralSociety.boundarySet, h3s]
            using P.s_mem_boundary
      have hinj : Function.Injective (X.replaceEndpoint0 P.t) :=
        X.replaceEndpoint0_injective (by
          intro i hi
          fin_cases i
          · exact False.elim (hi rfl)
          · exact endpoint_ne_end_of_off_path (P := P) h1_off
          · exact endpoint_ne_end_of_off_path (P := P) h2_off
          · intro h
            exact P.s_ne_t (by simpa [h3s] using h.symm))
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint0 P.t) := by
        have hfun :
            X.replaceEndpoint0 P.t = X.replaceEndpoints30 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint0,
            Cross.replaceEndpoints30, h3s]
        simpa [hfun] using halt_pair
      have hq_not_e3 :
          X.endpoints.endpoint 3 ∉ (P.pathTailToEnd h0_path).support := by
        simpa using
          P.pathTailToEnd_not_mem_of_supportIndex_lt h0_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToEnd h0_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 0 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToEnd_support_subset_pathSet h0_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact hw0
          · exact False.elim (h2_off (by simpa [hw2] using hwP))
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact False.elim (h1_off (by simpa [hw1] using hwP))
          · exact False.elim (hq_not_e3 (by simpa [hw3] using hw))
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint0_with_tail
          P hno_cross X X.firstPath.start_mem_support
          (P.pathTailToEnd h0_path) hendpoint_mem hinj halt
          (P.pathTailToEnd_isPath h0_path)
          (P.pathTailToEnd_internal_boundary_empty h0_path)
          hb0 hclean
  · by_cases hb0 : X.endpoints.endpoint 0 ∈ S.boundarySet
    · have h0t := h0_boundary_eq_end hb0
      have hendpoint_mem :
          forall i : Fin 4, X.replaceEndpoint3 P.s i ∈ S.boundarySet := by
        intro i
        fin_cases i
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet, h0t]
            using P.t_mem_boundary
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h1_off
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet] using
            GMIX24Split.canonicalOfNoCross_right_cross_endpoint_mem_original_of_off_path
              P hno_cross X h2_off
        · simpa [Cross.replaceEndpoint3, GeneralSociety.boundarySet] using
            P.s_mem_boundary
      have hinj : Function.Injective (X.replaceEndpoint3 P.s) :=
        X.replaceEndpoint3_injective (by
          intro i hi
          fin_cases i
          · intro h
            exact P.s_ne_t (by simpa [h0t] using h)
          · exact endpoint_ne_start_of_off_path (P := P) h1_off
          · exact endpoint_ne_start_of_off_path (P := P) h2_off
          · exact False.elim (hi rfl))
      have halt :
          CrossEndpointAlternating S.boundary (X.replaceEndpoint3 P.s) := by
        have hfun :
            X.replaceEndpoint3 P.s = X.replaceEndpoints30 P.s P.t := by
          funext i
          fin_cases i <;> simp [Cross.replaceEndpoint3,
            Cross.replaceEndpoints30, h0t]
        simpa [hfun] using halt_pair
      have hq_not_e0 :
          X.endpoints.endpoint 0 ∉ (P.pathTailToStart h3_path).support := by
        simpa using
          P.pathTailToStart_not_mem_of_supportIndex_lt h3_path horder
      have hclean :
          forall w : V,
            w ∈ (P.pathTailToStart h3_path).support ->
              (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
                w = X.endpoints.endpoint 3 := by
        intro w hw hwX
        have hwP : w ∈ P.pathSet :=
          P.pathTailToStart_support_subset_pathSet h3_path w hw
        rcases hwX with hwFirst | hwSecond
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_firstPath_pathSet_eq_endpoint
              P hno_cross X hwFirst hwP with hw0 | hw2
          · exact False.elim (hq_not_e0 (by simpa [hw0] using hw))
          · exact False.elim (h2_off (by simpa [hw2] using hwP))
        · rcases
            GMIX24Split.canonicalOfNoCross_right_cross_secondPath_pathSet_eq_endpoint
              P hno_cross X hwSecond hwP with hw1 | hw3
          · exact False.elim (h1_off (by simpa [hw1] using hwP))
          · exact hw3
      exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoint3_with_tail
          P hno_cross X X.secondPath.end_mem_support
          (P.pathTailToStart h3_path) hendpoint_mem hinj halt
          (P.pathTailToStart_isPath h3_path)
          (P.pathTailToStart_internal_boundary_empty h3_path)
          hb3 hclean
    · exact
        GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints30_to_start_end_of_adjacent30
          P hno_cross X h3_path h0_path h1_off h2_off hb3 hb0

theorem canonicalOfNoCross_left_cross_replaceEndpoints30_end_start_original_alternating_of_adjacent30
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet) :
    CrossEndpointAlternating S.boundary
      (X.replaceEndpoints30 P.t P.s) := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using
    (GMIX24Split.canonicalOfNoCross_right_cross_replaceEndpoints30_start_end_original_alternating_of_adjacent30
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off))


theorem canonicalOfNoCross_left_cross_lift_replaceEndpoints30_to_end_start_of_adjacent30
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (h3_not_boundary : X.endpoints.endpoint 3 ∉ S.boundarySet)
    (h0_not_boundary : X.endpoints.endpoint 0 ∉ S.boundarySet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_replaceEndpoints30_to_start_end_of_adjacent30
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_not_boundary)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_not_boundary)


theorem canonicalOfNoCross_left_cross_lift_of_adjacent30
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h3_path : X.endpoints.endpoint 3 ∈ P.pathSet)
    (h0_path : X.endpoints.endpoint 0 ∈ P.pathSet)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseLeftCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_right_cross_lift_of_adjacent30
      P.reverse hno_cross Xrev
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h3_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h0_path)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h1_off)
      (by simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseLeftCross] using h2_off)



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
