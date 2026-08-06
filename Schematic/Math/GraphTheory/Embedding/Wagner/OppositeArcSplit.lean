import Schematic.Math.GraphTheory.Embedding.Wagner.ArcRestriction

/-! Alternating cycle data from points on opposite complementary arcs. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner

/-- Interior points on opposite complementary arcs occur alternately with the
two common endpoints.  Cutting at those points gives the three-path package
used by the strict `K3,3` constructor. -/
noncomputable def alternatingCycleSplitOfOppositeArcInteriors
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 y1 x2 y2 : V} {C : G.Walk r r}
    (A : CycleTwoArcs C (x1 := y2) (x2 := y1))
    (hx1 : x1 ∈ Walk.InternalVertices A.first)
    (hx2 : x2 ∈ Walk.InternalVertices A.second) :
    AlternatingCycleSplit C (x1 := x1) (y1 := y1)
      (x2 := x2) (y2 := y2) := by
  classical
  let P1 : G.Walk y2 x1 := A.first.takeUntil x1 hx1.1
  let P2 : G.Walk x1 y1 := A.first.dropUntil x1 hx1.1
  let Q1 : G.Walk y2 x2 := A.second.takeUntil x2 hx2.1
  let Q2 : G.Walk x2 y1 := A.second.dropUntil x2 hx2.1
  let R : G.Walk x1 x2 := P1.reverse.append Q1
  have hP1 : P1.IsPath := by
    simpa [P1] using A.first_isPath.takeUntil hx1.1
  have hP2 : P2.IsPath := by
    simpa [P2] using A.first_isPath.dropUntil hx1.1
  have hQ1 : Q1.IsPath := by
    simpa [Q1] using A.second_isPath.takeUntil hx2.1
  have hQ2 : Q2.IsPath := by
    simpa [Q2] using A.second_isPath.dropUntil hx2.1
  have hy1_not_P1 : y1 ∉ P1.support := by
    simpa [P1] using
      (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        A.first_isPath hx1.1 hx1.2.2.symm)
  have hy1_not_Q1 : y1 ∉ Q1.support := by
    simpa [Q1] using
      (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
        A.second_isPath hx2.1 hx2.2.2.symm)
  have hy2_not_P2 : y2 ∉ P2.support := by
    simpa [P2] using
      (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        A.first_isPath hx1.1 hx1.2.1)
  have hy2_not_Q2 : y2 ∉ Q2.support := by
    simpa [Q2] using
      (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        A.second_isPath hx2.1 hx2.2.1)
  have hR : R.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint hP1.reverse hQ1 ?_
    intro z hzP1Rev hzQ1
    have hzP1 : z ∈ P1.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzP1Rev
      exact List.mem_reverse.mp hzP1Rev
    have hzFirst : z ∈ A.first.support :=
      SimpleGraph.Walk.support_takeUntil_subset A.first hx1.1
        (by simpa [P1] using hzP1)
    have hzSecond : z ∈ A.second.support :=
      SimpleGraph.Walk.support_takeUntil_subset A.second hx2.1
        (by simpa [Q1] using hzQ1)
    rcases A.support_inter_subset_endpoints hzFirst hzSecond with hzy2 | hzy1
    · exact hzy2
    · exact False.elim (hy1_not_P1 (by simpa [hzy1] using hzP1))
  refine {
    pX1X2 := R
    pX1Y1 := P2
    pX2Y1 := Q2
    pX1X2_isPath := hR
    pX1Y1_isPath := hP2
    pX2Y1_isPath := hQ2
    pX1X2_support := ?_
    pX1Y1_support := ?_
    pX2Y1_support := ?_
    y1_not_pX1X2 := ?_
    x2_not_pX1Y1 := ?_
    x1_not_pX2Y1 := ?_
    disjoint_X_X1Y1 := ?_
    disjoint_X_X2Y1 := ?_
    disjoint_X1Y1_X2Y1 := ?_
    y2_internal := ?_
  }
  · intro z hzR
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzR
    rcases hzR with hzP1Rev | hzQ1
    · have hzP1 : z ∈ P1.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzP1Rev
        exact List.mem_reverse.mp hzP1Rev
      exact A.first_support z
        (SimpleGraph.Walk.support_takeUntil_subset A.first hx1.1
          (by simpa [P1] using hzP1))
    · exact A.second_support z
        (SimpleGraph.Walk.support_takeUntil_subset A.second hx2.1
          (by simpa [Q1] using hzQ1))
  · intro z hzP2
    exact A.first_support z
      (SimpleGraph.Walk.support_dropUntil_subset A.first hx1.1
        (by simpa [P2] using hzP2))
  · intro z hzQ2
    exact A.second_support z
      (SimpleGraph.Walk.support_dropUntil_subset A.second hx2.1
        (by simpa [Q2] using hzQ2))
  · intro hy1R
    rw [SimpleGraph.Walk.mem_support_append_iff] at hy1R
    rcases hy1R with hy1P1Rev | hy1Q1
    · apply hy1_not_P1
      rw [SimpleGraph.Walk.support_reverse] at hy1P1Rev
      exact List.mem_reverse.mp hy1P1Rev
    · exact hy1_not_Q1 hy1Q1
  · intro hx2P2
    have hx2First : x2 ∈ A.first.support :=
      SimpleGraph.Walk.support_dropUntil_subset A.first hx1.1
        (by simpa [P2] using hx2P2)
    rcases A.support_inter_subset_endpoints hx2First hx2.1 with hxy2 | hxy1
    · exact hx2.2.1 hxy2
    · exact hx2.2.2 hxy1
  · intro hx1Q2
    have hx1Second : x1 ∈ A.second.support :=
      SimpleGraph.Walk.support_dropUntil_subset A.second hx2.1
        (by simpa [Q2] using hx1Q2)
    rcases A.support_inter_subset_endpoints hx1.1 hx1Second with hxy2 | hxy1
    · exact hx1.2.1 hxy2
    · exact hx1.2.2 hxy1
  · rw [Set.disjoint_left]
    intro z hzR hzP2
    have hzRSupport : z ∈ R.support := hzR.1
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzRSupport
    rcases hzRSupport with hzP1Rev | hzQ1
    · have hzP1 : z ∈ P1.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzP1Rev
        exact List.mem_reverse.mp hzP1Rev
      have hzx1 : z = x1 :=
        Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          A.first_isPath hx1.1 (by simpa [P1] using hzP1)
            (by simpa [P2] using hzP2.1)
      exact hzR.2.1 hzx1
    · have hzFirst : z ∈ A.first.support :=
        SimpleGraph.Walk.support_dropUntil_subset A.first hx1.1
          (by simpa [P2] using hzP2.1)
      have hzSecond : z ∈ A.second.support :=
        SimpleGraph.Walk.support_takeUntil_subset A.second hx2.1
          (by simpa [Q1] using hzQ1)
      rcases A.support_inter_subset_endpoints hzFirst hzSecond with hzy2 | hzy1
      · exact hy2_not_P2 (by simpa [hzy2] using hzP2.1)
      · exact hzP2.2.2 hzy1
  · rw [Set.disjoint_left]
    intro z hzR hzQ2
    have hzRSupport : z ∈ R.support := hzR.1
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzRSupport
    rcases hzRSupport with hzP1Rev | hzQ1
    · have hzP1 : z ∈ P1.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzP1Rev
        exact List.mem_reverse.mp hzP1Rev
      have hzFirst : z ∈ A.first.support :=
        SimpleGraph.Walk.support_takeUntil_subset A.first hx1.1
          (by simpa [P1] using hzP1)
      have hzSecond : z ∈ A.second.support :=
        SimpleGraph.Walk.support_dropUntil_subset A.second hx2.1
          (by simpa [Q2] using hzQ2.1)
      rcases A.support_inter_subset_endpoints hzFirst hzSecond with hzy2 | hzy1
      · exact hy2_not_Q2 (by simpa [hzy2] using hzQ2.1)
      · exact hzQ2.2.2 hzy1
    · have hzx2 : z = x2 :=
        Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
          A.second_isPath hx2.1 (by simpa [Q1] using hzQ1)
            (by simpa [Q2] using hzQ2.1)
      exact hzR.2.2 hzx2
  · rw [Set.disjoint_left]
    intro z hzP2 hzQ2
    have hzFirst : z ∈ A.first.support :=
      SimpleGraph.Walk.support_dropUntil_subset A.first hx1.1
        (by simpa [P2] using hzP2.1)
    have hzSecond : z ∈ A.second.support :=
      SimpleGraph.Walk.support_dropUntil_subset A.second hx2.1
        (by simpa [Q2] using hzQ2.1)
    rcases A.support_inter_subset_endpoints hzFirst hzSecond with hzy2 | hzy1
    · exact hy2_not_P2 (by simpa [hzy2] using hzP2.1)
    · exact hzP2.2.2 hzy1
  · have hy2P1 : y2 ∈ P1.support := P1.start_mem_support
    have hy2P1Rev : y2 ∈ P1.reverse.support := by
      rw [SimpleGraph.Walk.support_reverse]
      exact List.mem_reverse.mpr hy2P1
    have hy2R : y2 ∈ R.support := by
      rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hy2P1Rev
    exact ⟨hy2R, hx1.2.1.symm, hx2.2.1.symm⟩

end Wagner

end FourColor

end Schematic.Math.GraphTheory
