import Schematic.Math.GraphTheory.Embedding.Wagner.CycleArcs

/-! Restriction of complementary cycle arcs to an ordered subarc. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner

/-- Restrict the first cycle arc to an ordered subpath and route the
complement through its reversed prefix, the old second arc, and its reversed
suffix.  The result is again the two-arc decomposition of the same cycle. -/
noncomputable def CycleTwoArcs.subarcs
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 x2 a b : V} {C : G.Walk r r}
    (A : CycleTwoArcs C (x1 := x1) (x2 := x2))
    (ha : a ∈ A.first.support)
    (hb : b ∈ A.first.support)
    (hab : Walk.supportIndex A.first a < Walk.supportIndex A.first b) :
    CycleTwoArcs C (x1 := a) (x2 := b) := by
  classical
  let S : G.Walk a b :=
    Walk.segmentBetween A.first ha hb (Nat.le_of_lt hab)
  let pre : G.Walk x1 a := A.first.takeUntil a ha
  let suf : G.Walk b x2 := A.first.dropUntil b hb
  let L : G.Walk a x2 := pre.reverse.append A.second
  let R : G.Walk a b := L.append suf.reverse
  have ha_ne_x2 : a ≠ x2 := by
    intro h
    subst a
    have hb_le := Walk.IsPath.supportIndex_le_end A.first_isPath hb
    omega
  have hb_ne_x1 : b ≠ x1 := by
    intro h
    subst b
    have hstart := Walk.supportIndex_start_le (p := A.first) (x := a)
    omega
  have hpre : pre.IsPath := by
    simpa [pre] using A.first_isPath.takeUntil ha
  have hsuf : suf.IsPath := by
    simpa [suf] using A.first_isPath.dropUntil hb
  have hS : S.IsPath := by
    simpa [S] using
      Walk.segmentBetween_isPath A.first_isPath ha hb (Nat.le_of_lt hab)
  have hpre_second :
      forall z, z ∈ pre.reverse.support -> z ∈ A.second.support -> z = x1 := by
    intro z hzpreRev hzsecond
    have hzpre : z ∈ pre.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzpreRev
      exact List.mem_reverse.mp hzpreRev
    have hzfirst : z ∈ A.first.support :=
      SimpleGraph.Walk.support_takeUntil_subset A.first ha hzpre
    rcases A.support_inter_subset_endpoints hzfirst hzsecond with hzx1 | hzx2
    · exact hzx1
    · subst z
      exact False.elim
        (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          A.first_isPath ha ha_ne_x2.symm hzpre)
  have hL : L.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hpre.reverse A.second_isPath ?_
    intro z hzpreRev hzsecond
    exact hpre_second z hzpreRev hzsecond
  have hpre_suf_disjoint :
      Disjoint {z : V | z ∈ pre.support} {z : V | z ∈ suf.support} := by
    simpa [pre, suf] using
      Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
        A.first_isPath ha hb (by simpa [Walk.supportIndex] using hab)
  have hsecond_suf :
      forall z, z ∈ A.second.support -> z ∈ suf.reverse.support -> z = x2 := by
    intro z hzsecond hzsufRev
    have hzsuf : z ∈ suf.support := by
      rw [SimpleGraph.Walk.support_reverse] at hzsufRev
      exact List.mem_reverse.mp hzsufRev
    have hzfirst : z ∈ A.first.support :=
      SimpleGraph.Walk.support_dropUntil_subset A.first hb hzsuf
    rcases A.support_inter_subset_endpoints hzfirst hzsecond with hzx1 | hzx2
    · subst z
      exact False.elim
        (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          A.first_isPath hb hb_ne_x1 hzsuf)
    · exact hzx2
  have hL_suf :
      forall z, z ∈ L.support -> z ∈ suf.reverse.support -> z = x2 := by
    intro z hzL hzsufRev
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzL
    rcases hzL with hzpreRev | hzsecond
    · have hzpre : z ∈ pre.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzpreRev
        exact List.mem_reverse.mp hzpreRev
      have hzsuf : z ∈ suf.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzsufRev
        exact List.mem_reverse.mp hzsufRev
      exact False.elim
        (Set.disjoint_left.mp hpre_suf_disjoint hzpre hzsuf)
    · exact hsecond_suf z hzsecond hzsufRev
  have hR : R.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint hL hsuf.reverse ?_
    intro z hzL hzsufRev
    exact hL_suf z hzL hzsufRev
  refine {
    first := S
    second := R
    endpoints_ne := by
      intro heq
      subst b
      omega
    first_isPath := hS
    second_isPath := hR
    first_support := ?_
    second_support := ?_
    first_edges := ?_
    second_edges := ?_
    internally_disjoint := ?_
    cover := ?_
  }
  · intro z hzS
    exact A.first_support z
      (Walk.segmentBetween_support_subset ha hb (Nat.le_of_lt hab)
        (by simpa [S] using hzS))
  · intro z hzR
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzR
    rcases hzR with hzL | hzsufRev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hzL
      rcases hzL with hzpreRev | hzsecond
      · have hzpre : z ∈ pre.support := by
          rw [SimpleGraph.Walk.support_reverse] at hzpreRev
          exact List.mem_reverse.mp hzpreRev
        exact A.first_support z
          (SimpleGraph.Walk.support_takeUntil_subset A.first ha hzpre)
      · exact A.second_support z hzsecond
    · have hzsuf : z ∈ suf.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzsufRev
        exact List.mem_reverse.mp hzsufRev
      exact A.first_support z
        (SimpleGraph.Walk.support_dropUntil_subset A.first hb hzsuf)
  · intro e heS
    change e ∈
      (Walk.segmentBetween A.first ha hb (Nat.le_of_lt hab)).edges at heS
    unfold Walk.segmentBetween at heS
    have heDrop := SimpleGraph.Walk.edges_takeUntil_subset _ _ heS
    exact A.first_edges e
      (SimpleGraph.Walk.edges_dropUntil_subset A.first ha heDrop)
  · intro e heR
    change e ∈ (L.append suf.reverse).edges at heR
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at heR
    rcases heR with heL | heSufRev
    · change e ∈ (pre.reverse.append A.second).edges at heL
      rw [SimpleGraph.Walk.edges_append, List.mem_append] at heL
      rcases heL with hePreRev | heSecond
      · rw [SimpleGraph.Walk.edges_reverse] at hePreRev
        have hePre : e ∈ pre.edges := List.mem_reverse.mp hePreRev
        exact A.first_edges e
          (SimpleGraph.Walk.edges_takeUntil_subset A.first ha hePre)
      · exact A.second_edges e heSecond
    · rw [SimpleGraph.Walk.edges_reverse] at heSufRev
      have heSuf : e ∈ suf.edges := List.mem_reverse.mp heSufRev
      exact A.first_edges e
        (SimpleGraph.Walk.edges_dropUntil_subset A.first hb heSuf)
  · rw [Set.disjoint_left]
    intro z hzS hzR
    have hzSsupport : z ∈ S.support := hzS.1
    have hzRsupport : z ∈ R.support := hzR.1
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzRsupport
    rcases hzRsupport with hzL | hzsufRev
    · rw [SimpleGraph.Walk.mem_support_append_iff] at hzL
      rcases hzL with hzpreRev | hzsecond
      · have hzpre : z ∈ pre.support := by
          rw [SimpleGraph.Walk.support_reverse] at hzpreRev
          exact List.mem_reverse.mp hzpreRev
        have hza : z = a :=
          Walk.takeUntil_support_inter_segmentBetween_subset_left
            A.first_isPath ha hb (Nat.le_of_lt hab) hzpre
              (by simpa [S] using hzSsupport)
        exact hzS.2.1 hza
      · have hzfirst : z ∈ A.first.support :=
          Walk.segmentBetween_support_subset ha hb (Nat.le_of_lt hab)
            (by simpa [S] using hzSsupport)
        rcases A.support_inter_subset_endpoints hzfirst hzsecond with hzx1 | hzx2
        · have ha_le_z :=
            Walk.segmentBetween_supportIndex_left_le A.first_isPath
              ha hb (Nat.le_of_lt hab) (by simpa [S] using hzSsupport)
          have hx1_le_a := Walk.supportIndex_start_le
            (p := A.first) (x := a)
          have hidx :
              Walk.supportIndex A.first a = Walk.supportIndex A.first x1 := by
            exact le_antisymm (by simpa [hzx1] using ha_le_z) hx1_le_a
          have hax1 : a = x1 :=
            Walk.supportIndex_injective_of_mem ha hidx
          exact hzS.2.1 (hzx1.trans hax1.symm)
        · have hz_le_b :=
            Walk.segmentBetween_supportIndex_right_le ha hb
              (Nat.le_of_lt hab) (by simpa [S] using hzSsupport)
          have hb_le_x2 := Walk.IsPath.supportIndex_le_end A.first_isPath hb
          have hidx :
              Walk.supportIndex A.first b = Walk.supportIndex A.first x2 := by
            exact le_antisymm hb_le_x2 (by simpa [hzx2] using hz_le_b)
          have hbx2 : b = x2 :=
            Walk.supportIndex_injective_of_mem hb hidx
          exact hzS.2.2 (hzx2.trans hbx2.symm)
    · have hzsuf : z ∈ suf.support := by
        rw [SimpleGraph.Walk.support_reverse] at hzsufRev
        exact List.mem_reverse.mp hzsufRev
      have hzb : z = b :=
        Walk.segmentBetween_support_inter_dropUntil_subset_right
          A.first_isPath ha hb (Nat.le_of_lt hab)
            (by simpa [S] using hzSsupport) hzsuf
      exact hzS.2.2 hzb
  · intro z hzC
    rcases A.cover z hzC with hzfirst | hzsecond
    · by_cases hza :
          Walk.supportIndex A.first z <= Walk.supportIndex A.first a
      · right
        have hzpre : z ∈ pre.support := by
          exact Walk.mem_support_takeUntil_of_idxOf_le ha hzfirst
            (by simpa [Walk.supportIndex] using hza)
        have hzpreRev : z ∈ pre.reverse.support := by
          rw [SimpleGraph.Walk.support_reverse]
          exact List.mem_reverse.mpr hzpre
        have hzL : z ∈ L.support := by
          rw [SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inl hzpreRev
        rw [SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inl hzL
      · by_cases hzb :
          Walk.supportIndex A.first b <= Walk.supportIndex A.first z
        · right
          have hzsuf : z ∈ suf.support :=
            Walk.mem_support_dropUntil_of_idxOf_le hb hzfirst
              (by simpa [Walk.supportIndex] using hzb)
          have hzsufRev : z ∈ suf.reverse.support := by
            rw [SimpleGraph.Walk.support_reverse]
            exact List.mem_reverse.mpr hzsuf
          rw [SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hzsufRev
        · left
          have ha_le_z :
              Walk.supportIndex A.first a <= Walk.supportIndex A.first z := by
            omega
          have hz_le_b :
              Walk.supportIndex A.first z <= Walk.supportIndex A.first b := by
            omega
          have hzS : z ∈
              (Walk.segmentBetween A.first ha hb (Nat.le_of_lt hab)).support :=
            Walk.mem_support_segmentBetween_of_supportIndex_between
              ha hzfirst hb ha_le_z hz_le_b
          simpa [S] using hzS
    · right
      have hzL : z ∈ L.support := by
        rw [SimpleGraph.Walk.mem_support_append_iff]
        exact Or.inr hzsecond
      rw [SimpleGraph.Walk.mem_support_append_iff]
      exact Or.inl hzL

@[simp] theorem CycleTwoArcs.subarcs_first
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x1 x2 a b : V} {C : G.Walk r r}
    (A : CycleTwoArcs C (x1 := x1) (x2 := x2))
    (ha : a ∈ A.first.support)
    (hb : b ∈ A.first.support)
    (hab : Walk.supportIndex A.first a < Walk.supportIndex A.first b) :
    (A.subarcs ha hb hab).first =
      Walk.segmentBetween A.first ha hb (Nat.le_of_lt hab) := by
  simp [CycleTwoArcs.subarcs]

end Wagner

end FourColor

end Schematic.Math.GraphTheory
