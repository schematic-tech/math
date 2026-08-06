import Schematic.Math.GraphTheory.PathsTrees.Foundations.PathIntervals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
def Walk.chordShortcut
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    G.Walk u v :=
  ((p.takeUntil x hx).append hxy.toWalk).append (p.dropUntil y hy)

theorem Walk.length_chordShortcut
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    (Walk.chordShortcut p hx hy hxy).length =
      p.support.idxOf x + 1 + (p.length - p.support.idxOf y) := by
  simp [Walk.chordShortcut, SimpleGraph.Walk.length_takeUntil,
    SimpleGraph.Walk.length_dropUntil, Nat.add_assoc]

theorem Walk.chordShortcut_length_lt_of_idx_gap
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y)
    (hidx : p.support.idxOf x + 1 < p.support.idxOf y) :
    (Walk.chordShortcut p hx hy hxy).length < p.length := by
  rw [Walk.length_chordShortcut]
  have hyidx_le : p.support.idxOf y <= p.length := by
    have hyidx_lt := List.idxOf_lt_length_of_mem hy
    rw [SimpleGraph.Walk.length_support] at hyidx_lt
    omega
  omega

theorem Walk.chordShortcut_support_subset
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    {z : V | z ∈ (Walk.chordShortcut p hx hy hxy).support} ⊆
      {z : V | z ∈ p.support} := by
  intro z hz
  simp only [Walk.chordShortcut, SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · exact SimpleGraph.Walk.support_takeUntil_subset p hx hz
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
  · exact SimpleGraph.Walk.support_dropUntil_subset p hy hz

theorem Walk.chordShortcut_bypass_support_subset
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    {z : V | z ∈ (Walk.chordShortcut p hx hy hxy).bypass.support} ⊆
      {z : V | z ∈ p.support} := by
  intro z hz
  exact Walk.chordShortcut_support_subset p hx hy hxy
    (SimpleGraph.Walk.support_bypass_subset _ hz)

theorem Walk.IsPath.length_le_of_support_subset
    [DecidableEq V]
    {u v u' v' : V}
    {p : G.Walk u v}
    {q : G.Walk u' v'}
    (hp : p.IsPath)
    (hsubset : forall z : V, z ∈ p.support -> z ∈ q.support) :
    p.length <= q.length := by
  have hlen :
      p.support.length <= q.support.length :=
    list_length_le_of_nodup_subset hp.support_nodup hsubset
  rw [SimpleGraph.Walk.length_support, SimpleGraph.Walk.length_support] at hlen
  omega

theorem Walk.toSubgraph_adj_of_idxOf_succ_eq
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hidx : p.support.idxOf x + 1 = p.support.idxOf y) :
    p.toSubgraph.Adj x y := by
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  have hxlt : p.support.idxOf x < p.support.length :=
    List.idxOf_lt_length_of_mem hx
  have hylt : p.support.idxOf y < p.support.length :=
    List.idxOf_lt_length_of_mem hy
  have hinfix : [x, y] <:+: p.support := by
    rw [List.infix_iff_getElem?]
    refine ⟨p.support.idxOf x, ?_, ?_⟩
    · change 2 + p.support.idxOf x <= p.support.length
      omega
    intro j hj
    have hjlt : j < 2 := by
      simpa using hj
    have hj_cases : j = 0 ∨ j = 1 := by omega
    rcases hj_cases with rfl | rfl
    · simp only [Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_eq_getElem hxlt]
      exact congrArg some (List.getElem_idxOf hxlt)
    · have hpos : 1 + p.support.idxOf x = p.support.idxOf y := by omega
      simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [hpos, List.getElem?_eq_getElem hylt]
      exact congrArg some (List.getElem_idxOf hylt)
  exact
    (SimpleGraph.Walk.infix_support_iff_mem_edges
      (p := p) (u' := x) (v' := y)).mp (Or.inl hinfix)

theorem Walk.toSubgraph_adj_or_idx_gap_of_support_adj
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    p.toSubgraph.Adj x y ∨
      p.support.idxOf x + 1 < p.support.idxOf y ∨
        p.support.idxOf y + 1 < p.support.idxOf x := by
  rcases lt_trichotomy (p.support.idxOf x) (p.support.idxOf y) with hlt | heq | hgt
  · have hle : p.support.idxOf x + 1 <= p.support.idxOf y := by omega
    rcases lt_or_eq_of_le hle with hgap | hsucc
    · exact Or.inr (Or.inl hgap)
    · exact Or.inl (Walk.toSubgraph_adj_of_idxOf_succ_eq p hx hy hsucc)
  · have hxy_eq : x = y := (List.idxOf_inj hx).mp heq
    exact False.elim (hxy.ne hxy_eq)
  · have hle : p.support.idxOf y + 1 <= p.support.idxOf x := by omega
    rcases lt_or_eq_of_le hle with hgap | hsucc
    · exact Or.inr (Or.inr hgap)
    · exact Or.inl (Walk.toSubgraph_adj_of_idxOf_succ_eq p hy hx hsucc).symm

theorem Walk.IsPath.reachable_between_ends_in_delete_start_of_common_nonstart
    [DecidableEq V]
    {root a b z : V}
    {p : G.Walk root a}
    {q : G.Walk root b}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hzroot : z ≠ root) :
    (G.induce ({root} : Set V)ᶜ).Reachable
      ⟨a, by
        intro ha
        exact (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hp hzp hzroot) (ha ▸ (p.dropUntil z hzp).end_mem_support)⟩
      ⟨b, by
        intro hb
        exact (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hq hzq hzroot) (hb ▸ (q.dropUntil z hzq).end_mem_support)⟩ := by
  let r : G.Walk a b :=
    (p.dropUntil z hzp).reverse.append (q.dropUntil z hzq)
  have hp_avoid :
      root ∉ (p.dropUntil z hzp).support :=
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne hp hzp hzroot
  have hq_avoid :
      root ∉ (q.dropUntil z hzq).support :=
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne hq hzq hzroot
  have hr_avoid : forall y : V, y ∈ r.support -> y ≠ root := by
    intro y hy hyroot
    simp [r, SimpleGraph.Walk.mem_support_append_iff] at hy
    rcases hy with hy_rev | hy_q
    · exact hp_avoid (by simpa [hyroot] using hy_rev)
    · exact hq_avoid (by simpa [hyroot] using hy_q)
  exact Walk.reachable_induce_compl_singleton_of_support_avoids r hr_avoid

theorem Walk.IsPath.common_vertex_eq_start_of_delete_start_unreachable
    [DecidableEq V]
    {root a b z : V}
    {p : G.Walk root a}
    {q : G.Walk root b}
    (ha : a ≠ root)
    (hb : b ≠ root)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hunreachable :
      ¬ (G.induce ({root} : Set V)ᶜ).Reachable
          ⟨a, by exact ha⟩ ⟨b, by exact hb⟩)
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support) :
    z = root := by
  by_contra hzroot
  exact hunreachable (by
    simpa using
      (Walk.IsPath.reachable_between_ends_in_delete_start_of_common_nonstart
        hp hq hzp hzq hzroot))

theorem Walk.IsPath.support_takeUntil_inter_support_dropUntil_subset_singleton
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    {z : V |
        z ∈ (p.takeUntil w hw).support ∧
          z ∈ (p.dropUntil w hw).support} ⊆ ({w} : Set V) := by
  intro z hz
  simpa [Set.mem_singleton_iff] using
    (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hw hz.1 hz.2)

theorem Walk.IsPath.punctured_takeUntil_support_disjoint_dropUntil_support
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      {z : V | z ∈ (p.takeUntil w hw).support ∧ z ≠ w}
      {z : V | z ∈ (p.dropUntil w hw).support} := by
  rw [Set.disjoint_left]
  rintro z ⟨hz_take, hzne⟩ hz_drop
  exact hzne
    (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hw hz_take hz_drop)

theorem Walk.IsPath.takeUntil_support_disjoint_punctured_dropUntil_support
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      {z : V | z ∈ (p.takeUntil w hw).support}
      {z : V | z ∈ (p.dropUntil w hw).support ∧ z ≠ w} := by
  rw [Set.disjoint_left]
  rintro z hz_take ⟨hz_drop, hzne⟩
  exact hzne
    (Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hw hz_take hz_drop)

theorem Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support) :
    Disjoint
      (Walk.InternalVertices (p.takeUntil w hw))
      (Walk.InternalVertices (p.dropUntil w hw)) := by
  rw [Set.disjoint_left]
  intro z hz_take hz_drop
  have hzw :
      z = w :=
    Schematic.Math.GraphTheory.Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      hp hw hz_take.1 hz_drop.1
  exact hz_take.2.2 hzw

/-- Cutting a simple cycle at a vertex gives two arcs with disjoint internal
vertices.  This is the cycle analogue of
`Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil`;
the proof uses the cycle support count to rule out a non-endpoint appearing on
both sides of the cut. -/
theorem Walk.IsCycle.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
    [DecidableEq V]
    {u w : V}
    {c : G.Walk u u}
    (hc : c.IsCycle)
    (hw : w ∈ c.support) :
    Disjoint
      (Walk.InternalVertices (c.takeUntil w hw))
      (Walk.InternalVertices (c.dropUntil w hw)) := by
  rw [Set.disjoint_left]
  intro z hz_take hz_drop
  have hz_c : z ∈ c.support :=
    SimpleGraph.Walk.support_takeUntil_subset c hw hz_take.1
  have hzu : z ≠ u := hz_take.2.1
  have hzw : z ≠ w := hz_take.2.2
  have hz_drop_tail : z ∈ (c.dropUntil w hw).support.tail := by
    have hz_drop_support : z ∈ (c.dropUntil w hw).support := hz_drop.1
    rw [SimpleGraph.Walk.mem_support_iff] at hz_drop_support
    exact hz_drop_support.resolve_left hzw
  have hsupport :
      c.support =
        (c.takeUntil w hw).support ++ (c.dropUntil w hw).support.tail := by
    rw [← SimpleGraph.Walk.support_append]
    simp [SimpleGraph.Walk.take_spec]
  have hcount_ge_two : 2 <= c.support.count z := by
    rw [hsupport, List.count_append]
    have hcount_take : 1 <= (c.takeUntil w hw).support.count z :=
      List.one_le_count_iff.mpr hz_take.1
    have hcount_drop : 1 <= (c.dropUntil w hw).support.tail.count z :=
      List.one_le_count_iff.mpr hz_drop_tail
    omega
  have hcount_one : c.support.count z = 1 :=
    hc.count_support_of_mem hz_c hzu
  omega

theorem Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hw_ne_end : w ≠ v) :
    Walk.InternalVertices (p.takeUntil w hw) ⊆ Walk.InternalVertices p := by
  intro z hz
  refine ⟨SimpleGraph.Walk.support_takeUntil_subset p hw hz.1, hz.2.1, ?_⟩
  intro hz_end
  have hend_not_prefix : v ∉ (p.takeUntil w hw).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil hp hw hw_ne_end.symm
  exact hend_not_prefix (hz_end ▸ hz.1)

theorem Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
    [DecidableEq V]
    {u v w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hw : w ∈ p.support)
    (hw_ne_start : w ≠ u) :
    Walk.InternalVertices (p.dropUntil w hw) ⊆ Walk.InternalVertices p := by
  intro z hz
  refine ⟨SimpleGraph.Walk.support_dropUntil_subset p hw hz.1, ?_, hz.2.2⟩
  intro hz_start
  have hstart_not_suffix : u ∉ (p.dropUntil w hw).support :=
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne hp hw hw_ne_start
  exact hstart_not_suffix (hz_start ▸ hz.1)

theorem Walk.IsPath.leaf_mem_support_eq_endpoint
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    [Fintype (G.neighborSet x)]
    (hdegree : G.degree x = 1)
    (hx : x ∈ p.support) :
    x = u ∨ x = v := by
  classical
  by_cases hxu : x = u
  · exact Or.inl hxu
  · by_cases hxv : x = v
    · exact Or.inr hxv
    · have hsub : (G.neighborSet x).Subsingleton := by
        rcases (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree) with
          ⟨y, hy, hy_unique⟩
        intro a ha b hb
        exact (hy_unique a ha).trans (hy_unique b hb).symm
      exact False.elim
        (hp.isTrail.not_mem_support_of_subsingleton_neighborSet
          hxu hxv hsub hx)

theorem Walk.IsPath.not_mem_internalVertices_of_toSubgraph_le_degree_one
    {H : G.Subgraph}
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ H)
    [Fintype (H.neighborSet x)]
    (hdegree : H.degree x = 1) :
    x ∉ Walk.InternalVertices p := by
  classical
  intro hx
  obtain ⟨n, hn_eq, hn_le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx.1
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hx_eq_u : x = u := by
      simpa [hn_zero] using hn_eq.symm
    exact hx.2.1 hx_eq_u
  have hn_lt : n < p.length := by
    by_contra hn_not_lt
    have hn_length : n = p.length := by omega
    have hx_eq_v : x = v := by
      simpa [hn_length] using hn_eq.symm
    exact hx.2.2 hx_eq_v
  have hp_neighbor_ncard :
      (p.toSubgraph.neighborSet x).ncard = 2 := by
    simpa [hn_eq] using
      hp.ncard_neighborSet_toSubgraph_internal_eq_two hn_ne_zero hn_lt
  have hH_neighbor_ncard :
      (H.neighborSet x).ncard = 1 := by
    simpa [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card'] using hdegree
  have hle :
      (p.toSubgraph.neighborSet x).ncard <= (H.neighborSet x).ncard :=
    Set.ncard_le_ncard
      (SimpleGraph.Subgraph.neighborSet_subset_of_subgraph hp_le x)
  omega

theorem Walk.IsPath.ncard_neighborSet_toSubgraph_eq_two_of_mem_internalVertices
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ Walk.InternalVertices p) :
    (p.toSubgraph.neighborSet x).ncard = 2 := by
  obtain ⟨n, hn_eq, _hn_le⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx.1
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hx_eq_u : x = u := by
      simpa [hn_zero] using hn_eq.symm
    exact hx.2.1 hx_eq_u
  have hn_lt : n < p.length := by
    by_contra hn_not_lt
    have hn_length : n = p.length := by omega
    have hx_eq_v : x = v := by
      simpa [hn_length] using hn_eq.symm
    exact hx.2.2 hx_eq_v
  simpa [hn_eq] using
    hp.ncard_neighborSet_toSubgraph_internal_eq_two hn_ne_zero hn_lt

theorem Walk.IsPath.not_mem_internalVertices_of_degree_le_one
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    [Fintype (G.neighborSet x)]
    (hdegree : G.degree x <= 1) :
    x ∉ Walk.InternalVertices p := by
  classical
  intro hx
  have hp_neighbor_ncard :
      (p.toSubgraph.neighborSet x).ncard = 2 :=
    Walk.IsPath.ncard_neighborSet_toSubgraph_eq_two_of_mem_internalVertices
      hp hx
  have hneighbor_sub :
      p.toSubgraph.neighborSet x ⊆ G.neighborSet x := by
    intro y hy
    exact p.toSubgraph.adj_sub hy
  have hle :
      (p.toSubgraph.neighborSet x).ncard <= (G.neighborSet x).ncard :=
    Set.ncard_le_ncard hneighbor_sub
  have hdegree_ncard :
      (G.neighborSet x).ncard = G.degree x := by
    simp [Set.ncard_eq_toFinset_card']
  omega

theorem Walk.IsPath.ncard_neighborSet_toSubgraph_le_two_of_mem_support
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support) :
    (p.toSubgraph.neighborSet x).ncard <= 2 := by
  classical
  by_cases hnil : p.Nil
  · cases hnil
    simp [SimpleGraph.Walk.toSubgraph]
  · obtain ⟨i, hix, hi_le⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hi0 : i = 0
    · have hx_eq : x = u := by
        simpa [hi0] using hix.symm
      rw [hx_eq]
      rw [hp.neighborSet_toSubgraph_startpoint hnil]
      simp
    · by_cases hilast : i = p.length
      · have hx_eq : x = v := by
          rw [← hix, hilast]
          exact p.getVert_length
        rw [hx_eq]
        rw [hp.neighborSet_toSubgraph_endpoint hnil]
        simp
      · have hi_lt : i < p.length := lt_of_le_of_ne hi_le hilast
        have hcard :
            (p.toSubgraph.neighborSet x).ncard = 2 := by
          simpa [hix] using
            hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hi_lt
        omega

theorem Walk.IsPath.degree_ge_three_of_internal_and_extra_neighbor
    {H : G.Subgraph}
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ H)
    (hx : x ∈ Walk.InternalVertices p)
    [Fintype (H.neighborSet x)]
    (hy : y ∈ H.neighborSet x)
    (hy_not_path : y ∉ p.toSubgraph.neighborSet x) :
    3 <= H.degree x := by
  classical
  have hp_neighbor_ncard :
      (p.toSubgraph.neighborSet x).ncard = 2 :=
    Walk.IsPath.ncard_neighborSet_toSubgraph_eq_two_of_mem_internalVertices hp hx
  have hinsert_sub :
      insert y (p.toSubgraph.neighborSet x) ⊆ H.neighborSet x := by
    intro z hz
    rcases hz with rfl | hz_path
    · exact hy
    · exact SimpleGraph.Subgraph.neighborSet_subset_of_subgraph hp_le x hz_path
  have hpath_neighbor_finite :
      (p.toSubgraph.neighborSet x).Finite :=
    (Set.toFinite (H.neighborSet x)).subset
      (SimpleGraph.Subgraph.neighborSet_subset_of_subgraph hp_le x)
  have hinsert_ncard :
      (insert y (p.toSubgraph.neighborSet x)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hy_not_path hpath_neighbor_finite]
    rw [hp_neighbor_ncard]
  have hle :
      (insert y (p.toSubgraph.neighborSet x)).ncard <=
        (H.neighborSet x).ncard :=
    Set.ncard_le_ncard hinsert_sub
  have hdegree_ncard :
      (H.neighborSet x).ncard = H.degree x := by
    simp [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
  omega

/-- If a vertex of ambient degree at most two is internal on a simple path,
then every ambient neighbor of that vertex is one of the two neighbors supplied
by the path.  This is the local suppression fact used in the degree-two branch
of the Makarychev/Skopenkov contraction proof. -/
theorem Walk.IsPath.neighbor_mem_toSubgraph_of_internal_degree_le_two
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ Walk.InternalVertices p)
    [Fintype (G.neighborSet x)]
    (hdegree : G.degree x <= 2)
    (hxy : G.Adj x y) :
    y ∈ p.toSubgraph.neighborSet x := by
  classical
  by_contra hy_not_path
  let H : G.Subgraph := ⊤
  letI : Fintype (H.neighborSet x) := by
    change Fintype ((⊤ : G.Subgraph).neighborSet x)
    rw [SimpleGraph.Subgraph.neighborSet_top]
    infer_instance
  have hge : 3 <= H.degree x :=
    Walk.IsPath.degree_ge_three_of_internal_and_extra_neighbor
      (G := G) (H := H) (p := p) hp (by exact le_top) hx
      (by
        change y ∈ (⊤ : G.Subgraph).neighborSet x
        simpa using hxy)
      (by
        simpa [H] using hy_not_path)
  have htop_le : H.degree x <= G.degree x :=
    SimpleGraph.Subgraph.degree_le H x
  omega

theorem Walk.IsPath.degree_ge_two_of_start_and_extra_neighbor
    {H : G.Subgraph}
    {u v y : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (huv : u ≠ v)
    [Fintype (H.neighborSet u)]
    (hy : y ∈ H.neighborSet u)
    (hy_not_path : y ∉ p.toSubgraph.neighborSet u) :
    2 <= H.degree u := by
  classical
  have hnot_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) huv
  have hpath_neighbor :
      p.snd ∈ p.toSubgraph.neighborSet u :=
    SimpleGraph.Walk.toSubgraph_adj_snd p hnot_nil
  have hpath_neighbor_sub :
      p.snd ∈ H.neighborSet u :=
    SimpleGraph.Subgraph.neighborSet_subset_of_subgraph hp_le u hpath_neighbor
  have hy_ne_snd : y ≠ p.snd := by
    intro h
    exact hy_not_path (by simpa [h] using hpath_neighbor)
  have hpair_sub : ({y, p.snd} : Set V) ⊆ H.neighborSet u := by
    intro z hz
    rcases hz with rfl | hz
    · exact hy
    · have hz_eq : z = p.snd := Set.mem_singleton_iff.mp hz
      simpa [hz_eq] using hpath_neighbor_sub
  have hpair_ncard : ({y, p.snd} : Set V).ncard = 2 := by
    simp [hy_ne_snd]
  have hle :
      ({y, p.snd} : Set V).ncard <= (H.neighborSet u).ncard :=
    Set.ncard_le_ncard hpair_sub
  have hdegree_ncard :
      (H.neighborSet u).ncard = H.degree u := by
    simp [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
  omega

theorem Walk.IsPath.start_neighbor_mem_toSubgraph_of_degree_one
    {H : G.Subgraph}
    {u v y : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (huv : u ≠ v)
    [Fintype (H.neighborSet u)]
    (hdegree : H.degree u = 1)
    (hy : y ∈ H.neighborSet u) :
    y ∈ p.toSubgraph.neighborSet u := by
  by_contra hy_not_path
  have hdeg_ge :
      2 <= H.degree u :=
    Walk.IsPath.degree_ge_two_of_start_and_extra_neighbor
      hp_le huv hy hy_not_path
  omega

theorem Walk.IsPath.start_neighbor_eq_snd_of_degree_one
    {H : G.Subgraph}
    {u v y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ H)
    (huv : u ≠ v)
    [Fintype (H.neighborSet u)]
    (hdegree : H.degree u = 1)
    (hy : y ∈ H.neighborSet u) :
    y = p.snd := by
  have hy_path :
      y ∈ p.toSubgraph.neighborSet u :=
    Walk.IsPath.start_neighbor_mem_toSubgraph_of_degree_one
      hp_le huv hdegree hy
  have hnot_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) huv
  have hneighbors :
      p.toSubgraph.neighborSet u = {p.snd} :=
    hp.neighborSet_toSubgraph_startpoint hnot_nil
  exact Set.mem_singleton_iff.mp (by simpa [hneighbors] using hy_path)

theorem Walk.IsPath.degree_ge_two_of_end_and_extra_neighbor
    {H : G.Subgraph}
    {u v y : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (huv : u ≠ v)
    [Fintype (H.neighborSet v)]
    (hy : y ∈ H.neighborSet v)
    (hy_not_path : y ∉ p.toSubgraph.neighborSet v) :
    2 <= H.degree v := by
  simpa using
    Walk.IsPath.degree_ge_two_of_start_and_extra_neighbor
      (G := G) (H := H) (u := v) (v := u) (y := y)
      (p := p.reverse)
      (by simpa using hp_le)
      huv.symm hy (by
        simpa using hy_not_path)

theorem Walk.IsPath.end_neighbor_mem_toSubgraph_of_degree_one
    {H : G.Subgraph}
    {u v y : V}
    {p : G.Walk u v}
    (hp_le : p.toSubgraph ≤ H)
    (huv : u ≠ v)
    [Fintype (H.neighborSet v)]
    (hdegree : H.degree v = 1)
    (hy : y ∈ H.neighborSet v) :
    y ∈ p.toSubgraph.neighborSet v := by
  by_contra hy_not_path
  have hdeg_ge :
      2 <= H.degree v :=
    Walk.IsPath.degree_ge_two_of_end_and_extra_neighbor
      hp_le huv hy hy_not_path
  omega

theorem Walk.IsPath.end_neighbor_eq_penultimate_of_degree_one
    {H : G.Subgraph}
    {u v y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ H)
    (huv : u ≠ v)
    [Fintype (H.neighborSet v)]
    (hdegree : H.degree v = 1)
    (hy : y ∈ H.neighborSet v) :
    y = p.penultimate := by
  have hy_path :
      y ∈ p.toSubgraph.neighborSet v :=
    Walk.IsPath.end_neighbor_mem_toSubgraph_of_degree_one
      hp_le huv hdegree hy
  have hnot_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) huv
  have hneighbors :
      p.toSubgraph.neighborSet v = {p.penultimate} :=
    hp.neighborSet_toSubgraph_endpoint hnot_nil
  exact Set.mem_singleton_iff.mp (by simpa [hneighbors] using hy_path)

theorem Walk.IsPath.mem_support_eq_endpoint_of_toSubgraph_le_degree_one
    {H : G.Subgraph}
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ H)
    [Fintype (H.neighborSet x)]
    (hdegree : H.degree x = 1)
    (hx : x ∈ p.support) :
    x = u ∨ x = v := by
  by_cases hxu : x = u
  · exact Or.inl hxu
  · by_cases hxv : x = v
    · exact Or.inr hxv
    · exact False.elim
        (Walk.IsPath.not_mem_internalVertices_of_toSubgraph_le_degree_one
          hp hp_le hdegree ⟨hx, hxu, hxv⟩)

theorem Walk.IsPath.not_mem_support_of_toSubgraph_le_degree_one_of_ne_endpoints
    {H : G.Subgraph}
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ H)
    [Fintype (H.neighborSet x)]
    (hdegree : H.degree x = 1)
    (hx_ne_u : x ≠ u)
    (hx_ne_v : x ≠ v) :
    x ∉ p.support := by
  intro hx
  rcases Walk.IsPath.mem_support_eq_endpoint_of_toSubgraph_le_degree_one
      hp hp_le hdegree hx with hx_eq_u | hx_eq_v
  · exact hx_ne_u hx_eq_u
  · exact hx_ne_v hx_eq_v

theorem Subgraph.Walk.IsPath.mem_support_tree_leaf_eq_endpoint
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v : B.verts}
    {x : T.verts}
    {p : B.coe.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    [Fintype (T.coe.neighborSet x)]
    [Fintype (T.neighborSet (x : B.verts))]
    (hdegree : T.coe.degree x = 1)
    (hx : (x : B.verts) ∈ p.support) :
    (x : B.verts) = u ∨ (x : B.verts) = v := by
  have hdegree_sub : T.degree (x : B.verts) = 1 := by
    simpa using (SimpleGraph.Subgraph.coe_degree T x).symm.trans hdegree
  exact
    Walk.IsPath.mem_support_eq_endpoint_of_toSubgraph_le_degree_one
      (G := B.coe) (H := T) hp hp_le hdegree_sub hx

theorem Subgraph.Walk.IsPath.tree_leaf_not_mem_support_of_ne_endpoints
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v : B.verts}
    {x : T.verts}
    {p : B.coe.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    [Fintype (T.coe.neighborSet x)]
    [Fintype (T.neighborSet (x : B.verts))]
    (hdegree : T.coe.degree x = 1)
    (hx_ne_u : (x : B.verts) ≠ u)
    (hx_ne_v : (x : B.verts) ≠ v) :
    (x : B.verts) ∉ p.support := by
  intro hx
  rcases Subgraph.Walk.IsPath.mem_support_tree_leaf_eq_endpoint
      (G := G) (B := B) (T := T) hp hp_le hdegree hx with hx_eq_u | hx_eq_v
  · exact hx_ne_u hx_eq_u
  · exact hx_ne_v hx_eq_v

theorem Subgraph.Walk.IsPath.tree_leaf_not_mem_mapped_support_of_ne_endpoints
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v : B.verts}
    {x : T.verts}
    {p : B.coe.Walk u v}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    [Fintype (T.coe.neighborSet x)]
    [Fintype (T.neighborSet (x : B.verts))]
    (hdegree : T.coe.degree x = 1)
    (hx_ne_u : (x : B.verts) ≠ u)
    (hx_ne_v : (x : B.verts) ≠ v) :
    ((x : B.verts) : V) ∉ (p.map B.hom).support := by
  intro hx
  rw [SimpleGraph.Walk.support_map] at hx
  rcases List.mem_map.mp hx with ⟨z, hz_support, hz_eq⟩
  have hz_eq_x : z = (x : B.verts) := by
    apply Subtype.ext
    exact hz_eq
  exact
    Subgraph.Walk.IsPath.tree_leaf_not_mem_support_of_ne_endpoints
      (G := G) (B := B) (T := T) hp hp_le hdegree hx_ne_u hx_ne_v
      (by simpa [hz_eq_x] using hz_support)

theorem Subgraph.Walk.start_neighbor_mem_toSubgraph_of_tree_leaf
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v y : T.verts}
    {p : B.coe.Walk (u : B.verts) (v : B.verts)}
    (hp_le : p.toSubgraph ≤ T)
    (huv : (u : B.verts) ≠ (v : B.verts))
    [Fintype (T.coe.neighborSet u)]
    [Fintype (T.neighborSet (u : B.verts))]
    (hdegree : T.coe.degree u = 1)
    (hy : (y : B.verts) ∈ T.neighborSet (u : B.verts)) :
    (y : B.verts) ∈ p.toSubgraph.neighborSet (u : B.verts) := by
  have hdegree_sub : T.degree (u : B.verts) = 1 := by
    simpa using (SimpleGraph.Subgraph.coe_degree T u).symm.trans hdegree
  exact
    Walk.IsPath.start_neighbor_mem_toSubgraph_of_degree_one
      (G := B.coe) (H := T) (u := (u : B.verts)) (v := (v : B.verts))
      (y := (y : B.verts)) (p := p) hp_le huv hdegree_sub hy

theorem Subgraph.Walk.start_neighbor_eq_snd_of_tree_leaf
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v y : T.verts}
    {p : B.coe.Walk (u : B.verts) (v : B.verts)}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    (huv : (u : B.verts) ≠ (v : B.verts))
    [Fintype (T.coe.neighborSet u)]
    [Fintype (T.neighborSet (u : B.verts))]
    (hdegree : T.coe.degree u = 1)
    (hy : (y : B.verts) ∈ T.neighborSet (u : B.verts)) :
    (y : B.verts) = p.snd := by
  have hdegree_sub : T.degree (u : B.verts) = 1 := by
    simpa using (SimpleGraph.Subgraph.coe_degree T u).symm.trans hdegree
  exact
    Walk.IsPath.start_neighbor_eq_snd_of_degree_one
      (G := B.coe) (H := T) (u := (u : B.verts)) (v := (v : B.verts))
      (y := (y : B.verts)) (p := p) hp hp_le huv hdegree_sub hy

theorem Subgraph.Walk.end_neighbor_mem_toSubgraph_of_tree_leaf
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v y : T.verts}
    {p : B.coe.Walk (u : B.verts) (v : B.verts)}
    (hp_le : p.toSubgraph ≤ T)
    (huv : (u : B.verts) ≠ (v : B.verts))
    [Fintype (T.coe.neighborSet v)]
    [Fintype (T.neighborSet (v : B.verts))]
    (hdegree : T.coe.degree v = 1)
    (hy : (y : B.verts) ∈ T.neighborSet (v : B.verts)) :
    (y : B.verts) ∈ p.toSubgraph.neighborSet (v : B.verts) := by
  have hdegree_sub : T.degree (v : B.verts) = 1 := by
    simpa using (SimpleGraph.Subgraph.coe_degree T v).symm.trans hdegree
  exact
    Walk.IsPath.end_neighbor_mem_toSubgraph_of_degree_one
      (G := B.coe) (H := T) (u := (u : B.verts)) (v := (v : B.verts))
      (y := (y : B.verts)) (p := p) hp_le huv hdegree_sub hy

theorem Subgraph.Walk.end_neighbor_eq_penultimate_of_tree_leaf
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {u v y : T.verts}
    {p : B.coe.Walk (u : B.verts) (v : B.verts)}
    (hp : p.IsPath)
    (hp_le : p.toSubgraph ≤ T)
    (huv : (u : B.verts) ≠ (v : B.verts))
    [Fintype (T.coe.neighborSet v)]
    [Fintype (T.neighborSet (v : B.verts))]
    (hdegree : T.coe.degree v = 1)
    (hy : (y : B.verts) ∈ T.neighborSet (v : B.verts)) :
    (y : B.verts) = p.penultimate := by
  have hdegree_sub : T.degree (v : B.verts) = 1 := by
    simpa using (SimpleGraph.Subgraph.coe_degree T v).symm.trans hdegree
  exact
    Walk.IsPath.end_neighbor_eq_penultimate_of_degree_one
      (G := B.coe) (H := T) (u := (u : B.verts)) (v := (v : B.verts))
      (y := (y : B.verts)) (p := p) hp hp_le huv hdegree_sub hy

theorem walk_punctured_supports_disjoint_of_forall_eq_root
    {ι : Type*}
    {root : V}
    (stem : ι -> Sigma fun terminal : V => G.Walk root terminal)
    (hmeet :
      forall {i j : ι}, i ≠ j ->
        forall {z : V},
          z ∈ (stem i).2.support ->
            z ∈ (stem j).2.support ->
              z = root) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).2.support ∧ z ≠ root}
        {z : V | z ∈ (stem j).2.support ∧ z ≠ root} := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hzne⟩ ⟨hzj, _hzjne⟩
  exact hzne (hmeet hij hzi hzj)

theorem walk_family_punctured_supports_disjoint_of_forall_eq_root
    {ι : Type*}
    {root : V}
    {terminal : ι -> V}
    (stem : forall i : ι, G.Walk root (terminal i))
    (hmeet :
      forall {i j : ι}, i ≠ j ->
        forall {z : V},
          z ∈ (stem i).support ->
            z ∈ (stem j).support ->
              z = root) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).support ∧ z ≠ root}
        {z : V | z ∈ (stem j).support ∧ z ≠ root} := by
  intro i j hij
  rw [Set.disjoint_left]
  rintro z ⟨hzi, hzne⟩ ⟨hzj, _hzjne⟩
  exact hzne (hmeet hij hzi hzj)

theorem walk_family_punctured_supports_disjoint_of_delete_root_unreachable
    [DecidableEq V]
    {ι : Type*}
    {root : V}
    {terminal : ι -> V}
    (stem : forall i : ι, G.Walk root (terminal i))
    (hterminal_ne : forall i : ι, terminal i ≠ root)
    (hstem_path : forall i : ι, (stem i).IsPath)
    (hunreachable :
      forall {i j : ι}, i ≠ j ->
        ¬ (G.induce ({root} : Set V)ᶜ).Reachable
            ⟨terminal i, by exact hterminal_ne i⟩
            ⟨terminal j, by exact hterminal_ne j⟩) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).support ∧ z ≠ root}
        {z : V | z ∈ (stem j).support ∧ z ≠ root} := by
  refine walk_family_punctured_supports_disjoint_of_forall_eq_root
    (G := G) (root := root) (terminal := terminal) stem ?_
  intro i j hij z hzi hzj
  exact
    Walk.IsPath.common_vertex_eq_start_of_delete_start_unreachable
      (hterminal_ne i) (hterminal_ne j) (hstem_path i) (hstem_path j)
      (hunreachable hij) hzi hzj

theorem walk_support_punctured_disjoint_of_forall_not_mem
    {u v : V}
    (p : G.Walk u v)
    {ι : Type*}
    (stem : ι -> Sigma fun start : V => Sigma fun terminal : V => G.Walk start terminal)
    (endpoint : ι -> V)
    (hnot :
      forall i : ι, forall {z : V},
        z ∈ Walk.InternalVertices p ->
          z ∈ (stem i).2.2.support ->
            z ≠ endpoint i ->
              False) :
    forall i : ι,
      Disjoint
        (Walk.InternalVertices p)
        {z : V | z ∈ (stem i).2.2.support ∧ z ≠ endpoint i} := by
  intro i
  rw [Set.disjoint_left]
  rintro z hzbridge ⟨hzstem, hzend⟩
  exact hnot i hzbridge hzstem hzend

theorem Walk.punctured_support_nil_eq_empty
    {u : V} :
    {z : V | z ∈ (SimpleGraph.Walk.nil : G.Walk u u).support ∧ z ≠ u} = ∅ := by
  ext z
  simp

theorem Walk.disjoint_punctured_support_nil_left
    {u : V}
    (A : Set V) :
    Disjoint
      {z : V | z ∈ (SimpleGraph.Walk.nil : G.Walk u u).support ∧ z ≠ u} A := by
  rw [Walk.punctured_support_nil_eq_empty]
  rw [Set.disjoint_left]
  simp

theorem Walk.disjoint_punctured_support_nil_right
    {u : V}
    (A : Set V) :
    Disjoint A
      {z : V | z ∈ (SimpleGraph.Walk.nil : G.Walk u u).support ∧ z ≠ u} := by
  exact (Walk.disjoint_punctured_support_nil_left (G := G) (u := u) A).symm


end Schematic.Math.GraphTheory
