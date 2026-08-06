import Schematic.Math.GraphTheory.PathsTrees.Foundations.ShortcutsAndDegrees

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
def IsPathSubgraph {V : Type u} {G : SimpleGraph V} (P : G.Subgraph) : Prop :=
  P.coe.Connected ∧ forall v : P.verts, Nat.card (P.coe.neighborSet v) <= 2

def IsCycleSubgraph {V : Type u} {G : SimpleGraph V} (C : G.Subgraph) : Prop :=
  C.coe.Connected ∧ forall v : C.verts, Nat.card (C.coe.neighborSet v) = 2

private theorem walk_toSubgraph_coe_neighbor_natCard_eq_subgraph_neighbor_ncard
    {u v : V} (p : G.Walk u v) (x : p.toSubgraph.verts) :
    Nat.card (p.toSubgraph.coe.neighborSet x) =
      (p.toSubgraph.neighborSet (x : V)).ncard := by
  classical
  letI : Fintype (p.toSubgraph.neighborSet (x : V)) :=
    (p.finite_neighborSet_toSubgraph).fintype
  letI : Fintype (p.toSubgraph.coe.neighborSet x) :=
    SimpleGraph.Subgraph.coeFiniteAt x
  rw [Nat.card_eq_fintype_card]
  rw [Set.ncard_eq_toFinset_card' (p.toSubgraph.neighborSet (x : V))]
  rw [Set.toFinset_card]
  exact Fintype.card_congr (SimpleGraph.Subgraph.coeNeighborSetEquiv x)

theorem Walk.isPathSubgraph_toSubgraph
    {u v : V}
    (p : G.Walk u v)
    (hp : p.IsPath) :
    IsPathSubgraph p.toSubgraph := by
  classical
  constructor
  · exact p.toSubgraph_connected.coe
  · intro x
    rw [walk_toSubgraph_coe_neighbor_natCard_eq_subgraph_neighbor_ncard p x]
    have hx_support : (x : V) ∈ p.support := p.mem_verts_toSubgraph.mp x.2
    by_cases hnil : p.Nil
    · cases hnil
      simp [SimpleGraph.Walk.toSubgraph]
    · obtain ⟨i, hix, hi_le⟩ :=
        SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx_support
      by_cases hi0 : i = 0
      · have hx_eq : (x : V) = u := by
          simpa [hi0] using hix.symm
        rw [hx_eq]
        rw [hp.neighborSet_toSubgraph_startpoint hnil]
        simp
      · by_cases hilast : i = p.length
        · have hx_eq : (x : V) = v := by
            rw [← hix, hilast]
            exact p.getVert_length
          rw [hx_eq]
          rw [hp.neighborSet_toSubgraph_endpoint hnil]
          simp
        · have hi_lt : i < p.length := lt_of_le_of_ne hi_le hilast
          rw [← hix]
          rw [hp.neighborSet_toSubgraph_internal hi0 hi_lt]
          calc
            ({p.getVert (i - 1), p.getVert (i + 1)} : Set V).ncard <=
                ({p.getVert (i + 1)} : Set V).ncard + 1 := by
              simpa using
                Set.ncard_insert_le (p.getVert (i - 1))
                  ({p.getVert (i + 1)} : Set V)
            _ = 2 := by simp

theorem Walk.isCycleSubgraph_toSubgraph
    {u : V}
    (p : G.Walk u u)
    (hp : p.IsCycle) :
    IsCycleSubgraph p.toSubgraph := by
  constructor
  · exact p.toSubgraph_connected.coe
  · intro x
    rw [walk_toSubgraph_coe_neighbor_natCard_eq_subgraph_neighbor_ncard p x]
    exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp x.2)

theorem Walk.IsChordless.toSubgraph_adj_of_adj
    {u v : V}
    {p : G.Walk u v}
    (hchordless : p.IsChordless)
    {x y : V}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : G.Adj x y) :
    p.toSubgraph.Adj x y := by
  rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact hchordless.mem_edges hx hy hxy

theorem Walk.IsChordless.neighborSet_inter_support_subset_toSubgraph_neighborSet
    {u v x : V}
    {p : G.Walk u v}
    (hchordless : p.IsChordless)
  (hx : x ∈ p.support) :
    G.neighborSet x ∩ {y : V | y ∈ p.support} ⊆
      p.toSubgraph.neighborSet x := by
  intro y hy
  exact Schematic.Math.GraphTheory.Walk.IsChordless.toSubgraph_adj_of_adj hchordless hx hy.2 hy.1

theorem Walk.IsPath.ncard_neighborSet_inter_support_le_two_of_isChordless
    [Fintype V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hchordless : p.IsChordless)
  (hx : x ∈ p.support) :
    (G.neighborSet x ∩ {y : V | y ∈ p.support}).ncard <= 2 := by
  exact le_trans
    (Set.ncard_le_ncard
      (Schematic.Math.GraphTheory.Walk.IsChordless.neighborSet_inter_support_subset_toSubgraph_neighborSet
        hchordless hx)
      (ht := p.finite_neighborSet_toSubgraph))
    (Schematic.Math.GraphTheory.Walk.IsPath.ncard_neighborSet_toSubgraph_le_two_of_mem_support hp hx)

theorem Walk.IsPath.ncard_neighborSet_inter_support_le_one_of_start_isChordless
    [Fintype V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hchordless : p.IsChordless) :
    (G.neighborSet u ∩ {y : V | y ∈ p.support}).ncard <= 1 := by
  have hsubset :
      G.neighborSet u ∩ {y : V | y ∈ p.support} ⊆
        p.toSubgraph.neighborSet u :=
    Schematic.Math.GraphTheory.Walk.IsChordless.neighborSet_inter_support_subset_toSubgraph_neighborSet
      hchordless p.start_mem_support
  have hright : (p.toSubgraph.neighborSet u).ncard <= 1 := by
    classical
    by_cases hnil : p.Nil
    · cases hnil
      simp [SimpleGraph.Walk.toSubgraph]
    · rw [hp.neighborSet_toSubgraph_startpoint hnil]
      simp
  exact le_trans
    (Set.ncard_le_ncard hsubset (ht := p.finite_neighborSet_toSubgraph))
    hright

theorem Walk.IsPath.ncard_neighborSet_inter_support_le_one_of_end_isChordless
    [Fintype V]
    {u v : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hchordless : p.IsChordless) :
    (G.neighborSet v ∩ {y : V | y ∈ p.support}).ncard <= 1 := by
  have hsubset :
      G.neighborSet v ∩ {y : V | y ∈ p.support} ⊆
        p.toSubgraph.neighborSet v :=
    Schematic.Math.GraphTheory.Walk.IsChordless.neighborSet_inter_support_subset_toSubgraph_neighborSet
      hchordless p.end_mem_support
  have hright : (p.toSubgraph.neighborSet v).ncard <= 1 := by
    classical
    by_cases hnil : p.Nil
    · cases hnil
      simp [SimpleGraph.Walk.toSubgraph]
    · rw [hp.neighborSet_toSubgraph_endpoint hnil]
      simp
  exact le_trans
    (Set.ncard_le_ncard hsubset (ht := p.finite_neighborSet_toSubgraph))
    hright

theorem Walk.not_isChordless_iff_exists_adj_not_toSubgraph_adj
    {u v : V}
    (p : G.Walk u v) :
    ¬ p.IsChordless ↔
      Exists fun x : V =>
        x ∈ p.support ∧
          Exists fun y : V =>
            y ∈ p.support ∧ G.Adj x y ∧ ¬ p.toSubgraph.Adj x y := by
  constructor
  · intro hnot
    rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges] at hnot
    push Not at hnot
    rcases hnot with ⟨x, y, hx, hy, hxy, hnot_edge⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact hnot_edge
  · rintro ⟨x, hx, y, hy, hxy, hnot_toSubgraph⟩ hchordless
    exact hnot_toSubgraph
      (Schematic.Math.GraphTheory.Walk.IsChordless.toSubgraph_adj_of_adj hchordless hx hy hxy)

theorem Walk.isChordless_of_length_eq_dist
    [DecidableEq V]
    {u v : V}
    (p : G.Walk u v)
    (hpdist : p.length = G.dist u v) :
    p.IsChordless := by
  by_contra hnot
  obtain ⟨x, hx, y, hy, hxy, hnot_toSubgraph⟩ :=
    (Walk.not_isChordless_iff_exists_adj_not_toSubgraph_adj
      (G := G) p).mp hnot
  have hgap :=
    Walk.toSubgraph_adj_or_idx_gap_of_support_adj
      (G := G) p hx hy hxy
  rcases hgap with htoSubgraph | hgap
  · exact hnot_toSubgraph htoSubgraph
  · rcases hgap with hxy_gap | hyx_gap
    · have hshort :
          (Walk.chordShortcut p hx hy hxy).length < p.length :=
        Walk.chordShortcut_length_lt_of_idx_gap p hx hy hxy hxy_gap
      have hdist_le :
          G.dist u v <= (Walk.chordShortcut p hx hy hxy).length :=
        SimpleGraph.dist_le (Walk.chordShortcut p hx hy hxy)
      omega
    · have hshort :
          (Walk.chordShortcut p hy hx hxy.symm).length < p.length :=
        Walk.chordShortcut_length_lt_of_idx_gap p hy hx hxy.symm hyx_gap
      have hdist_le :
          G.dist u v <= (Walk.chordShortcut p hy hx hxy.symm).length :=
        SimpleGraph.dist_le (Walk.chordShortcut p hy hx hxy.symm)
      omega

theorem Walk.toSubgraph_eq_induce_support_of_isChordless
    {u v : V}
    (p : G.Walk u v)
    (hchordless : p.IsChordless) :
    p.toSubgraph =
      (⊤ : G.Subgraph).induce {x : V | x ∈ p.support} := by
  ext x y
  · rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    simp [SimpleGraph.Subgraph.induce]
  · constructor
    · intro hxy
      exact ⟨p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxy),
        p.mem_verts_toSubgraph.mp
          (p.toSubgraph.edge_vert (p.toSubgraph.symm hxy)),
        p.toSubgraph.adj_sub hxy⟩
    · intro hxy
      exact Walk.IsChordless.toSubgraph_adj_of_adj
        hchordless hxy.1 hxy.2.1 (by simpa using hxy.2.2)

def Walk.supportIndex
    [DecidableEq V]
    {u v : V}
    (p : G.Walk u v)
    (x : V) : Nat :=
  p.support.idxOf x

theorem Walk.supportIndex_start_le
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v} :
    Walk.supportIndex p u <= Walk.supportIndex p x := by
  rw [Walk.supportIndex, Walk.idxOf_start_support]
  exact Nat.zero_le _

theorem Walk.supportIndex_lt_support_length
    [DecidableEq V]
    {u v : V}
    (p : G.Walk u v)
    {x : V}
    (hx : x ∈ p.support) :
    Walk.supportIndex p x < p.support.length := by
  simpa [Walk.supportIndex] using
    (List.idxOf_lt_length_iff.mpr hx)

theorem Walk.supportIndex_injective_of_mem
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    {x y : V}
    (hx : x ∈ p.support)
    (hidx : Walk.supportIndex p x = Walk.supportIndex p y) :
    x = y := by
  exact (List.idxOf_inj hx).mp (by
    simpa [Walk.supportIndex] using hidx)

theorem Walk.IsPath.supportIndex_le_end
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support) :
    Walk.supportIndex p x <= Walk.supportIndex p v := by
  by_cases hxv : x = v
  · simp [Walk.supportIndex, hxv]
  · exact le_of_lt (by
      simpa [Walk.supportIndex] using
        Walk.IsPath.idxOf_lt_end_of_mem_support_ne_end hp hx hxv)

theorem Walk.supportIndex_ne_of_mem_of_ne
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    {x y : V}
    (hx : x ∈ p.support)
    (hxy : x ≠ y) :
    Walk.supportIndex p x ≠ Walk.supportIndex p y := by
  intro hidx
  exact hxy (Walk.supportIndex_injective_of_mem hx hidx)

theorem Walk.supportIndex_lt_of_le_of_mem_of_ne
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    {x y : V}
    (hx : x ∈ p.support)
    (hle : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hxy : x ≠ y) :
    Walk.supportIndex p x < Walk.supportIndex p y := by
  have hne : Walk.supportIndex p x ≠ Walk.supportIndex p y :=
    Walk.supportIndex_ne_of_mem_of_ne hx hxy
  omega

theorem Walk.support_disjoint_of_supportIndex_bounds
    [DecidableEq V]
    {u v s t a b : V}
    {p : G.Walk u v}
    {qLeft : G.Walk s t}
    {qRight : G.Walk a b}
    {first last : V}
    (hidx : Walk.supportIndex p first < Walk.supportIndex p last)
    (hleft :
      forall z : V, z ∈ qLeft.support ->
        Walk.supportIndex p z <= Walk.supportIndex p first)
    (hright :
      forall z : V, z ∈ qRight.support ->
        Walk.supportIndex p last <= Walk.supportIndex p z) :
    Disjoint {z : V | z ∈ qLeft.support}
      {z : V | z ∈ qRight.support} := by
  rw [Set.disjoint_left]
  intro z hzLeft hzRight
  have hz_le := hleft z hzLeft
  have hlast_le := hright z hzRight
  omega

theorem Walk.exists_ordered_three_support_indices
    [DecidableEq V]
    {u v : V}
    {p : G.Walk u v}
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (hfeet_mem : forall i : Fin 3, feet i ∈ p.support) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        Exists fun k : Fin 3 =>
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            Walk.supportIndex p (feet i) <
              Walk.supportIndex p (feet j) ∧
            Walk.supportIndex p (feet j) <
              Walk.supportIndex p (feet k) := by
  classical
  let n0 := Walk.supportIndex p (feet 0)
  let n1 := Walk.supportIndex p (feet 1)
  let n2 := Walk.supportIndex p (feet 2)
  have h01v : feet 0 ≠ feet 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (hfeet_injective h)
  have h02v : feet 0 ≠ feet 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (hfeet_injective h)
  have h12v : feet 1 ≠ feet 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (hfeet_injective h)
  have h01 : n0 ≠ n1 := by
    simpa [n0, n1] using
      Walk.supportIndex_ne_of_mem_of_ne (hfeet_mem 0) h01v
  have h02 : n0 ≠ n2 := by
    simpa [n0, n2] using
      Walk.supportIndex_ne_of_mem_of_ne (hfeet_mem 0) h02v
  have h12 : n1 ≠ n2 := by
    simpa [n1, n2] using
      Walk.supportIndex_ne_of_mem_of_ne (hfeet_mem 1) h12v
  by_cases h0lt1 : n0 < n1
  · by_cases h1lt2 : n1 < n2
    · exact ⟨0, 1, 2, by decide, by decide, by decide,
        by simpa [n0, n1] using h0lt1,
        by simpa [n1, n2] using h1lt2⟩
    · have h2lt1 : n2 < n1 :=
        lt_of_le_of_ne (Nat.le_of_not_gt h1lt2) h12.symm
      by_cases h0lt2 : n0 < n2
      · exact ⟨0, 2, 1, by decide, by decide, by decide,
          by simpa [n0, n2] using h0lt2,
          by simpa [n2, n1] using h2lt1⟩
      · have h2lt0 : n2 < n0 :=
          lt_of_le_of_ne (Nat.le_of_not_gt h0lt2) h02.symm
        exact ⟨2, 0, 1, by decide, by decide, by decide,
          by simpa [n2, n0] using h2lt0,
          by simpa [n0, n1] using h0lt1⟩
  · have h1lt0 : n1 < n0 :=
      lt_of_le_of_ne (Nat.le_of_not_gt h0lt1) h01.symm
    by_cases h0lt2 : n0 < n2
    · exact ⟨1, 0, 2, by decide, by decide, by decide,
        by simpa [n1, n0] using h1lt0,
        by simpa [n0, n2] using h0lt2⟩
    · have h2lt0 : n2 < n0 :=
        lt_of_le_of_ne (Nat.le_of_not_gt h0lt2) h02.symm
      by_cases h1lt2 : n1 < n2
      · exact ⟨1, 2, 0, by decide, by decide, by decide,
          by simpa [n1, n2] using h1lt2,
          by simpa [n2, n0] using h2lt0⟩
      · have h2lt1 : n2 < n1 :=
          lt_of_le_of_ne (Nat.le_of_not_gt h1lt2) h12.symm
        exact ⟨2, 1, 0, by decide, by decide, by decide,
          by simpa [n2, n1] using h2lt1,
          by simpa [n1, n0] using h1lt0⟩

def Walk.segmentBetween
    [DecidableEq V]
    {u v x y : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y) :
    G.Walk x y :=
  (p.dropUntil x hx).takeUntil y
    (Walk.mem_support_dropUntil_of_idxOf_le hx hy (by
      simpa [Walk.supportIndex] using hxy))

theorem Walk.segmentBetween_isPath
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y) :
    (Walk.segmentBetween p hx hy hxy).IsPath := by
  unfold Walk.segmentBetween
  exact (hp.dropUntil hx).takeUntil
    (Walk.mem_support_dropUntil_of_idxOf_le hx hy (by
      simpa [Walk.supportIndex] using hxy))

theorem Walk.segmentBetween_support_subset
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz : z ∈ (Walk.segmentBetween p hx hy hxy).support) :
    z ∈ p.support := by
  unfold Walk.segmentBetween at hz
  exact SimpleGraph.Walk.support_dropUntil_subset p hx
    (SimpleGraph.Walk.support_takeUntil_subset _ _ hz)

theorem Walk.mem_support_segmentBetween_of_supportIndex_between
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hyz : Walk.supportIndex p y <= Walk.supportIndex p z) :
    y ∈
      (Walk.segmentBetween p hx hz (le_trans hxy hyz)).support := by
  unfold Walk.segmentBetween
  have hmem_take :
      y ∈
        (p.dropUntil x hx).support.take
          ((p.dropUntil x hx).support.idxOf z + 1) := by
    rw [SimpleGraph.Walk.dropUntil_eq_drop]
    simp only [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min]
    have hxidx_le_length : p.support.idxOf x <= p.length := by
      have hxlt := List.idxOf_lt_length_of_mem hx
      rw [SimpleGraph.Walk.length_support] at hxlt
      omega
    rw [Nat.min_eq_left hxidx_le_length]
    exact
      list_mem_drop_take_idxOf_succ_of_idxOf_between
        hx hy hz (by simpa [Walk.supportIndex] using hxy)
        (by simpa [Walk.supportIndex] using hyz)
  simpa [SimpleGraph.Walk.takeUntil_eq_take,
    SimpleGraph.Walk.take_support_eq_support_take_succ] using hmem_take

theorem Walk.segmentBetween_supportIndex_left_le
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz : z ∈ (Walk.segmentBetween p hx hy hxy).support) :
    Walk.supportIndex p x <= Walk.supportIndex p z := by
  unfold Walk.segmentBetween at hz
  have hz_drop :
      z ∈ (p.dropUntil x hx).support :=
    SimpleGraph.Walk.support_takeUntil_subset _ _ hz
  simpa [Walk.supportIndex] using
    (Walk.idxOf_le_of_mem_dropUntil hp hx hz_drop)

theorem Walk.segmentBetween_supportIndex_right_le
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz : z ∈ (Walk.segmentBetween p hx hy hxy).support) :
    Walk.supportIndex p z <= Walk.supportIndex p y := by
  unfold Walk.segmentBetween at hz
  simp only [SimpleGraph.Walk.takeUntil_eq_take,
    SimpleGraph.Walk.dropUntil_eq_drop,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.take_support_eq_support_take_succ,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
  have hxidx_le_length : p.support.idxOf x <= p.length := by
    have hxlt := List.idxOf_lt_length_of_mem hx
    rw [SimpleGraph.Walk.length_support] at hxlt
    omega
  rw [Nat.min_eq_left hxidx_le_length] at hz
  exact
    list_idxOf_le_of_mem_drop_take_idxOf_succ_of_nodup
      hx hy (by simpa [Walk.supportIndex] using hxy)
      (by simpa [Walk.supportIndex] using hz)

theorem Walk.segmentBetween_support_inter_subset_common
    [DecidableEq V]
    {u v x y z w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hyz : Walk.supportIndex p y <= Walk.supportIndex p z)
    (hw_left : w ∈ (Walk.segmentBetween p hx hy hxy).support)
    (hw_right : w ∈ (Walk.segmentBetween p hy hz hyz).support) :
    w = y := by
  have hw_p : w ∈ p.support :=
    Walk.segmentBetween_support_subset hx hy hxy hw_left
  have hle_y :
      Walk.supportIndex p w <= Walk.supportIndex p y :=
    Walk.segmentBetween_supportIndex_right_le hx hy hxy hw_left
  have hy_le :
      Walk.supportIndex p y <= Walk.supportIndex p w :=
    Walk.segmentBetween_supportIndex_left_le hp hy hz hyz hw_right
  exact
    (Walk.supportIndex_injective_of_mem hw_p
      (le_antisymm hle_y hy_le))

theorem Walk.takeUntil_support_inter_segmentBetween_subset_left
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz_take : z ∈ (p.takeUntil x hx).support)
    (hz_seg : z ∈ (Walk.segmentBetween p hx hy hxy).support) :
    z = x := by
  have hz_p : z ∈ p.support :=
    SimpleGraph.Walk.support_takeUntil_subset p hx hz_take
  have hz_le_x : Walk.supportIndex p z <= Walk.supportIndex p x := by
    simpa [Walk.supportIndex] using
      Walk.idxOf_le_of_mem_takeUntil hx hz_take
  have hx_le_z :
      Walk.supportIndex p x <= Walk.supportIndex p z :=
    Walk.segmentBetween_supportIndex_left_le hp hx hy hxy hz_seg
  exact
    Walk.supportIndex_injective_of_mem hz_p
      (le_antisymm hz_le_x hx_le_z)

theorem Walk.segmentBetween_support_inter_dropUntil_subset_right
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz_seg : z ∈ (Walk.segmentBetween p hx hy hxy).support)
    (hz_drop : z ∈ (p.dropUntil y hy).support) :
    z = y := by
  have hz_p : z ∈ p.support :=
    Walk.segmentBetween_support_subset hx hy hxy hz_seg
  have hz_le_y :
      Walk.supportIndex p z <= Walk.supportIndex p y :=
    Walk.segmentBetween_supportIndex_right_le hx hy hxy hz_seg
  have hy_le_z : Walk.supportIndex p y <= Walk.supportIndex p z := by
    simpa [Walk.supportIndex] using
      Walk.idxOf_le_of_mem_dropUntil hp hy hz_drop
  exact
    Walk.supportIndex_injective_of_mem hz_p
      (le_antisymm hz_le_y hy_le_z)

theorem Walk.takeUntil_reverse_support_inter_segmentBetween_subset_left
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz_take : z ∈ (p.takeUntil x hx).reverse.support)
    (hz_seg : z ∈ (Walk.segmentBetween p hx hy hxy).support) :
    z = x := by
  have hz_take' : z ∈ (p.takeUntil x hx).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_take
    exact List.mem_reverse.mp hz_take
  exact
    Walk.takeUntil_support_inter_segmentBetween_subset_left
      hp hx hy hxy hz_take' hz_seg

theorem Walk.segmentBetween_support_inter_dropUntil_reverse_subset_right
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz_seg : z ∈ (Walk.segmentBetween p hx hy hxy).support)
    (hz_drop : z ∈ (p.dropUntil y hy).reverse.support) :
    z = y := by
  have hz_drop' : z ∈ (p.dropUntil y hy).support := by
    rw [SimpleGraph.Walk.support_reverse] at hz_drop
    exact List.mem_reverse.mp hz_drop
  exact
    Walk.segmentBetween_support_inter_dropUntil_subset_right
      hp hx hy hxy hz_seg hz_drop'

theorem Walk.segmentBetween_punctured_support_disjoint
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hyz : Walk.supportIndex p y <= Walk.supportIndex p z) :
    Disjoint
      {w : V | w ∈ (Walk.segmentBetween p hx hy hxy).support ∧ w ≠ y}
      {w : V | w ∈ (Walk.segmentBetween p hy hz hyz).support ∧ w ≠ y} := by
  rw [Set.disjoint_left]
  intro w hw_left hw_right
  exact hw_left.2
    (Walk.segmentBetween_support_inter_subset_common
      hp hx hy hz hxy hyz hw_left.1 hw_right.1)

theorem Walk.segmentBetween_support_disjoint_of_right_lt_left
    [DecidableEq V]
    {u v x y z w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hw : w ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hzw : Walk.supportIndex p z <= Walk.supportIndex p w)
    (hyz : Walk.supportIndex p y < Walk.supportIndex p z) :
    Disjoint
      {a : V | a ∈ (Walk.segmentBetween p hx hy hxy).support}
      {a : V | a ∈ (Walk.segmentBetween p hz hw hzw).support} := by
  rw [Set.disjoint_left]
  intro a ha_left ha_right
  have ha_le_y :
      Walk.supportIndex p a <= Walk.supportIndex p y :=
    Walk.segmentBetween_supportIndex_right_le hx hy hxy ha_left
  have hz_le_a :
      Walk.supportIndex p z <= Walk.supportIndex p a :=
    Walk.segmentBetween_supportIndex_left_le hp hz hw hzw ha_right
  omega

theorem Walk.segmentBetween_reverse_support_subset
    [DecidableEq V]
    {u v x y z : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hz : z ∈ (Walk.segmentBetween p hx hy hxy).reverse.support) :
    z ∈ p.support := by
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
  exact Walk.segmentBetween_support_subset hx hy hxy hz

theorem Walk.segmentBetween_reverse_isPath
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y) :
    (Walk.segmentBetween p hx hy hxy).reverse.IsPath :=
  (Walk.segmentBetween_isPath hp hx hy hxy).reverse

theorem Walk.segmentBetween_reverse_support_disjoint_of_right_lt_left
    [DecidableEq V]
    {u v x y z w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hw : w ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hzw : Walk.supportIndex p z <= Walk.supportIndex p w)
    (hyz : Walk.supportIndex p y < Walk.supportIndex p z) :
    Disjoint
      {a : V | a ∈ (Walk.segmentBetween p hx hy hxy).reverse.support}
      {a : V | a ∈ (Walk.segmentBetween p hz hw hzw).support} := by
  rw [Set.disjoint_left]
  intro a ha_left ha_right
  have ha_left' :
      a ∈ (Walk.segmentBetween p hx hy hxy).support := by
    have h :
        a ∈ (Walk.segmentBetween p hx hy hxy).support.reverse := by
      simpa [SimpleGraph.Walk.support_reverse] using ha_left
    exact List.mem_reverse.mp h
  have hdis :=
    Walk.segmentBetween_support_disjoint_of_right_lt_left
      hp hx hy hz hw hxy hzw hyz
  exact
    (Set.disjoint_left.mp hdis (by simpa using ha_left')) ha_right

theorem Walk.segmentBetween_support_disjoint_reverse_of_right_lt_left
    [DecidableEq V]
    {u v x y z w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hw : w ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hzw : Walk.supportIndex p z <= Walk.supportIndex p w)
    (hyz : Walk.supportIndex p y < Walk.supportIndex p z) :
    Disjoint
      {a : V | a ∈ (Walk.segmentBetween p hx hy hxy).support}
      {a : V | a ∈ (Walk.segmentBetween p hz hw hzw).reverse.support} := by
  rw [Set.disjoint_left]
  intro a ha_left ha_right
  have ha_right' :
      a ∈ (Walk.segmentBetween p hz hw hzw).support := by
    have h :
        a ∈ (Walk.segmentBetween p hz hw hzw).support.reverse := by
      simpa [SimpleGraph.Walk.support_reverse] using ha_right
    exact List.mem_reverse.mp h
  have hdis :=
    Walk.segmentBetween_support_disjoint_of_right_lt_left
      hp hx hy hz hw hxy hzw hyz
  exact
    (Set.disjoint_left.mp hdis ha_left) (by simpa using ha_right')

theorem Walk.segmentBetween_reverse_support_disjoint_reverse_of_right_lt_left
    [DecidableEq V]
    {u v x y z w : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hz : z ∈ p.support)
    (hw : w ∈ p.support)
    (hxy : Walk.supportIndex p x <= Walk.supportIndex p y)
    (hzw : Walk.supportIndex p z <= Walk.supportIndex p w)
    (hyz : Walk.supportIndex p y < Walk.supportIndex p z) :
    Disjoint
      {a : V | a ∈ (Walk.segmentBetween p hx hy hxy).reverse.support}
      {a : V | a ∈ (Walk.segmentBetween p hz hw hzw).reverse.support} := by
  rw [Set.disjoint_left]
  intro a ha_left ha_right
  have ha_left' :
      a ∈ (Walk.segmentBetween p hx hy hxy).support := by
    have h :
        a ∈ (Walk.segmentBetween p hx hy hxy).support.reverse := by
      simpa [SimpleGraph.Walk.support_reverse] using ha_left
    exact List.mem_reverse.mp h
  have ha_right' :
      a ∈ (Walk.segmentBetween p hz hw hzw).support := by
    have h :
        a ∈ (Walk.segmentBetween p hz hw hzw).support.reverse := by
      simpa [SimpleGraph.Walk.support_reverse] using ha_right
    exact List.mem_reverse.mp h
  have hdis :=
    Walk.segmentBetween_support_disjoint_of_right_lt_left
      hp hx hy hz hw hxy hzw hyz
  exact
    (Set.disjoint_left.mp hdis (by simpa using ha_left'))
      (by simpa using ha_right')

def Walk.prefixTailToStart
    [DecidableEq V]
    {u v x : V}
    (p : G.Walk u v)
    (hx : x ∈ p.support) :
    G.Walk x u :=
  (Walk.segmentBetween p p.start_mem_support hx
    (Walk.supportIndex_start_le (p := p))).reverse

def Walk.suffixTailToEnd
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
  (hp : p.IsPath)
  (hx : x ∈ p.support) :
  G.Walk x v :=
  Walk.segmentBetween p hx p.end_mem_support
    (Walk.IsPath.supportIndex_le_end hp hx)

theorem Walk.prefixTailToStart_isPath
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support) :
    (Walk.prefixTailToStart p hx).IsPath := by
  simpa [Walk.prefixTailToStart] using
    Walk.segmentBetween_reverse_isPath
      hp p.start_mem_support hx
      (Walk.supportIndex_start_le (p := p))

theorem Walk.suffixTailToEnd_isPath
    [DecidableEq V]
    {u v x : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support) :
    (Walk.suffixTailToEnd hp hx).IsPath := by
  simpa [Walk.suffixTailToEnd] using
    Walk.segmentBetween_isPath hp hx p.end_mem_support
      (Walk.IsPath.supportIndex_le_end hp hx)

theorem Walk.prefixTailToStart_support_subset
    [DecidableEq V]
    {u v x z : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hz : z ∈ (Walk.prefixTailToStart p hx).support) :
    z ∈ p.support := by
  simpa [Walk.prefixTailToStart] using
    Walk.segmentBetween_reverse_support_subset
      p.start_mem_support hx
      (Walk.supportIndex_start_le (p := p)) hz

theorem Walk.suffixTailToEnd_support_subset
    [DecidableEq V]
    {u v x z : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hz : z ∈ (Walk.suffixTailToEnd hp hx).support) :
    z ∈ p.support := by
  simpa [Walk.suffixTailToEnd] using
    Walk.segmentBetween_support_subset hx p.end_mem_support
      (Walk.IsPath.supportIndex_le_end hp hx) hz

theorem Walk.prefixTailToStart_support_disjoint_suffixTailToEnd
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hx : x ∈ p.support)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x < Walk.supportIndex p y) :
    Disjoint
      {z : V | z ∈ (Walk.prefixTailToStart p hx).support}
      {z : V | z ∈ (Walk.suffixTailToEnd hp hy).support} := by
  simpa [Walk.prefixTailToStart, Walk.suffixTailToEnd] using
    Walk.segmentBetween_reverse_support_disjoint_of_right_lt_left
      hp p.start_mem_support hx hy p.end_mem_support
      (Walk.supportIndex_start_le (p := p))
      (Walk.IsPath.supportIndex_le_end hp hy) hxy

theorem Walk.not_mem_prefixTailToStart_of_lt
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hx : x ∈ p.support)
    (hxy : Walk.supportIndex p x < Walk.supportIndex p y) :
    y ∉ (Walk.prefixTailToStart p hx).support := by
  intro hy_tail
  have hy_segment :
      y ∈
        (Walk.segmentBetween p p.start_mem_support hx
          (Walk.supportIndex_start_le (p := p))).support := by
    have h :
        y ∈
          (Walk.segmentBetween p p.start_mem_support hx
            (Walk.supportIndex_start_le (p := p))).support.reverse := by
      simpa [Walk.prefixTailToStart, SimpleGraph.Walk.support_reverse]
        using hy_tail
    exact List.mem_reverse.mp h
  have hy_le_x :
      Walk.supportIndex p y <= Walk.supportIndex p x :=
    Walk.segmentBetween_supportIndex_right_le
      p.start_mem_support hx
      (Walk.supportIndex_start_le (p := p)) hy_segment
  omega

theorem Walk.not_mem_suffixTailToEnd_of_lt
    [DecidableEq V]
    {u v x y : V}
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hy : y ∈ p.support)
    (hxy : Walk.supportIndex p x < Walk.supportIndex p y) :
    x ∉ (Walk.suffixTailToEnd hp hy).support := by
  intro hx_tail
  have hy_le_x :
      Walk.supportIndex p y <= Walk.supportIndex p x := by
    simpa [Walk.suffixTailToEnd] using
      Walk.segmentBetween_supportIndex_left_le
        hp hy p.end_mem_support
          (Walk.IsPath.supportIndex_le_end hp hy) hx_tail
  omega

def Walk.orderedThreeBoundaryTails
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    (p : G.Walk (newBoundary 0) (newBoundary 2))
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1)) :
    forall i : Fin 3, G.Walk (oldBoundary i) (newBoundary i)
  | 0 => Walk.prefixTailToStart p (hold 0)
  | 1 => middle
  | 2 => Walk.suffixTailToEnd hp (hold 2)

theorem Walk.orderedThreeBoundaryTails_zero
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1)) :
    Walk.orderedThreeBoundaryTails p hp hold middle 0 =
      Walk.prefixTailToStart p (hold 0) :=
  rfl

theorem Walk.orderedThreeBoundaryTails_one
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1)) :
    Walk.orderedThreeBoundaryTails p hp hold middle 1 = middle :=
  rfl

theorem Walk.orderedThreeBoundaryTails_two
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1)) :
    Walk.orderedThreeBoundaryTails p hp hold middle 2 =
      Walk.suffixTailToEnd hp (hold 2) :=
  rfl

theorem Walk.orderedThreeBoundaryTails_isPath
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    {middle : G.Walk (oldBoundary 1) (newBoundary 1)}
    (hmiddle : middle.IsPath) :
    forall i : Fin 3,
      (Walk.orderedThreeBoundaryTails p hp hold middle i).IsPath := by
  intro i
  fin_cases i
  · exact Walk.prefixTailToStart_isPath hp (hold 0)
  · exact hmiddle
  · exact Walk.suffixTailToEnd_isPath hp (hold 2)

theorem Walk.orderedThreeBoundaryTails_zero_support_subset
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    {z : V}
    (hz : z ∈
      (Walk.orderedThreeBoundaryTails p hp hold middle 0).support) :
    z ∈ p.support := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.prefixTailToStart_support_subset (hold 0) hz

theorem Walk.orderedThreeBoundaryTails_two_support_subset
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    {z : V}
    (hz : z ∈
      (Walk.orderedThreeBoundaryTails p hp hold middle 2).support) :
    z ∈ p.support := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.suffixTailToEnd_support_subset hp (hold 2) hz

theorem Walk.orderedThreeBoundaryTails_outer_disjoint
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    (h02 :
      Walk.supportIndex p (oldBoundary 0) <
        Walk.supportIndex p (oldBoundary 2)) :
    Disjoint
      {z : V | z ∈
        (Walk.orderedThreeBoundaryTails p hp hold middle 0).support}
      {z : V | z ∈
        (Walk.orderedThreeBoundaryTails p hp hold middle 2).support} := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.prefixTailToStart_support_disjoint_suffixTailToEnd
      hp (hold 0) (hold 2) h02

theorem Walk.orderedThreeBoundaryTails_one_not_mem_zero_of_order
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    (h01 :
      Walk.supportIndex p (oldBoundary 0) <
        Walk.supportIndex p (oldBoundary 1)) :
    oldBoundary 1 ∉
      (Walk.orderedThreeBoundaryTails p hp hold middle 0).support := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.not_mem_prefixTailToStart_of_lt
      (hold 0) h01

theorem Walk.orderedThreeBoundaryTails_one_not_mem_two_of_order
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    (h12 :
      Walk.supportIndex p (oldBoundary 1) <
        Walk.supportIndex p (oldBoundary 2)) :
    oldBoundary 1 ∉
      (Walk.orderedThreeBoundaryTails p hp hold middle 2).support := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.not_mem_suffixTailToEnd_of_lt
      hp (hold 2) h12

theorem Walk.orderedThreeBoundaryTails_two_not_mem_zero_of_order
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    (h02 :
      Walk.supportIndex p (oldBoundary 0) <
        Walk.supportIndex p (oldBoundary 2)) :
    oldBoundary 2 ∉
      (Walk.orderedThreeBoundaryTails p hp hold middle 0).support := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.not_mem_prefixTailToStart_of_lt
      (hold 0) h02

theorem Walk.orderedThreeBoundaryTails_zero_not_mem_two_of_order
    [DecidableEq V]
    {oldBoundary newBoundary : Fin 3 -> V}
    {p : G.Walk (newBoundary 0) (newBoundary 2)}
    (hp : p.IsPath)
    (hold : forall i : Fin 3, oldBoundary i ∈ p.support)
    (middle : G.Walk (oldBoundary 1) (newBoundary 1))
    (h02 :
      Walk.supportIndex p (oldBoundary 0) <
        Walk.supportIndex p (oldBoundary 2)) :
    oldBoundary 0 ∉
      (Walk.orderedThreeBoundaryTails p hp hold middle 2).support := by
  simpa [Walk.orderedThreeBoundaryTails] using
    Walk.not_mem_suffixTailToEnd_of_lt
      hp (hold 2) h02


end Schematic.Math.GraphTheory
