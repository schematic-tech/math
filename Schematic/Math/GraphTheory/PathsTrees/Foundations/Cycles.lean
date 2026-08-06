import Schematic.Math.GraphTheory.PathsTrees.Foundations.ChordlessSegments

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- Mapping a chordless walk along an adjacency-reflecting graph homomorphism
preserves chordlessness.  Injectivity is deliberately not required: support
membership supplies preimages, while adjacency reflection is exactly the
extra property needed to rule out new chords. -/
theorem Walk.IsChordless.map_of_adj_reflecting
    {W : Type*} {H : SimpleGraph W}
    {u v : V} {p : G.Walk u v}
    (hp : p.IsChordless)
    (f : G →g H)
    (hreflect : forall x y : V, H.Adj (f x) (f y) -> G.Adj x y) :
    (p.map f).IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  simp only [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
  rcases hx with ⟨x₀, hx₀, rfl⟩
  rcases hy with ⟨y₀, hy₀, rfl⟩
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.mpr
    ⟨s(x₀, y₀), hp.mem_edges hx₀ hy₀ (hreflect x₀ y₀ hxy), by simp⟩

theorem connected_induce_exists_chordless_path_support_subset
    [DecidableEq V]
    {A : Set V}
    (hA : (G.induce A).Connected)
    {u v : V}
    (hu : u ∈ A)
    (hv : v ∈ A) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧ p.IsChordless ∧
        forall x : V, x ∈ p.support -> x ∈ A := by
  classical
  obtain ⟨pA, hpA_path, hpA_dist⟩ :=
    hA.exists_path_of_dist ⟨u, hu⟩ ⟨v, hv⟩
  let p : G.Walk u v :=
    pA.map (SimpleGraph.Embedding.induce (G := G) A).toHom
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      (SimpleGraph.Embedding.induce (G := G) A).injective hpA_path
  have hpA_chordless : pA.IsChordless :=
    Walk.isChordless_of_length_eq_dist pA hpA_dist
  have hp_chordless : p.IsChordless := by
    exact Walk.IsChordless.map_of_adj_reflecting hpA_chordless
      (SimpleGraph.Embedding.induce (G := G) A).toHom
      (fun _ _ hxy => hxy)
  refine ⟨p, hp_path, hp_chordless, ?_⟩
  intro x hx
  change x ∈
    (pA.map (SimpleGraph.Embedding.induce (G := G) A).toHom).support at hx
  simp only [SimpleGraph.Walk.support_map, List.mem_map] at hx
  rcases hx with ⟨xA, _hxA, rfl⟩
  exact xA.2

theorem reachable_induce_exists_chordless_path_support_subset
    [DecidableEq V]
    {A : Set V}
    {u v : V}
    (hu : u ∈ A)
    (hv : v ∈ A)
    (hreach :
      (G.induce A).Reachable
        (⟨u, hu⟩ : A) (⟨v, hv⟩ : A)) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧ p.IsChordless ∧
        forall x : V, x ∈ p.support -> x ∈ A := by
  classical
  let G0 : SimpleGraph A := G.induce A
  let uA : A := ⟨u, hu⟩
  let vA : A := ⟨v, hv⟩
  let C : G0.ConnectedComponent := G0.connectedComponentMk uA
  have huC : uA ∈ C.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hvC : vA ∈ C.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  have hC_connected : (G0.induce C.supp).Connected := by
    simpa [G0, C, SimpleGraph.ConnectedComponent.toSimpleGraph] using
      (SimpleGraph.ConnectedComponent.connected_toSimpleGraph C)
  obtain ⟨pA, hpA_path, hpA_chordless, _hpA_supportC⟩ :=
    connected_induce_exists_chordless_path_support_subset
      (G := G0) hC_connected huC hvC
  let p : G.Walk u v :=
    pA.map (SimpleGraph.Embedding.induce (G := G) A).toHom
  have hp_path : p.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective
      (SimpleGraph.Embedding.induce (G := G) A).injective hpA_path
  have hp_chordless : p.IsChordless := by
    exact Walk.IsChordless.map_of_adj_reflecting hpA_chordless
      (SimpleGraph.Embedding.induce (G := G) A).toHom
      (fun _ _ hxy => hxy)
  refine ⟨p, hp_path, hp_chordless, ?_⟩
  intro x hx
  change x ∈
    (pA.map (SimpleGraph.Embedding.induce (G := G) A).toHom).support at hx
  simp only [SimpleGraph.Walk.support_map, List.mem_map] at hx
  rcases hx with ⟨xA, _hxA, rfl⟩
  exact xA.2

theorem Walk.exists_isCycle_of_cycle_chord
    [DecidableEq V]
    {x a b : V}
    (c : G.Walk x x)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hab : G.Adj a b)
    (hnot : ¬ c.toSubgraph.Adj a b) :
    Exists fun c' : G.Walk a a =>
      c'.IsCycle ∧ c'.length < c.length ∧
        forall v : V, v ∈ c'.support -> v ∈ c.support := by
  let r : G.Walk a a := c.rotate a ha
  have hcr : r.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.rotate ha hc
  have hb_r : b ∈ r.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  let p : G.Walk a b := r.takeUntil b hb_r
  have hp_path : p.IsPath := by
    exact hcr.isPath_takeUntil hb_r
  have hnot_r : ¬ r.toSubgraph.Adj a b := by
    intro hr
    exact hnot (by simpa [r] using hr)
  have hnot_edge_r : s(a, b) ∉ r.edges := by
    intro he
    exact hnot_r ((SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).mpr he)
  have hnot_edge_p : s(a, b) ∉ p.reverse.edges := by
    intro he
    rw [SimpleGraph.Walk.edges_reverse] at he
    exact hnot_edge_r
      ((SimpleGraph.Walk.edges_takeUntil_subset r hb_r) (List.mem_reverse.mp he))
  have hp_len_lt : p.length < r.length := by
    exact SimpleGraph.Walk.length_takeUntil_lt hb_r hab.ne'
  have hp_len_ne_pred : p.length ≠ r.length - 1 := by
    intro hp_eq
    have hb_pen : b = r.penultimate := by
      have hget := SimpleGraph.Walk.getVert_length_takeUntil (p := r) hb_r
      change r.getVert p.length = b at hget
      rw [hp_eq] at hget
      simpa [SimpleGraph.Walk.penultimate] using hget.symm
    have h_adj_pen : r.toSubgraph.Adj a b := by
      have hpa : r.toSubgraph.Adj r.penultimate a :=
        SimpleGraph.Walk.toSubgraph_adj_penultimate r hcr.not_nil
      simpa [hb_pen] using hpa.symm
    exact hnot_r h_adj_pen
  have hp_len_add_lt : p.length + 1 < r.length := by
    omega
  refine ⟨SimpleGraph.Walk.cons hab p.reverse, ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff p.reverse hab).mpr
      ⟨hp_path.reverse, hnot_edge_p⟩
  · rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_reverse]
    simpa [r] using hp_len_add_lt
  · intro v hv
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hvp_rev
    · exact ha
    · rw [SimpleGraph.Walk.support_reverse] at hvp_rev
      have hvp : v ∈ p.support := List.mem_reverse.mp hvp_rev
      have hvr : v ∈ r.support :=
        SimpleGraph.Walk.support_takeUntil_subset r hb_r hvp
      exact (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mp hvr

theorem Walk.IsCycle.exists_path_between_avoiding
    [DecidableEq V]
    {r x y z : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hx : x ∈ c.support)
    (hy : y ∈ c.support)
    (hz : z ∈ c.support)
    (hxy : x ≠ y)
    (hzx : z ≠ x)
    (hzy : z ≠ y) :
    Exists fun p : G.Walk x y =>
      p.IsPath ∧
        (forall a : V, a ∈ p.support -> a ∈ c.support) ∧
          z ∉ p.support := by
  classical
  let c' : G.Walk x x := c.rotate x hx
  have hc' : c'.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.rotate hx hc
  have hy' : y ∈ c'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hy
  have hz' : z ∈ c'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hz
  let p₁ : G.Walk x y := c'.takeUntil y hy'
  let p₂ : G.Walk y x := c'.dropUntil y hy'
  have hp₁_path : p₁.IsPath := by
    exact hc'.isPath_takeUntil hy'
  have hp₁_support : forall a : V, a ∈ p₁.support -> a ∈ c.support := by
    intro a ha
    have ha' : a ∈ c'.support :=
      SimpleGraph.Walk.support_takeUntil_subset c' hy' ha
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mp ha'
  have hp₂_path : p₂.IsPath := by
    have hp₁_not_nil : ¬ p₁.Nil := by
      rw [SimpleGraph.Walk.nil_takeUntil]
      exact hxy
    have hcycle_append : (p₁.append p₂).IsCycle := by
      simpa [p₁, p₂] using hc'
    exact hcycle_append.isPath_of_append_right hp₁_not_nil
  have hp₂_reverse_support : forall a : V, a ∈ p₂.reverse.support -> a ∈ c.support := by
    intro a ha
    rw [SimpleGraph.Walk.support_reverse] at ha
    have ha₂ : a ∈ p₂.support := List.mem_reverse.mp ha
    have ha' : a ∈ c'.support :=
      SimpleGraph.Walk.support_dropUntil_subset c' hy' ha₂
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mp ha'
  by_cases hz₁ : z ∈ p₁.support
  · refine ⟨p₂.reverse, hp₂_path.reverse, hp₂_reverse_support, ?_⟩
    intro hz₂_rev
    rw [SimpleGraph.Walk.support_reverse] at hz₂_rev
    have hz₂ : z ∈ p₂.support := List.mem_reverse.mp hz₂_rev
    have hz₂_tail : z ∈ p₂.support.tail := by
      rw [SimpleGraph.Walk.mem_support_iff] at hz₂
      exact hz₂.resolve_left hzy
    have hcount_ge_two : 2 <= c'.support.count z := by
      have hsupport :
          c'.support = p₁.support ++ p₂.support.tail := by
        rw [← SimpleGraph.Walk.support_append p₁ p₂]
        simp [p₁, p₂]
      rw [hsupport, List.count_append]
      have hcount₁ : 1 <= p₁.support.count z :=
        List.one_le_count_iff.mpr hz₁
      have hcount₂ : 1 <= p₂.support.tail.count z :=
        List.one_le_count_iff.mpr hz₂_tail
      omega
    have hcount_one : c'.support.count z = 1 :=
      hc'.count_support_of_mem hz' hzx
    omega
  · exact ⟨p₁, hp₁_path, hp₁_support, hz₁⟩

/-- A cycle split into an `x`-`y` arc avoiding `z` and the complementary arc
through `z`.  The complementary arc is returned as two paths ending at `z`,
and all three resulting branches have pairwise-disjoint internal vertices.

This is the path-contact normalization used when a hanging cycle and an
external attachment path are converted into a suppressed-edge theta
subdivision. -/
theorem Walk.IsCycle.exists_avoiding_path_and_split_through
    [DecidableEq V]
    {r x y z : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hx : x ∈ c.support)
    (hy : y ∈ c.support)
    (hz : z ∈ c.support)
    (hxy : x ≠ y)
    (hzx : z ≠ x)
    (hzy : z ≠ y) :
    Exists fun pXY : G.Walk x y =>
      Exists fun pXZ : G.Walk x z =>
      Exists fun pYZ : G.Walk y z =>
        pXY.IsPath ∧ pXZ.IsPath ∧ pYZ.IsPath ∧
          (forall a : V, a ∈ pXY.support -> a ∈ c.support) ∧
            (forall a : V, a ∈ pXZ.support -> a ∈ c.support) ∧
              (forall a : V, a ∈ pYZ.support -> a ∈ c.support) ∧
                z ∉ pXY.support ∧
                  y ∉ pXZ.support ∧
                  x ∉ pYZ.support ∧
                  Disjoint (Walk.InternalVertices pXY)
                    (Walk.InternalVertices pXZ) ∧
                  Disjoint (Walk.InternalVertices pXY)
                    (Walk.InternalVertices pYZ) ∧
                  Disjoint (Walk.InternalVertices pXZ)
                    (Walk.InternalVertices pYZ) := by
  classical
  let c' : G.Walk x x := c.rotate x hx
  have hc' : c'.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.rotate hx hc
  have hy' : y ∈ c'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hy
  have hz' : z ∈ c'.support := by
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mpr hz
  let p₁ : G.Walk x y := c'.takeUntil y hy'
  let p₂ : G.Walk y x := c'.dropUntil y hy'
  have hp₁_path : p₁.IsPath := by
    exact hc'.isPath_takeUntil hy'
  have hp₁_support : forall a : V, a ∈ p₁.support -> a ∈ c.support := by
    intro a ha
    have ha' : a ∈ c'.support :=
      SimpleGraph.Walk.support_takeUntil_subset c' hy' ha
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mp ha'
  have hp₂_path : p₂.IsPath := by
    have hp₁_not_nil : ¬ p₁.Nil := by
      rw [SimpleGraph.Walk.nil_takeUntil]
      exact hxy
    have hcycle_append : (p₁.append p₂).IsCycle := by
      simpa [p₁, p₂] using hc'
    exact hcycle_append.isPath_of_append_right hp₁_not_nil
  have hp₂_support : forall a : V, a ∈ p₂.support -> a ∈ c.support := by
    intro a ha
    have ha' : a ∈ c'.support :=
      SimpleGraph.Walk.support_dropUntil_subset c' hy' ha
    exact (SimpleGraph.Walk.mem_support_rotate_iff c x hx).mp ha'
  have hp₂_reverse_support :
      forall a : V, a ∈ p₂.reverse.support -> a ∈ c.support := by
    intro a ha
    rw [SimpleGraph.Walk.support_reverse] at ha
    exact hp₂_support a (List.mem_reverse.mp ha)
  have hcycle_split_disjoint :
      Disjoint (Walk.InternalVertices p₁) (Walk.InternalVertices p₂) := by
    simpa [p₁, p₂] using
      Walk.IsCycle.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hc' hy'
  by_cases hz₁ : z ∈ p₁.support
  · let pXY : G.Walk x y := p₂.reverse
    let pXZ : G.Walk x z := p₁.takeUntil z hz₁
    let pYZ : G.Walk y z := (p₁.dropUntil z hz₁).reverse
    have hpXY : pXY.IsPath := by
      simpa [pXY] using hp₂_path.reverse
    have hpXZ : pXZ.IsPath := by
      simpa [pXZ] using hp₁_path.takeUntil hz₁
    have hpYZ : pYZ.IsPath := by
      simpa [pYZ] using (hp₁_path.dropUntil hz₁).reverse
    have hpXZ_support : forall a : V, a ∈ pXZ.support -> a ∈ c.support := by
      intro a ha
      exact hp₁_support a
        (SimpleGraph.Walk.support_takeUntil_subset p₁ hz₁ (by simpa [pXZ] using ha))
    have hpYZ_support : forall a : V, a ∈ pYZ.support -> a ∈ c.support := by
      intro a ha
      have ha_drop : a ∈ (p₁.dropUntil z hz₁).support := by
        have ha_rev : a ∈ (p₁.dropUntil z hz₁).reverse.support := by
          simpa [pYZ] using ha
        rw [SimpleGraph.Walk.support_reverse] at ha_rev
        exact List.mem_reverse.mp ha_rev
      exact hp₁_support a
        (SimpleGraph.Walk.support_dropUntil_subset p₁ hz₁ ha_drop)
    have hz_not_pXY : z ∉ pXY.support := by
      intro hz₂_rev
      have hz₂ : z ∈ p₂.support := by
        have hz₂_rev' : z ∈ p₂.reverse.support := by
          simpa [pXY] using hz₂_rev
        rw [SimpleGraph.Walk.support_reverse] at hz₂_rev'
        exact List.mem_reverse.mp hz₂_rev'
      have hz₂_tail : z ∈ p₂.support.tail := by
        rw [SimpleGraph.Walk.mem_support_iff] at hz₂
        exact hz₂.resolve_left hzy
      have hcount_ge_two : 2 <= c'.support.count z := by
        have hsupport :
            c'.support = p₁.support ++ p₂.support.tail := by
          rw [← SimpleGraph.Walk.support_append p₁ p₂]
          simp [p₁, p₂]
        rw [hsupport, List.count_append]
        have hcount₁ : 1 <= p₁.support.count z :=
          List.one_le_count_iff.mpr hz₁
        have hcount₂ : 1 <= p₂.support.tail.count z :=
          List.one_le_count_iff.mpr hz₂_tail
        omega
      have hcount_one : c'.support.count z = 1 :=
        hc'.count_support_of_mem hz' hzx
      omega
    have hy_not_pXZ : y ∉ pXZ.support := by
      intro hy_pXZ
      exact
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          hp₁_path hz₁ hzy.symm
          (by simpa [pXZ] using hy_pXZ)
    have hx_not_pYZ : x ∉ pYZ.support := by
      intro hx_pYZ
      have hx_drop : x ∈ (p₁.dropUntil z hz₁).support := by
        have hx_rev : x ∈ (p₁.dropUntil z hz₁).reverse.support := by
          simpa [pYZ] using hx_pYZ
        rw [SimpleGraph.Walk.support_reverse] at hx_rev
        exact List.mem_reverse.mp hx_rev
      exact
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hp₁_path hz₁ hzx hx_drop
    have hXY_XZ :
        Disjoint (Walk.InternalVertices pXY) (Walk.InternalVertices pXZ) := by
      rw [Set.disjoint_left]
      intro q hqXY hqXZ
      have hq₂ : q ∈ Walk.InternalVertices p₂ := by
        exact (Walk.mem_internalVertices_reverse_iff p₂).1 (by
          simpa [pXY] using hqXY)
      have hq₁ : q ∈ Walk.InternalVertices p₁ :=
        Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
          hp₁_path hz₁ hzy (by simpa [pXZ] using hqXZ)
      exact Set.disjoint_left.mp hcycle_split_disjoint hq₁ hq₂
    have hXY_YZ :
        Disjoint (Walk.InternalVertices pXY) (Walk.InternalVertices pYZ) := by
      rw [Set.disjoint_left]
      intro q hqXY hqYZ
      have hq₂ : q ∈ Walk.InternalVertices p₂ := by
        exact (Walk.mem_internalVertices_reverse_iff p₂).1 (by
          simpa [pXY] using hqXY)
      have hq_drop :
          q ∈ Walk.InternalVertices (p₁.dropUntil z hz₁) := by
        exact (Walk.mem_internalVertices_reverse_iff (p₁.dropUntil z hz₁)).1
          (by simpa [pYZ] using hqYZ)
      have hq₁ : q ∈ Walk.InternalVertices p₁ :=
        Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
          hp₁_path hz₁ hzx hq_drop
      exact Set.disjoint_left.mp hcycle_split_disjoint hq₁ hq₂
    have hXZ_YZ :
        Disjoint (Walk.InternalVertices pXZ) (Walk.InternalVertices pYZ) := by
      have hsplit :=
        Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
          (G := G) hp₁_path hz₁
      simpa [pXZ, pYZ, Walk.internalVertices_reverse] using hsplit
    exact ⟨pXY, pXZ, pYZ, hpXY, hpXZ, hpYZ,
      by simpa [pXY] using hp₂_reverse_support,
      hpXZ_support, hpYZ_support, hz_not_pXY,
      hy_not_pXZ, hx_not_pYZ, hXY_XZ, hXY_YZ, hXZ_YZ⟩
  · have hz₂ : z ∈ p₂.support := by
      have hz_split : z ∈ (p₁.append p₂).support := by
        simpa [p₁, p₂] using hz'
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz_split
      rcases hz_split with hz_take | hz_drop
      · exact False.elim (hz₁ (by simpa [p₁] using hz_take))
      · simpa [p₂] using hz_drop
    let pXY : G.Walk x y := p₁
    let pXZ : G.Walk x z := (p₂.dropUntil z hz₂).reverse
    let pYZ : G.Walk y z := p₂.takeUntil z hz₂
    have hpXY : pXY.IsPath := by
      simpa [pXY] using hp₁_path
    have hpXZ : pXZ.IsPath := by
      simpa [pXZ] using (hp₂_path.dropUntil hz₂).reverse
    have hpYZ : pYZ.IsPath := by
      simpa [pYZ] using hp₂_path.takeUntil hz₂
    have hpXZ_support : forall a : V, a ∈ pXZ.support -> a ∈ c.support := by
      intro a ha
      have ha_drop : a ∈ (p₂.dropUntil z hz₂).support := by
        have ha_rev : a ∈ (p₂.dropUntil z hz₂).reverse.support := by
          simpa [pXZ] using ha
        rw [SimpleGraph.Walk.support_reverse] at ha_rev
        exact List.mem_reverse.mp ha_rev
      exact hp₂_support a
        (SimpleGraph.Walk.support_dropUntil_subset p₂ hz₂ ha_drop)
    have hpYZ_support : forall a : V, a ∈ pYZ.support -> a ∈ c.support := by
      intro a ha
      exact hp₂_support a
        (SimpleGraph.Walk.support_takeUntil_subset p₂ hz₂ (by simpa [pYZ] using ha))
    have hy_not_pXZ : y ∉ pXZ.support := by
      intro hy_pXZ
      have hy_drop : y ∈ (p₂.dropUntil z hz₂).support := by
        have hy_rev : y ∈ (p₂.dropUntil z hz₂).reverse.support := by
          simpa [pXZ] using hy_pXZ
        rw [SimpleGraph.Walk.support_reverse] at hy_rev
        exact List.mem_reverse.mp hy_rev
      exact
        Walk.IsPath.start_not_mem_dropUntil_support_of_ne
          hp₂_path hz₂ hzy hy_drop
    have hx_not_pYZ : x ∉ pYZ.support := by
      intro hx_pYZ
      exact
        SimpleGraph.Walk.endpoint_notMem_support_takeUntil
          hp₂_path hz₂ hzx.symm
          (by simpa [pYZ] using hx_pYZ)
    have hXY_XZ :
        Disjoint (Walk.InternalVertices pXY) (Walk.InternalVertices pXZ) := by
      rw [Set.disjoint_left]
      intro q hqXY hqXZ
      have hq_drop :
          q ∈ Walk.InternalVertices (p₂.dropUntil z hz₂) := by
        exact (Walk.mem_internalVertices_reverse_iff (p₂.dropUntil z hz₂)).1
          (by simpa [pXZ] using hqXZ)
      have hq₂ : q ∈ Walk.InternalVertices p₂ :=
        Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
          hp₂_path hz₂ hzy hq_drop
      have hq₁ : q ∈ Walk.InternalVertices p₁ := by
        simpa [pXY] using hqXY
      exact Set.disjoint_left.mp hcycle_split_disjoint hq₁ hq₂
    have hXY_YZ :
        Disjoint (Walk.InternalVertices pXY) (Walk.InternalVertices pYZ) := by
      rw [Set.disjoint_left]
      intro q hqXY hqYZ
      have hq₂ : q ∈ Walk.InternalVertices p₂ :=
        Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
          hp₂_path hz₂ hzx (by simpa [pYZ] using hqYZ)
      have hq₁ : q ∈ Walk.InternalVertices p₁ := by
        simpa [pXY] using hqXY
      exact Set.disjoint_left.mp hcycle_split_disjoint hq₁ hq₂
    have hXZ_YZ :
        Disjoint (Walk.InternalVertices pXZ) (Walk.InternalVertices pYZ) := by
      have hsplit :=
        Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
          (G := G) hp₂_path hz₂
      simpa [pXZ, pYZ, Walk.internalVertices_reverse] using hsplit.symm
    exact ⟨pXY, pXZ, pYZ, hpXY, hpXZ, hpYZ,
      by simpa [pXY] using hp₁_support,
      hpXZ_support, hpYZ_support,
      by simpa [pXY] using hz₁,
      hy_not_pXZ, hx_not_pYZ,
      hXY_XZ, hXY_YZ, hXZ_YZ⟩

/-- Every simple cycle contains a consecutive two-edge segment `a-b-d` with
distinct ends.  This source-normalization is used in the Kuratowski bridge
when a final cycle is combined with two deleted endpoints: the edge `a--d` is
then represented by the complementary arc of the cycle. -/
theorem Walk.IsCycle.exists_consecutive_triple
    {r : V}
    (c : G.Walk r r)
    (hc : c.IsCycle) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun d : V =>
          a ∈ c.support ∧ b ∈ c.support ∧ d ∈ c.support ∧
            G.Adj a b ∧ G.Adj b d ∧ a ≠ d := by
  let a : V := c.getVert 0
  let b : V := c.getVert 1
  let d : V := c.getVert 2
  have hlen : 3 <= c.length := SimpleGraph.Walk.IsCycle.three_le_length hc
  have ha : a ∈ c.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨0, ⟨rfl, by omega⟩⟩
  have hb : b ∈ c.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, ⟨rfl, by omega⟩⟩
  have hd : d ∈ c.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, ⟨rfl, by omega⟩⟩
  have hab : G.Adj a b := by
    simpa [a, b] using c.adj_getVert_succ (by omega : 0 < c.length)
  have hbd : G.Adj b d := by
    simpa [b, d] using c.adj_getVert_succ (by omega : 1 < c.length)
  have had : a ≠ d := by
    simpa [a, d] using
      SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one
        (p := c) hc (i := 1) (by omega : 1 <= c.length)
  exact ⟨a, b, d, ha, hb, hd, hab, hbd, had⟩

/-- A simple cycle has two distinct support vertices different from any
specified support vertex.  This is the support-count normalization used in
the hanging-cycle part of the Kuratowski bridge. -/
theorem Walk.IsCycle.exists_two_support_ne
    {r v : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (hv : v ∈ c.support) :
    Exists fun a : V =>
      Exists fun b : V =>
        a ∈ c.support ∧ b ∈ c.support ∧ a ≠ v ∧ b ≠ v ∧ a ≠ b := by
  classical
  let c' : G.Walk v v := c.rotate v hv
  have hc' : c'.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.rotate hv hc
  let a : V := c'.getVert 1
  let b : V := c'.getVert 2
  have hlen : 3 <= c'.length := hc'.three_le_length
  have ha' : a ∈ c'.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨1, ⟨rfl, by omega⟩⟩
  have hb' : b ∈ c'.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨2, ⟨rfl, by omega⟩⟩
  have ha : a ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c v hv).mp ha'
  have hb : b ∈ c.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c v hv).mp hb'
  have ha_ne_v : a ≠ v := by
    intro hav
    have hendpoint :
        1 = 0 ∨ 1 = c'.length :=
      (hc'.getVert_endpoint_iff (i := 1) (by omega)).mp hav
    omega
  have hb_ne_v : b ≠ v := by
    intro hbv
    have hendpoint :
        2 = 0 ∨ 2 = c'.length :=
      (hc'.getVert_endpoint_iff (i := 2) (by omega)).mp hbv
    omega
  have hab : a ≠ b := by
    intro hab_eq
    have hidx :
        1 = 2 :=
      hc'.getVert_injOn
        (by
          constructor <;> omega)
        (by
          constructor <;> omega)
        hab_eq
    omega
  exact ⟨a, b, ha, hb, ha_ne_v, hb_ne_v, hab⟩

/-- A finite connected nontrivial graph of minimum degree at least two contains
a simple cycle.  This is the base existence fact for the
Makarychev/Skopenkov block/cactus reduction: if the deleted graph has no
hanging vertices, it cannot be a tree. -/
theorem exists_isCycle_of_preconnected_min_degree_two
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hconn : G.Preconnected)
    (hdegree : forall v : V, 2 <= G.degree v) :
    Exists fun r : V =>
      Exists fun c : G.Walk r r => c.IsCycle := by
  classical
  by_contra hnone
  have hacyclic : G.IsAcyclic := by
    intro v c hc
    exact hnone ⟨v, c, hc⟩
  have htree : G.IsTree :=
    { connected := ⟨hconn⟩
      isAcyclic := hacyclic }
  rcases SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial
      (G := G) htree with
    ⟨v, hv⟩
  have hv_min : 2 <= G.degree v := hdegree v
  omega

/-- A finite connected graph in which every vertex except a named root has
degree at least two contains a simple cycle, provided some vertex is not the
root.  This is the leaf-count form used when adding a cut vertex back to one
component of a deleted graph: a tree has at least two leaves, so one leaf is
not the exceptional cut vertex. -/
theorem exists_isCycle_of_connected_min_degree_two_away_from_root
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected)
    {root : V}
    (hne : Exists fun v : V => v ≠ root)
    (hdegree : forall v : V, v ≠ root -> 2 <= G.degree v) :
    Exists fun r : V =>
      Exists fun c : G.Walk r r => c.IsCycle := by
  classical
  rcases hne with ⟨w, hwroot⟩
  haveI : Nontrivial V := ⟨⟨root, w, by
    intro hrootw
    exact hwroot hrootw.symm⟩⟩
  by_contra hnone
  have hacyclic : G.IsAcyclic := by
    intro v c hc
    exact hnone ⟨v, c, hc⟩
  have htree : G.IsTree :=
    { connected := hconn
      isAcyclic := hacyclic }
  rcases IsTree.exists_two_distinct_degree_one_of_nontrivial
      (G := G) htree with
    ⟨a, b, hab, ha_degree, hb_degree⟩
  by_cases ha_root : a = root
  · have hb_root : b ≠ root := by
      intro hbroot
      exact hab (by rw [ha_root, hbroot])
    have hb_min : 2 <= G.degree b := hdegree b hb_root
    omega
  · have ha_min : 2 <= G.degree a := hdegree a ha_root
    omega

/-- A finite nonempty graph of minimum degree at least two contains a simple
cycle.  This disconnected form is the first graph-theoretic step in the
block/cactus reduction: an acyclic finite graph has a degree-at-most-one
vertex in some component. -/
theorem exists_isCycle_of_nonempty_min_degree_two
    [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hdegree : forall v : V, 2 <= G.degree v) :
    Exists fun r : V =>
      Exists fun c : G.Walk r r => c.IsCycle := by
  classical
  by_contra hnone
  have hacyclic : G.IsAcyclic := by
    intro v c hc
    exact hnone ⟨v, c, hc⟩
  rcases exists_vertex_degree_le_one_of_finite_acyclic
      (G := G) hacyclic with
    ⟨v, hv⟩
  have hv_min : 2 <= G.degree v := hdegree v
  omega

/-- If a vertex outside a displayed cycle has positive degree, no edge is
allowed to be completely outside the cycle, and all contacts from that outside
vertex to the cycle hit the same cycle vertex `v`, then the outside vertex is
a leaf.  This packages the leaf step in the hanging-cycle block argument. -/
theorem Walk.degree_eq_one_of_outside_cycle_no_edges_of_only_contact
    [Fintype V] [DecidableRel G.Adj]
    {r p v : V}
    (c : G.Walk r r)
    (hp_out : p ∉ c.support)
    (hno_edge :
      forall {a b : V}, G.Adj a b ->
        a ∉ c.support -> b ∉ c.support -> False)
    (honly :
      forall {a b : V}, G.Adj a b ->
        a ∉ c.support -> b ∈ c.support -> b = v)
    (hpos : 0 < G.degree p) :
    G.degree p = 1 := by
  classical
  rcases (G.degree_pos_iff_exists_adj p).mp hpos with ⟨w, hpw⟩
  have hwC : w ∈ c.support := by
    by_contra hw_out
    exact hno_edge hpw hp_out hw_out
  have hw_eq_v : w = v := honly hpw hp_out hwC
  have hpv : G.Adj p v := by
    simpa [hw_eq_v] using hpw
  exact (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mpr
    ⟨v, hpv, by
      intro y hpy
      by_cases hyC : y ∈ c.support
      · exact honly hpy hp_out hyC
      · exact False.elim (hno_edge hpy hp_out hyC)⟩

/-- A closed walk of length three has support contained in its first three
listed vertices; the fourth vertex is the starting vertex again. -/
theorem Walk.support_subset_getVert012_of_length_eq_three
    {r z : V}
    (c : G.Walk r r)
    (hlen : c.length = 3)
    (hz : z ∈ c.support) :
    z = c.getVert 0 ∨ z = c.getVert 1 ∨ z = c.getVert 2 := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
  rcases hz with ⟨i, hi_eq, hi_le⟩
  have hi_le_three : i <= 3 := by omega
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl
  · exact Or.inl hi_eq.symm
  · exact Or.inr (Or.inl hi_eq.symm)
  · exact Or.inr (Or.inr hi_eq.symm)
  · have h30 : c.getVert 3 = c.getVert 0 := by
      rw [show 3 = c.length by omega, SimpleGraph.Walk.getVert_length,
        SimpleGraph.Walk.getVert_zero]
    exact Or.inl (by simpa [h30] using hi_eq.symm)

/-- A nontrivial closed walk has at most `length` distinct support vertices,
because the initial vertex occurs again as the final vertex. -/
theorem Walk.support_toFinset_card_le_length_of_closed
    [DecidableEq V]
    {r : V}
    (c : G.Walk r r)
    (hnil : ¬ c.Nil) :
    c.support.toFinset.card <= c.length := by
  classical
  have hr_tail : r ∈ c.support.tail :=
    SimpleGraph.Walk.end_mem_tail_support hnil
  have hcons : r :: c.support.tail = c.support :=
    SimpleGraph.Walk.cons_tail_support c
  have hsupport_card_le_tail :
      c.support.toFinset.card <= c.support.tail.toFinset.card := by
    apply Finset.card_le_card
    intro z hz
    rw [List.mem_toFinset] at hz ⊢
    rw [← hcons] at hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hr_tail
    · exact hz
  have htail_card_le_length :
      c.support.tail.toFinset.card <= c.length := by
    have htail_len : c.support.tail.length = c.length := by
      rw [List.length_tail, SimpleGraph.Walk.length_support]
      omega
    exact (List.toFinset_card_le c.support.tail).trans_eq htail_len
  exact hsupport_card_le_tail.trans htail_card_le_length


end Schematic.Math.GraphTheory
