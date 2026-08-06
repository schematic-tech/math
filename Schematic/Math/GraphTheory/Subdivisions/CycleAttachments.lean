import Schematic.Math.GraphTheory.Subdivisions.EdgeThetaPaths

/-! Theta subdivisions extracted from cycle attachments and connectors. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

/-- Mixed-end version of the end-cycle theta extraction. If two cycle
vertices `a,b` attach to opposite ends `x,y` of an external edge `xy`, then
the cycle and the two-edge external path form a suppressed-edge theta
subdivision. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_adjacent_endpoint_path
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b z x y : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hax : G.Adj a x)
    (hxy : G.Adj x y)
    (hby : G.Adj b y)
    (hx_cycle : x ∉ c.support)
    (hy_cycle : y ∉ c.support) :
    ContainsEdgeThetaSubdivision G := by
  classical
  rcases
    Walk.IsCycle.exists_avoiding_path_and_split_through
      (G := G) c hc ha hb hz hab haz.symm hbz.symm with
    ⟨pAB, pAZ, pBZ, hAB, hAZ, hBZ,
      hpAB_support, hpAZ_support, hpBZ_support,
      hz_not_pAB, hb_not_pAZ, ha_not_pBZ,
      hAB_AZ, hAB_BZ, hAZ_BZ⟩
  let pBX : G.Walk b x := hby.toWalk.append hxy.symm.toWalk
  have hax_ne : a ≠ x := by
    intro h
    exact hx_cycle (by simpa [← h] using ha)
  have hbx : b ≠ x := by
    intro h
    exact hx_cycle (by simpa [← h] using hb)
  have hxz : x ≠ z := by
    intro h
    exact hx_cycle (by simpa [h] using hz)
  have hya : y ≠ a := by
    intro h
    exact hy_cycle (by simpa [h] using ha)
  have hyb : y ≠ b := by
    intro h
    exact hy_cycle (by simpa [h] using hb)
  have hyz : y ≠ z := by
    intro h
    exact hy_cycle (by simpa [h] using hz)
  have hyx : y ≠ x := hxy.ne.symm
  have hBX : pBX.IsPath := by
    have hb_not_nil : b ∉ (SimpleGraph.Walk.nil : G.Walk x x).support := by
      intro hbmem
      simp at hbmem
      exact hbx hbmem
    have hy_not_nil : y ∉ (SimpleGraph.Walk.nil : G.Walk x x).support := by
      intro hymem
      simp at hymem
      exact hyx hymem
    have hpath :=
      Walk.two_edge_append_isPath hby hxy.symm
        (q := (SimpleGraph.Walk.nil : G.Walk x x))
        SimpleGraph.Walk.IsPath.nil hb_not_nil hy_not_nil
    simpa [pBX] using hpath
  refine
    ContainsEdgeThetaSubdivision.of_five_paths_explicit
      pAB hax.toWalk pBX pAZ pBZ
      hab hax_ne haz hbx hbz hxz
      hAB (SimpleGraph.Walk.IsPath.of_adj hax) hBX hAZ hBZ
      ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · exact hq.2.2
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqx
        exact hx_cycle (by simpa [hqx] using hpAB_support q hq.1)
      · intro hqz
        exact hz_not_pAB (by simpa [hqz] using hq.1)
  · intro q hq d
    exact (Walk.not_mem_internalVertices_toWalk hax hq).elim
  · intro q hq d
    have hqy : q = y := by
      exact
        (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
          (by simpa [pBX] using hq)
    subst q
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hya
      · exact hyb
    · fin_cases j <;> simp [edgeThetaBranch]
      · exact hyx
      · exact hyz
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · intro hqb
        exact hb_not_pAZ (by simpa [hqb] using hq.1)
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqx
        exact hx_cycle (by simpa [hqx] using hpAZ_support q hq.1)
      · exact hq.2.2
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · intro hqa
        exact ha_not_pBZ (by simpa [hqa] using hq.1)
      · exact hq.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqx
        exact hx_cycle (by simpa [hqx] using hpBZ_support q hq.1)
      · exact hq.2.2
  · intro L M hLM
    rcases L <;> rcases M <;>
      simp [edgeThetaPathInternalSet] at hLM ⊢
    all_goals
      rw [Set.disjoint_left]
      intro q hqL hqR
      first
      | exact (Walk.not_mem_internalVertices_toWalk hax hqL).elim
      | exact (Walk.not_mem_internalVertices_toWalk hax hqR).elim
      | exact Set.disjoint_left.mp hAB_AZ hqL hqR
      | exact Set.disjoint_left.mp hAB_AZ.symm hqL hqR
      | exact Set.disjoint_left.mp hAB_BZ hqL hqR
      | exact Set.disjoint_left.mp hAB_BZ.symm hqL hqR
      | exact Set.disjoint_left.mp hAZ_BZ hqL hqR
      | exact Set.disjoint_left.mp hAZ_BZ.symm hqL hqR
      | have hqy : q = y := by
          exact
            (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
              (by simpa [pBX] using hqL)
        exact hy_cycle (by simpa [hqy] using hpAB_support q hqR.1)
      | have hqy : q = y := by
          exact
            (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
              (by simpa [pBX] using hqR)
        exact hy_cycle (by simpa [hqy] using hpAB_support q hqL.1)
      | have hqy : q = y := by
          exact
            (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
              (by simpa [pBX] using hqL)
        exact hy_cycle (by simpa [hqy] using hpAZ_support q hqR.1)
      | have hqy : q = y := by
          exact
            (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
              (by simpa [pBX] using hqR)
        exact hy_cycle (by simpa [hqy] using hpAZ_support q hqL.1)
      | have hqy : q = y := by
          exact
            (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
              (by simpa [pBX] using hqL)
        exact hy_cycle (by simpa [hqy] using hpBZ_support q hqR.1)
      | have hqy : q = y := by
          exact
            (Walk.mem_internalVertices_two_edge_toWalk_iff hby hxy.symm).mp
              (by simpa [pBX] using hqR)
        exact hy_cycle (by simpa [hqy] using hpBZ_support q hqL.1)

/-- Source-facing case split for the end-cycle theta sentence: if two
distinct cycle vertices each attach to one of the endpoints of an external
edge `xy`, then the graph contains a suppressed-edge theta subdivision. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_two_endpoint_attachments
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b z x y : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hxy : G.Adj x y)
    (ha_attach : G.Adj a x ∨ G.Adj a y)
    (hb_attach : G.Adj b x ∨ G.Adj b y)
    (hx_cycle : x ∉ c.support)
    (hy_cycle : y ∉ c.support) :
    ContainsEdgeThetaSubdivision G := by
  classical
  rcases ha_attach with hax | hay
  · rcases hb_attach with hbx | hby
    · exact
        ContainsEdgeThetaSubdivision.of_cycle_common_neighbor
          c hc ha hb hz hab haz hbz hax hbx hx_cycle
    · exact
        ContainsEdgeThetaSubdivision.of_cycle_adjacent_endpoint_path
          c hc ha hb hz hab haz hbz hax hxy hby hx_cycle hy_cycle
  · rcases hb_attach with hbx | hby
    · exact
        ContainsEdgeThetaSubdivision.of_cycle_adjacent_endpoint_path
          c hc ha hb hz hab haz hbz hay hxy.symm hbx hy_cycle hx_cycle
    · exact
        ContainsEdgeThetaSubdivision.of_cycle_common_neighbor
          c hc ha hb hz hab haz hbz hay hby hy_cycle

/-- A chord of a simple cycle gives a suppressed-edge theta subdivision.

This is the graph-theoretic sentence used in the Skopenkov/Makarychev bridge:
under the no-theta hypothesis, every spanning cycle obtained in an edge-end
deletion is automatically chordless.  The direct chord is the suppressed
`x--y` branch of `EdgeThetaGraph`; the two complementary cycle arcs are split
at their first internal vertices. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_chord
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hab : G.Adj a b)
    (hnot : ¬ c.toSubgraph.Adj a b) :
    ContainsEdgeThetaSubdivision G := by
  classical
  let c' : G.Walk a a := c.rotate a ha
  have hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate ha hc
  have hb' : b ∈ c'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  have hnot' : ¬ c'.toSubgraph.Adj a b := by
    intro h
    exact hnot (by simpa [c'] using h)
  let p₁ : G.Walk a b := c'.takeUntil b hb'
  let p₂ : G.Walk b a := c'.dropUntil b hb'
  have hp₁_path : p₁.IsPath := by
    simpa [p₁] using hc'.isPath_takeUntil hb'
  have hp₁_not_nil : ¬ p₁.Nil := by
    change ¬ (c'.takeUntil b hb').Nil
    rw [SimpleGraph.Walk.nil_takeUntil]
    exact hab.ne
  have hcycle_append : (p₁.append p₂).IsCycle := by
    simpa [p₁, p₂] using hc'
  have hp₂_path : p₂.IsPath :=
    hcycle_append.isPath_of_append_right hp₁_not_nil
  have hp₂_not_nil : ¬ p₂.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hab.ne.symm
  let u : V := p₁.snd
  let w : V := p₂.snd
  have hu_support : u ∈ p₁.support := by
    exact List.mem_of_mem_tail (p₁.snd_mem_tail_support hp₁_not_nil)
  have hw_support : w ∈ p₂.support := by
    exact List.mem_of_mem_tail (p₂.snd_mem_tail_support hp₂_not_nil)
  have hau : G.Adj a u := by
    simpa [u] using p₁.adj_snd hp₁_not_nil
  have hbw : G.Adj b w := by
    simpa [w] using p₂.adj_snd hp₂_not_nil
  have hu_ne_a : u ≠ a := hau.ne.symm
  have hw_ne_b : w ≠ b := hbw.ne.symm
  have hu_ne_b : u ≠ b := by
    intro hub
    have hp₁_adj : p₁.toSubgraph.Adj a b := by
      simpa [u, hub] using p₁.toSubgraph_adj_snd hp₁_not_nil
    have hc'_adj : c'.toSubgraph.Adj a b :=
      (Walk.toSubgraph_takeUntil_le c' hb').2 hp₁_adj
    exact hnot' hc'_adj
  have hw_ne_a : w ≠ a := by
    intro hwa
    have hp₂_adj : p₂.toSubgraph.Adj b a := by
      simpa [w, hwa] using p₂.toSubgraph_adj_snd hp₂_not_nil
    have hc'_adj : c'.toSubgraph.Adj b a :=
      (Walk.toSubgraph_dropUntil_le c' hb').2 hp₂_adj
    exact hnot' hc'_adj.symm
  have hsplit :
      Disjoint (Walk.InternalVertices p₁) (Walk.InternalVertices p₂) := by
    simpa [p₁, p₂] using
      Walk.IsCycle.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hc' hb'
  have hu_internal : u ∈ Walk.InternalVertices p₁ :=
    ⟨hu_support, hu_ne_a, hu_ne_b⟩
  have hw_internal : w ∈ Walk.InternalVertices p₂ :=
    ⟨hw_support, hw_ne_b, hw_ne_a⟩
  have hu_ne_w : u ≠ w := by
    intro huw
    exact Set.disjoint_left.mp hsplit hu_internal (by simpa [huw] using hw_internal)
  let pYU : G.Walk b u := (p₁.dropUntil u hu_support).reverse
  let pXW : G.Walk a w := (p₂.dropUntil w hw_support).reverse
  have hYU_path : pYU.IsPath := by
    simpa [pYU] using (hp₁_path.dropUntil hu_support).reverse
  have hXW_path : pXW.IsPath := by
    simpa [pXW] using (hp₂_path.dropUntil hw_support).reverse
  have hYU_internal_subset :
      Walk.InternalVertices pYU ⊆ Walk.InternalVertices p₁ := by
    intro q hq
    have hq_drop :
        q ∈ Walk.InternalVertices (p₁.dropUntil u hu_support) := by
      exact (Walk.mem_internalVertices_reverse_iff (p₁.dropUntil u hu_support)).1
        (by simpa [pYU] using hq)
    exact
      Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
        hp₁_path hu_support hu_ne_a hq_drop
  have hXW_internal_subset :
      Walk.InternalVertices pXW ⊆ Walk.InternalVertices p₂ := by
    intro q hq
    have hq_drop :
        q ∈ Walk.InternalVertices (p₂.dropUntil w hw_support) := by
      exact (Walk.mem_internalVertices_reverse_iff (p₂.dropUntil w hw_support)).1
        (by simpa [pXW] using hq)
    exact
      Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
        hp₂_path hw_support hw_ne_b hq_drop
  refine
    ContainsEdgeThetaSubdivision.of_five_paths_explicit
      hab.toWalk hau.toWalk pYU pXW hbw.toWalk
      hab.ne hau.ne hw_ne_a.symm hu_ne_b.symm hbw.ne hu_ne_w
      (SimpleGraph.Walk.IsPath.of_adj hab) (SimpleGraph.Walk.IsPath.of_adj hau) hYU_path
      hXW_path (SimpleGraph.Walk.IsPath.of_adj hbw)
      ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq d
    exact (Walk.not_mem_internalVertices_toWalk hab hq).elim
  · intro q hq d
    exact (Walk.not_mem_internalVertices_toWalk hau hq).elim
  · intro q hq d
    have hq₁ : q ∈ Walk.InternalVertices p₁ := hYU_internal_subset hq
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq₁.2.1
      · exact hq.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · exact hq.2.2
      · intro hqw
        exact Set.disjoint_left.mp hsplit hq₁ (by simpa [hqw] using hw_internal)
  · intro q hq d
    have hq₂ : q ∈ Walk.InternalVertices p₂ := hXW_internal_subset hq
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · exact hq₂.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqu
        exact Set.disjoint_left.mp hsplit (by simpa [hqu] using hu_internal) hq₂
      · exact hq.2.2
  · intro q hq d
    exact (Walk.not_mem_internalVertices_toWalk hbw hq).elim
  · intro L M hLM
    rcases L <;> rcases M <;>
      simp [edgeThetaPathInternalSet] at hLM ⊢
    all_goals
      rw [Set.disjoint_left]
      intro q hqL hqR
      first
      | exact (Walk.not_mem_internalVertices_toWalk hab hqL).elim
      | exact (Walk.not_mem_internalVertices_toWalk hab hqR).elim
      | exact (Walk.not_mem_internalVertices_toWalk hau hqL).elim
      | exact (Walk.not_mem_internalVertices_toWalk hau hqR).elim
      | exact (Walk.not_mem_internalVertices_toWalk hbw hqL).elim
      | exact (Walk.not_mem_internalVertices_toWalk hbw hqR).elim
      | exact
          Set.disjoint_left.mp hsplit
            (hYU_internal_subset hqL) (hXW_internal_subset hqR)
      | exact
          Set.disjoint_left.mp hsplit
            (hYU_internal_subset hqR) (hXW_internal_subset hqL)

/-- A path outside a simple cycle between two nonconsecutive cycle vertices
gives a suppressed-edge theta subdivision.  This is the path version of
`of_cycle_chord`, needed in the block/cactus proof: if a component outside a
cycle touches the cycle at two separated vertices, the external path together
with the two cycle arcs is a theta. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_external_path_nonadjacent
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hab_ne : a ≠ b)
    (hnot_adj : ¬ c.toSubgraph.Adj a b)
    (p : G.Walk a b)
    (hp : p.IsPath)
    (hp_internal_outside :
      forall {z : V}, z ∈ Walk.InternalVertices p -> z ∉ c.support) :
    ContainsEdgeThetaSubdivision G := by
  classical
  let c' : G.Walk a a := c.rotate a ha
  have hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate ha hc
  have hb' : b ∈ c'.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mpr hb
  have hnot' : ¬ c'.toSubgraph.Adj a b := by
    intro h
    exact hnot_adj (by simpa [c'] using h)
  let p₁ : G.Walk a b := c'.takeUntil b hb'
  let p₂ : G.Walk b a := c'.dropUntil b hb'
  have hp₁_path : p₁.IsPath := by
    simpa [p₁] using hc'.isPath_takeUntil hb'
  have hp₁_not_nil : ¬ p₁.Nil := by
    change ¬ (c'.takeUntil b hb').Nil
    rw [SimpleGraph.Walk.nil_takeUntil]
    exact hab_ne
  have hcycle_append : (p₁.append p₂).IsCycle := by
    simpa [p₁, p₂] using hc'
  have hp₂_path : p₂.IsPath :=
    hcycle_append.isPath_of_append_right hp₁_not_nil
  have hp₂_not_nil : ¬ p₂.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hab_ne.symm
  let u : V := p₁.snd
  let w : V := p₂.snd
  have hu_support : u ∈ p₁.support := by
    exact List.mem_of_mem_tail (p₁.snd_mem_tail_support hp₁_not_nil)
  have hw_support : w ∈ p₂.support := by
    exact List.mem_of_mem_tail (p₂.snd_mem_tail_support hp₂_not_nil)
  have hau : G.Adj a u := by
    simpa [u] using p₁.adj_snd hp₁_not_nil
  have hbw : G.Adj b w := by
    simpa [w] using p₂.adj_snd hp₂_not_nil
  have hu_ne_a : u ≠ a := hau.ne.symm
  have hw_ne_b : w ≠ b := hbw.ne.symm
  have hu_ne_b : u ≠ b := by
    intro hub
    have hp₁_adj : p₁.toSubgraph.Adj a b := by
      simpa [u, hub] using p₁.toSubgraph_adj_snd hp₁_not_nil
    have hc'_adj : c'.toSubgraph.Adj a b :=
      (Walk.toSubgraph_takeUntil_le c' hb').2 hp₁_adj
    exact hnot' hc'_adj
  have hw_ne_a : w ≠ a := by
    intro hwa
    have hp₂_adj : p₂.toSubgraph.Adj b a := by
      simpa [w, hwa] using p₂.toSubgraph_adj_snd hp₂_not_nil
    have hc'_adj : c'.toSubgraph.Adj b a :=
      (Walk.toSubgraph_dropUntil_le c' hb').2 hp₂_adj
    exact hnot' hc'_adj.symm
  have hsplit :
      Disjoint (Walk.InternalVertices p₁) (Walk.InternalVertices p₂) := by
    simpa [p₁, p₂] using
      Walk.IsCycle.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hc' hb'
  have hu_internal : u ∈ Walk.InternalVertices p₁ :=
    ⟨hu_support, hu_ne_a, hu_ne_b⟩
  have hw_internal : w ∈ Walk.InternalVertices p₂ :=
    ⟨hw_support, hw_ne_b, hw_ne_a⟩
  have hu_ne_w : u ≠ w := by
    intro huw
    exact Set.disjoint_left.mp hsplit hu_internal (by simpa [huw] using hw_internal)
  have hu_cycle : u ∈ c.support := by
    have hu_c' : u ∈ c'.support :=
      SimpleGraph.Walk.support_takeUntil_subset c' hb' hu_support
    exact (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mp hu_c'
  have hw_cycle : w ∈ c.support := by
    have hw_c' : w ∈ c'.support :=
      SimpleGraph.Walk.support_dropUntil_subset c' hb' hw_support
    exact (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mp hw_c'
  let pYU : G.Walk b u := (p₁.dropUntil u hu_support).reverse
  let pXW : G.Walk a w := (p₂.dropUntil w hw_support).reverse
  have hYU_path : pYU.IsPath := by
    simpa [pYU] using (hp₁_path.dropUntil hu_support).reverse
  have hXW_path : pXW.IsPath := by
    simpa [pXW] using (hp₂_path.dropUntil hw_support).reverse
  have hYU_internal_subset :
      Walk.InternalVertices pYU ⊆ Walk.InternalVertices p₁ := by
    intro q hq
    have hq_drop :
        q ∈ Walk.InternalVertices (p₁.dropUntil u hu_support) := by
      exact (Walk.mem_internalVertices_reverse_iff (p₁.dropUntil u hu_support)).1
        (by simpa [pYU] using hq)
    exact
      Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
        hp₁_path hu_support hu_ne_a hq_drop
  have hXW_internal_subset :
      Walk.InternalVertices pXW ⊆ Walk.InternalVertices p₂ := by
    intro q hq
    have hq_drop :
        q ∈ Walk.InternalVertices (p₂.dropUntil w hw_support) := by
      exact (Walk.mem_internalVertices_reverse_iff (p₂.dropUntil w hw_support)).1
        (by simpa [pXW] using hq)
    exact
      Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
        hp₂_path hw_support hw_ne_b hq_drop
  have hYU_internal_cycle :
      forall {q : V}, q ∈ Walk.InternalVertices pYU -> q ∈ c.support := by
    intro q hq
    have hq₁ : q ∈ Walk.InternalVertices p₁ := hYU_internal_subset hq
    have hq_c' : q ∈ c'.support :=
      SimpleGraph.Walk.support_takeUntil_subset c' hb' hq₁.1
    exact (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mp hq_c'
  have hXW_internal_cycle :
      forall {q : V}, q ∈ Walk.InternalVertices pXW -> q ∈ c.support := by
    intro q hq
    have hq₂ : q ∈ Walk.InternalVertices p₂ := hXW_internal_subset hq
    have hq_c' : q ∈ c'.support :=
      SimpleGraph.Walk.support_dropUntil_subset c' hb' hq₂.1
    exact (SimpleGraph.Walk.mem_support_rotate_iff c a ha).mp hq_c'
  refine
    ContainsEdgeThetaSubdivision.of_five_paths_explicit
      p hau.toWalk pYU pXW hbw.toWalk
      hab_ne hau.ne hw_ne_a.symm hu_ne_b.symm hbw.ne hu_ne_w
      hp (SimpleGraph.Walk.IsPath.of_adj hau) hYU_path hXW_path (SimpleGraph.Walk.IsPath.of_adj hbw)
      ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · exact hq.2.2
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqu
        exact hp_internal_outside hq (by simpa [hqu] using hu_cycle)
      · intro hqw
        exact hp_internal_outside hq (by simpa [hqw] using hw_cycle)
  · intro q hq d
    exact (Walk.not_mem_internalVertices_toWalk hau hq).elim
  · intro q hq d
    have hq₁ : q ∈ Walk.InternalVertices p₁ := hYU_internal_subset hq
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq₁.2.1
      · exact hq.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · exact hq.2.2
      · intro hqw
        exact Set.disjoint_left.mp hsplit hq₁ (by simpa [hqw] using hw_internal)
  · intro q hq d
    have hq₂ : q ∈ Walk.InternalVertices p₂ := hXW_internal_subset hq
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · exact hq₂.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqu
        exact Set.disjoint_left.mp hsplit (by simpa [hqu] using hu_internal) hq₂
      · exact hq.2.2
  · intro q hq d
    exact (Walk.not_mem_internalVertices_toWalk hbw hq).elim
  · intro L M hLM
    rcases L <;> rcases M <;>
      simp [edgeThetaPathInternalSet] at hLM ⊢
    · rw [Set.disjoint_left]
      intro q _hqL hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqR).elim
    · rw [Set.disjoint_left]
      intro q hqL hqR
      exact hp_internal_outside hqL (hYU_internal_cycle hqR)
    · rw [Set.disjoint_left]
      intro q hqL hqR
      exact hp_internal_outside hqL (hXW_internal_cycle hqR)
    · rw [Set.disjoint_left]
      intro q _hqL hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqR).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL hqR
      exact hp_internal_outside hqR (hYU_internal_cycle hqL)
    · rw [Set.disjoint_left]
      intro q _hqL hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqR).elim
    · rw [Set.disjoint_left]
      intro q hqL hqR
      exact
        Set.disjoint_left.mp hsplit
          (hYU_internal_subset hqL) (hXW_internal_subset hqR)
    · rw [Set.disjoint_left]
      intro q _hqL hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqR).elim
    · rw [Set.disjoint_left]
      intro q hqL hqR
      exact hp_internal_outside hqR (hXW_internal_cycle hqL)
    · rw [Set.disjoint_left]
      intro q _hqL hqR
      exact (Walk.not_mem_internalVertices_toWalk hau hqR).elim
    · rw [Set.disjoint_left]
      intro q hqL hqR
      exact
        Set.disjoint_left.mp hsplit
          (hYU_internal_subset hqR) (hXW_internal_subset hqL)
    · rw [Set.disjoint_left]
      intro q _hqL hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqR).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqL).elim
    · rw [Set.disjoint_left]
      intro q hqL _hqR
      exact (Walk.not_mem_internalVertices_toWalk hbw hqL).elim

/-- A path with a genuine outside internal vertex between two vertices of a
simple cycle gives a theta, regardless of whether the two cycle vertices are
consecutive.  The cycle is split at a third cycle vertex `z`; the external
path is split at one outside internal vertex. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_external_path_with_internal
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b z : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab_ne : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (p : G.Walk a b)
    (hp : p.IsPath)
    (hp_internal_outside :
      forall {q : V}, q ∈ Walk.InternalVertices p -> q ∉ c.support)
    (hinternal : Exists fun u : V => u ∈ Walk.InternalVertices p) :
    ContainsEdgeThetaSubdivision G := by
  classical
  rcases hinternal with ⟨u, hu_internal⟩
  have hu_outside : u ∉ c.support := hp_internal_outside hu_internal
  rcases
      Walk.IsCycle.exists_avoiding_path_and_split_through
        (G := G) c hc ha hb hz hab_ne haz.symm hbz.symm with
    ⟨pXY, pXZ, pYZ, hXY, hXZ, hYZ,
      hpXY_support, hpXZ_support, hpYZ_support,
      hz_not_pXY, hb_not_pXZ, ha_not_pYZ,
      hXY_XZ, hXY_YZ, hXZ_YZ⟩
  let pXU : G.Walk a u := p.takeUntil u hu_internal.1
  let pYU : G.Walk b u := (p.dropUntil u hu_internal.1).reverse
  have hXU : pXU.IsPath := by
    simpa [pXU] using hp.takeUntil hu_internal.1
  have hYU : pYU.IsPath := by
    simpa [pYU] using (hp.dropUntil hu_internal.1).reverse
  have hXU_internal_subset :
      Walk.InternalVertices pXU ⊆ Walk.InternalVertices p := by
    exact
      Walk.IsPath.internalVertices_takeUntil_subset_internalVertices
        hp hu_internal.1 hu_internal.2.2
  have hYU_internal_subset :
      Walk.InternalVertices pYU ⊆ Walk.InternalVertices p := by
    intro q hq
    have hq_drop :
        q ∈ Walk.InternalVertices (p.dropUntil u hu_internal.1) := by
      exact (Walk.mem_internalVertices_reverse_iff (p.dropUntil u hu_internal.1)).1
        (by simpa [pYU] using hq)
    exact
      Walk.IsPath.internalVertices_dropUntil_subset_internalVertices
        hp hu_internal.1 hu_internal.2.1 hq_drop
  have hXU_outside :
      forall {q : V}, q ∈ Walk.InternalVertices pXU -> q ∉ c.support := by
    intro q hq
    exact hp_internal_outside (hXU_internal_subset hq)
  have hYU_outside :
      forall {q : V}, q ∈ Walk.InternalVertices pYU -> q ∉ c.support := by
    intro q hq
    exact hp_internal_outside (hYU_internal_subset hq)
  have hXU_YU :
      Disjoint (Walk.InternalVertices pXU) (Walk.InternalVertices pYU) := by
    have hsplit :=
      Walk.IsPath.internalVertices_takeUntil_disjoint_internalVertices_dropUntil
        (G := G) hp hu_internal.1
    rw [Set.disjoint_left]
    intro q hqXU hqYU
    have hq_drop :
        q ∈ Walk.InternalVertices (p.dropUntil u hu_internal.1) := by
      exact (Walk.mem_internalVertices_reverse_iff (p.dropUntil u hu_internal.1)).1
        (by simpa [pYU] using hqYU)
    exact Set.disjoint_left.mp hsplit (by simpa [pXU] using hqXU) hq_drop
  have hxy_u : a ≠ u := by
    intro hau
    exact hu_outside (by simpa [hau] using ha)
  have hyu : b ≠ u := by
    intro hbu
    exact hu_outside (by simpa [hbu] using hb)
  have hzu : u ≠ z := by
    intro huz
    exact hu_outside (by simpa [huz] using hz)
  refine
    ContainsEdgeThetaSubdivision.of_five_paths_explicit
      pXY pXU pYU pXZ pYZ
      hab_ne hxy_u haz hyu hbz hzu
      hXY hXU hYU hXZ hYZ
      ?_ ?_ ?_ ?_ ?_ ?_
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · exact hq.2.2
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqu
        exact hu_outside (by simpa [hqu] using hpXY_support q hq.1)
      · intro hqz
        exact hz_not_pXY (by simpa [hqz] using hq.1)
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · intro hqb
        exact hXU_outside hq (by simpa [hqb] using hb)
    · fin_cases j <;> simp [edgeThetaBranch]
      · exact hq.2.2
      · intro hqz
        exact hXU_outside hq (by simpa [hqz] using hz)
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · intro hqa
        exact hYU_outside hq (by simpa [hqa] using ha)
      · exact hq.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · exact hq.2.2
      · intro hqz
        exact hYU_outside hq (by simpa [hqz] using hz)
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · exact hq.2.1
      · intro hqb
        exact hb_not_pXZ (by simpa [hqb] using hq.1)
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqu
        exact hu_outside (by simpa [hqu] using hpXZ_support q hq.1)
      · exact hq.2.2
  · intro q hq d
    rcases d with i | j
    · fin_cases i <;> simp [edgeThetaBranch]
      · intro hqa
        exact ha_not_pYZ (by simpa [hqa] using hq.1)
      · exact hq.2.1
    · fin_cases j <;> simp [edgeThetaBranch]
      · intro hqu
        exact hu_outside (by simpa [hqu] using hpYZ_support q hq.1)
      · exact hq.2.2
  · intro L M hLM
    rcases L <;> rcases M <;>
      simp [edgeThetaPathInternalSet] at hLM ⊢
    all_goals
      rw [Set.disjoint_left]
      intro q hqL hqR
      first
      | exact Set.disjoint_left.mp hXY_XZ hqL hqR
      | exact Set.disjoint_left.mp hXY_XZ.symm hqL hqR
      | exact Set.disjoint_left.mp hXY_YZ hqL hqR
      | exact Set.disjoint_left.mp hXY_YZ.symm hqL hqR
      | exact Set.disjoint_left.mp hXZ_YZ hqL hqR
      | exact Set.disjoint_left.mp hXZ_YZ.symm hqL hqR
      | exact Set.disjoint_left.mp hXU_YU hqL hqR
      | exact Set.disjoint_left.mp hXU_YU.symm hqL hqR
      | exact hXU_outside hqL (hpXY_support q hqR.1)
      | exact hXU_outside hqR (hpXY_support q hqL.1)
      | exact hYU_outside hqL (hpXY_support q hqR.1)
      | exact hYU_outside hqR (hpXY_support q hqL.1)
      | exact hXU_outside hqL (hpXZ_support q hqR.1)
      | exact hXU_outside hqR (hpXZ_support q hqL.1)
      | exact hYU_outside hqL (hpXZ_support q hqR.1)
      | exact hYU_outside hqR (hpXZ_support q hqL.1)
      | exact hXU_outside hqL (hpYZ_support q hqR.1)
      | exact hXU_outside hqR (hpYZ_support q hqL.1)
      | exact hYU_outside hqL (hpYZ_support q hqR.1)
      | exact hYU_outside hqR (hpYZ_support q hqL.1)

/-- Connector form of `of_cycle_external_path_with_internal`: a path outside a
cycle, plus two contact edges to distinct cycle vertices, forms a theta.  The
third cycle vertex `z` specifies the split of the cycle into two internally
disjoint branches. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_external_connector
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b z u v : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hz : z ∈ c.support)
    (hab_ne : a ≠ b)
    (haz : a ≠ z)
    (hbz : b ≠ z)
    (hau : G.Adj a u)
    (q : G.Walk u v)
    (hq : q.IsPath)
    (hq_outside : forall {t : V}, t ∈ q.support -> t ∉ c.support)
    (hbv : G.Adj b v) :
    ContainsEdgeThetaSubdivision G := by
  classical
  let pAU : G.Walk a u := hau.toWalk
  let pAUV : G.Walk a v := pAU.append q
  let p : G.Walk a b := pAUV.append hbv.symm.toWalk
  have hu_outside : u ∉ c.support := hq_outside q.start_mem_support
  have hv_outside : v ∉ c.support := hq_outside q.end_mem_support
  have hpAUV_path : pAUV.IsPath := by
    refine
      Walk.IsPath.append_of_support_inter_eq_endpoint
        (SimpleGraph.Walk.IsPath.of_adj hau) hq ?_
    intro t ht_edge htq
    have ht_edge_cases : t = a ∨ t = u := by
      simpa [pAU] using ht_edge
    rcases ht_edge_cases with rfl | rfl
    · exact False.elim ((hq_outside htq) ha)
    · rfl
  have hp_path : p.IsPath := by
    refine
      Walk.IsPath.append_of_support_inter_eq_endpoint
        hpAUV_path (SimpleGraph.Walk.IsPath.of_adj hbv.symm) ?_
    intro t ht_left ht_edge
    have ht_edge_cases : t = v ∨ t = b := by
      simpa using ht_edge
    rcases ht_edge_cases with htv | htb
    · exact htv
    · exfalso
      have hb_left : b ∈ pAUV.support := by simpa [htb] using ht_left
      rw [SimpleGraph.Walk.mem_support_append_iff] at hb_left
      rcases hb_left with hb_edge | hb_q
      · have hb_edge_cases : b = a ∨ b = u := by
          simpa [pAU] using hb_edge
        rcases hb_edge_cases with hba | hbu
        · exact hab_ne hba.symm
        · exact hu_outside (by simpa [hbu] using hb)
      · exact (hq_outside hb_q) hb
  have hp_internal_outside :
      forall {t : V}, t ∈ Walk.InternalVertices p -> t ∉ c.support := by
    intro t ht htC
    have ht_support : t ∈ p.support := ht.1
    change t ∈ (pAUV.append hbv.symm.toWalk).support at ht_support
    rw [SimpleGraph.Walk.mem_support_append_iff] at ht_support
    rcases ht_support with ht_left | ht_edge
    · have ht_left' : t ∈ pAUV.support := ht_left
      rw [SimpleGraph.Walk.mem_support_append_iff] at ht_left'
      rcases ht_left' with ht_edge | ht_q
      · have ht_edge_cases : t = a ∨ t = u := by
          simpa [pAU] using ht_edge
        rcases ht_edge_cases with rfl | rfl
        · exact ht.2.1 rfl
        · exact hu_outside htC
      · exact (hq_outside ht_q) htC
    · have ht_edge_cases : t = v ∨ t = b := by
        simpa using ht_edge
      rcases ht_edge_cases with rfl | rfl
      · exact hv_outside htC
      · exact ht.2.2 rfl
  have hu_ne_a : u ≠ a := by
    intro hua
    exact hu_outside (by simpa [hua] using ha)
  have hu_ne_b : u ≠ b := by
    intro hub
    exact hu_outside (by simpa [hub] using hb)
  have hu_support_pAUV : u ∈ pAUV.support := by
    change u ∈ (pAU.append q).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    right
    exact q.start_mem_support
  have hu_support_p : u ∈ p.support := by
    change u ∈ (pAUV.append hbv.symm.toWalk).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl hu_support_pAUV
  have hu_internal_p : u ∈ Walk.InternalVertices p :=
    ⟨hu_support_p, hu_ne_a, hu_ne_b⟩
  exact
    ContainsEdgeThetaSubdivision.of_cycle_external_path_with_internal
      c hc ha hb hz hab_ne haz hbz p hp_path hp_internal_outside
      ⟨u, hu_internal_p⟩

/-- If an outside path component attaches to two nonconsecutive vertices of a
simple cycle, then the graph contains a suppressed-edge theta subdivision.

This is the block/cactus contact form of
`ContainsEdgeThetaSubdivision.of_cycle_external_path_nonadjacent`: prepend and
append the two contact edges to a path whose support is outside the cycle, then
use the resulting cycle-avoiding path between the two cycle vertices. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_external_connector_nonadjacent
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b u v : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hab_ne : a ≠ b)
    (hnot_adj : ¬ c.toSubgraph.Adj a b)
    (hau : G.Adj a u)
    (q : G.Walk u v)
    (hq : q.IsPath)
    (hq_outside : forall {z : V}, z ∈ q.support -> z ∉ c.support)
    (hbv : G.Adj b v) :
    ContainsEdgeThetaSubdivision G := by
  classical
  let pAU : G.Walk a u := hau.toWalk
  let pAUV : G.Walk a v := pAU.append q
  let p : G.Walk a b := pAUV.append hbv.symm.toWalk
  have hu_outside : u ∉ c.support := hq_outside q.start_mem_support
  have hv_outside : v ∉ c.support := hq_outside q.end_mem_support
  have hpAUV_path : pAUV.IsPath := by
    refine
      Walk.IsPath.append_of_support_inter_eq_endpoint
        (SimpleGraph.Walk.IsPath.of_adj hau) hq ?_
    intro z hz_edge hzq
    have hz_edge_cases : z = a ∨ z = u := by
      simpa [pAU] using hz_edge
    rcases hz_edge_cases with rfl | rfl
    · exact False.elim ((hq_outside hzq) ha)
    · rfl
  have hp_path : p.IsPath := by
    refine
      Walk.IsPath.append_of_support_inter_eq_endpoint
        hpAUV_path (SimpleGraph.Walk.IsPath.of_adj hbv.symm) ?_
    intro z hz_left hz_edge
    have hz_edge_cases : z = v ∨ z = b := by
      simpa using hz_edge
    rcases hz_edge_cases with hzv | hzb
    · exact hzv
    · exfalso
      have hb_left : b ∈ pAUV.support := by simpa [hzb] using hz_left
      rw [SimpleGraph.Walk.mem_support_append_iff] at hb_left
      rcases hb_left with hb_edge | hb_q
      · have hb_edge_cases : b = a ∨ b = u := by
          simpa [pAU] using hb_edge
        rcases hb_edge_cases with hba | hbu
        · exact hab_ne hba.symm
        · exact hu_outside (by simpa [hbu] using hb)
      · exact (hq_outside hb_q) hb
  have hp_internal_outside :
      forall {z : V}, z ∈ Walk.InternalVertices p -> z ∉ c.support := by
    intro z hz hzC
    have hz_support : z ∈ p.support := hz.1
    change z ∈ (pAUV.append hbv.symm.toWalk).support at hz_support
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz_support
    rcases hz_support with hz_left | hz_edge
    · have hz_left' : z ∈ pAUV.support := hz_left
      rw [SimpleGraph.Walk.mem_support_append_iff] at hz_left'
      rcases hz_left' with hz_edge | hz_q
      · have hz_edge_cases : z = a ∨ z = u := by
          simpa [pAU] using hz_edge
        rcases hz_edge_cases with rfl | rfl
        · exact hz.2.1 rfl
        · exact hu_outside hzC
      · exact (hq_outside hz_q) hzC
    · have hz_edge_cases : z = v ∨ z = b := by
        simpa using hz_edge
      rcases hz_edge_cases with rfl | rfl
      · exact hv_outside hzC
      · exact hz.2.2 rfl
  exact
    ContainsEdgeThetaSubdivision.of_cycle_external_path_nonadjacent
      c hc ha hb hab_ne hnot_adj p hp_path hp_internal_outside

/-- Reachability version of the outside-contact theta obstruction.  If two
outside neighbours of nonconsecutive cycle vertices lie in the same component
of the graph induced outside the cycle, the induced outside path plus the two
contact edges gives a suppressed-edge theta subdivision. -/
theorem ContainsEdgeThetaSubdivision.of_cycle_external_reachable_nonadjacent
    {V : Type v} [DecidableEq V]
    {G : SimpleGraph V}
    {r a b u v : V}
    (c : G.Walk r r)
    (hc : c.IsCycle)
    (ha : a ∈ c.support)
    (hb : b ∈ c.support)
    (hab_ne : a ≠ b)
    (hnot_adj : ¬ c.toSubgraph.Adj a b)
    (hu_outside : u ∉ c.support)
    (hv_outside : v ∉ c.support)
    (hreach :
      (G.induce {z : V | z ∉ c.support}).Reachable
        (⟨u, hu_outside⟩ : {z : V | z ∉ c.support})
        (⟨v, hv_outside⟩ : {z : V | z ∉ c.support}))
    (hau : G.Adj a u)
    (hbv : G.Adj b v) :
    ContainsEdgeThetaSubdivision G := by
  classical
  rcases
      reachable_induce_exists_chordless_path_support_subset
        (G := G) (A := {z : V | z ∉ c.support})
        hu_outside hv_outside hreach with
    ⟨q, hq_path, _hq_chordless, hq_support⟩
  exact
    ContainsEdgeThetaSubdivision.of_cycle_external_connector_nonadjacent
      c hc ha hb hab_ne hnot_adj hau q hq_path
      (by
        intro z hz
        exact hq_support z hz)
      hbv


end Schematic.Math.GraphTheory
