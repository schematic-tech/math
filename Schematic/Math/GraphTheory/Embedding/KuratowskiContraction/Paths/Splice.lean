import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Forward-order path contraction across one collapsed edge.  If a simple
source path meets the contracted edge as consecutive vertices `a,b`, then the
two clean quotient halves splice to a simple path in the contracted graph. -/
theorem exists_isPath_collapseEdge_splice_forward
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b u v : V}
    (hab : G.Adj a b)
    {p : G.Walk u v}
    (hp : p.IsPath)
    (ha : a ∈ p.support)
    (hb : b ∈ p.support)
    (hidx : p.support.idxOf b = p.support.idxOf a + 1) :
    Exists fun q :
      (GraphContraction.collapseEdge G hab).graph.Walk
        ((GraphContraction.collapseEdge G hab).map u)
        ((GraphContraction.collapseEdge G hab).map v) =>
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun x : V =>
              x ∈ p.support ∧
                (GraphContraction.collapseEdge G hab).map x = z := by
  classical
  let C := GraphContraction.collapseEdge G hab
  have ha_lt_b : p.support.idxOf a < p.support.idxOf b := by
    rw [hidx]
    omega
  have hb_not_left :
      b ∉ (p.takeUntil a ha).support :=
    Walk.not_mem_takeUntil_of_idxOf_lt ha ha_lt_b
  have ha_not_right :
      a ∉ (p.dropUntil b hb).support :=
    Walk.IsPath.earlier_not_mem_dropUntil_of_idx_lt hp hb ha_lt_b
  have hnot_left :
      ¬ (a ∈ (p.takeUntil a ha).support ∧
        b ∈ (p.takeUntil a ha).support) := by
    intro h
    exact hb_not_left h.2
  have hnot_right :
      ¬ (a ∈ (p.dropUntil b hb).support ∧
        b ∈ (p.dropUntil b hb).support) := by
    intro h
    exact ha_not_right h.1
  let qL :=
    GraphContraction.collapseEdgeWalkOfNotPairBoth
      (G := G) hab (p.takeUntil a ha) hnot_left
  let qR0 :=
    GraphContraction.collapseEdgeWalkOfNotPairBoth
      (G := G) hab (p.dropUntil b hb) hnot_right
  have hmap_ba : C.map b = C.map a := by
    rw [GraphContraction.collapseEdge_map_eq_iff]
    left
    constructor <;> simp
  let qR :
      C.graph.Walk (C.map a) (C.map v) :=
    qR0.copy hmap_ba rfl
  let q : C.graph.Walk (C.map u) (C.map v) := qL.append qR
  have hqL : qL.IsPath := by
    simpa [qL, C] using
      GraphContraction.isPath_collapseEdgeWalkOfNotPairBoth
        (G := G) hab (p.takeUntil a ha) (hp.takeUntil ha) hnot_left
  have hqR0 : qR0.IsPath := by
    simpa [qR0, C] using
      GraphContraction.isPath_collapseEdgeWalkOfNotPairBoth
        (G := G) hab (p.dropUntil b hb) (hp.dropUntil hb) hnot_right
  have hqR : qR.IsPath := by
    simpa [qR] using
      (SimpleGraph.Walk.isPath_copy qR0 hmap_ba rfl).mpr hqR0
  have hsplit_disjoint :
      Disjoint
        {z : V | z ∈ (p.takeUntil a ha).support}
        {z : V | z ∈ (p.dropUntil b hb).support} :=
    Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
      hp ha hb ha_lt_b
  have hdisjoint :
      Disjoint
        {z : C.Target | z ∈ qL.support ∧ z ≠ C.map a}
        {z : C.Target | z ∈ qR.support ∧ z ≠ C.map a} := by
    rw [Set.disjoint_left]
    rintro z ⟨hzL, hz_ne⟩ ⟨hzR, _hzR_ne⟩
    have hzR0 : z ∈ qR0.support := by
      simpa [qR, SimpleGraph.Walk.support_copy] using hzR
    have hzL_map :
        z ∈ (p.takeUntil a ha).support.map C.map := by
      simpa [qL, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzL
    have hzR_map :
        z ∈ (p.dropUntil b hb).support.map C.map := by
      simpa [qR0, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzR0
    rcases List.mem_map.mp hzL_map with ⟨x, hx_left, hx_map⟩
    rcases List.mem_map.mp hzR_map with ⟨y, hy_right, hy_map⟩
    have hxy_map : C.map x = C.map y := by
      exact hx_map.trans hy_map.symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := x) (w := y)).mp hxy_map with
      hpair | houtside
    · have hx_pair : x = a ∨ x = b := by
        simpa using hpair.1
      have hy_pair : y = a ∨ y = b := by
        simpa using hpair.2
      rcases hx_pair with rfl | rfl
      · rcases hy_pair with rfl | rfl
        · exact hz_ne hx_map.symm
        · exact hz_ne hx_map.symm
      · exact False.elim (hb_not_left hx_left)
    · have hxy : x = y := houtside.1
      exact Set.disjoint_left.mp hsplit_disjoint hx_left
        (by simpa [hxy] using hy_right)
  have hq : q.IsPath := by
    exact Walk.IsPath.append_of_punctured_supports_disjoint hqL hqR hdisjoint
  refine ⟨q, hq, ?_⟩
  intro z hz
  simp only [q, SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzL | hzR
  · have hzL_map :
        z ∈ (p.takeUntil a ha).support.map C.map := by
      simpa [qL, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzL
    rcases List.mem_map.mp hzL_map with ⟨x, hx, hxmap⟩
    exact ⟨x,
      SimpleGraph.Walk.support_takeUntil_subset p ha hx,
      by simpa [C] using hxmap⟩
  · have hzR0 : z ∈ qR0.support := by
      simpa [qR, SimpleGraph.Walk.support_copy] using hzR
    have hzR_map :
        z ∈ (p.dropUntil b hb).support.map C.map := by
      simpa [qR0, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzR0
    rcases List.mem_map.mp hzR_map with ⟨x, hx, hxmap⟩
    exact ⟨x,
      SimpleGraph.Walk.support_dropUntil_subset p hb hx,
      by simpa [C] using hxmap⟩

/-- Reverse-order variant of `exists_isPath_collapseEdge_splice_forward`. -/
theorem exists_isPath_collapseEdge_splice_reverse
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b u v : V}
    (hab : G.Adj a b)
    {p : G.Walk u v}
    (hp : p.IsPath)
    (ha : a ∈ p.support)
    (hb : b ∈ p.support)
    (hidx : p.support.idxOf a = p.support.idxOf b + 1) :
    Exists fun q :
      (GraphContraction.collapseEdge G hab).graph.Walk
        ((GraphContraction.collapseEdge G hab).map u)
        ((GraphContraction.collapseEdge G hab).map v) =>
      q.IsPath ∧
        forall z,
          z ∈ q.support ->
            Exists fun x : V =>
              x ∈ p.support ∧
                (GraphContraction.collapseEdge G hab).map x = z := by
  classical
  let C := GraphContraction.collapseEdge G hab
  have hb_lt_a : p.support.idxOf b < p.support.idxOf a := by
    rw [hidx]
    omega
  have ha_not_left :
      a ∉ (p.takeUntil b hb).support :=
    Walk.not_mem_takeUntil_of_idxOf_lt hb hb_lt_a
  have hb_not_right :
      b ∉ (p.dropUntil a ha).support :=
    Walk.IsPath.earlier_not_mem_dropUntil_of_idx_lt hp ha hb_lt_a
  have hnot_left :
      ¬ (a ∈ (p.takeUntil b hb).support ∧
        b ∈ (p.takeUntil b hb).support) := by
    intro h
    exact ha_not_left h.1
  have hnot_right :
      ¬ (a ∈ (p.dropUntil a ha).support ∧
        b ∈ (p.dropUntil a ha).support) := by
    intro h
    exact hb_not_right h.2
  let qL :=
    GraphContraction.collapseEdgeWalkOfNotPairBoth
      (G := G) hab (p.takeUntil b hb) hnot_left
  let qR0 :=
    GraphContraction.collapseEdgeWalkOfNotPairBoth
      (G := G) hab (p.dropUntil a ha) hnot_right
  have hmap_ab : C.map a = C.map b := by
    rw [GraphContraction.collapseEdge_map_eq_iff]
    left
    constructor <;> simp
  let qR :
      C.graph.Walk (C.map b) (C.map v) :=
    qR0.copy hmap_ab rfl
  let q : C.graph.Walk (C.map u) (C.map v) := qL.append qR
  have hqL : qL.IsPath := by
    simpa [qL, C] using
      GraphContraction.isPath_collapseEdgeWalkOfNotPairBoth
        (G := G) hab (p.takeUntil b hb) (hp.takeUntil hb) hnot_left
  have hqR0 : qR0.IsPath := by
    simpa [qR0, C] using
      GraphContraction.isPath_collapseEdgeWalkOfNotPairBoth
        (G := G) hab (p.dropUntil a ha) (hp.dropUntil ha) hnot_right
  have hqR : qR.IsPath := by
    simpa [qR] using
      (SimpleGraph.Walk.isPath_copy qR0 hmap_ab rfl).mpr hqR0
  have hsplit_disjoint :
      Disjoint
        {z : V | z ∈ (p.takeUntil b hb).support}
        {z : V | z ∈ (p.dropUntil a ha).support} :=
    Walk.IsPath.takeUntil_support_disjoint_dropUntil_support_of_idx_lt
      hp hb ha hb_lt_a
  have hdisjoint :
      Disjoint
        {z : C.Target | z ∈ qL.support ∧ z ≠ C.map b}
        {z : C.Target | z ∈ qR.support ∧ z ≠ C.map b} := by
    rw [Set.disjoint_left]
    rintro z ⟨hzL, hz_ne⟩ ⟨hzR, _hzR_ne⟩
    have hzR0 : z ∈ qR0.support := by
      simpa [qR, SimpleGraph.Walk.support_copy] using hzR
    have hzL_map :
        z ∈ (p.takeUntil b hb).support.map C.map := by
      simpa [qL, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzL
    have hzR_map :
        z ∈ (p.dropUntil a ha).support.map C.map := by
      simpa [qR0, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzR0
    rcases List.mem_map.mp hzL_map with ⟨x, hx_left, hx_map⟩
    rcases List.mem_map.mp hzR_map with ⟨y, hy_right, hy_map⟩
    have hxy_map : C.map x = C.map y := by
      exact hx_map.trans hy_map.symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := x) (w := y)).mp hxy_map with
      hpair | houtside
    · have hx_pair : x = a ∨ x = b := by
        simpa using hpair.1
      have hy_pair : y = a ∨ y = b := by
        simpa using hpair.2
      rcases hx_pair with rfl | rfl
      · exact False.elim (ha_not_left hx_left)
      · rcases hy_pair with rfl | rfl
        · exact hz_ne hx_map.symm
        · exact hz_ne hx_map.symm
    · have hxy : x = y := houtside.1
      exact Set.disjoint_left.mp hsplit_disjoint hx_left
        (by simpa [hxy] using hy_right)
  have hq : q.IsPath := by
    exact Walk.IsPath.append_of_punctured_supports_disjoint hqL hqR hdisjoint
  refine ⟨q, hq, ?_⟩
  intro z hz
  simp only [q, SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with hzL | hzR
  · have hzL_map :
        z ∈ (p.takeUntil b hb).support.map C.map := by
      simpa [qL, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzL
    rcases List.mem_map.mp hzL_map with ⟨x, hx, hxmap⟩
    exact ⟨x,
      SimpleGraph.Walk.support_takeUntil_subset p hb hx,
      by simpa [C] using hxmap⟩
  · have hzR0 : z ∈ qR0.support := by
      simpa [qR, SimpleGraph.Walk.support_copy] using hzR
    have hzR_map :
        z ∈ (p.dropUntil a ha).support.map C.map := by
      simpa [qR0, C, GraphContraction.support_collapseEdgeWalkOfNotPairBoth]
        using hzR0
    rcases List.mem_map.mp hzR_map with ⟨x, hx, hxmap⟩
    exact ⟨x,
      SimpleGraph.Walk.support_dropUntil_subset p ha hx,
      by simpa [C] using hxmap⟩
end FourColor

end Schematic.Math.GraphTheory
