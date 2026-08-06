import Schematic.Math.GraphTheory.Contractions.TripleCollapse

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GraphContraction

variable {G : SimpleGraph V}


noncomputable def comp
    (C1 : GraphContraction G)
    (C2 : GraphContraction C1.graph) :
    GraphContraction G where
  Target := C2.Target
  graph := C2.graph
  map v := C2.map (C1.map v)
  map_adj := by
    intro v w hvw
    rcases C1.map_adj hvw with hsame | hadj
    · exact Or.inl (by rw [hsame])
    · rcases C2.map_adj hadj with hsame | hadj2
      · exact Or.inl hsame
      · exact Or.inr hadj2
  edge_lift := by
    intro y z hyz
    obtain ⟨a, b, ha, hb, hab⟩ := C2.edge_lift hyz
    obtain ⟨v, w, hv, hw, hvw⟩ := C1.edge_lift hab
    exact ⟨v, w, by simp [ha, hv], by simp [hb, hw], hvw⟩
  surjective := by
    intro y
    obtain ⟨a, ha⟩ := C2.surjective y
    obtain ⟨v, hv⟩ := C1.surjective a
    exact ⟨v, by simpa [hv] using ha⟩
  connected_fiber := by
    intro y
    let H2 : C1.graph.Subgraph :=
      (⊤ : C1.graph.Subgraph).induce {a : C1.Target | C2.map a = y}
    have hH2_coe : H2.coe.Connected := by
      simpa [H2, SimpleGraph.induce_eq_coe_induce_top] using
        C2.connected_fiber y
    have hpre :
        (C1.PreimageSubgraph H2).coe.Connected :=
      GraphContraction.preimageSubgraph_connected (C := C1) hH2_coe
    have hpre_subgraph :
        (C1.PreimageSubgraph H2).Connected := ⟨hpre⟩
    have hpre_induce :
        (G.induce (C1.PreimageSubgraph H2).verts).Connected :=
      SimpleGraph.Subgraph.Connected.induce_verts hpre_subgraph
    simpa [PreimageSubgraph, H2] using hpre_induce

@[simp] theorem comp_map
    (C1 : GraphContraction G)
    (C2 : GraphContraction C1.graph)
    (v : V) :
    (C1.comp C2).map v = C2.map (C1.map v) :=
  rfl

@[simp] theorem comp_graph
    (C1 : GraphContraction G)
    (C2 : GraphContraction C1.graph) :
    (C1.comp C2).graph = C2.graph :=
  rfl

/-- Map a source walk through a graph contraction, suppressing precisely those
steps whose endpoints are identified by the contraction map.  This is the
walk-level form of the `G/e` operation used in the Makarychev/Skopenkov proof. -/
noncomputable def mapWalk
    (C : GraphContraction G) :
    {u v : V} -> G.Walk u v -> C.graph.Walk (C.map u) (C.map v)
  | _, _, .nil => .nil
  | _, _, .cons (u := a) (v := b) huv p =>
      letI : DecidableEq C.Target := Classical.decEq C.Target
      if hsame : C.map a = C.map b then
          (mapWalk C p).copy hsame.symm rfl
      else
        let hadj : C.graph.Adj (C.map a) (C.map b) := (by
          rcases C.map_adj huv with h | h
          · exact False.elim (hsame h)
          · exact h)
        Walk.cons hadj (mapWalk C p)

theorem mapWalk_support_reflects
    (C : GraphContraction G)
    {u v : V} :
    (p : G.Walk u v) ->
      {y : C.Target} ->
        y ∈ (C.mapWalk p).support ->
          Exists fun x : V => x ∈ p.support ∧ C.map x = y
  | .nil, y, hy => by
      simp [mapWalk] at hy
      exact ⟨u, by simp, hy.symm⟩
  | @Walk.cons _ _ a b c hab p, y, hy => by
      classical
      dsimp [mapWalk] at hy
      by_cases hsame : C.map a = C.map b
      · have hy' : y ∈ (C.mapWalk p).support := by
          simpa [mapWalk, hsame] using hy
        rcases mapWalk_support_reflects C p hy' with ⟨x, hx, hxy⟩
        exact ⟨x, SimpleGraph.Walk.support_subset_support_cons p hab hx, hxy⟩
      · simp [hsame, SimpleGraph.Walk.support_cons] at hy
        rcases hy with hy_a | hy_tail
        · exact ⟨a, by simp, hy_a.symm⟩
        · rcases mapWalk_support_reflects C p hy_tail with ⟨x, hx, hxy⟩
          exact ⟨x, SimpleGraph.Walk.support_subset_support_cons p hab hx, hxy⟩

noncomputable def mapWalkOfSupportInjective
    (C : GraphContraction G) :
    {u v : V} ->
      (p : G.Walk u v) ->
      (forall a b : V, a ∈ p.support -> b ∈ p.support ->
        C.map a = C.map b -> a = b) ->
      C.graph.Walk (C.map u) (C.map v)
  | _, _, .nil, _ => Walk.nil
  | _, _, .cons (u := a) (v := b) (w := c) huv p, hinj =>
      have hmap_ne : C.map a ≠ C.map b := by
        intro hsame
        have huv_eq := hinj a b (by simp) (by simp) hsame
        exact huv.ne huv_eq
      have hmap_adj : C.graph.Adj (C.map a) (C.map b) := by
        rcases C.map_adj huv with hsame | hadj
        · exact False.elim (hmap_ne hsame)
        · exact hadj
      Walk.cons hmap_adj
        (mapWalkOfSupportInjective C p (by
          intro x y hx hy hxy
          exact hinj x y
            (SimpleGraph.Walk.support_subset_support_cons p huv hx)
            (SimpleGraph.Walk.support_subset_support_cons p huv hy)
            hxy))

theorem support_mapWalkOfSupportInjective
    (C : GraphContraction G)
    {u v : V}
    (p : G.Walk u v)
    (hinj :
      forall a b : V, a ∈ p.support -> b ∈ p.support ->
        C.map a = C.map b -> a = b) :
    (C.mapWalkOfSupportInjective p hinj).support = p.support.map C.map := by
  induction p with
  | nil =>
      simp [mapWalkOfSupportInjective]
  | cons huv p ih =>
      simp [mapWalkOfSupportInjective, ih]

theorem isPath_mapWalkOfSupportInjective
    (C : GraphContraction G)
    {u v : V}
    (p : G.Walk u v)
    (hp : p.IsPath)
    (hinj :
      forall a b : V, a ∈ p.support -> b ∈ p.support ->
        C.map a = C.map b -> a = b) :
    (C.mapWalkOfSupportInjective p hinj).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,
    GraphContraction.support_mapWalkOfSupportInjective]
  exact hp.support_nodup.map_on (by
    intro a ha b hb hab
    exact hinj a b ha hb hab)

noncomputable def collapseEdgeWalkOfNotPairBoth
    {u v a b : V}
    (hab : G.Adj a b)
    (p : G.Walk u v)
    (hnot_both : ¬ (a ∈ p.support ∧ b ∈ p.support)) :
    (GraphContraction.collapseEdge G hab).graph.Walk
      ((GraphContraction.collapseEdge G hab).map u)
      ((GraphContraction.collapseEdge G hab).map v) :=
  (GraphContraction.collapseEdge G hab).mapWalkOfSupportInjective p
    (GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
      G hab {z : V | z ∈ p.support} (by
        intro h
        exact hnot_both h))

theorem support_collapseEdgeWalkOfNotPairBoth
    {u v a b : V}
    (hab : G.Adj a b)
    (p : G.Walk u v)
    (hnot_both : ¬ (a ∈ p.support ∧ b ∈ p.support)) :
    (GraphContraction.collapseEdgeWalkOfNotPairBoth
        (G := G) hab p hnot_both).support =
      p.support.map (GraphContraction.collapseEdge G hab).map := by
  exact GraphContraction.support_mapWalkOfSupportInjective
    (GraphContraction.collapseEdge G hab) p
    (GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
      G hab {z : V | z ∈ p.support} (by
        intro h
        exact hnot_both h))

theorem isPath_collapseEdgeWalkOfNotPairBoth
    {u v a b : V}
    (hab : G.Adj a b)
    (p : G.Walk u v)
    (hp : p.IsPath)
    (hnot_both : ¬ (a ∈ p.support ∧ b ∈ p.support)) :
    (GraphContraction.collapseEdgeWalkOfNotPairBoth
        (G := G) hab p hnot_both).IsPath :=
  GraphContraction.isPath_mapWalkOfSupportInjective
    (GraphContraction.collapseEdge G hab) p hp
    (GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
      G hab {z : V | z ∈ p.support} (by
        intro h
        exact hnot_both h))


end GraphContraction

end Schematic.Math.GraphTheory
