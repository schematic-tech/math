import Schematic.Math.GraphTheory.Contractions.SubgraphCollapse

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GraphContraction

variable {G : SimpleGraph V}

/-- The subgraph induced by two vertices.  Naming this ubiquitous subgraph
keeps dependent contraction types from repeating its construction. -/
def inducedPairSubgraph (G : SimpleGraph V) (a b : V) : G.Subgraph :=
  (⊤ : G.Subgraph).induce ({a, b} : Set V)

@[simp]
theorem inducedPairSubgraph_verts (G : SimpleGraph V) (a b : V) :
    (inducedPairSubgraph G a b).verts = ({a, b} : Set V) :=
  rfl

theorem inducedPairSubgraph_comm (G : SimpleGraph V) (a b : V) :
    inducedPairSubgraph G a b = inducedPairSubgraph G b a := by
  unfold inducedPairSubgraph
  rw [Set.pair_comm]

theorem connected_top_induce_pair_of_adj
    {a b : V}
    (hab : G.Adj a b) :
    (inducedPairSubgraph G a b).coe.Connected := by
  apply connected_top_induce_of_forall_eq_or_adj
    ({a, b} : Set V) (c := a) (by simp)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hxa | hxb
  · exact Or.inl hxa
  · have hxb' : x = b := Set.mem_singleton_iff.mp hxb
    subst x
    exact Or.inr hab

theorem inducedPairSubgraph_connected
    {a b : V}
    (hab : G.Adj a b) :
    (inducedPairSubgraph G a b).coe.Connected :=
  connected_top_induce_pair_of_adj (G := G) hab

/-! Edge contraction.

This is the concrete simple-graph operation used in the Makarychev/Skopenkov
proof of Kuratowski's criterion: contract one edge, then suppress the loop and
parallel edges by passing through `contractionTargetGraph`. -/

noncomputable def collapseEdge
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    GraphContraction G :=
  GraphContraction.collapseSubgraph G
    (inducedPairSubgraph G a b)
    (inducedPairSubgraph_connected (G := G) hab)

noncomputable instance collapseEdgeTargetFintype
    [Fintype V]
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    Fintype (GraphContraction.collapseEdge G hab).Target := by
  unfold GraphContraction.collapseEdge
  infer_instance

noncomputable instance collapseEdgeTargetDecidableEq
    [DecidableEq V]
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    DecidableEq (GraphContraction.collapseEdge G hab).Target := by
  unfold GraphContraction.collapseEdge
  change DecidableEq
    (Option {v : V // v ∉ (inducedPairSubgraph G a b).verts})
  infer_instance

theorem collapseEdge_target_card_lt
    [Fintype V]
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    Fintype.card (GraphContraction.collapseEdge G hab).Target <
      Fintype.card V := by
  classical
  let H : G.Subgraph := inducedPairSubgraph G a b
  let hH : H.coe.Connected := connected_top_induce_pair_of_adj (G := G) hab
  change Fintype.card (GraphContraction.collapseSubgraph G H hH).Target <
    Fintype.card V
  letI := GraphContraction.collapseSubgraphTargetFintype G H hH
  exact GraphContraction.collapseSubgraph_target_card_lt
    G H hH
    (a := a) (b := b)
    (by
      change a ∈ ({a, b} : Set V)
      simp)
    (by
      change b ∈ ({a, b} : Set V)
      simp)
    hab.ne

theorem collapseEdge_contracts_pair
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    (GraphContraction.collapseEdge G hab).ContractsConnectedSubgraph
      (inducedPairSubgraph G a b) := by
  classical
  unfold GraphContraction.collapseEdge
  exact GraphContraction.collapseSubgraph_contractsConnectedSubgraph
    G (inducedPairSubgraph G a b)
    (connected_top_induce_pair_of_adj (G := G) hab)

theorem collapseEdge_map_eq_iff
    (G : SimpleGraph V) {a b v w : V}
    (hab : G.Adj a b) :
    (GraphContraction.collapseEdge G hab).map v =
        (GraphContraction.collapseEdge G hab).map w ↔
      (v ∈ ({a, b} : Set V) ∧ w ∈ ({a, b} : Set V)) ∨
        (v = w ∧ v ∉ ({a, b} : Set V) ∧
          w ∉ ({a, b} : Set V)) := by
  classical
  unfold GraphContraction.collapseEdge
  simpa using
    (GraphContraction.collapseSubgraph_map_eq_iff
      G (inducedPairSubgraph G a b)
      (connected_top_induce_pair_of_adj (G := G) hab)
      (v := v) (w := w))

theorem collapseEdge_map_injective_on_set_of_not_pair_both
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    (S : Set V)
    (hnot_both : ¬ (a ∈ S ∧ b ∈ S)) :
    forall x y : V, x ∈ S -> y ∈ S ->
      (GraphContraction.collapseEdge G hab).map x =
        (GraphContraction.collapseEdge G hab).map y ->
          x = y := by
  classical
  intro x y hxS hyS hxy
  rcases
      (GraphContraction.collapseEdge_map_eq_iff
        (G := G) hab (v := x) (w := y)).mp hxy with
    hpair | houtside
  · have hx_pair : x = a ∨ x = b := by
      simpa using hpair.1
    have hy_pair : y = a ∨ y = b := by
      simpa using hpair.2
    rcases hx_pair with rfl | rfl
    · rcases hy_pair with rfl | rfl
      · rfl
      · exact False.elim (hnot_both ⟨hxS, hyS⟩)
    · rcases hy_pair with rfl | rfl
      · exact False.elim (hnot_both ⟨hyS, hxS⟩)
      · rfl
  · exact houtside.1

/-- The graph with the left endpoint of a contracted edge deleted maps
injectively into the edge contraction. -/
noncomputable def collapseEdgeDeleteLeftHom
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    G.induce {z : V | z ≠ a} →g
      (GraphContraction.collapseEdge G hab).graph where
  toFun z := (GraphContraction.collapseEdge G hab).map (z : V)
  map_rel' := by
    intro x y hxy
    have hneq :
        (GraphContraction.collapseEdge G hab).map (x : V) ≠
          (GraphContraction.collapseEdge G hab).map (y : V) := by
      intro hsame
      have hval :
          (x : V) = (y : V) :=
        GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
          G hab {z : V | z ≠ a}
          (by simp)
          (x : V) (y : V) x.2 y.2 hsame
      exact hxy.ne (Subtype.ext hval)
    rcases (GraphContraction.collapseEdge G hab).map_adj hxy with hsame | hadj
    · exact False.elim (hneq hsame)
    · exact hadj

theorem collapseEdgeDeleteLeftHom_injective
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    Function.Injective (GraphContraction.collapseEdgeDeleteLeftHom G hab) := by
  classical
  intro x y hxy
  apply Subtype.ext
  exact
      GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
        G hab {z : V | z ≠ a}
      (by simp)
      (x : V) (y : V) x.2 y.2 hxy

/-- The graph with the right endpoint of a contracted edge deleted maps
injectively into the edge contraction. -/
noncomputable def collapseEdgeDeleteRightHom
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    G.induce {z : V | z ≠ b} →g
      (GraphContraction.collapseEdge G hab).graph where
  toFun z := (GraphContraction.collapseEdge G hab).map (z : V)
  map_rel' := by
    intro x y hxy
    have hneq :
        (GraphContraction.collapseEdge G hab).map (x : V) ≠
          (GraphContraction.collapseEdge G hab).map (y : V) := by
      intro hsame
      have hval :
          (x : V) = (y : V) :=
        GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
          G hab {z : V | z ≠ b}
          (by simp)
          (x : V) (y : V) x.2 y.2 hsame
      exact hxy.ne (Subtype.ext hval)
    rcases (GraphContraction.collapseEdge G hab).map_adj hxy with hsame | hadj
    · exact False.elim (hneq hsame)
    · exact hadj

theorem collapseEdgeDeleteRightHom_injective
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    Function.Injective (GraphContraction.collapseEdgeDeleteRightHom G hab) := by
  classical
  intro x y hxy
  apply Subtype.ext
  exact
      GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
        G hab {z : V | z ≠ b}
      (by simp)
      (x : V) (y : V) x.2 y.2 hxy

/-- The quotient target corresponding to a vertex outside the contracted edge.
This keeps later statements about `collapseEdge` from exposing the internal
`collapseSubgraph` subtype. -/
def collapseEdgeOutside
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    (v : V)
    (hv : v ∉ ({a, b} : Set V)) :
    (GraphContraction.collapseEdge G hab).Target := by
  classical
  unfold GraphContraction.collapseEdge
  exact some
    (⟨v, by
      exact hv⟩ :
      {v : V // v ∉ ((⊤ : G.Subgraph).induce ({a, b} : Set V)).verts})

/-- Interpret a non-collapsed vertex of an edge contraction as the
corresponding original source vertex. -/
noncomputable def collapseEdgeUncollapse
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    (y : (GraphContraction.collapseEdge G hab).Target)
    (hy : y ≠ none) : V := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  let y' : (GraphContraction.collapseSubgraph G H hH).Target := y
  have hy' : y' ≠ none := by
    intro h
    exact hy (by simpa [y', GraphContraction.collapseEdge, H, hH] using h)
  exact GraphContraction.collapseSubgraphOutsideEmbedding G H hH ⟨y', hy'⟩

@[simp]
theorem collapseEdgeUncollapse_outside
    (G : SimpleGraph V) {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hy :
      GraphContraction.collapseEdgeOutside G hab v hv ≠
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    GraphContraction.collapseEdgeUncollapse G hab
        (GraphContraction.collapseEdgeOutside G hab v hv) hy = v := by
  rfl

theorem collapseEdgeUncollapse_congr
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (h : y = z) :
    GraphContraction.collapseEdgeUncollapse G hab y hy =
      GraphContraction.collapseEdgeUncollapse G hab z hz := by
  subst z
  congr

theorem collapseEdgeUncollapse_injective
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (h :
      GraphContraction.collapseEdgeUncollapse G hab y hy =
        GraphContraction.collapseEdgeUncollapse G hab z hz) :
    y = z := by
  classical
  cases y with
  | none => exact False.elim (hy rfl)
  | some yv =>
      cases z with
      | none => exact False.elim (hz rfl)
      | some zv =>
          apply congrArg some
          apply Subtype.ext
          simpa [GraphContraction.collapseEdgeUncollapse] using h

theorem collapseEdgeUncollapse_not_mem_pair
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none) :
    GraphContraction.collapseEdgeUncollapse G hab y hy ∉ ({a, b} : Set V) := by
  classical
  cases y with
  | none => exact False.elim (hy rfl)
  | some yv =>
      simpa [GraphContraction.collapseEdgeUncollapse] using yv.2

/-- Away from the collapsed endpoint, `collapseEdge` is exactly the original
graph.  This is the formal version of the reference identity
`G - a - b = (G / ab) - [ab]` used before the face-boundary argument. -/
theorem collapseEdge_graph_adj_outside_iff
    (G : SimpleGraph V) {a b v w : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hw : w ∉ ({a, b} : Set V)) :
    (GraphContraction.collapseEdge G hab).graph.Adj
        (GraphContraction.collapseEdgeOutside G hab v hv)
        (GraphContraction.collapseEdgeOutside G hab w hw) ↔
      G.Adj v w := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  have hvH : v ∉ H.verts := by
    change v ∉ ({a, b} : Set V)
    exact hv
  have hwH : w ∉ H.verts := by
    change w ∉ ({a, b} : Set V)
    exact hw
  change
    (GraphContraction.collapseSubgraph G H hH).graph.Adj
        (some (⟨v, hvH⟩ : {x : V // x ∉ H.verts}))
        (some (⟨w, hwH⟩ : {x : V // x ∉ H.verts})) ↔
      G.Adj v w
  simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap,
    contractionTargetGraph]
  constructor
  · intro h
    exact h.2.2.2
  · intro hvw
    exact ⟨hvw.ne, hvH, hwH, hvw⟩

/-- The outside of an edge contraction is isomorphic to deleting the two
contracted endpoints. -/
noncomputable def collapseEdgeOutsideIso
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    G.induce (({a, b} : Set V)ᶜ) ≃g
      (GraphContraction.collapseEdge G hab).graph.induce
        {y : (GraphContraction.collapseEdge G hab).Target |
          y ≠ (none : (GraphContraction.collapseEdge G hab).Target)} where
  toFun x :=
    ⟨GraphContraction.collapseEdgeOutside G hab x.1 x.2, by
        simp [GraphContraction.collapseEdgeOutside]⟩
  invFun y :=
    ⟨GraphContraction.collapseEdgeUncollapse G hab y.1 y.2, by
      exact GraphContraction.collapseEdgeUncollapse_not_mem_pair
        G hab y.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have hx :
        (x : V) ∉ ({a, b} : Set V) := by
      exact x.2
    have hne :
        GraphContraction.collapseEdgeOutside G hab (x : V) hx ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      simp [GraphContraction.collapseEdgeOutside]
    change
      GraphContraction.collapseEdgeUncollapse G hab
        (GraphContraction.collapseEdgeOutside G hab (x : V) hx) hne =
        (x : V)
    exact
      GraphContraction.collapseEdgeUncollapse_outside
        G hab hx hne
  right_inv := by
    intro y
    apply Subtype.ext
    cases y with
    | mk y hy =>
        cases y with
        | none => exact False.elim (hy rfl)
        | some yv =>
            cases yv
            rfl
  map_rel_iff' := by
    intro x y
    exact
      GraphContraction.collapseEdge_graph_adj_outside_iff
        (G := G) hab
        x.2 y.2

/-- Edge-contraction version of the clean outside-walk lift with arbitrary
non-collapsed quotient endpoints. -/
noncomputable def collapseEdgeWalkOutside
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseEdge G hab).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    G.Walk
      (GraphContraction.collapseEdgeUncollapse G hab y hy)
      (GraphContraction.collapseEdgeUncollapse G hab z hz) := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  let y' : (GraphContraction.collapseSubgraph G H hH).Target := y
  let z' : (GraphContraction.collapseSubgraph G H hH).Target := z
  have hy' : y' ≠ none := by
    intro h
    exact hy (by simpa [y', GraphContraction.collapseEdge, H, hH] using h)
  have hz' : z' ≠ none := by
    intro h
    exact hz (by simpa [z', GraphContraction.collapseEdge, H, hH] using h)
  let p' : (GraphContraction.collapseSubgraph G H hH).graph.Walk y' z' := by
    simpa [y', z', GraphContraction.collapseEdge, H, hH] using p
  have hpavoid' : forall t, t ∈ p'.support ->
      t ≠ (none : (GraphContraction.collapseSubgraph G H hH).Target) := by
    intro t ht htnone
    exact
      hpavoid t
        (by
          simpa [p', y', z', GraphContraction.collapseEdge, H, hH] using ht)
        (by
          simpa [GraphContraction.collapseEdge, H, hH] using htnone)
  exact GraphContraction.collapseSubgraphOutsideWalk G H hH hy' hz' p' hpavoid'

theorem collapseEdgeWalkOutside_isPath
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseEdge G hab).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hp : p.IsPath) :
    (GraphContraction.collapseEdgeWalkOutside G hab hy hz p hpavoid).IsPath := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  let y' : (GraphContraction.collapseSubgraph G H hH).Target := y
  let z' : (GraphContraction.collapseSubgraph G H hH).Target := z
  have hy' : y' ≠ none := by
    intro h
    exact hy (by simpa [y', GraphContraction.collapseEdge, H, hH] using h)
  have hz' : z' ≠ none := by
    intro h
    exact hz (by simpa [z', GraphContraction.collapseEdge, H, hH] using h)
  let p' : (GraphContraction.collapseSubgraph G H hH).graph.Walk y' z' := by
    simpa [y', z', GraphContraction.collapseEdge, H, hH] using p
  have hpavoid' : forall t, t ∈ p'.support ->
      t ≠ (none : (GraphContraction.collapseSubgraph G H hH).Target) := by
    intro t ht htnone
    exact
      hpavoid t
        (by
          simpa [p', y', z', GraphContraction.collapseEdge, H, hH] using ht)
        (by
          simpa [GraphContraction.collapseEdge, H, hH] using htnone)
  have hp' : p'.IsPath := by
    simpa [p', y', z', GraphContraction.collapseEdge, H, hH] using hp
  have hq :=
    GraphContraction.collapseSubgraphOutsideWalk_isPath G H hH hy' hz' p'
      hpavoid' hp'
  simpa [GraphContraction.collapseEdgeWalkOutside, H, hH, y', z', p', hy',
    hz', hpavoid'] using hq

theorem collapseEdgeWalkOutside_support_outside
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseEdge G hab).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {t : V}
    (ht :
      t ∈
        (GraphContraction.collapseEdgeWalkOutside G hab hy hz p hpavoid).support) :
    t ∉ ({a, b} : Set V) := by
  classical
  simp [GraphContraction.collapseEdgeWalkOutside,
    GraphContraction.collapseEdgeUncollapse,
    GraphContraction.collapseSubgraphOutsideWalk,
    GraphContraction.collapseSubgraphOutsideEmbedding,
    SimpleGraph.Walk.support_map] at ht
  rcases ht with ⟨qv, _hqv, _hqv_mem, hqv_eq⟩
  subst t
  cases qv with
  | none => contradiction
  | some qv =>
      exact qv.2

theorem collapseEdgeWalkOutside_support_reflects
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseEdge G hab).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {t : V}
    (ht :
      t ∈
        (GraphContraction.collapseEdgeWalkOutside
          G hab hy hz p hpavoid).support) :
    Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
      Exists fun _ : qv ∈ p.support =>
        Exists fun hqv_ne : qv ≠ none =>
          GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = t := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  let y' : (GraphContraction.collapseSubgraph G H hH).Target := y
  let z' : (GraphContraction.collapseSubgraph G H hH).Target := z
  have hy' : y' ≠ none := by
    intro h
    exact hy (by simpa [y', GraphContraction.collapseEdge, H, hH] using h)
  have hz' : z' ≠ none := by
    intro h
    exact hz (by simpa [z', GraphContraction.collapseEdge, H, hH] using h)
  let p' : (GraphContraction.collapseSubgraph G H hH).graph.Walk y' z' := by
    simpa [y', z', GraphContraction.collapseEdge, H, hH] using p
  have hpavoid' : forall t, t ∈ p'.support ->
      t ≠ (none : (GraphContraction.collapseSubgraph G H hH).Target) := by
    intro qv hqv hnone
    exact
      hpavoid qv
        (by
          simpa [p', y', z', GraphContraction.collapseEdge, H, hH] using hqv)
        (by simpa [GraphContraction.collapseEdge, H, hH] using hnone)
  have ht' :
      t ∈
        (GraphContraction.collapseSubgraphOutsideWalk
          G H hH hy' hz' p' hpavoid').support := by
    simpa [GraphContraction.collapseEdgeWalkOutside, H, hH, y', z', p',
      hy', hz', hpavoid'] using ht
  rcases
      GraphContraction.collapseSubgraphOutsideWalk_support_reflects
        G H hH hy' hz' p' hpavoid' ht' with
    ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  refine ⟨qv, ?_, ?_, ?_⟩
  · simpa [p', y', z', GraphContraction.collapseEdge, H, hH] using hqv_mem
  · intro hnone
    exact hqv_ne (by simpa [GraphContraction.collapseEdge, H, hH] using hnone)
  · simpa [GraphContraction.collapseEdgeUncollapse, H, hH, y'] using hqv_eq

/-- Edges from the collapsed quotient vertex are exactly edges from one of the
two original endpoints of the contracted edge. -/
theorem collapseEdge_adj_none_outside_iff
    (G : SimpleGraph V) {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V)) :
    (GraphContraction.collapseEdge G hab).graph.Adj
        (none : (GraphContraction.collapseEdge G hab).Target)
        (GraphContraction.collapseEdgeOutside G hab v hv) ↔
      G.Adj a v ∨ G.Adj b v := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected := GraphContraction.connected_top_induce_pair_of_adj
    (G := G) hab
  have hvH : v ∉ H.verts := by
    change v ∉ ({a, b} : Set V)
    exact hv
  change
    (GraphContraction.collapseSubgraph G H hH).graph.Adj none
        (some (⟨v, hvH⟩ : {v : V // v ∉ H.verts})) ↔
      G.Adj a v ∨ G.Adj b v
  constructor
  · intro h
    rcases h with ⟨_hne, x, y, hx, hy, hxy⟩
    have hxH : x ∈ H.verts := by
      by_contra hxH
      simp [hxH] at hx
    have hy_eq : y = v := by
      by_cases hyH : y ∈ H.verts
      · simp [hyH] at hy
      · have hsome :
            some (⟨y, hyH⟩ : {v : V // v ∉ H.verts}) =
              some ⟨v, hvH⟩ := by
          simpa [GraphContraction.collapseSubgraph,
            GraphContraction.ofMap, hyH] using hy
        exact congrArg Subtype.val (Option.some.inj hsome)
    have hx_pair : x = a ∨ x = b := by
      change x ∈ ({a, b} : Set V) at hxH
      simpa using hxH
    rcases hx_pair with rfl | rfl
    · exact Or.inl (by simpa [hy_eq] using hxy)
    · exact Or.inr (by simpa [hy_eq] using hxy)
  · intro h
    rcases h with hav | hbv
    · refine ⟨by simp, a, v, ?_, ?_, hav⟩
      · exact GraphContraction.collapseSubgraph_map_eq_none_of_mem
          G H hH (by
            change a ∈ ({a, b} : Set V)
            simp)
      · exact GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
          G H hH hvH
    · refine ⟨by simp, b, v, ?_, ?_, hbv⟩
      · exact GraphContraction.collapseSubgraph_map_eq_none_of_mem
          G H hH (by
            change b ∈ ({a, b} : Set V)
            simp)
      · exact GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
          G H hH hvH

/-- First-step decoder for quotient walks starting at the collapsed vertex:
the second vertex of any nontrivial walk from the collapsed vertex is an
outside vertex adjacent in the original graph to one of the contracted
endpoints. -/
theorem collapseEdge_walk_first_step_side
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y : (GraphContraction.collapseEdge G hab).Target}
    (p : (GraphContraction.collapseEdge G hab).graph.Walk
      (none : (GraphContraction.collapseEdge G hab).Target) y)
    (hy : y ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        p.snd = GraphContraction.collapseEdgeOutside G hab v hv ∧
          (G.Adj a v ∨ G.Adj b v) := by
  classical
  have hp_not_nil : ¬ p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) (by
      intro h
      exact hy h.symm)
  have hadj_snd : (GraphContraction.collapseEdge G hab).graph.Adj
      (none : (GraphContraction.collapseEdge G hab).Target) p.snd :=
    p.adj_snd hp_not_nil
  cases hsnd : (p.snd : (GraphContraction.collapseEdge G hab).Target) with
  | none =>
      rw [hsnd] at hadj_snd
      exact False.elim
        ((GraphContraction.collapseEdge G hab).graph.loopless.irrefl _
          hadj_snd)
  | some v =>
      have hv : (v : V) ∉ ({a, b} : Set V) := v.2
      have hside : G.Adj a (v : V) ∨ G.Adj b (v : V) := by
        have hadj_out : (GraphContraction.collapseEdge G hab).graph.Adj
            (none : (GraphContraction.collapseEdge G hab).Target)
            (GraphContraction.collapseEdgeOutside G hab (v : V) hv) := by
          rw [hsnd] at hadj_snd
          simpa [GraphContraction.collapseEdgeOutside] using hadj_snd
        exact
          (GraphContraction.collapseEdge_adj_none_outside_iff
            G hab hv).mp hadj_out
      refine ⟨v, hv, ?_, hside⟩
      simp [GraphContraction.collapseEdgeOutside]

/-- Edge-contraction specialization of `collapseSubgraphOutsideWalk`: a
quotient walk between outside vertices whose support avoids the collapsed
vertex is an original walk between the corresponding source vertices. -/
noncomputable def collapseEdgeOutsideWalk
    (G : SimpleGraph V) {a b v w : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hw : w ∉ ({a, b} : Set V))
    (p : (GraphContraction.collapseEdge G hab).graph.Walk
          (GraphContraction.collapseEdgeOutside G hab v hv)
          (GraphContraction.collapseEdgeOutside G hab w hw))
    (hpavoid : forall t, t ∈ p.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    G.Walk v w := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  let y : (GraphContraction.collapseSubgraph G H hH).Target :=
    GraphContraction.collapseEdgeOutside G hab v hv
  let z : (GraphContraction.collapseSubgraph G H hH).Target :=
    GraphContraction.collapseEdgeOutside G hab w hw
  have hy : y ≠ none := by
    simp [y, GraphContraction.collapseEdgeOutside, H]
  have hz : z ≠ none := by
    simp [z, GraphContraction.collapseEdgeOutside, H]
  let p' : (GraphContraction.collapseSubgraph G H hH).graph.Walk y z := by
    simpa [y, z, GraphContraction.collapseEdge, H, hH] using p
  have hpavoid' : forall t, t ∈ p'.support ->
      t ≠ (none : (GraphContraction.collapseSubgraph G H hH).Target) := by
    intro t ht htnone
    exact
      hpavoid t
        (by
          simpa [p', y, z, GraphContraction.collapseEdge, H, hH] using ht)
        (by
          simpa [GraphContraction.collapseEdge, H, hH] using htnone)
  let q := GraphContraction.collapseSubgraphOutsideWalk G H hH hy hz p' hpavoid'
  exact q.copy (by rfl) (by rfl)

theorem collapseEdgeOutsideWalk_isPath
    (G : SimpleGraph V) {a b v w : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hw : w ∉ ({a, b} : Set V))
    (p : (GraphContraction.collapseEdge G hab).graph.Walk
          (GraphContraction.collapseEdgeOutside G hab v hv)
          (GraphContraction.collapseEdgeOutside G hab w hw))
    (hpavoid : forall t, t ∈ p.support ->
      t ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hp : p.IsPath) :
    (GraphContraction.collapseEdgeOutsideWalk G hab hv hw p hpavoid).IsPath := by
  classical
  let H : G.Subgraph := (⊤ : G.Subgraph).induce ({a, b} : Set V)
  let hH : H.coe.Connected :=
    GraphContraction.connected_top_induce_pair_of_adj (G := G) hab
  let y : (GraphContraction.collapseSubgraph G H hH).Target :=
    GraphContraction.collapseEdgeOutside G hab v hv
  let z : (GraphContraction.collapseSubgraph G H hH).Target :=
    GraphContraction.collapseEdgeOutside G hab w hw
  have hy : y ≠ none := by
    simp [y, GraphContraction.collapseEdgeOutside, H]
  have hz : z ≠ none := by
    simp [z, GraphContraction.collapseEdgeOutside, H]
  let p' : (GraphContraction.collapseSubgraph G H hH).graph.Walk y z := by
    simpa [y, z, GraphContraction.collapseEdge, H, hH] using p
  have hpavoid' : forall t, t ∈ p'.support ->
      t ≠ (none : (GraphContraction.collapseSubgraph G H hH).Target) := by
    intro t ht htnone
    exact
      hpavoid t
        (by
          simpa [p', y, z, GraphContraction.collapseEdge, H, hH] using ht)
        (by
          simpa [GraphContraction.collapseEdge, H, hH] using htnone)
  have hp' : p'.IsPath := by
    simpa [p', y, z, GraphContraction.collapseEdge, H, hH] using hp
  have hq :=
    GraphContraction.collapseSubgraphOutsideWalk_isPath G H hH hy hz p'
      hpavoid' hp'
  simpa [GraphContraction.collapseEdgeOutsideWalk, H, hH, y, z, p', hy, hz,
    hpavoid'] using hq


end GraphContraction

end Schematic.Math.GraphTheory
