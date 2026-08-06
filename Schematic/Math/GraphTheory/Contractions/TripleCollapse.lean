import Schematic.Math.GraphTheory.Contractions.EdgeCollapse

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GraphContraction

/-- The subgraph induced by three vertices. -/
def inducedTripleSubgraph (G : SimpleGraph V) (a b c : V) : G.Subgraph :=
  (⊤ : G.Subgraph).induce ({a, b, c} : Set V)

@[simp]
theorem inducedTripleSubgraph_verts (G : SimpleGraph V) (a b c : V) :
    (inducedTripleSubgraph G a b c).verts = ({a, b, c} : Set V) :=
  rfl

theorem inducedTripleSubgraph_eq_of_set_eq
    (G : SimpleGraph V) {a b c x y z : V}
    (h : ({a, b, c} : Set V) = {x, y, z}) :
    inducedTripleSubgraph G a b c = inducedTripleSubgraph G x y z := by
  unfold inducedTripleSubgraph
  rw [h]

theorem inducedTripleSubgraph_swap_right
    (G : SimpleGraph V) (a b c : V) :
    inducedTripleSubgraph G a b c = inducedTripleSubgraph G a c b :=
  inducedTripleSubgraph_eq_of_set_eq G
    (congrArg (Set.insert a) (Set.pair_comm b c))

theorem connected_top_induce_triple_of_adj
    {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    (inducedTripleSubgraph G a b c).coe.Connected := by
  apply connected_top_induce_of_forall_eq_or_adj
    ({a, b, c} : Set V) (c := a) (by simp)
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hxa | hx
  · exact Or.inl hxa
  · rcases Set.mem_insert_iff.mp hx with hxb | hxc
    · subst x
      exact Or.inr hab
    · have hxc' : x = c := Set.mem_singleton_iff.mp hxc
      subst x
      exact Or.inr hac

theorem inducedTripleSubgraph_connected
    {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    (inducedTripleSubgraph G a b c).coe.Connected :=
  connected_top_induce_triple_of_adj (G := G) hab hac

/-- Contract the connected subgraph induced by a three-vertex star. -/
noncomputable def collapseTriple
    (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    GraphContraction G :=
  GraphContraction.collapseSubgraph G (inducedTripleSubgraph G a b c)
    (inducedTripleSubgraph_connected (G := G) hab hac)

noncomputable instance collapseTripleTargetFintype
    [Fintype V]
    (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    Fintype (GraphContraction.collapseTriple G hab hac).Target := by
  unfold GraphContraction.collapseTriple
  infer_instance

noncomputable instance collapseTripleTargetDecidableEq
    [DecidableEq V]
    (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    DecidableEq (GraphContraction.collapseTriple G hab hac).Target := by
  unfold GraphContraction.collapseTriple
  change DecidableEq
    (Option {v : V // v ∉ (inducedTripleSubgraph G a b c).verts})
  infer_instance

theorem collapseTriple_target_card_lt
    [Fintype V]
    (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    Fintype.card (GraphContraction.collapseTriple G hab hac).Target <
      Fintype.card V := by
  classical
  unfold GraphContraction.collapseTriple
  exact GraphContraction.collapseSubgraph_target_card_lt
    G (inducedTripleSubgraph G a b c)
      (connected_top_induce_triple_of_adj (G := G) hab hac)
      (a := a) (b := b) (by simp) (by simp) hab.ne

theorem collapseTriple_contracts_triple
    (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    (GraphContraction.collapseTriple G hab hac).ContractsConnectedSubgraph
      (inducedTripleSubgraph G a b c) := by
  unfold GraphContraction.collapseTriple
  exact GraphContraction.collapseSubgraph_contractsConnectedSubgraph
    G (inducedTripleSubgraph G a b c)
      (connected_top_induce_triple_of_adj (G := G) hab hac)

theorem collapseTriple_map_eq_iff
    (G : SimpleGraph V) {a b c v w : V}
    (hab : G.Adj a b)
    (hac : G.Adj a c) :
    (GraphContraction.collapseTriple G hab hac).map v =
        (GraphContraction.collapseTriple G hab hac).map w ↔
      (v ∈ ({a, b, c} : Set V) ∧ w ∈ ({a, b, c} : Set V)) ∨
        (v = w ∧ v ∉ ({a, b, c} : Set V) ∧
          w ∉ ({a, b, c} : Set V)) := by
  classical
  unfold GraphContraction.collapseTriple
  simpa using
    (GraphContraction.collapseSubgraph_map_eq_iff
      G (inducedTripleSubgraph G a b c)
      (connected_top_induce_triple_of_adj (G := G) hab hac)
      (v := v) (w := w))

end GraphContraction

end Schematic.Math.GraphTheory
