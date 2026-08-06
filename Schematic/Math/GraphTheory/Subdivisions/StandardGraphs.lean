import Schematic.Math.GraphTheory.Subdivisions.MinorModels

/-! Standard complete, bipartite, and theta obstruction graphs. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

abbrev CompleteGraphOn (n : Nat) : SimpleGraph (Fin n) :=
  SimpleGraph.completeGraph (Fin n)

abbrev K4Graph : SimpleGraph (Fin 4) :=
  CompleteGraphOn 4

abbrev K5Graph : SimpleGraph (Fin 5) :=
  CompleteGraphOn 5

abbrev K33Vertex : Type :=
  Fin 3 ⊕ Fin 3

abbrev K23Vertex : Type :=
  Fin 2 ⊕ Fin 3

abbrev EdgeThetaVertex : Type :=
  Fin 2 ⊕ Fin 2

theorem card_K33Vertex : Fintype.card K33Vertex = 6 := by
  simp [K33Vertex]

theorem card_K23Vertex : Fintype.card K23Vertex = 5 := by
  simp [K23Vertex]

theorem card_EdgeThetaVertex : Fintype.card EdgeThetaVertex = 4 := by
  simp [EdgeThetaVertex]

theorem card_K5HatVertex : Fintype.card (Fin 6) = 6 := by
  simp

def K33Graph : SimpleGraph K33Vertex where
  Adj
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    rintro (i | i) (j | j) h <;> simp_all
  loopless := ⟨by
    rintro (i | i) h <;> simp_all⟩

def K23Graph : SimpleGraph K23Vertex where
  Adj
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    rintro (i | i) (j | j) h <;> simp_all
  loopless := ⟨by
    rintro (i | i) h <;> simp_all⟩

def EdgeThetaGraph : SimpleGraph EdgeThetaVertex where
  Adj
    | Sum.inl i, Sum.inl j => i ≠ j
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (i | i) (j | j) h <;> simp_all [ne_comm]
  loopless := ⟨by
    rintro (i | i) h <;> simp_all⟩

abbrev ContainsThetaSubdivision {V : Type v} (G : SimpleGraph V) : Prop :=
  ContainsStrictSubdivision K23Graph G

abbrev ContainsEdgeThetaSubdivision {V : Type v} (G : SimpleGraph V) : Prop :=
  ContainsStrictSubdivision EdgeThetaGraph G

/-- A theta homeomorph in which one of the three internally disjoint branches
between the two degree-three ends is the direct edge `x--y`, and the other two
branches have one internal vertex each.  This complements
`ContainsThetaSubdivision K23Graph`: source texts often call this graph a
theta as well, since it is homeomorphic to `K_{2,3}` after suppressing one
degree-two vertex. -/
def ContainsEdgeTheta {V : Type v} (G : SimpleGraph V) : Prop :=
  Exists fun x : V =>
    Exists fun y : V =>
      Exists fun u : V =>
        Exists fun v : V =>
          G.Adj x y ∧ G.Adj x u ∧ G.Adj y u ∧
            G.Adj x v ∧ G.Adj y v ∧ u ≠ v

end Schematic.Math.GraphTheory
