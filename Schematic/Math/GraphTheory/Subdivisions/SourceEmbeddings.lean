import Schematic.Math.GraphTheory.Subdivisions.CycleAttachments

/-! Embeddings and finite combinatorics of the standard source graphs. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem K23Graph_exists_adj (x : K23Vertex) :
    Exists fun y : K23Vertex => K23Graph.Adj x y := by
  rcases x with i | j
  · exact ⟨Sum.inr 0, by simp [K23Graph]⟩
  · exact ⟨Sum.inl 0, by simp [K23Graph]⟩

def K23Graph.toK33Embedding : K23Vertex ↪ K33Vertex where
  toFun
    | Sum.inl i => Sum.inl ⟨i, by
        have hi : (i : Nat) < 2 := i.isLt
        omega⟩
    | Sum.inr j => Sum.inr j
  inj' := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j
    · simp at hxy ⊢
      exact Fin.ext hxy
    · simp at hxy
    · simp at hxy
    · simp at hxy ⊢
      exact hxy

theorem K23Graph.toK33Embedding_adj
    {x y : K23Vertex}
    (hxy : K23Graph.Adj x y) :
    K33Graph.Adj (K23Graph.toK33Embedding x)
      (K23Graph.toK33Embedding y) := by
  rcases x with i | i <;> rcases y with j | j <;>
    simp [K23Graph, K33Graph, K23Graph.toK33Embedding] at hxy ⊢

def K23Graph.toK5Embedding : K23Vertex ↪ Fin 5 where
  toFun
    | Sum.inl 0 => 0
    | Sum.inl 1 => 1
    | Sum.inr 0 => 2
    | Sum.inr 1 => 3
    | Sum.inr 2 => 4
  inj' := by
    intro x y hxy
    rcases x with i | i <;> rcases y with j | j <;>
      fin_cases i <;> fin_cases j <;> simp at hxy ⊢

theorem K23Graph.toK5Embedding_adj
    {x y : K23Vertex}
    (hxy : K23Graph.Adj x y) :
    K5Graph.Adj (K23Graph.toK5Embedding x)
      (K23Graph.toK5Embedding y) := by
  rcases x with i | i <;> rcases y with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [K23Graph, K5Graph, CompleteGraphOn] at hxy ⊢

theorem K5Graph_exists_adj (x : Fin 5) :
    Exists fun y : Fin 5 => K5Graph.Adj x y := by
  by_cases hx : x = 0
  · exact ⟨1, by simp [K5Graph, CompleteGraphOn, hx]⟩
  · exact ⟨0, by simp [K5Graph, CompleteGraphOn, hx]⟩

theorem K5Graph.adj_of_ne {x y : Fin 5} (hxy : x ≠ y) :
    K5Graph.Adj x y := by
  simpa [K5Graph, CompleteGraphOn] using hxy

theorem K5Graph.exists_vertex_not_four (a b c d : Fin 5) :
    Exists fun z : Fin 5 => z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> decide

theorem K5Graph.exists_two_vertices_not_three (a b c : Fin 5) :
    Exists fun d : Fin 5 =>
      Exists fun e : Fin 5 =>
        d ≠ e ∧
          d ≠ a ∧ d ≠ b ∧ d ≠ c ∧
            e ≠ a ∧ e ≠ b ∧ e ≠ c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

end Schematic.Math.GraphTheory
