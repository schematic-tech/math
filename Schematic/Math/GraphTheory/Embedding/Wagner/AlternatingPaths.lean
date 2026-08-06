import Schematic.Math.GraphTheory.Embedding.Wagner.SubdivisionAssembly
import Schematic.Math.GraphTheory.Subdivisions.StandardGraphs

/-! The strict `K3,3` obstruction from four alternating paths. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner
def alternatingBranch
    {V : Type u} (x y x1 y1 x2 y2 : V) : K33Vertex -> V
  | Sum.inl 0 => x
  | Sum.inl 1 => y1
  | Sum.inl 2 => y2
  | Sum.inr 0 => y
  | Sum.inr 1 => x1
  | Sum.inr 2 => x2

noncomputable def alternatingEdgePath
    {V : Type u} {G : SimpleGraph V}
    {x y x1 y1 x2 y2 : V}
    (p11 : G.Walk x1 y1)
    (p12 : G.Walk y1 x2)
    (p22 : G.Walk x2 y2)
    (p21 : G.Walk y2 x1)
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    {i j : K33Vertex} (hij : K33Graph.Adj i j) :
    G.Walk
      (alternatingBranch x y x1 y1 x2 y2 i)
      (alternatingBranch x y x1 y1 x2 y2 j) :=
  match i, j with
  | Sum.inl _, Sum.inl _ => False.elim (by simp [K33Graph] at hij)
  | Sum.inr _, Sum.inr _ => False.elim (by simp [K33Graph] at hij)
  | Sum.inl 0, Sum.inr 0 => hxy.toWalk
  | Sum.inl 0, Sum.inr 1 => hxx1.toWalk
  | Sum.inl 0, Sum.inr 2 => hxx2.toWalk
  | Sum.inl 1, Sum.inr 0 => hyy1.symm.toWalk
  | Sum.inl 1, Sum.inr 1 => p11.reverse
  | Sum.inl 1, Sum.inr 2 => p12
  | Sum.inl 2, Sum.inr 0 => hyy2.symm.toWalk
  | Sum.inl 2, Sum.inr 1 => p21
  | Sum.inl 2, Sum.inr 2 => p22.reverse
  | Sum.inr 0, Sum.inl 0 => hxy.symm.toWalk
  | Sum.inr 0, Sum.inl 1 => hyy1.toWalk
  | Sum.inr 0, Sum.inl 2 => hyy2.toWalk
  | Sum.inr 1, Sum.inl 0 => hxx1.symm.toWalk
  | Sum.inr 1, Sum.inl 1 => p11
  | Sum.inr 1, Sum.inl 2 => p21.reverse
  | Sum.inr 2, Sum.inl 0 => hxx2.symm.toWalk
  | Sum.inr 2, Sum.inl 1 => p12.reverse
  | Sum.inr 2, Sum.inl 2 => p22

theorem alternatingEdgePath_isPath
    {V : Type u} {G : SimpleGraph V}
    {x y x1 y1 x2 y2 : V}
    {p11 : G.Walk x1 y1} {p12 : G.Walk y1 x2}
    {p22 : G.Walk x2 y2} {p21 : G.Walk y2 x1}
    (hp11 : p11.IsPath) (hp12 : p12.IsPath)
    (hp22 : p22.IsPath) (hp21 : p21.IsPath)
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    {i j : K33Vertex} (hij : K33Graph.Adj i j) :
    (alternatingEdgePath p11 p12 p22 p21
      hxy hxx1 hxx2 hyy1 hyy2 hij).IsPath := by
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j
  all_goals simp [K33Graph] at hij
  all_goals simp only [alternatingEdgePath]
  all_goals
    first
    | exact False.elim hij
    | exact SimpleGraph.Walk.IsPath.of_adj hxy
    | exact SimpleGraph.Walk.IsPath.of_adj hxy.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hxx1
    | exact SimpleGraph.Walk.IsPath.of_adj hxx1.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hxx2
    | exact SimpleGraph.Walk.IsPath.of_adj hxx2.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hyy1
    | exact SimpleGraph.Walk.IsPath.of_adj hyy1.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hyy2
    | exact SimpleGraph.Walk.IsPath.of_adj hyy2.symm
    | exact hp11
    | exact hp11.reverse
    | exact hp12
    | exact hp12.reverse
    | exact hp22
    | exact hp22.reverse
    | exact hp21
    | exact hp21.reverse

theorem alternatingEdgePath_internal_cases
    {V : Type u} {G : SimpleGraph V}
    {x y x1 y1 x2 y2 : V}
    (p11 : G.Walk x1 y1) (p12 : G.Walk y1 x2)
    (p22 : G.Walk x2 y2) (p21 : G.Walk y2 x1)
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    {i j : K33Vertex} (hij : K33Graph.Adj i j) {z : V}
    (hz : z ∈ Walk.InternalVertices
      (alternatingEdgePath p11 p12 p22 p21
        hxy hxx1 hxx2 hyy1 hyy2 hij)) :
    (((i = Sum.inl 1 ∧ j = Sum.inr 1) ∨
        (i = Sum.inr 1 ∧ j = Sum.inl 1)) ∧
      z ∈ Walk.InternalVertices p11) ∨
    (((i = Sum.inl 1 ∧ j = Sum.inr 2) ∨
        (i = Sum.inr 2 ∧ j = Sum.inl 1)) ∧
      z ∈ Walk.InternalVertices p12) ∨
    (((i = Sum.inl 2 ∧ j = Sum.inr 2) ∨
        (i = Sum.inr 2 ∧ j = Sum.inl 2)) ∧
      z ∈ Walk.InternalVertices p22) ∨
    (((i = Sum.inl 2 ∧ j = Sum.inr 1) ∨
        (i = Sum.inr 1 ∧ j = Sum.inl 2)) ∧
      z ∈ Walk.InternalVertices p21) := by
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j
  all_goals simp [K33Graph] at hij
  all_goals simp only [alternatingEdgePath] at hz
  all_goals
    first
    | exact False.elim hij
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxy
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxy.symm
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxx1
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxx1.symm
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxx2
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxx2.symm
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyy1
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyy1.symm
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyy2
          (by simpa [alternatingBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyy2.symm
          (by simpa [alternatingBranch] using hz))
    | exact Or.inl ⟨Or.inl ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff p11).mp
          (by simpa [alternatingBranch] using hz)⟩
    | exact Or.inl ⟨Or.inr ⟨rfl, rfl⟩,
        by simpa [alternatingBranch] using hz⟩
    | exact Or.inr (Or.inl ⟨Or.inl ⟨rfl, rfl⟩,
        by simpa [alternatingBranch] using hz⟩)
    | exact Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff p12).mp
          (by simpa [alternatingBranch] using hz)⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff p22).mp
          (by simpa [alternatingBranch] using hz)⟩))
    | exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩,
        by simpa [alternatingBranch] using hz⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨rfl, rfl⟩,
        by simpa [alternatingBranch] using hz⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff p21).mp
          (by simpa [alternatingBranch] using hz)⟩))

theorem containsStrictSubdivision_K33_of_alternating_paths
    {V : Type u} {G : SimpleGraph V}
    {x y x1 y1 x2 y2 : V}
    (p11 : G.Walk x1 y1) (p12 : G.Walk y1 x2)
    (p22 : G.Walk x2 y2) (p21 : G.Walk y2 x1)
    (hp11 : p11.IsPath) (hp12 : p12.IsPath)
    (hp22 : p22.IsPath) (hp21 : p21.IsPath)
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    (hbranch : Function.Injective (alternatingBranch x y x1 y1 x2 y2))
    (hno11 : forall {z}, z ∈ Walk.InternalVertices p11 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w)
    (hno12 : forall {z}, z ∈ Walk.InternalVertices p12 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w)
    (hno22 : forall {z}, z ∈ Walk.InternalVertices p22 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w)
    (hno21 : forall {z}, z ∈ Walk.InternalVertices p21 ->
      forall w, z ≠ alternatingBranch x y x1 y1 x2 y2 w)
    (hd11_12 : Disjoint (Walk.InternalVertices p11) (Walk.InternalVertices p12))
    (hd11_22 : Disjoint (Walk.InternalVertices p11) (Walk.InternalVertices p22))
    (hd11_21 : Disjoint (Walk.InternalVertices p11) (Walk.InternalVertices p21))
    (hd12_22 : Disjoint (Walk.InternalVertices p12) (Walk.InternalVertices p22))
    (hd12_21 : Disjoint (Walk.InternalVertices p12) (Walk.InternalVertices p21))
    (hd22_21 : Disjoint (Walk.InternalVertices p22) (Walk.InternalVertices p21)) :
    ContainsStrictSubdivision K33Graph G := by
  classical
  let f := alternatingBranch x y x1 y1 x2 y2
  let e : K33Vertex ↪ V := ⟨f, hbranch⟩
  let edgePath : forall {i j}, K33Graph.Adj i j -> G.Walk (e i) (e j) := by
    intro i j hij
    simpa [e, f] using
      alternatingEdgePath p11 p12 p22 p21 hxy hxx1 hxx2 hyy1 hyy2 hij
  refine containsStrictSubdivision_of_edgePaths e edgePath ?_ ?_ ?_
  · intro i j hij
    simpa [edgePath, e, f] using
      alternatingEdgePath_isPath hp11 hp12 hp22 hp21
        hxy hxx1 hxx2 hyy1 hyy2 hij
  ·
      intro i j hij z hz w
      have hcases := alternatingEdgePath_internal_cases
        p11 p12 p22 p21 hxy hxx1 hxx2 hyy1 hyy2 hij
        (z := z) (by simpa [edgePath, e, f] using hz)
      rcases hcases with h11 | h12 | h22 | h21
      · exact hno11 h11.2 w
      · exact hno12 h12.2 w
      · exact hno22 h22.2 w
      · exact hno21 h21.2 w
  ·
      intro i j i' j' hij hi'j' hne
      rw [Set.disjoint_left]
      intro z hz hz'
      have hcases := alternatingEdgePath_internal_cases
        p11 p12 p22 p21 hxy hxx1 hxx2 hyy1 hyy2 hij
        (z := z) (by simpa [edgePath, e, f] using hz)
      have hcases' := alternatingEdgePath_internal_cases
        p11 p12 p22 p21 hxy hxx1 hxx2 hyy1 hyy2 hi'j'
        (z := z) (by simpa [edgePath, e, f] using hz')
      rcases hcases with ⟨h11, hz11⟩ | ⟨h12, hz12⟩ |
          ⟨h22, hz22⟩ | ⟨h21, hz21⟩
      · rcases hcases' with ⟨h11', hz11'⟩ | ⟨h12', hz12'⟩ |
            ⟨h22', hz22'⟩ | ⟨h21', hz21'⟩
        · apply hne
          rcases h11 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h11' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        · exact Set.disjoint_left.mp hd11_12 hz11 hz12'
        · exact Set.disjoint_left.mp hd11_22 hz11 hz22'
        · exact Set.disjoint_left.mp hd11_21 hz11 hz21'
      · rcases hcases' with ⟨h11', hz11'⟩ | ⟨h12', hz12'⟩ |
            ⟨h22', hz22'⟩ | ⟨h21', hz21'⟩
        · exact Set.disjoint_left.mp hd11_12.symm hz12 hz11'
        · apply hne
          rcases h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h12' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        · exact Set.disjoint_left.mp hd12_22 hz12 hz22'
        · exact Set.disjoint_left.mp hd12_21 hz12 hz21'
      · rcases hcases' with ⟨h11', hz11'⟩ | ⟨h12', hz12'⟩ |
            ⟨h22', hz22'⟩ | ⟨h21', hz21'⟩
        · exact Set.disjoint_left.mp hd11_22.symm hz22 hz11'
        · exact Set.disjoint_left.mp hd12_22.symm hz22 hz12'
        · apply hne
          rcases h22 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h22' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        · exact Set.disjoint_left.mp hd22_21 hz22 hz21'
      · rcases hcases' with ⟨h11', hz11'⟩ | ⟨h12', hz12'⟩ |
            ⟨h22', hz22'⟩ | ⟨h21', hz21'⟩
        · exact Set.disjoint_left.mp hd11_21.symm hz21 hz11'
        · exact Set.disjoint_left.mp hd12_21.symm hz21 hz12'
        · exact Set.disjoint_left.mp hd22_21.symm hz21 hz22'
        · apply hne
          rcases h21 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases h21' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

end Wagner

end FourColor

end Schematic.Math.GraphTheory
