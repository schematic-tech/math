import Schematic.Math.GraphTheory.Embedding.Wagner.SubdivisionAssembly
import Schematic.Math.GraphTheory.PathsTrees.Foundations.Cycles
import Schematic.Math.GraphTheory.Subdivisions.StandardGraphs

/-! The strict `K5` obstruction from three common cycle attachments. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner
def threeJoinedBranch
    {V : Type u} (x y a b c : V) : Fin 5 -> V
  | 0 => x
  | 1 => y
  | 2 => a
  | 3 => b
  | 4 => c

noncomputable def threeJoinedEdgePath
    {V : Type u} {G : SimpleGraph V}
    {x y a b c : V}
    (pAB : G.Walk a b)
    (pAC : G.Walk a c)
    (pBC : G.Walk b c)
    (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    {i j : Fin 5} (hij : K5Graph.Adj i j) :
    G.Walk
      (threeJoinedBranch x y a b c i)
      (threeJoinedBranch x y a b c j) :=
  match i, j with
  | 0, 0 => False.elim (hij.ne rfl)
  | 0, 1 => hxy.toWalk
  | 0, 2 => hxa.toWalk
  | 0, 3 => hxb.toWalk
  | 0, 4 => hxc.toWalk
  | 1, 0 => hxy.symm.toWalk
  | 1, 1 => False.elim (hij.ne rfl)
  | 1, 2 => hya.toWalk
  | 1, 3 => hyb.toWalk
  | 1, 4 => hyc.toWalk
  | 2, 0 => hxa.symm.toWalk
  | 2, 1 => hya.symm.toWalk
  | 2, 2 => False.elim (hij.ne rfl)
  | 2, 3 => pAB
  | 2, 4 => pAC
  | 3, 0 => hxb.symm.toWalk
  | 3, 1 => hyb.symm.toWalk
  | 3, 2 => pAB.reverse
  | 3, 3 => False.elim (hij.ne rfl)
  | 3, 4 => pBC
  | 4, 0 => hxc.symm.toWalk
  | 4, 1 => hyc.symm.toWalk
  | 4, 2 => pAC.reverse
  | 4, 3 => pBC.reverse
  | 4, 4 => False.elim (hij.ne rfl)

theorem threeJoinedEdgePath_isPath
    {V : Type u} {G : SimpleGraph V}
    {x y a b c : V}
    {pAB : G.Walk a b} {pAC : G.Walk a c} {pBC : G.Walk b c}
    (hpAB : pAB.IsPath) (hpAC : pAC.IsPath) (hpBC : pBC.IsPath)
    (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    {i j : Fin 5} (hij : K5Graph.Adj i j) :
    (threeJoinedEdgePath pAB pAC pBC hxy hxa hxb hxc hya hyb hyc hij).IsPath := by
  fin_cases i <;> fin_cases j
  all_goals simp [K5Graph, CompleteGraphOn] at hij
  all_goals
    simp only [threeJoinedEdgePath]
    first
    | exact False.elim (hij rfl)
    | exact SimpleGraph.Walk.IsPath.of_adj hxy
    | exact SimpleGraph.Walk.IsPath.of_adj hxy.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hxa
    | exact SimpleGraph.Walk.IsPath.of_adj hxa.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hxb
    | exact SimpleGraph.Walk.IsPath.of_adj hxb.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hxc
    | exact SimpleGraph.Walk.IsPath.of_adj hxc.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hya
    | exact SimpleGraph.Walk.IsPath.of_adj hya.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hyb
    | exact SimpleGraph.Walk.IsPath.of_adj hyb.symm
    | exact SimpleGraph.Walk.IsPath.of_adj hyc
    | exact SimpleGraph.Walk.IsPath.of_adj hyc.symm
    | exact hpAB
    | exact hpAB.reverse
    | exact hpAC
    | exact hpAC.reverse
    | exact hpBC
    | exact hpBC.reverse

theorem threeJoinedEdgePath_internal_cases
    {V : Type u} {G : SimpleGraph V}
    {x y a b c : V}
    (pAB : G.Walk a b) (pAC : G.Walk a c) (pBC : G.Walk b c)
    (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    {i j : Fin 5} (hij : K5Graph.Adj i j) {z : V}
    (hz :
      z ∈ Walk.InternalVertices
        (threeJoinedEdgePath pAB pAC pBC hxy hxa hxb hxc hya hyb hyc hij)) :
    ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) ∧
        z ∈ Walk.InternalVertices pAB ∨
      (((i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2)) ∧
        z ∈ Walk.InternalVertices pAC) ∨
      (((i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3)) ∧
        z ∈ Walk.InternalVertices pBC) := by
  fin_cases i <;> fin_cases j
  all_goals simp [K5Graph, CompleteGraphOn] at hij
  all_goals simp only [threeJoinedEdgePath] at hz
  all_goals
    first
    | exact False.elim (hij rfl)
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxy
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxy.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxa
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxa.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxb
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxb.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxc
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hxc.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hya
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hya.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyb
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyb.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyc
          (by simpa [threeJoinedBranch] using hz))
    | exact False.elim
        (Walk.not_mem_internalVertices_toWalk hyc.symm
          (by simpa [threeJoinedBranch] using hz))
    | exact Or.inl ⟨Or.inl ⟨rfl, rfl⟩,
        by simpa [threeJoinedBranch] using hz⟩
    | exact Or.inl ⟨Or.inr ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff pAB).mp
          (by simpa [threeJoinedBranch] using hz)⟩
    | exact Or.inr (Or.inl ⟨Or.inl ⟨rfl, rfl⟩,
        by simpa [threeJoinedBranch] using hz⟩)
    | exact Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff pAC).mp
          (by simpa [threeJoinedBranch] using hz)⟩)
    | exact Or.inr (Or.inr ⟨Or.inl ⟨rfl, rfl⟩,
        by simpa [threeJoinedBranch] using hz⟩)
    | exact Or.inr (Or.inr ⟨Or.inr ⟨rfl, rfl⟩,
        (Walk.mem_internalVertices_reverse_iff pBC).mp
          (by simpa [threeJoinedBranch] using hz)⟩)

theorem containsStrictSubdivision_K5_of_cycle_three_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {r x y a b c : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    ContainsStrictSubdivision K5Graph G := by
  classical
  rcases
      Walk.IsCycle.exists_avoiding_path_and_split_through
        (G := G) C hC ha hb hc hab hac.symm hbc.symm with
    ⟨pAB, pAC, pBC, hpAB, hpAC, hpBC,
      hpAB_support, hpAC_support, hpBC_support,
      hc_not_pAB, hb_not_pAC, ha_not_pBC,
      hAB_AC, hAB_BC, hAC_BC⟩
  let f : Fin 5 -> V := threeJoinedBranch x y a b c
  have hf_inj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, threeJoinedBranch] at hij ⊢
    all_goals
      first
      | rfl
      | exact False.elim (hxy.ne hij)
      | exact False.elim (hxy.ne hij.symm)
      | exact False.elim (hxa.ne hij)
      | exact False.elim (hxa.ne hij.symm)
      | exact False.elim (hxb.ne hij)
      | exact False.elim (hxb.ne hij.symm)
      | exact False.elim (hxc.ne hij)
      | exact False.elim (hxc.ne hij.symm)
      | exact False.elim (hya.ne hij)
      | exact False.elim (hya.ne hij.symm)
      | exact False.elim (hyb.ne hij)
      | exact False.elim (hyb.ne hij.symm)
      | exact False.elim (hyc.ne hij)
      | exact False.elim (hyc.ne hij.symm)
      | exact False.elim (hab hij)
      | exact False.elim (hab hij.symm)
      | exact False.elim (hac hij)
      | exact False.elim (hac hij.symm)
      | exact False.elim (hbc hij)
      | exact False.elim (hbc hij.symm)
  let e : Fin 5 ↪ V := ⟨f, hf_inj⟩
  let edgePath :
      forall {i j : Fin 5}, K5Graph.Adj i j ->
        G.Walk (e i) (e j) := by
    intro i j hij
    simpa [e, f] using
      threeJoinedEdgePath pAB pAC pBC hxy hxa hxb hxc hya hyb hyc hij
  have hpAB_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices pAB ->
        forall w : Fin 5, z ≠ e w := by
    intro z hz w
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using hpAB_support z hz.1)
    · intro hzy
      exact hyC (by simpa [hzy] using hpAB_support z hz.1)
    · exact hz.2.1
    · exact hz.2.2
    · intro hzc
      exact hc_not_pAB (by simpa [hzc] using hz.1)
  have hpAC_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices pAC ->
        forall w : Fin 5, z ≠ e w := by
    intro z hz w
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using hpAC_support z hz.1)
    · intro hzy
      exact hyC (by simpa [hzy] using hpAC_support z hz.1)
    · exact hz.2.1
    · intro hzb
      exact hb_not_pAC (by simpa [hzb] using hz.1)
    · exact hz.2.2
  have hpBC_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices pBC ->
        forall w : Fin 5, z ≠ e w := by
    intro z hz w
    fin_cases w
    · intro hzx
      exact hxC (by simpa [hzx] using hpBC_support z hz.1)
    · intro hzy
      exact hyC (by simpa [hzy] using hpBC_support z hz.1)
    · intro hza
      exact ha_not_pBC (by simpa [hza] using hz.1)
    · exact hz.2.1
    · exact hz.2.2
  refine containsStrictSubdivision_of_edgePaths e edgePath ?_ ?_ ?_
  · intro i j hij
    simpa [edgePath, e, f] using
      threeJoinedEdgePath_isPath hpAB hpAC hpBC
        hxy hxa hxb hxc hya hyb hyc hij
  ·
      intro i j hij z hz w
      have hcases :=
        threeJoinedEdgePath_internal_cases
          pAB pAC pBC hxy hxa hxb hxc hya hyb hyc hij
          (z := z) (by simpa [edgePath, e, f] using hz)
      rcases hcases with hAB | hAC | hBC
      · exact hpAB_no_branch hAB.2 w
      · exact hpAC_no_branch hAC.2 w
      · exact hpBC_no_branch hBC.2 w
  ·
      intro i j i' j' hij hi'j' hne
      rw [Set.disjoint_left]
      intro z hz hz'
      have hcases :=
        threeJoinedEdgePath_internal_cases
          pAB pAC pBC hxy hxa hxb hxc hya hyb hyc hij
          (z := z) (by simpa [edgePath, e, f] using hz)
      have hcases' :=
        threeJoinedEdgePath_internal_cases
          pAB pAC pBC hxy hxa hxb hxc hya hyb hyc hi'j'
          (z := z) (by simpa [edgePath, e, f] using hz')
      rcases hcases with ⟨hABij, hzAB⟩ |
          ⟨hACij, hzAC⟩ | ⟨hBCij, hzBC⟩ <;>
        rcases hcases' with ⟨hABi'j', hzAB'⟩ |
          ⟨hACi'j', hzAC'⟩ | ⟨hBCi'j', hzBC'⟩
      · apply hne
        rcases hABij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hABi'j' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · exact Set.disjoint_left.mp hAB_AC hzAB hzAC'
      · exact Set.disjoint_left.mp hAB_BC hzAB hzBC'
      · exact Set.disjoint_left.mp hAB_AC.symm hzAC hzAB'
      · apply hne
        rcases hACij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hACi'j' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      · exact Set.disjoint_left.mp hAC_BC hzAC hzBC'
      · exact Set.disjoint_left.mp hAB_BC.symm hzBC hzAB'
      · exact Set.disjoint_left.mp hAC_BC.symm hzBC hzAC'
      · apply hne
        rcases hBCij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hBCi'j' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp


end Wagner

end FourColor

end Schematic.Math.GraphTheory
