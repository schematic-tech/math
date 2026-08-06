import Schematic.Math.GraphTheory.Connectivity.Separations
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
Degree structure of finite trees and acyclic graphs.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem degree_le_two_of_mem_component_ncard_le_three
    [Fintype V] [DecidableRel G.Adj]
    (C : G.ConnectedComponent)
    {v : V}
    (hv : v ∈ C.supp)
    (hcard : C.supp.ncard <= 3) :
    G.degree v <= 2 := by
  classical
  have hsubset : G.neighborSet v ⊆ C.supp \ {v} := by
    intro w hw
    exact ⟨C.mem_supp_of_adj_mem_supp hv hw, by
      intro hwv
      exact hw.ne (Set.mem_singleton_iff.mp hwv).symm⟩
  have hneigh_card : (G.neighborSet v).ncard <= (C.supp \ {v}).ncard :=
    Set.ncard_le_ncard hsubset
  have hdiff_card : (C.supp \ {v}).ncard <= 2 := by
    have hdiff_add : (C.supp \ {v}).ncard + 1 = C.supp.ncard :=
      Set.ncard_diff_singleton_add_one hv
    omega
  have hdegree : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  omega

theorem connectedComponent_degree_eq
    [Fintype V] [DecidableRel G.Adj]
    (C : G.ConnectedComponent)
    [Fintype C]
    [DecidableRel C.toSimpleGraph.Adj]
    (v : C) :
    G.degree (v : V) = C.toSimpleGraph.degree v := by
  classical
  let e : G.neighborSet (v : V) ≃ C.toSimpleGraph.neighborSet v := {
    toFun w := ⟨⟨w, C.mem_supp_of_adj_mem_supp v.2 w.2⟩, by
      exact w.2⟩
    invFun w := ⟨w, by
      exact w.2⟩
    left_inv w := by
      rfl
    right_inv w := by
      rfl
  }
  have hcard := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
  rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
  exact hcard

theorem exists_vertex_degree_le_one_of_finite_acyclic
    [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hacyclic : G.IsAcyclic) :
    Exists fun v : V => G.degree v <= 1 := by
  classical
  let x : V := Classical.choice inferInstance
  let C : G.ConnectedComponent := G.connectedComponentMk x
  letI : Fintype C := C.supp.toFinite.fintype
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  rcases subsingleton_or_nontrivial C with hsub | hnontrivial
  · let c : C := ⟨x, by
      change x ∈ (G.connectedComponentMk x).supp
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    have hdegC : C.toSimpleGraph.degree c = 0 := by
      rw [← SimpleGraph.card_neighborSet_eq_degree]
      exact Fintype.card_eq_zero_iff.mpr ⟨fun y =>
        y.2.ne (by
          change (c : V) = (y.1 : V)
          exact congrArg Subtype.val (Subsingleton.elim c y.1))⟩
    refine ⟨c, ?_⟩
    rw [connectedComponent_degree_eq C c, hdegC]
    omega
  · have htree : C.toSimpleGraph.IsTree :=
      hacyclic.isTree_connectedComponent C
    obtain ⟨c, hc_degree⟩ :=
      htree.exists_vert_degree_one_of_nontrivial
    refine ⟨c, ?_⟩
    rw [connectedComponent_degree_eq C c, hc_degree]

theorem IsTree.exists_two_distinct_degree_one_of_nontrivial
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) :
    Exists fun u : V =>
      Exists fun v : V => u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  classical
  obtain ⟨u, hu_degree⟩ := hT.exists_vert_degree_one_of_nontrivial
  by_contra hno
  have hno_other :
      forall v : V, v ≠ u -> G.degree v ≠ 1 := by
    intro v hv hdeg
    exact hno ⟨u, v, hv.symm, hu_degree, hdeg⟩
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  have hdeg_ge_two :
      forall v : V, v ∈ (Finset.univ.erase u : Finset V) -> 2 <= G.degree v := by
    intro v hv
    have hv_ne_u : v ≠ u := by
      simpa using (Finset.mem_erase.mp hv).1
    have hpos : 0 < G.degree v :=
      hT.connected.preconnected.degree_pos_of_nontrivial v
    have hne_one : G.degree v ≠ 1 := hno_other v hv_ne_u
    omega
  have hsum_erase_lower :
      2 * (Fintype.card V - 1) <=
        (Finset.univ.erase u : Finset V).sum (fun v => G.degree v) := by
    have hsum_const :
        (Finset.univ.erase u : Finset V).sum (fun _v => 2) =
          2 * (Fintype.card V - 1) := by
      have hcard_erase :
          (Finset.univ.erase u).card = Fintype.card V - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
      simp [Finset.sum_const, hcard_erase, Nat.mul_comm]
    rw [← hsum_const]
    exact Finset.sum_le_sum hdeg_ge_two
  have hsum_total_lower :
      1 + 2 * (Fintype.card V - 1) <= ∑ v : V, G.degree v := by
    have hnotmem : u ∉ (Finset.univ.erase u : Finset V) := by simp
    rw [← Finset.insert_erase (Finset.mem_univ u), Finset.sum_insert hnotmem]
    rw [hu_degree]
    exact Nat.add_le_add_left hsum_erase_lower 1
  have hsum_total_eq :
      ∑ v : V, G.degree v = 2 * (Fintype.card V - 1) := by
    have hedge :
        (G.edgeFinset.card + 1 = Fintype.card V) := hT.card_edgeFinset
    have hsum := G.sum_degrees_eq_twice_card_edges
    have hedge_eq : G.edgeFinset.card = Fintype.card V - 1 := by
      omega
    rw [hsum, hedge_eq]
  omega

theorem IsTree.card_degree_ge_three_add_two_le_card_degree_one
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree) :
    ((Finset.univ.filter fun v : V => 3 <= G.degree v).card + 2 <=
      (Finset.univ.filter fun v : V => G.degree v = 1).card) := by
  classical
  let branch : Finset V := Finset.univ.filter fun v : V => 3 <= G.degree v
  let leaf : Finset V := Finset.univ.filter fun v : V => G.degree v = 1
  have hpoint :
      forall v : V,
        (2 : ℤ) + (if 3 <= G.degree v then (1 : ℤ) else 0) -
            (if G.degree v = 1 then (1 : ℤ) else 0) <=
          (G.degree v : ℤ) := by
    intro v
    have hpos : 0 < G.degree v :=
      hT.connected.preconnected.degree_pos_of_nontrivial v
    by_cases hleaf : G.degree v = 1
    · simp [hleaf]
    · by_cases hbranch : 3 <= G.degree v
      · have hbranch_int : (3 : ℤ) <= (G.degree v : ℤ) := by
          exact_mod_cast hbranch
        simp [hleaf, hbranch]
      · have hdeg_two : G.degree v = 2 := by omega
        simp [hdeg_two]
  have hsum_lower :
      (∑ v : V,
          ((2 : ℤ) + (if 3 <= G.degree v then (1 : ℤ) else 0) -
            (if G.degree v = 1 then (1 : ℤ) else 0))) <=
        ∑ v : V, (G.degree v : ℤ) :=
    Finset.sum_le_sum (by
      intro v _hv
      exact hpoint v)
  have hsum_branch :
      (∑ v : V, (if 3 <= G.degree v then (1 : ℤ) else 0)) =
        (branch.card : ℤ) := by
    simp [branch]
  have hsum_leaf :
      (∑ v : V, (if G.degree v = 1 then (1 : ℤ) else 0)) =
        (leaf.card : ℤ) := by
    simp [leaf]
  have hsum_lower' :
      (2 * (Fintype.card V : ℤ) + (branch.card : ℤ) - (leaf.card : ℤ)) <=
        ∑ v : V, (G.degree v : ℤ) := by
    simpa [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      hsum_branch, hsum_leaf, nsmul_eq_mul, mul_comm, mul_left_comm,
      mul_assoc] using hsum_lower
  have hsum_nat :
      ∑ v : V, G.degree v = 2 * (Fintype.card V - 1) := by
    have hedge :
        G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
    have hedge_eq : G.edgeFinset.card = Fintype.card V - 1 := by omega
    rw [G.sum_degrees_eq_twice_card_edges, hedge_eq]
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  have hsum_eq :
      (∑ v : V, (G.degree v : ℤ)) =
        2 * (Fintype.card V : ℤ) - 2 := by
    have hsum_eq' :
        (∑ v : V, (G.degree v : ℤ)) =
          ((2 * (Fintype.card V - 1) : ℕ) : ℤ) := by
      exact_mod_cast hsum_nat
    rw [hsum_eq']
    omega
  have hineq_int :
      (branch.card : ℤ) + 2 <= (leaf.card : ℤ) := by
    have hmain :
        2 * (Fintype.card V : ℤ) + (branch.card : ℤ) -
            (leaf.card : ℤ) <=
          2 * (Fintype.card V : ℤ) - 2 := by
      simpa [hsum_eq] using hsum_lower'
    omega
  change branch.card + 2 <= leaf.card
  exact_mod_cast hineq_int

theorem IsTree.card_degree_one_eq_two_of_no_degree_ge_three
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree)
    (hno_branch : forall v : V, ¬ 3 <= G.degree v) :
    (Finset.univ.filter fun v : V => G.degree v = 1).card = 2 := by
  classical
  let leaf : Finset V := Finset.univ.filter fun v : V => G.degree v = 1
  have hpoint :
      forall v : V,
        (G.degree v : ℤ) =
          (2 : ℤ) - (if G.degree v = 1 then (1 : ℤ) else 0) := by
    intro v
    have hpos : 0 < G.degree v :=
      hT.connected.preconnected.degree_pos_of_nontrivial v
    have hle_two : G.degree v <= 2 := by
      have hnot := hno_branch v
      omega
    by_cases hleaf : G.degree v = 1
    · simp [hleaf]
    · have hdeg_two : G.degree v = 2 := by omega
      simp [hdeg_two]
  have hsum_leaf :
      (∑ v : V, (if G.degree v = 1 then (1 : ℤ) else 0)) =
        (leaf.card : ℤ) := by
    simp [leaf]
  have hsum_by_leaf :
      (∑ v : V, (G.degree v : ℤ)) =
        2 * (Fintype.card V : ℤ) - (leaf.card : ℤ) := by
    calc
      (∑ v : V, (G.degree v : ℤ)) =
          ∑ v : V, ((2 : ℤ) - (if G.degree v = 1 then (1 : ℤ) else 0)) := by
            exact Finset.sum_congr rfl (fun v _hv => hpoint v)
      _ = 2 * (Fintype.card V : ℤ) - (leaf.card : ℤ) := by
            simp [Finset.sum_sub_distrib, Finset.sum_const, hsum_leaf,
              mul_comm]
  have hsum_nat :
      ∑ v : V, G.degree v = 2 * (Fintype.card V - 1) := by
    have hedge :
        (G.edgeFinset.card + 1 = Fintype.card V) := hT.card_edgeFinset
    have hedge_eq : G.edgeFinset.card = Fintype.card V - 1 := by omega
    rw [G.sum_degrees_eq_twice_card_edges, hedge_eq]
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  have hsum_tree :
      (∑ v : V, (G.degree v : ℤ)) =
        2 * (Fintype.card V : ℤ) - 2 := by
    have hsum_eq' :
        (∑ v : V, (G.degree v : ℤ)) =
          ((2 * (Fintype.card V - 1) : ℕ) : ℤ) := by
      exact_mod_cast hsum_nat
    rw [hsum_eq']
    omega
  have hleaf_int : (leaf.card : ℤ) = 2 := by omega
  change leaf.card = 2
  exact_mod_cast hleaf_int

theorem IsTree.exists_degree_ge_three_of_three_le_card_degree_one
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree)
    (hleaf : 3 <=
      (Finset.univ.filter fun v : V => G.degree v = 1).card) :
    Exists fun v : V => 3 <= G.degree v := by
  by_contra hno_exists
  push Not at hno_exists
  have hcard_two :=
    Schematic.Math.GraphTheory.IsTree.card_degree_one_eq_two_of_no_degree_ge_three
      (G := G) hT (fun v hv => (not_le_of_gt (hno_exists v)) hv)
  omega

theorem IsTree.exists_degree_ge_three_of_three_distinct_degree_one
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree)
    {terminal : Fin 3 -> V}
    (hterminal_injective : Function.Injective terminal)
    (hterminal_degree : forall i : Fin 3, G.degree (terminal i) = 1) :
    Exists fun v : V => 3 <= G.degree v := by
  classical
  let leaf : Finset V := Finset.univ.filter fun v : V => G.degree v = 1
  let f : Fin 3 -> leaf := fun i =>
    ⟨terminal i, by simp [leaf, hterminal_degree i]⟩
  have hf_injective : Function.Injective f := by
    intro i j hij
    apply hterminal_injective
    exact congrArg (fun x : leaf => (x : V)) hij
  have hleaf :
      3 <= (Finset.univ.filter fun v : V => G.degree v = 1).card := by
    have hcard :
        Fintype.card (Fin 3) <= Fintype.card leaf :=
      Fintype.card_le_of_injective f hf_injective
    rwa [Fintype.card_fin, Fintype.card_coe] at hcard
  exact Schematic.Math.GraphTheory.IsTree.exists_degree_ge_three_of_three_le_card_degree_one
    (G := G) hT hleaf

theorem IsTree.exists_unique_degree_ge_three_of_three_distinct_degree_one
    [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (hT : G.IsTree)
    {terminal : Fin 3 -> V}
    (hterminal_injective : Function.Injective terminal)
    (hterminal_degree : forall i : Fin 3, G.degree (terminal i) = 1)
    (hbranch_card_le_one :
      (Finset.univ.filter fun v : V => 3 <= G.degree v).card <= 1) :
    Exists fun root : V =>
      3 <= G.degree root ∧
        forall z : V, 3 <= G.degree z -> z = root := by
  classical
  obtain ⟨root, hroot_degree⟩ :=
    Schematic.Math.GraphTheory.IsTree.exists_degree_ge_three_of_three_distinct_degree_one
      (G := G) hT hterminal_injective hterminal_degree
  let branch : Finset V := Finset.univ.filter fun v : V => 3 <= G.degree v
  have hbranch_subsingleton :
      forall {a b : V}, a ∈ branch -> b ∈ branch -> a = b :=
    Finset.card_le_one_iff.mp (by simpa [branch] using hbranch_card_le_one)
  refine ⟨root, hroot_degree, ?_⟩
  intro z hz
  have hroot_mem : root ∈ branch := by
    simp [branch, hroot_degree]
  have hz_mem : z ∈ branch := by
    simp [branch, hz]
  exact hbranch_subsingleton hz_mem hroot_mem

theorem exists_two_distinct_degree_one_of_finite_acyclic_no_isolated
    [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hacyclic : G.IsAcyclic)
    (hno_isolated : forall v : V, G.degree v ≠ 0) :
    Exists fun u : V =>
      Exists fun v : V => u ≠ v ∧ G.degree u = 1 ∧ G.degree v = 1 := by
  classical
  let x : V := Classical.choice inferInstance
  have hx_degree_pos : 0 < G.degree x := by
    exact Nat.pos_of_ne_zero (hno_isolated x)
  rw [SimpleGraph.degree_pos_iff_exists_adj] at hx_degree_pos
  obtain ⟨y, hxy⟩ := hx_degree_pos
  let C : G.ConnectedComponent := G.connectedComponentMk x
  letI : Fintype C := C.supp.toFinite.fintype
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  have hnontrivial : Nontrivial C := by
    refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩, ?_⟩
    · change x ∈ (G.connectedComponentMk x).supp
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    · exact C.mem_supp_of_adj_mem_supp
        (by
          change x ∈ (G.connectedComponentMk x).supp
          exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
        hxy
    · intro h
      exact hxy.ne (congrArg Subtype.val h)
  have htree : C.toSimpleGraph.IsTree :=
    hacyclic.isTree_connectedComponent C
  obtain ⟨u, v, huv, hu_degree, hv_degree⟩ :=
    IsTree.exists_two_distinct_degree_one_of_nontrivial
      (G := C.toSimpleGraph) htree
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro huv_val
    exact huv (Subtype.ext huv_val)
  · rw [connectedComponent_degree_eq C u]
    exact hu_degree
  · rw [connectedComponent_degree_eq C v]
    exact hv_degree

end Schematic.Math.GraphTheory
