import Schematic.Math.GraphTheory.Connectivity.Components

/-!
Degree and boundary consequences of higher connectivity.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem four_connected_minDegree_atLeast_four
    [Fintype V] [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    (v : V) :
    4 <= G.degree v :=
  IsKConnected.degree_atLeast hG v

theorem complete_of_four_connected_card_le_five
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    (hcard : Fintype.card V <= 5) :
    forall u v : V, u ≠ v -> G.Adj u v := by
  classical
  intro u v huv
  by_contra hnot_adj
  have hsubset : G.neighborFinset u ⊆ (Finset.univ.erase u).erase v := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ w⟩
    · intro hwv
      subst w
      exact hnot_adj hw
    · exact hw.ne'
  have hv_mem : v ∈ Finset.univ.erase u := by
    rw [Finset.mem_erase]
    exact ⟨huv.symm, Finset.mem_univ v⟩
  have htarget_card : ((Finset.univ.erase u).erase v).card <= 3 := by
    rw [Finset.card_erase_of_mem hv_mem]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u)]
    rw [Finset.card_univ]
    omega
  have hdegree_le_three : G.degree u <= 3 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact le_trans (Finset.card_le_card hsubset) htarget_card
  have hdegree_ge_four : 4 <= G.degree u :=
    four_connected_minDegree_atLeast_four hG u
  omega

theorem IsFourConnected.card_gt_five_of_not_complete
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : IsFourConnected G)
    (h_not_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    5 < Fintype.card V := by
  by_contra hcard
  have hcard_le : Fintype.card V <= 5 := by omega
  exact h_not_complete
    (complete_of_four_connected_card_le_five hG hcard_le)

theorem exists_neighbor_outside_set_of_inside_neighbors_lt_degree
    [Fintype V] [DecidableRel G.Adj]
    (S : Set V)
    {v : V}
    (hinside : (G.neighborSet v ∩ S).ncard < G.degree v) :
    Exists fun u : V =>
      u ∈ ((⊤ : G.Subgraph).deleteVerts S).verts ∧ G.Adj u v := by
  classical
  by_contra hno
  have hsubset : G.neighborSet v ⊆ G.neighborSet v ∩ S := by
    intro u hu
    refine ⟨hu, ?_⟩
    by_contra huS
    apply hno
    refine ⟨u, ?_, hu.symm⟩
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    exact ⟨by simp, huS⟩
  have hcard : (G.neighborSet v).ncard <= (G.neighborSet v ∩ S).ncard :=
    Set.ncard_le_ncard hsubset
  have hdegree : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  omega

theorem exists_neighbor_outside_set_of_degree_atLeast_four_of_inside_neighbors_atMost_three
    [Fintype V] [DecidableRel G.Adj]
    (S : Set V)
    {v : V}
    (hdeg : 4 <= G.degree v)
    (hinside : (G.neighborSet v ∩ S).ncard <= 3) :
    Exists fun u : V =>
      u ∈ ((⊤ : G.Subgraph).deleteVerts S).verts ∧ G.Adj u v := by
  apply exists_neighbor_outside_set_of_inside_neighbors_lt_degree S
  omega

theorem IsTwoConnected.boundary_ncard_ge_two
    [Fintype V]
    (hG : IsTwoConnected G)
    {A S : Set V}
    (hA_nonempty : A.Nonempty)
    (hA_disjoint_S : Disjoint A S)
    (hS_large : 1 < S.ncard)
    (hclosed : forall a : V, a ∈ A -> forall b : V, G.Adj a b -> b ∈ A ∨ b ∈ S) :
    2 <= ({v : V | v ∈ S ∧ Exists fun a : V => a ∈ A ∧ G.Adj a v}).ncard := by
  classical
  let B : Set V := {v : V | v ∈ S ∧ Exists fun a : V => a ∈ A ∧ G.Adj a v}
  change 2 <= B.ncard
  by_contra hnot
  have hB_le_one : B.ncard <= 1 := by omega
  have hB_lt_two : B.ncard < 2 := by omega
  have hconn : (G.induce Bᶜ).Connected := hG.2 B hB_lt_two
  have hB_sub_S : B ⊆ S := by
    intro v hv
    exact hv.1
  have hS_not_subset_B : ¬ S ⊆ B := by
    intro hsub
    have hcard_le : S.ncard <= B.ncard := Set.ncard_le_ncard hsub
    omega
  rw [Set.subset_def] at hS_not_subset_B
  push Not at hS_not_subset_B
  obtain ⟨b, hbS, hbB⟩ := hS_not_subset_B
  have hbA : b ∉ A := by
    intro hbA
    exact Set.disjoint_left.mp hA_disjoint_S hbA hbS
  let A' : Set (Bᶜ : Set V) := {x | (x : V) ∈ A}
  have hA'_nonempty : A'.Nonempty := by
    rcases hA_nonempty with ⟨a, haA⟩
    have haB : a ∉ B := by
      intro haB
      exact Set.disjoint_left.mp hA_disjoint_S haA (hB_sub_S haB)
    exact ⟨⟨a, haB⟩, haA⟩
  have hA'_compl_nonempty : A'ᶜ.Nonempty := by
    exact ⟨⟨b, hbB⟩, by
      change ¬ b ∈ A
      exact hbA⟩
  obtain ⟨u, huA, v, hvA, huv⟩ :=
    Connected.exists_adjacent_crossing
      (G := G.induce Bᶜ) hconn (S := A') hA'_nonempty hA'_compl_nonempty
  have huA_base : (u : V) ∈ A := huA
  have hv_not_A_base : (v : V) ∉ A := hvA
  have huv_base : G.Adj (u : V) (v : V) := by
    exact huv
  rcases hclosed (u : V) huA_base (v : V) huv_base with hvA_base | hvS_base
  · exact hv_not_A_base hvA_base
  · exact v.2 ⟨hvS_base, u, huA_base, huv_base⟩

end Schematic.Math.GraphTheory
