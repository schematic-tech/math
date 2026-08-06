import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Logic.Equiv.Fintype

/-!
Basic graph-theoretic vocabulary used by the formalization, but not specific to
the Dominating 4-Colour Theorem paper.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

theorem Walk.mem_support_of_mem_induce_support
    {G : SimpleGraph V}
    {S : Set V}
    {u v : V}
    (p : G.Walk u v)
    (hpS : forall x : V, x ∈ p.support -> x ∈ S)
    {x : S}
    (hx : x ∈ (p.induce S hpS).support) :
    (x : V) ∈ p.support := by
  rw [SimpleGraph.Walk.support_induce] at hx
  change x ∈ p.support.attachWith (fun t => t ∈ S) hpS at hx
  rw [List.attachWith] at hx
  rcases List.mem_pmap.mp hx with ⟨a, ha, hxa⟩
  have hval : a = (x : V) := congrArg Subtype.val hxa
  simpa [hval] using ha

theorem Walk.mem_induce_support_of_mem_support
    {G : SimpleGraph V}
    {S : Set V}
    {u v : V}
    (p : G.Walk u v)
    (hpS : forall x : V, x ∈ p.support -> x ∈ S)
    {x : V}
    (hx : x ∈ p.support) :
    (⟨x, hpS x hx⟩ : S) ∈ (p.induce S hpS).support := by
  rw [SimpleGraph.Walk.support_induce]
  change (⟨x, hpS x hx⟩ : S) ∈
    p.support.attachWith (fun t => t ∈ S) hpS
  rw [List.attachWith]
  exact List.mem_pmap.mpr ⟨x, hx, rfl⟩

theorem finset_card_le_two_cases
    {α : Type*}
    [DecidableEq α]
    (s : Finset α)
    (hs : s.card <= 2) :
    s = ∅ ∨ (Exists fun a : α => s = {a}) ∨
      Exists fun a : α => Exists fun b : α => a ≠ b ∧ s = {a, b} := by
  classical
  by_cases h0 : s.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp h0)
  · by_cases h1 : s.card = 1
    · exact Or.inr (Or.inl (Finset.card_eq_one.mp h1))
    · have h2 : s.card = 2 := by omega
      exact Or.inr (Or.inr (Finset.card_eq_two.mp h2))

/-- The range of an injective family indexed by three elements has exactly
three elements. -/
theorem ncard_range_fin3_of_injective
    {f : Fin 3 -> V}
    (hf : Function.Injective f) :
    (Set.range f).ncard = 3 := by
  rw [Set.ncard_range_of_injective hf]
  simp

/-- Removing one member from the range of an injective three-element family
leaves exactly two elements. -/
theorem ncard_range_fin3_diff_singleton_eq_two
    {f : Fin 3 -> V}
    (hf : Function.Injective f)
    (i : Fin 3) :
    (Set.range f \ {f i}).ncard = 2 := by
  have hi : f i ∈ Set.range f := ⟨i, rfl⟩
  rw [Set.ncard_diff_singleton_of_mem hi,
    ncard_range_fin3_of_injective hf]

theorem ncard_range_fin3_diff_singleton_le_two
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet)
    (i : Fin 3) :
    (Set.range feet \ {feet i}).ncard <= 2 := by
  rw [ncard_range_fin3_diff_singleton_eq_two hfeet_injective i]

/-- Adjoining one element to the range of an injective three-element family
produces a set of cardinality at most four. -/
theorem ncard_insert_range_fin3_le_four
    {f : Fin 3 -> V}
    (hf : Function.Injective f)
    (x : V) :
    (insert x (Set.range f)).ncard <= 4 := by
  calc
    (insert x (Set.range f)).ncard <=
        (Set.range f).ncard + 1 := Set.ncard_insert_le _ _
    _ = 4 := by rw [ncard_range_fin3_of_injective hf]

/-- Adjoining one element after deleting a chosen range member from an
injective three-element family produces at most three elements. -/
theorem ncard_insert_range_fin3_diff_singleton_le_three
    {f : Fin 3 -> V}
    (hf : Function.Injective f)
    (i : Fin 3)
    (x : V) :
    (insert x (Set.range f \ {f i})).ncard <= 3 := by
  calc
    (insert x (Set.range f \ {f i})).ncard <=
        (Set.range f \ {f i}).ncard + 1 := Set.ncard_insert_le _ _
    _ = 3 := by
      rw [ncard_range_fin3_diff_singleton_eq_two hf i]

theorem fin4_exists_embedding_zero_two
    {i j : Fin 4}
    (hij : i ≠ j) :
    Exists fun σ : Fin 4 ↪ Fin 4 =>
      σ (0 : Fin 4) = i ∧ σ (2 : Fin 4) = j := by
  classical
  let f : Fin 2 -> Fin 4
    | 0 => 0
    | 1 => 2
  let g : Fin 2 -> Fin 4
    | 0 => i
    | 1 => j
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [f] at h ⊢
  have hg : Function.Injective g := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [g] at h ⊢
    · exact False.elim (hij h)
    · exact False.elim (hij h.symm)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ.toEmbedding, ?_, ?_⟩
  · simpa [f, g] using hσ (0 : Fin 2)
  · simpa [f, g] using hσ (1 : Fin 2)

theorem fin4_exists_embedding_zero_one_two
    {i j k : Fin 4}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    Exists fun σ : Fin 4 ↪ Fin 4 =>
      σ (0 : Fin 4) = i ∧
        σ (1 : Fin 4) = j ∧
          σ (2 : Fin 4) = k := by
  classical
  obtain ⟨σ, hσ0, hσ2⟩ := fin4_exists_embedding_zero_two hik
  have hsurj : Function.Surjective σ :=
    Finite.surjective_of_injective σ.injective
  rcases hsurj j with ⟨t, ht⟩
  have ht_ne0 : t ≠ (0 : Fin 4) := by
    intro ht0
    exact hij.symm (by simpa [ht0, hσ0] using ht.symm)
  have ht_ne2 : t ≠ (2 : Fin 4) := by
    intro ht2
    exact hjk (by simpa [ht2, hσ2] using ht.symm)
  fin_cases t
  · exact False.elim (ht_ne0 rfl)
  · exact ⟨σ, hσ0, ht, hσ2⟩
  · exact False.elim (ht_ne2 rfl)
  · let swap13 : Equiv.Perm (Fin 4) :=
      Equiv.swap (1 : Fin 4) (3 : Fin 4)
    let σ' : Fin 4 ↪ Fin 4 := swap13.toEmbedding.trans σ
    refine ⟨σ', ?_, ?_, ?_⟩
    · change σ (swap13 (0 : Fin 4)) = i
      simpa [swap13] using hσ0
    · change σ (swap13 (1 : Fin 4)) = j
      simpa [swap13] using ht
    · change σ (swap13 (2 : Fin 4)) = k
      simpa [swap13] using hσ2

theorem fin4_embedding_preimages_zero_one_two
    (σ : Fin 4 ↪ Fin 4) :
    Exists fun c : Fin 4 =>
      Exists fun l : Fin 4 =>
        Exists fun r : Fin 4 =>
          σ c = (0 : Fin 4) ∧
            σ l = (1 : Fin 4) ∧
              σ r = (2 : Fin 4) ∧
                c ≠ l ∧ c ≠ r ∧ l ≠ r := by
  classical
  have hsurj : Function.Surjective σ :=
    Finite.surjective_of_injective σ.injective
  rcases hsurj (0 : Fin 4) with ⟨c, hc⟩
  rcases hsurj (1 : Fin 4) with ⟨l, hl⟩
  rcases hsurj (2 : Fin 4) with ⟨r, hr⟩
  refine ⟨c, l, r, hc, hl, hr, ?_, ?_, ?_⟩
  · intro hcl
    have h01 : (0 : Fin 4) = 1 := by
      calc
        (0 : Fin 4) = σ c := hc.symm
        _ = σ l := by rw [hcl]
        _ = 1 := hl
    exact (by decide : (0 : Fin 4) ≠ 1) h01
  · intro hcr
    have h02 : (0 : Fin 4) = 2 := by
      calc
        (0 : Fin 4) = σ c := hc.symm
        _ = σ r := by rw [hcr]
        _ = 2 := hr
    exact (by decide : (0 : Fin 4) ≠ 2) h02
  · intro hlr
    have h12 : (1 : Fin 4) = 2 := by
      calc
        (1 : Fin 4) = σ l := hl.symm
        _ = σ r := by rw [hlr]
        _ = 2 := hr
    exact (by decide : (1 : Fin 4) ≠ 2) h12

theorem fin4_embedding_zero_two_remaining_ne
    {i j : Fin 4}
    {σ : Fin 4 ↪ Fin 4}
    (hσ0 : σ (0 : Fin 4) = i)
    (hσ2 : σ (2 : Fin 4) = j) :
    σ (1 : Fin 4) ≠ i ∧
      σ (1 : Fin 4) ≠ j ∧
        σ (3 : Fin 4) ≠ i ∧
          σ (3 : Fin 4) ≠ j ∧
            σ (1 : Fin 4) ≠ σ (3 : Fin 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (by decide : (1 : Fin 4) ≠ (0 : Fin 4))
      (σ.injective (h.trans hσ0.symm))
  · intro h
    exact (by decide : (1 : Fin 4) ≠ (2 : Fin 4))
      (σ.injective (h.trans hσ2.symm))
  · intro h
    exact (by decide : (3 : Fin 4) ≠ (0 : Fin 4))
      (σ.injective (h.trans hσ0.symm))
  · intro h
    exact (by decide : (3 : Fin 4) ≠ (2 : Fin 4))
      (σ.injective (h.trans hσ2.symm))
  · intro h
    exact (by decide : (1 : Fin 4) ≠ (3 : Fin 4))
      (σ.injective h)

theorem fin4_exists_embedding_zero_two_avoiding_values
    {α : Type*}
    [DecidableEq α]
    (a : Fin 4 -> α)
    {i j : Fin 4}
    (hij : i ≠ j)
    (hvalij : a i ≠ a j)
    (hthird :
      Exists fun k : Fin 4 => a k ≠ a i ∧ a k ≠ a j) :
    Exists fun σ : Fin 4 ↪ Fin 4 =>
      σ (0 : Fin 4) = i ∧
        σ (2 : Fin 4) = j ∧
          a (σ (1 : Fin 4)) ≠ a i ∧
            a (σ (3 : Fin 4)) ≠ a j := by
  classical
  obtain ⟨σ, hσ0, hσ2⟩ := fin4_exists_embedding_zero_two hij
  have hsurj : Function.Surjective σ :=
    Finite.surjective_of_injective σ.injective
  obtain ⟨k, hk_ne_i, hk_ne_j⟩ := hthird
  obtain ⟨m, rfl⟩ := hsurj k
  have hthird_slot :
      (a (σ (1 : Fin 4)) ≠ a i ∧ a (σ (1 : Fin 4)) ≠ a j) ∨
        (a (σ (3 : Fin 4)) ≠ a i ∧ a (σ (3 : Fin 4)) ≠ a j) := by
    fin_cases m
    · exact False.elim (hk_ne_i (by simp [hσ0]))
    · exact Or.inl ⟨hk_ne_i, hk_ne_j⟩
    · exact False.elim (hk_ne_j (by simp [hσ2]))
    · exact Or.inr ⟨hk_ne_i, hk_ne_j⟩
  by_cases hslot1 : a (σ (1 : Fin 4)) ≠ a i
  · by_cases hslot3 : a (σ (3 : Fin 4)) ≠ a j
    · exact ⟨σ, hσ0, hσ2, hslot1, hslot3⟩
    · let swap13 : Equiv.Perm (Fin 4) :=
        Equiv.swap (1 : Fin 4) (3 : Fin 4)
      let σ' : Fin 4 ↪ Fin 4 := swap13.toEmbedding.trans σ
      have hσ'0 : σ' (0 : Fin 4) = i := by
        change σ (swap13 (0 : Fin 4)) = i
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact hσ0
      have hσ'2 : σ' (2 : Fin 4) = j := by
        change σ (swap13 (2 : Fin 4)) = j
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact hσ2
      have hslot3_eq : a (σ (3 : Fin 4)) = a j := of_not_not hslot3
      have hσ3_ne_i : a (σ (3 : Fin 4)) ≠ a i := by
        intro h
        exact hvalij (h.symm.trans hslot3_eq)
      have hσ1_ne_j : a (σ (1 : Fin 4)) ≠ a j := by
        rcases hthird_slot with hthird1 | hthird3
        · exact hthird1.2
        · exact False.elim (hthird3.2 hslot3_eq)
      refine ⟨σ', hσ'0, hσ'2, ?_, ?_⟩
      · change a (σ (swap13 (1 : Fin 4))) ≠ a i
        rw [Equiv.swap_apply_left]
        exact hσ3_ne_i
      · change a (σ (swap13 (3 : Fin 4))) ≠ a j
        rw [Equiv.swap_apply_right]
        exact hσ1_ne_j
  · let swap13 : Equiv.Perm (Fin 4) :=
      Equiv.swap (1 : Fin 4) (3 : Fin 4)
    let σ' : Fin 4 ↪ Fin 4 := swap13.toEmbedding.trans σ
    have hσ'0 : σ' (0 : Fin 4) = i := by
      change σ (swap13 (0 : Fin 4)) = i
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact hσ0
    have hσ'2 : σ' (2 : Fin 4) = j := by
      change σ (swap13 (2 : Fin 4)) = j
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact hσ2
    have hslot1_eq : a (σ (1 : Fin 4)) = a i := of_not_not hslot1
    have hσ1_ne_j : a (σ (1 : Fin 4)) ≠ a j := by
      intro h
      exact hvalij (hslot1_eq.symm.trans h)
    have hσ3_ne_i : a (σ (3 : Fin 4)) ≠ a i := by
      rcases hthird_slot with hthird1 | hthird3
      · exact False.elim (hthird1.1 hslot1_eq)
      · exact hthird3.1
    refine ⟨σ', hσ'0, hσ'2, ?_, ?_⟩
    · change a (σ (swap13 (1 : Fin 4))) ≠ a i
      rw [Equiv.swap_apply_left]
      exact hσ3_ne_i
    · change a (σ (swap13 (3 : Fin 4))) ≠ a j
      rw [Equiv.swap_apply_right]
      exact hσ1_ne_j

theorem fin4_exists_embedding_zero_two_cross_avoiding_values
    {α : Type*}
    [DecidableEq α]
    (a : Fin 4 -> α)
    {i j : Fin 4}
    (hij : i ≠ j)
    (hvalij : a i ≠ a j)
    (hthird :
      Exists fun k : Fin 4 => a k ≠ a i ∧ a k ≠ a j) :
    Exists fun σ : Fin 4 ↪ Fin 4 =>
      σ (0 : Fin 4) = i ∧
        σ (2 : Fin 4) = j ∧
          a (σ (1 : Fin 4)) ≠ a j ∧
            a (σ (3 : Fin 4)) ≠ a i := by
  classical
  obtain ⟨σ, hσ0, hσ2⟩ := fin4_exists_embedding_zero_two hij
  have hsurj : Function.Surjective σ :=
    Finite.surjective_of_injective σ.injective
  obtain ⟨k, hk_ne_i, hk_ne_j⟩ := hthird
  obtain ⟨m, rfl⟩ := hsurj k
  have hthird_slot :
      (a (σ (1 : Fin 4)) ≠ a i ∧ a (σ (1 : Fin 4)) ≠ a j) ∨
        (a (σ (3 : Fin 4)) ≠ a i ∧ a (σ (3 : Fin 4)) ≠ a j) := by
    fin_cases m
    · exact False.elim (hk_ne_i (by simp [hσ0]))
    · exact Or.inl ⟨hk_ne_i, hk_ne_j⟩
    · exact False.elim (hk_ne_j (by simp [hσ2]))
    · exact Or.inr ⟨hk_ne_i, hk_ne_j⟩
  by_cases hslot1 : a (σ (1 : Fin 4)) ≠ a j
  · by_cases hslot3 : a (σ (3 : Fin 4)) ≠ a i
    · exact ⟨σ, hσ0, hσ2, hslot1, hslot3⟩
    · let swap13 : Equiv.Perm (Fin 4) :=
        Equiv.swap (1 : Fin 4) (3 : Fin 4)
      let σ' : Fin 4 ↪ Fin 4 := swap13.toEmbedding.trans σ
      have hσ'0 : σ' (0 : Fin 4) = i := by
        change σ (swap13 (0 : Fin 4)) = i
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact hσ0
      have hσ'2 : σ' (2 : Fin 4) = j := by
        change σ (swap13 (2 : Fin 4)) = j
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact hσ2
      have hslot3_eq : a (σ (3 : Fin 4)) = a i := of_not_not hslot3
      have hσ3_ne_j : a (σ (3 : Fin 4)) ≠ a j := by
        intro h
        exact hvalij (hslot3_eq.symm.trans h)
      have hσ1_ne_i : a (σ (1 : Fin 4)) ≠ a i := by
        rcases hthird_slot with hthird1 | hthird3
        · exact hthird1.1
        · exact False.elim (hthird3.1 hslot3_eq)
      refine ⟨σ', hσ'0, hσ'2, ?_, ?_⟩
      · change a (σ (swap13 (1 : Fin 4))) ≠ a j
        rw [Equiv.swap_apply_left]
        exact hσ3_ne_j
      · change a (σ (swap13 (3 : Fin 4))) ≠ a i
        rw [Equiv.swap_apply_right]
        exact hσ1_ne_i
  · let swap13 : Equiv.Perm (Fin 4) :=
      Equiv.swap (1 : Fin 4) (3 : Fin 4)
    let σ' : Fin 4 ↪ Fin 4 := swap13.toEmbedding.trans σ
    have hσ'0 : σ' (0 : Fin 4) = i := by
      change σ (swap13 (0 : Fin 4)) = i
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact hσ0
    have hσ'2 : σ' (2 : Fin 4) = j := by
      change σ (swap13 (2 : Fin 4)) = j
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact hσ2
    have hslot1_eq : a (σ (1 : Fin 4)) = a j := of_not_not hslot1
    have hσ1_ne_i : a (σ (1 : Fin 4)) ≠ a i := by
      intro h
      exact hvalij (h.symm.trans hslot1_eq)
    have hσ3_ne_j : a (σ (3 : Fin 4)) ≠ a j := by
      rcases hthird_slot with hthird1 | hthird3
      · exact False.elim (hthird1.2 hslot1_eq)
      · exact hthird3.2
    refine ⟨σ', hσ'0, hσ'2, ?_, ?_⟩
    · change a (σ (swap13 (1 : Fin 4))) ≠ a j
      rw [Equiv.swap_apply_left]
      exact hσ3_ne_j
    · change a (σ (swap13 (3 : Fin 4))) ≠ a i
      rw [Equiv.swap_apply_right]
      exact hσ1_ne_i

theorem fin4_exists_third_value_of_three_pairwise_distinct
    {α : Type*}
    [DecidableEq α]
    (a : Fin 4 -> α)
    {i j p q r : Fin 4}
    (hpq : a p ≠ a q)
    (hpr : a p ≠ a r)
    (hqr : a q ≠ a r) :
    Exists fun k : Fin 4 => a k ≠ a i ∧ a k ≠ a j := by
  classical
  by_contra hnone
  have hvalues : forall k : Fin 4, a k = a i ∨ a k = a j := by
    intro k
    by_cases hki : a k = a i
    · exact Or.inl hki
    · by_cases hkj : a k = a j
      · exact Or.inr hkj
      · exact False.elim (hnone ⟨k, hki, hkj⟩)
  have hpq_split :
      (a p = a i ∧ a q = a j) ∨
        (a p = a j ∧ a q = a i) := by
    rcases hvalues p with hp_i | hp_j
    · rcases hvalues q with hq_i | hq_j
      · exact False.elim (hpq (hp_i.trans hq_i.symm))
      · exact Or.inl ⟨hp_i, hq_j⟩
    · rcases hvalues q with hq_i | hq_j
      · exact Or.inr ⟨hp_j, hq_i⟩
      · exact False.elim (hpq (hp_j.trans hq_j.symm))
  rcases hpq_split with ⟨hp_i, hq_j⟩ | ⟨hp_j, hq_i⟩
  · rcases hvalues r with hr_i | hr_j
    · exact hpr (hp_i.trans hr_i.symm)
    · exact hqr (hq_j.trans hr_j.symm)
  · rcases hvalues r with hr_i | hr_j
    · exact hqr (hq_i.trans hr_i.symm)
    · exact hpr (hp_j.trans hr_j.symm)

theorem fin3_not_four_pairwise_distinct
    (a b c d : Fin 3)
    (hab : a ≠ b)
    (hac : a ≠ c)
    (had : a ≠ d)
    (hbc : b ≠ c)
    (hbd : b ≠ d)
    (hcd : c ≠ d) :
    False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp at *

theorem not_injective_fin4_fin3 (f : Fin 4 -> Fin 3) :
    Not (Function.Injective f) := by
  intro hf
  exact fin3_not_four_pairwise_distinct
    (f 0) (f 1) (f 2) (f 3)
    (fun h => by exact (by decide : (0 : Fin 4) ≠ 1) (hf h))
    (fun h => by exact (by decide : (0 : Fin 4) ≠ 2) (hf h))
    (fun h => by exact (by decide : (0 : Fin 4) ≠ 3) (hf h))
    (fun h => by exact (by decide : (1 : Fin 4) ≠ 2) (hf h))
    (fun h => by exact (by decide : (1 : Fin 4) ≠ 3) (hf h))
    (fun h => by exact (by decide : (2 : Fin 4) ≠ 3) (hf h))

theorem not_injective_of_maps_fin4_into_injective_fin3_range
    {α : Type*}
    {boundary : Fin 3 -> α}
    (endpoint : Fin 4 -> α)
    (hendpoint_range : forall i : Fin 4, endpoint i ∈ Set.range boundary) :
    Not (Function.Injective endpoint) := by
  classical
  let idx : Fin 4 -> Fin 3 := fun i => Classical.choose (hendpoint_range i)
  have hidx_spec : forall i : Fin 4, boundary (idx i) = endpoint i := by
    intro i
    exact Classical.choose_spec (hendpoint_range i)
  intro hendpoint_injective
  have hidx_injective : Function.Injective idx := by
    intro i j hij
    apply hendpoint_injective
    calc
      endpoint i = boundary (idx i) := (hidx_spec i).symm
      _ = boundary (idx j) := by rw [hij]
      _ = endpoint j := hidx_spec j
  exact not_injective_fin4_fin3 idx hidx_injective

abbrev FourColorable (G : SimpleGraph V) : Prop :=
  G.Colorable 4

abbrev FiveChromaticOrMore (G : SimpleGraph V) : Prop :=
  Not (G.Colorable 4)

def HasAtLeastVertices [Fintype V] (_G : SimpleGraph V) (n : Nat) : Prop :=
  n <= Fintype.card V

def ConnectedSubgraph {G : SimpleGraph V} (H : G.Subgraph) : Prop :=
  H.coe.Connected

def IsTriangle (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

theorem IsTriangle.injective_fin3
    {G : SimpleGraph V}
    {feet : Fin 3 -> V}
    (h_triangle : IsTriangle G (feet 0) (feet 1) (feet 2)) :
    Function.Injective feet := by
  rcases h_triangle with ⟨h01, h12, h20, _⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact False.elim (h01 hij)
  · exact False.elim (h20.symm hij)
  · exact False.elim (h01 hij.symm)
  · exact False.elim (h12 hij)
  · exact False.elim (h20 hij)
  · exact False.elim (h12 hij.symm)

def HasTriangleDisjointFromPair (G : SimpleGraph V) (v1 v2 : V) : Prop :=
  Exists fun a : V =>
    Exists fun b : V =>
      Exists fun c : V =>
        IsTriangle G a b c ∧
          a ≠ v1 ∧ a ≠ v2 ∧ b ≠ v1 ∧ b ≠ v2 ∧ c ≠ v1 ∧ c ≠ v2

def MaxDegreeAtMost [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : Nat) : Prop :=
  forall v : V, G.degree v <= d

def NoAdjacentVerticesDegreeAtLeast [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : Nat) : Prop :=
  forall v w : V, G.Adj v w -> Not (d <= G.degree v ∧ d <= G.degree w)

theorem colorable_four_of_delete_vertex_colorable_of_degree_le_three
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (x : V)
    (h_degree : G.degree x <= 3)
    (h_color : (G.induce ({x} : Set V)ᶜ).Colorable 4) :
    G.Colorable 4 := by
  classical
  obtain ⟨C⟩ := h_color
  let deletedColor : V -> Fin 4 := fun v =>
    if h : v = x then 0
    else C ⟨v, by simp [Set.mem_compl_iff, Set.mem_singleton_iff, h]⟩
  let usedColors : Finset (Fin 4) := (G.neighborFinset x).image deletedColor
  have h_used_card_le : usedColors.card <= 3 := by
    calc
      usedColors.card <= (G.neighborFinset x).card := Finset.card_image_le
      _ = G.degree x := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ <= 3 := h_degree
  have h_used_card_lt_univ : usedColors.card < (Finset.univ : Finset (Fin 4)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨fresh, _hfresh_univ, hfresh⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card h_used_card_lt_univ
  let color : V -> Fin 4 := fun v => if v = x then fresh else deletedColor v
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw
  by_cases hvx : v = x
  · subst v
    have hw_ne : w ≠ x := hvw.ne'
    have hw_mem : w ∈ G.neighborFinset x := by
      rw [SimpleGraph.mem_neighborFinset]
      exact hvw
    have hw_used : deletedColor w ∈ usedColors :=
      Finset.mem_image.mpr ⟨w, hw_mem, rfl⟩
    have hw_used' :
        C ⟨w, by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hw_ne⟩ ∈
          usedColors := by
      simpa [deletedColor, hw_ne] using hw_used
    intro h_same
    simp [color, deletedColor, hw_ne] at h_same
    exact hfresh (by
      rw [h_same]
      exact hw_used')
  · by_cases hwx : w = x
    · subst w
      have hv_mem : v ∈ G.neighborFinset x := by
        rw [SimpleGraph.mem_neighborFinset]
        exact hvw.symm
      have hv_used : deletedColor v ∈ usedColors :=
        Finset.mem_image.mpr ⟨v, hv_mem, rfl⟩
      have hv_used' :
          C ⟨v, by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hvx⟩ ∈
            usedColors := by
        simpa [deletedColor, hvx] using hv_used
      intro h_same
      simp [color, deletedColor, hvx] at h_same
      exact hfresh (by
        rw [← h_same]
        exact hv_used')
    · have hv_compl : v ∈ ({x} : Set V)ᶜ := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hvx
      have hw_compl : w ∈ ({x} : Set V)ᶜ := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hwx
      have h_induced :
          (G.induce ({x} : Set V)ᶜ).Adj ⟨v, hv_compl⟩ ⟨w, hw_compl⟩ := by
        simpa using hvw
      have h_valid := C.valid h_induced
      intro h_same
      simp [color, deletedColor, hvx, hwx] at h_same
      exact h_valid h_same

theorem degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (x : V)
    (h_not_colorable : Not (G.Colorable 4))
    (h_delete_colorable : (G.induce ({x} : Set V)ᶜ).Colorable 4) :
    4 <= G.degree x := by
  by_contra h_degree
  have h_degree_le_three : G.degree x <= 3 := by omega
  exact h_not_colorable
    (colorable_four_of_delete_vertex_colorable_of_degree_le_three
      (G := G) x h_degree_le_three h_delete_colorable)

structure VertexDeletionMinimalNonFourColorable
    (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] : Prop where
  not_colorable : Not (G.Colorable 4)
  delete_colorable :
    forall x : V, (G.induce ({x} : Set V)ᶜ).Colorable 4

theorem VertexDeletionMinimalNonFourColorable.degree_atLeast_four
    {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : VertexDeletionMinimalNonFourColorable G)
    (x : V) :
    4 <= G.degree x :=
  degree_atLeast_four_of_not_colorable_four_of_delete_vertex_colorable
    (G := G) x hG.not_colorable (hG.delete_colorable x)

theorem card_gt_four_of_not_colorable_four
    {G : SimpleGraph V}
    [Fintype V]
    (h_not_colorable : Not (G.Colorable 4)) :
    4 < Fintype.card V := by
  by_contra h
  have h_card_le : Fintype.card V <= 4 := by omega
  exact h_not_colorable
    (SimpleGraph.Colorable.mono h_card_le G.colorable_of_fintype)

theorem colorable_four_of_card_le_five_of_nonadjacent
    {G : SimpleGraph V}
    [Fintype V]
    (u v : V)
    (huv : u ≠ v)
    (h_not_adj : Not (G.Adj u v))
    (h_card : Fintype.card V <= 5) :
    G.Colorable 4 := by
  classical
  let R : V -> Prop := fun x => x ≠ u ∧ x ≠ v
  let P : V -> Prop := fun x => x = u ∨ x = v
  letI : Fintype {x : V // P x} := Fintype.ofFinite _
  letI : Fintype {x : V // R x} := Fintype.ofFinite _
  have hP_card : Fintype.card {x : V // P x} = 2 := by
    rw [Fintype.card_of_subtype ({u, v} : Finset V)]
    · exact Finset.card_pair huv
    · intro x
      simp [P]
  have hR_notP : forall x : V, R x ↔ ¬ P x := by
    intro x
    constructor
    · rintro ⟨hxu, hxv⟩ hP
      exact hP.elim hxu hxv
    · intro hP
      exact ⟨fun hxu => hP (Or.inl hxu), fun hxv => hP (Or.inr hxv)⟩
  have hR_card : Fintype.card {x : V // R x} <= 3 := by
    have hcompl : Fintype.card {x : V // ¬ P x} = Fintype.card V - 2 := by
      rw [Fintype.card_subtype_compl P, hP_card]
    let e : {x : V // R x} ≃ {x : V // ¬ P x} := {
      toFun x := ⟨x, (hR_notP x).mp x.2⟩
      invFun x := ⟨x, (hR_notP x).mpr x.2⟩
      left_inv x := by rfl
      right_inv x := by rfl
    }
    have hcard_eq : Fintype.card {x : V // R x} = Fintype.card {x : V // ¬ P x} :=
      Fintype.card_congr e
    rw [hcard_eq, hcompl]
    omega
  obtain ⟨eR⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := {x : V // R x}) (β := Fin 3) hR_card
  let color : V -> Fin 4 := fun x =>
    if hx : x = u ∨ x = v then
      0
    else
      Fin.succ (eR ⟨x, (hR_notP x).mpr hx⟩)
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro a b hab hsame
  by_cases haP : P a
  · by_cases hbP : P b
    · rcases haP with rfl | rfl <;> rcases hbP with rfl | rfl
      · exact hab.ne rfl
      · exact h_not_adj hab
      · exact h_not_adj hab.symm
      · exact hab.ne rfl
    · have hcolor_a : color a = 0 := by simp [color, P, haP]
      have hcolor_b :
          Exists fun k : Fin 3 => color b = Fin.succ k := by
        refine ⟨eR ⟨b, (hR_notP b).mpr hbP⟩, ?_⟩
        simp [color, P, hbP]
      rcases hcolor_b with ⟨k, hk⟩
      rw [hcolor_a, hk] at hsame
      exact Fin.succ_ne_zero k hsame.symm
  · by_cases hbP : P b
    · have hcolor_a :
          Exists fun k : Fin 3 => color a = Fin.succ k := by
        refine ⟨eR ⟨a, (hR_notP a).mpr haP⟩, ?_⟩
        simp [color, P, haP]
      have hcolor_b : color b = 0 := by simp [color, P, hbP]
      rcases hcolor_a with ⟨k, hk⟩
      rw [hk, hcolor_b] at hsame
      exact Fin.succ_ne_zero k hsame
    · have hsame_R :
          eR ⟨a, (hR_notP a).mpr haP⟩ =
            eR ⟨b, (hR_notP b).mpr hbP⟩ := by
        have hsame_succ :
            Fin.succ (eR ⟨a, (hR_notP a).mpr haP⟩) =
              Fin.succ (eR ⟨b, (hR_notP b).mpr hbP⟩) := by
          simpa [color, P, haP, hbP] using hsame
        exact (Fin.succ_injective 3) hsame_succ
      have hab_eq : a = b := by
        exact congrArg Subtype.val (eR.injective hsame_R)
      exact hab.ne hab_eq

theorem colorable_four_of_card_le_five_of_not_complete
    {G : SimpleGraph V}
    [Fintype V]
    (h_card : Fintype.card V <= 5)
    (h_not_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    G.Colorable 4 := by
  classical
  push Not at h_not_complete
  obtain ⟨u, v, huv, h_not_adj⟩ := h_not_complete
  exact colorable_four_of_card_le_five_of_nonadjacent u v huv h_not_adj h_card

theorem card_gt_five_of_not_colorable_four_of_not_complete
    {G : SimpleGraph V}
    [Fintype V]
    (h_not_colorable : Not (G.Colorable 4))
    (h_not_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    5 < Fintype.card V := by
  by_contra hcard
  have hcard_le : Fintype.card V <= 5 := by omega
  exact h_not_colorable
    (colorable_four_of_card_le_five_of_not_complete
      (G := G) hcard_le h_not_complete)

end Schematic.Math.GraphTheory
