import Schematic.Math.GraphTheory.Basic

/-!
Definitions and elementary consequences of finite vertex connectivity.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def IsKConnected {V : Type u} (G : SimpleGraph V) (k : Nat) : Prop :=
  k < Nat.card V ∧ forall S : Set V, S.ncard < k -> (G.induce Sᶜ).Connected

abbrev IsTwoConnected (G : SimpleGraph V) : Prop := IsKConnected G 2
abbrev IsThreeConnected (G : SimpleGraph V) : Prop := IsKConnected G 3
abbrev IsFourConnected (G : SimpleGraph V) : Prop := IsKConnected G 4

theorem IsKConnected.mono
    {k l : Nat}
    (hkl : k <= l)
    (hG : IsKConnected G l) :
    IsKConnected G k := by
  refine ⟨lt_of_le_of_lt hkl hG.1, ?_⟩
  intro S hS
  exact hG.2 S (lt_of_lt_of_le hS hkl)

theorem IsKConnected.connected
    {k : Nat}
    (hG : IsKConnected G k)
    (hk : 0 < k) :
    G.Connected := by
  have h_empty : (G.induce ((∅ : Set V)ᶜ)).Connected :=
    hG.2 (∅ : Set V) (by simpa using hk)
  exact {
    preconnected := by
      intro u v
      let u' : ((∅ : Set V)ᶜ : Set V) := ⟨u, by simp⟩
      let v' : ((∅ : Set V)ᶜ : Set V) := ⟨v, by simp⟩
      exact (h_empty u' v').map (SimpleGraph.Embedding.induce ((∅ : Set V)ᶜ)).toHom
    nonempty := by
      obtain ⟨u⟩ := h_empty.nonempty
      exact ⟨u⟩
  }

/-- Every vertex of a finite `k`-connected graph has degree at least `k`.
Deleting all of a lower-degree vertex's neighbors would leave that vertex
isolated from another surviving vertex. -/
theorem IsKConnected.degree_atLeast
    [Fintype V] [DecidableRel G.Adj]
    {k : Nat}
    (hG : IsKConnected G k)
    (v : V) :
    k <= G.degree v := by
  classical
  by_contra hlt
  have hdeg_lt : G.degree v < k := Nat.lt_of_not_ge hlt
  let N : Set V := G.neighborSet v
  have hNcard : N.ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hN_lt : N.ncard < k := by
    rw [hNcard]
    exact hdeg_lt
  let S : Set V := insert v N
  have hS_card : S.ncard <= k := by
    calc
      S.ncard <= N.ncard + 1 := Set.ncard_insert_le v N
      _ = G.degree v + 1 := by rw [hNcard]
      _ <= k := hdeg_lt
  have hS_ne_univ : S ≠ Set.univ := by
    intro hS
    have hcard_le : Nat.card V <= k := by
      rw [← Set.ncard_univ V, ← hS]
      exact hS_card
    exact (Nat.not_lt_of_ge hcard_le) hG.1
  have hnot_forall : ¬ forall w : V, w ∈ S := by
    intro hall
    exact hS_ne_univ (Set.eq_univ_iff_forall.mpr hall)
  obtain ⟨w, hwS⟩ := not_forall.mp hnot_forall
  have hw_ne_v : w ≠ v := by
    intro hwv
    apply hwS
    rw [hwv]
    exact Set.mem_insert v N
  have hw_not_N : w ∉ N := by
    intro hwN
    exact hwS (Set.mem_insert_of_mem v hwN)
  have hconn := hG.2 N hN_lt
  let vv : (Nᶜ : Set V) := ⟨v, by simp [N]⟩
  let ww : (Nᶜ : Set V) := ⟨w, hw_not_N⟩
  have hvw_ne : vv ≠ ww := by
    intro h
    exact hw_ne_v (congrArg Subtype.val h).symm
  have hneigh_empty : (G.induce Nᶜ).neighborSet vv = ∅ := by
    ext x
    constructor
    · intro hx
      exact False.elim (x.2 hx)
    · intro hx
      exact False.elim (Set.notMem_empty x hx)
  exact not_reachable_of_neighborSet_left_eq_empty hvw_ne hneigh_empty
    (hconn vv ww)

theorem not_isKConnected_exists_small_cut
    {k : Nat}
    (hcard : k < Nat.card V)
    (hnot : ¬ IsKConnected G k) :
    Exists fun S : Set V => S.ncard < k ∧ Not ((G.induce Sᶜ).Connected) := by
  by_contra hnone
  apply hnot
  refine ⟨hcard, ?_⟩
  intro S hS
  by_contra hdisc
  exact hnone ⟨S, hS, hdisc⟩

theorem not_isTwoConnected_exists_small_cut
    (hcard : 2 < Nat.card V)
    (hnot : ¬ IsTwoConnected G) :
    Exists fun S : Set V => S.ncard < 2 ∧ Not ((G.induce Sᶜ).Connected) := by
  exact not_isKConnected_exists_small_cut hcard hnot

theorem SimpleGraph.Connected.map_of_adj_eq_or_adj
    {W : Type*} {H : SimpleGraph W}
    (hG : G.Connected)
    (f : V → W)
    (hf :
      forall {x y : V}, G.Adj x y →
        f x = f y ∨ H.Adj (f x) (f y))
    (hsurj : Function.Surjective f) :
    H.Connected := by
  refine {
    preconnected := ?_
    nonempty := hG.nonempty.map f
  }
  intro x y
  obtain ⟨u, rfl⟩ := hsurj x
  obtain ⟨v, rfl⟩ := hsurj y
  obtain ⟨p⟩ := hG u v
  induction p with
  | nil =>
      exact Reachable.rfl
  | cons huv p ih =>
      rcases hf huv with hsame | hadj
      · rw [hsame]
        exact ih
      · exact hadj.reachable.trans ih

theorem connected_induce_univ_of_connected
    (hG : G.Connected) :
    (G.induce Set.univ).Connected :=
  (SimpleGraph.induceUnivIso G).connected_iff.mpr hG

theorem not_isTwoConnected_exists_cutVertex_of_connected
    [Fintype V]
    (hconn : G.Connected)
    (hcard : 2 < Nat.card V)
    (hnot : ¬ IsTwoConnected G) :
    Exists fun v : V => Not ((G.induce ({v} : Set V)ᶜ).Connected) := by
  classical
  rcases not_isTwoConnected_exists_small_cut (G := G) hcard hnot with
    ⟨S, hS_lt, hS_disc⟩
  have hS_le_one : S.ncard <= 1 := by
    omega
  rcases (Set.ncard_le_one_iff_eq (s := S)).mp hS_le_one with
    hS_empty | ⟨v, hS_singleton⟩
  · rw [hS_empty] at hS_disc
    have hconn_delete : (G.induce ((∅ : Set V)ᶜ)).Connected := by
      have hcompl : ((∅ : Set V)ᶜ) = Set.univ := by
        ext z
        simp
      rw [hcompl]
      exact connected_induce_univ_of_connected (G := G) hconn
    exact False.elim (hS_disc hconn_delete)
  · rw [hS_singleton] at hS_disc
    exact ⟨v, hS_disc⟩

theorem not_isTwoConnected_exists_cutVertex_ne_root_of_connected
    [Fintype V]
    {root : V}
    (hconn : G.Connected)
    (hcard : 2 < Nat.card V)
    (hroot_connected : (G.induce (({root} : Set V)ᶜ)).Connected)
    (hnot : ¬ IsTwoConnected G) :
    Exists fun v : V =>
      v ≠ root ∧ Not ((G.induce ({v} : Set V)ᶜ).Connected) := by
  classical
  rcases
      not_isTwoConnected_exists_cutVertex_of_connected
        (G := G) hconn hcard hnot with
    ⟨v, hvcut⟩
  by_cases hvroot : v = root
  · subst v
    exact False.elim (hvcut hroot_connected)
  · exact ⟨v, hvroot, hvcut⟩

theorem natCard_gt_two_of_nonempty_min_degree_two
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (hdegree : forall v : V, 2 <= G.degree v) :
    2 < Nat.card V := by
  classical
  let v : V := Classical.choice inferInstance
  have hneigh_large : 1 < (G.neighborSet v).ncard := by
    have hdegree_card :
        (G.neighborSet v).ncard = G.degree v := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    have hvdegree : 2 <= G.degree v := hdegree v
    omega
  rcases (Set.one_lt_ncard_iff (s := G.neighborSet v)).mp hneigh_large with
    ⟨a, b, ha, hb, hab⟩
  have hva : v ≠ a := ha.ne
  have hvb : v ≠ b := hb.ne
  have htri : ({v, a, b} : Set V).ncard = 3 := by
    simp [hva, hvb, hab]
  have hle :
      ({v, a, b} : Set V).ncard <= (Set.univ : Set V).ncard :=
    Set.ncard_le_ncard (by
      intro x _hx
      exact Set.mem_univ x)
  have huniv : (Set.univ : Set V).ncard = Nat.card V := by
    simp
  omega

theorem natCard_gt_two_of_min_degree_two_away_from_root
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {root : V}
    (hne : Exists fun v : V => v ≠ root)
    (hdegree : forall v : V, v ≠ root -> 2 <= G.degree v) :
    2 < Nat.card V := by
  classical
  rcases hne with ⟨v, hvroot⟩
  have hneigh_large : 1 < (G.neighborSet v).ncard := by
    have hdegree_card :
        (G.neighborSet v).ncard = G.degree v := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    have hvdegree : 2 <= G.degree v := hdegree v hvroot
    omega
  rcases (Set.one_lt_ncard_iff (s := G.neighborSet v)).mp hneigh_large with
    ⟨a, b, ha, hb, hab⟩
  have hva : v ≠ a := ha.ne
  have hvb : v ≠ b := hb.ne
  have htri : ({v, a, b} : Set V).ncard = 3 := by
    simp [hva, hvb, hab]
  have hle :
      ({v, a, b} : Set V).ncard <= (Set.univ : Set V).ncard :=
    Set.ncard_le_ncard (by
      intro x _hx
      exact Set.mem_univ x)
  have huniv : (Set.univ : Set V).ncard = Nat.card V := by
    simp
  omega

end Schematic.Math.GraphTheory
