import Schematic.Math.GraphTheory.Connectivity.Components
import Schematic.Math.GraphTheory.Separations

/-!
Connectivity criteria expressed through vertex deletions and separations.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem Separation.separator_nonempty_of_connected
    (S : Separation G)
    (hG : G.Connected)
    (hproper : S.Proper) :
    S.separator.Nonempty := by
  classical
  rcases hproper with ⟨hleft_only, hright_only⟩
  obtain ⟨a, ha_left, ha_not_right⟩ := hleft_only
  obtain ⟨b, hb_right, hb_not_left⟩ := hright_only
  have hleft_only_compl_nonempty : (S.left \ S.right)ᶜ.Nonempty := by
    exact ⟨b, by
      intro hb
      exact hb_not_left hb.1⟩
  obtain ⟨u, hu_left_only, v, hv_not_left_only, huv⟩ :=
    Connected.exists_adjacent_crossing (G := G) hG
      (S := S.left \ S.right)
      ⟨a, ha_left, ha_not_right⟩ hleft_only_compl_nonempty
  have hu_left : u ∈ S.left := hu_left_only.1
  have hu_not_right : u ∉ S.right := hu_left_only.2
  have hv_cover : v ∈ S.left ∪ S.right := by
    rw [S.covers]
    exact Set.mem_univ v
  rcases hv_cover with hv_left | hv_right
  · have hv_right : v ∈ S.right := by
      by_contra hv_not_right
      exact hv_not_left_only ⟨hv_left, hv_not_right⟩
    exact ⟨v, hv_left, hv_right⟩
  · by_cases hv_left : v ∈ S.left
    · exact ⟨v, hv_left, hv_right⟩
    · exact False.elim (S.no_cross hu_left hu_not_right hv_right hv_left huv)

theorem Separation.exists_unique_separator_of_connected_orderAtMost_one
    (S : Separation G)
    (hG : G.Connected)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 1) :
    Exists fun x : V =>
      x ∈ S.left ∧ x ∈ S.right ∧
        forall y : V, y ∈ S.left -> y ∈ S.right -> y = x := by
  classical
  obtain ⟨x, hx_left, hx_right⟩ :=
    S.separator_nonempty_of_connected hG hproper
  rcases horder with ⟨F, hF, hcard⟩
  have hF_subsingleton :
      forall {a b : V}, a ∈ F -> b ∈ F -> a = b :=
    Finset.card_le_one_iff.mp hcard
  refine ⟨x, hx_left, hx_right, ?_⟩
  intro y hy_left hy_right
  have hyF : y ∈ F := by
    have hySep : y ∈ S.separator := ⟨hy_left, hy_right⟩
    change y ∈ (F : Set V)
    rw [hF]
    exact hySep
  have hxF : x ∈ F := by
    have hxSep : x ∈ S.separator := ⟨hx_left, hx_right⟩
    change x ∈ (F : Set V)
    rw [hF]
    exact hxSep
  exact hF_subsingleton
    hyF hxF

theorem Separation.induce_left_connected_of_connected_unique_separator
    (S : Separation G)
    (hG : G.Connected)
    {sep : V}
    (hsep_left : sep ∈ S.left)
    (hseparator_unique : forall x : V, x ∈ S.left -> x ∈ S.right -> x = sep) :
    (G.induce S.left).Connected := by
  classical
  let sep' : S.left := ⟨sep, hsep_left⟩
  have hreach_sep :
      forall u : S.left, (G.induce S.left).Reachable u sep' := by
    intro u
    by_contra hnot
    let C : Set V :=
      {x | Exists fun hx : x ∈ S.left =>
        (G.induce S.left).Reachable u ⟨x, hx⟩}
    have huC : (u : V) ∈ C := by
      exact ⟨u.2, SimpleGraph.Reachable.refl u⟩
    have hsep_not_C : sep ∉ C := by
      rintro ⟨hsep_left', hreach⟩
      exact hnot (by
        simpa [sep'] using hreach)
    have hC_compl_nonempty : Cᶜ.Nonempty := ⟨sep, hsep_not_C⟩
    obtain ⟨a, haC, b, hbC, hab⟩ :=
      Connected.exists_adjacent_crossing (G := G) hG
        (S := C) ⟨u, huC⟩ hC_compl_nonempty
    have haC_full : a ∈ C := haC
    rcases haC with ⟨ha_left, ha_reach⟩
    have ha_not_right : a ∉ S.right := by
      intro ha_right
      have ha_eq_sep : a = sep := hseparator_unique a ha_left ha_right
      exact hsep_not_C (by simpa [ha_eq_sep] using haC_full)
    have hb_cover : b ∈ S.left ∪ S.right := by
      rw [S.covers]
      exact Set.mem_univ b
    rcases hb_cover with hb_left | hb_right
    · exact hbC ⟨hb_left, ha_reach.trans (SimpleGraph.Adj.reachable (by
        exact hab))⟩
    · by_cases hb_left : b ∈ S.left
      · exact hbC ⟨hb_left, ha_reach.trans (SimpleGraph.Adj.reachable (by
          exact hab))⟩
      · exact S.no_cross ha_left ha_not_right hb_right hb_left hab
  refine {
    preconnected := ?_
    nonempty := ⟨sep'⟩
  }
  intro u v
  exact (hreach_sep u).trans (hreach_sep v).symm

theorem Separation.induce_right_connected_of_connected_unique_separator
    (S : Separation G)
    (hG : G.Connected)
    {sep : V}
    (hsep_right : sep ∈ S.right)
    (hseparator_unique : forall x : V, x ∈ S.left -> x ∈ S.right -> x = sep) :
    (G.induce S.right).Connected := by
  classical
  let S' := S.symm
  have hunique' :
      forall x : V, x ∈ S'.left -> x ∈ S'.right -> x = sep := by
    intro x hx_left hx_right
    exact hseparator_unique x hx_right hx_left
  exact S'.induce_left_connected_of_connected_unique_separator
    hG hsep_right hunique'

theorem Separation.adj_mem_right_of_mem_right_not_left
    (S : Separation G)
    {v w : V}
    (hv_right : v ∈ S.right)
    (hv_not_left : v ∉ S.left)
    (hvw : G.Adj v w) :
    w ∈ S.right := by
  have hw_cover : w ∈ S.left ∪ S.right := by
    rw [S.covers]
    exact Set.mem_univ w
  rcases hw_cover with hw_left | hw_right
  · by_cases hw_right : w ∈ S.right
    · exact hw_right
    · exact False.elim (S.no_cross hw_left hw_right hv_right hv_not_left hvw.symm)
  · exact hw_right

theorem Separation.adj_mem_left_of_mem_left_not_right
    (S : Separation G)
    {v w : V}
    (hv_left : v ∈ S.left)
    (hv_not_right : v ∉ S.right)
    (hvw : G.Adj v w) :
    w ∈ S.left :=
  S.symm.adj_mem_right_of_mem_right_not_left hv_left hv_not_right hvw

theorem Separation.walk_hits_other_of_separator_pair_of_avoids_one
    (S : Separation G)
    {x y a b : V}
    (hseparator : S.separator = ({x, y} : Set V))
    (ha_left : a ∈ S.left)
    (hb_right_only : b ∈ S.right \ S.left)
    (p : G.Walk a b)
    (hy_not_support : y ∉ p.support) :
    x ∈ p.support := by
  classical
  obtain ⟨d, hd_mem, hd_left, hd_not_left⟩ :=
    p.exists_boundary_dart S.left ha_left hb_right_only.2
  have hd_snd_right : d.snd ∈ S.right := by
    exact S.mem_right_of_not_mem_left hd_not_left
  have hd_fst_right : d.fst ∈ S.right := by
    by_contra hd_fst_not_right
    exact S.no_cross hd_left hd_fst_not_right hd_snd_right hd_not_left d.2
  have hd_fst_sep : d.fst ∈ S.separator := ⟨hd_left, hd_fst_right⟩
  have hfst_pair : d.fst = x ∨ d.fst = y := by
    have : d.fst ∈ ({x, y} : Set V) := by
      simpa [hseparator] using hd_fst_sep
    simpa using this
  have hfst_support : d.fst ∈ p.support :=
    p.dart_fst_mem_support_of_mem_darts hd_mem
  rcases hfst_pair with hfst_x | hfst_y
  · simpa [hfst_x] using hfst_support
  · exact False.elim (hy_not_support (by simpa [hfst_y] using hfst_support))

theorem Separation.degree_induce_right_eq_of_mem_right_not_left
    [Fintype V] [DecidableRel G.Adj]
    (S : Separation G)
    [Fintype S.right] [DecidableRel (G.induce S.right).Adj]
    {v : V}
    (hv_right : v ∈ S.right)
    (hv_not_left : v ∉ S.left) :
    (G.induce S.right).degree ⟨v, hv_right⟩ = G.degree v := by
  classical
  let e : (G.induce S.right).neighborSet ⟨v, hv_right⟩ ≃ G.neighborSet v := {
    toFun := fun w => ⟨w, by exact w.2⟩
    invFun := fun w =>
      ⟨⟨w, S.adj_mem_right_of_mem_right_not_left hv_right hv_not_left w.2⟩, by
        exact w.2⟩
    left_inv := by
      intro w
      rfl
    right_inv := by
      intro w
      rfl
  }
  have hcard := Fintype.card_congr e
  rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
  rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
  exact hcard

theorem Separation.degree_induce_left_eq_of_mem_left_not_right
    [Fintype V] [DecidableRel G.Adj]
    (S : Separation G)
    [Fintype S.left] [DecidableRel (G.induce S.left).Adj]
    {v : V}
    (hv_left : v ∈ S.left)
    (hv_not_right : v ∉ S.right) :
    (G.induce S.left).degree ⟨v, hv_left⟩ = G.degree v := by
  letI : Fintype S.symm.right := inferInstanceAs (Fintype S.left)
  letI : DecidableRel (G.induce S.symm.right).Adj :=
    inferInstanceAs (DecidableRel (G.induce S.left).Adj)
  exact S.symm.degree_induce_right_eq_of_mem_right_not_left hv_left hv_not_right

theorem Separation.left_only_ncard_ge_two_of_min_degree_four_orderAtMost_three
    [Fintype V] [DecidableRel G.Adj]
    (S : Separation G)
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 3) :
    2 <= (S.left \ S.right).ncard := by
  classical
  by_contra hlt
  have hleft_only_pos : 0 < (S.left \ S.right).ncard := by
    rcases hproper.1 with ⟨a, ha_left, ha_not_right⟩
    exact (Set.ncard_pos (s := S.left \ S.right)).mpr
      ⟨a, ha_left, ha_not_right⟩
  have hleft_only_card : (S.left \ S.right).ncard = 1 := by omega
  obtain ⟨a, ha_singleton⟩ := Set.ncard_eq_one.mp hleft_only_card
  have ha_left_only : a ∈ S.left \ S.right := by
    rw [ha_singleton]
    simp
  have hneighbor_subset : G.neighborSet a ⊆ S.separator := by
    intro w haw
    have hw_cover : w ∈ S.left ∪ S.right := by
      rw [S.covers]
      exact Set.mem_univ w
    rcases hw_cover with hw_left | hw_right
    · by_cases hw_right : w ∈ S.right
      · exact ⟨hw_left, hw_right⟩
      · have hw_left_only : w ∈ S.left \ S.right := ⟨hw_left, hw_right⟩
        have hwa : w = a := by
          have hw_singleton : w ∈ ({a} : Set V) := by
            rw [← ha_singleton]
            exact hw_left_only
          exact Set.mem_singleton_iff.mp hw_singleton
        exact False.elim (haw.ne hwa.symm)
    · by_cases hw_left : w ∈ S.left
      · exact ⟨hw_left, hw_right⟩
      · exact False.elim
          (S.no_cross ha_left_only.1 ha_left_only.2 hw_right hw_left haw)
  have hneighbor_ncard_le_separator :
      (G.neighborSet a).ncard <= S.separator.ncard :=
    Set.ncard_le_ncard hneighbor_subset
  have hseparator_le_three : S.separator.ncard <= 3 :=
    S.separator_ncard_le_of_orderAtMost horder
  have hdegree_eq : (G.neighborSet a).ncard = G.degree a := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hdegree_le_three : G.degree a <= 3 := by omega
  have hdegree_ge_four : 4 <= G.degree a := hmin_degree a
  omega

theorem Separation.right_only_ncard_ge_two_of_min_degree_four_orderAtMost_three
    [Fintype V] [DecidableRel G.Adj]
    (S : Separation G)
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 3) :
    2 <= (S.right \ S.left).ncard := by
  simpa [Separation.symm] using
    S.symm.left_only_ncard_ge_two_of_min_degree_four_orderAtMost_three
      hmin_degree ((S.proper_symm).mpr hproper)
      ((S.orderAtMost_symm 3).mpr horder)

theorem degree_le_induce_compl_degree_add_ncard
    [Fintype V] [DecidableRel G.Adj]
    (A : Set V)
    [Fintype (Aᶜ : Set V)] [DecidableRel (G.induce Aᶜ).Adj]
    {v : V}
    (hv : v ∈ Aᶜ) :
    G.degree v <= (G.induce Aᶜ).degree ⟨v, hv⟩ + A.ncard := by
  classical
  let outsideNeighbors : Set V := {w | w ∈ Aᶜ ∧ G.Adj v w}
  have hneighbor_subset :
      G.neighborSet v ⊆ A ∪ outsideNeighbors := by
    intro w hw
    by_cases hwA : w ∈ A
    · exact Or.inl hwA
    · exact Or.inr ⟨hwA, hw⟩
  letI : Fintype outsideNeighbors := outsideNeighbors.toFinite.fintype
  let e : outsideNeighbors ≃ (G.induce Aᶜ).neighborSet ⟨v, hv⟩ := {
    toFun := fun w => ⟨⟨w, w.2.1⟩, w.2.2⟩
    invFun := fun w => ⟨w, w.1.2, w.2⟩
    left_inv := by
      intro w
      rfl
    right_inv := by
      intro w
      rfl
  }
  have houtside_card :
      outsideNeighbors.ncard = (G.induce Aᶜ).degree ⟨v, hv⟩ := by
    rw [← Set.fintypeCard_eq_ncard]
    rw [Fintype.card_congr e]
    rw [SimpleGraph.card_neighborSet_eq_degree]
  have hdegree_card : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hle_union :
      (G.neighborSet v).ncard <= (A ∪ outsideNeighbors).ncard :=
    Set.ncard_le_ncard hneighbor_subset
  have hunion_le :
      (A ∪ outsideNeighbors).ncard <= A.ncard + outsideNeighbors.ncard :=
    Set.ncard_union_le A outsideNeighbors
  omega

theorem degree_le_induce_compl_degree_add_neighbor_inter_ncard
    [Fintype V] [DecidableRel G.Adj]
    (A : Set V)
    [Fintype (Aᶜ : Set V)] [DecidableRel (G.induce Aᶜ).Adj]
    {v : V}
    (hv : v ∈ Aᶜ) :
    G.degree v <=
      (G.induce Aᶜ).degree ⟨v, hv⟩ + (G.neighborSet v ∩ A).ncard := by
  classical
  let outsideNeighbors : Set V := {w | w ∈ Aᶜ ∧ G.Adj v w}
  have hneighbor_subset :
      G.neighborSet v ⊆ outsideNeighbors ∪ (G.neighborSet v ∩ A) := by
    intro w hw
    by_cases hwA : w ∈ A
    · exact Or.inr ⟨hw, hwA⟩
    · exact Or.inl ⟨hwA, hw⟩
  letI : Fintype outsideNeighbors := outsideNeighbors.toFinite.fintype
  let e : outsideNeighbors ≃ (G.induce Aᶜ).neighborSet ⟨v, hv⟩ := {
    toFun := fun w => ⟨⟨w, w.2.1⟩, w.2.2⟩
    invFun := fun w => ⟨w, w.1.2, w.2⟩
    left_inv := by
      intro w
      rfl
    right_inv := by
      intro w
      rfl
  }
  have houtside_card :
      outsideNeighbors.ncard = (G.induce Aᶜ).degree ⟨v, hv⟩ := by
    rw [← Set.fintypeCard_eq_ncard]
    rw [Fintype.card_congr e]
    rw [SimpleGraph.card_neighborSet_eq_degree]
  have hdegree_card : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  have hle_union :
      (G.neighborSet v).ncard <=
        (outsideNeighbors ∪ (G.neighborSet v ∩ A)).ncard :=
    Set.ncard_le_ncard hneighbor_subset
  have hunion_le :
      (outsideNeighbors ∪ (G.neighborSet v ∩ A)).ncard <=
        outsideNeighbors.ncard + (G.neighborSet v ∩ A).ncard :=
    Set.ncard_union_le outsideNeighbors (G.neighborSet v ∩ A)
  omega

/-- Deleting vertices from the top subgraph is the same graph as inducing on the complement. -/
def deleteVertsTopIsoInduceCompl (G : SimpleGraph V) (S : Set V) :
    (((⊤ : G.Subgraph).deleteVerts S).coe) ≃g (G.induce Sᶜ) where
  toFun := fun x =>
    ⟨x, by
      rcases x with ⟨x, hx⟩
      have hx' : x ∈ (Set.univ : Set V) \ S := by
        simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hx
      exact hx'.2⟩
  invFun := fun x =>
    ⟨x, by
      rcases x with ⟨x, hx⟩
      rw [SimpleGraph.Subgraph.deleteVerts_verts]
      exact ⟨by simp, hx⟩⟩
  left_inv := by
    intro x
    rfl
  right_inv := by
    intro x
    rfl
  map_rel_iff' := by
    intro x y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    have hx_not : x ∉ S := by
      have hx' : x ∈ (Set.univ : Set V) \ S := by
        simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hx
      exact hx'.2
    have hy_not : y ∉ S := by
      have hy' : y ∈ (Set.univ : Set V) \ S := by
        simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hy
      exact hy'.2
    change G.Adj x y ↔ ((⊤ : G.Subgraph).deleteVerts S).Adj x y
    rw [SimpleGraph.Subgraph.deleteVerts_adj]
    simp [hx_not, hy_not]

theorem connected_deleteVerts_top_iff_induce_compl (S : Set V) :
    (((⊤ : G.Subgraph).deleteVerts S).coe).Connected ↔
      (G.induce Sᶜ).Connected :=
  (deleteVertsTopIsoInduceCompl G S).connected_iff

theorem not_kplusone_connected_has_small_disconnected_deletion
    [Fintype V]
    (k : Nat)
    (h_card : k + 1 < Nat.card V)
    (h_not : Not (IsKConnected G (k + 1))) :
    Exists fun S : Set V => S.ncard <= k ∧ Not ((G.induce Sᶜ).Connected) := by
  classical
  have hfail :
      Not (forall S : Set V, S.ncard < k + 1 -> (G.induce Sᶜ).Connected) := by
    intro hconn
    exact h_not ⟨h_card, hconn⟩
  obtain ⟨S, hS⟩ := not_forall.mp hfail
  have hS' := Classical.not_imp.mp hS
  exact ⟨S, Nat.lt_succ_iff.mp hS'.1, hS'.2⟩

theorem disconnected_deletion_has_proper_separation_subset
    [Fintype V]
    (S : Set V)
    (hS_nontrivial : 1 < Sᶜ.ncard)
    (h_disc : Not ((G.induce Sᶜ).Connected)) :
    Exists fun T : Separation G =>
      T.Proper ∧ T.separator ⊆ S ∧ T.OrderAtMost S.ncard := by
  classical
  obtain ⟨x, hxS, y, hyS, hxy_ne⟩ := (Set.one_lt_ncard (s := Sᶜ)).mp hS_nontrivial
  let x' : (Sᶜ : Set V) := ⟨x, hxS⟩
  haveI : Nonempty (Sᶜ : Set V) := ⟨x'⟩
  have h_not_preconnected : Not ((G.induce Sᶜ).Preconnected) := by
    intro hconn
    exact h_disc ⟨hconn⟩
  obtain ⟨u, hu⟩ := not_forall.mp h_not_preconnected
  obtain ⟨v, huv⟩ := not_forall.mp hu
  let C : Set V :=
    {z | Exists fun hz : z ∈ Sᶜ =>
      (G.induce Sᶜ).Reachable u ⟨z, hz⟩}
  have huC : (u : V) ∈ C := by
    exact ⟨u.2, SimpleGraph.Reachable.rfl⟩
  have hv_not_C : (v : V) ∉ C := by
    rintro ⟨hvS, hvreach⟩
    exact huv (by simpa using hvreach)
  refine ⟨
    { left := S ∪ C
      right := S ∪ Cᶜ
      covers := by
        ext z
        by_cases hzS : z ∈ S <;> by_cases hzC : z ∈ C <;> simp [hzS, hzC]
      no_cross := ?_ },
    ?_,
    ?_,
    ?_⟩
  · intro a b ha han hb hbn hab
    have ha_not_S : a ∉ S := by
      intro haS
      exact han (Or.inl haS)
    have haC : a ∈ C := by
      rcases ha with haS | haC
      · exact False.elim (ha_not_S haS)
      · exact haC
    have hb_not_S : b ∉ S := by
      intro hbS
      exact hbn (Or.inl hbS)
    have hb_not_C : b ∉ C := by
      intro hbC
      exact hbn (Or.inr hbC)
    rcases haC with ⟨haS, hua⟩
    have hbS : b ∈ Sᶜ := hb_not_S
    have hab' : (G.induce Sᶜ).Adj ⟨a, haS⟩ ⟨b, hbS⟩ := by
      simpa using hab
    exact hb_not_C ⟨hbS, hua.trans hab'.reachable⟩
  · constructor
    · refine ⟨(u : V), ?_, ?_⟩
      · exact Or.inr huC
      · intro hur
        rcases hur with huS | hu_not_C
        · exact u.2 huS
        · exact hu_not_C huC
    · refine ⟨(v : V), ?_, ?_⟩
      · exact Or.inr hv_not_C
      · intro hvl
        rcases hvl with hvS | hvC
        · exact v.2 hvS
        · exact hv_not_C hvC
  · intro z hz
    simp only [Separation.separator, Set.mem_inter_iff, Set.mem_union,
      Set.mem_compl_iff] at hz
    rcases hz with ⟨hzl, hzr⟩
    rcases hzl with hzS | hzC
    · exact hzS
    · rcases hzr with hzS | hz_not_C
      · exact hzS
      · exact False.elim (hz_not_C hzC)
  · refine ⟨S.toFinite.toFinset, ?_, ?_⟩
    rw [S.toFinite.coe_toFinset]
    ext z
    simp only [Separation.separator, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    constructor
    · intro hzS
      exact ⟨Or.inl hzS, Or.inl hzS⟩
    · intro hz
      rcases hz with ⟨hzl, hzr⟩
      rcases hzl with hzS | hzC
      · exact hzS
      · rcases hzr with hzS | hz_not_C
        · exact hzS
        · exact False.elim (hz_not_C hzC)
    · rw [← Set.ncard_eq_toFinset_card S S.toFinite]

theorem disconnected_deletion_has_proper_separation
    [Fintype V]
    (S : Set V)
    (hS_nontrivial : 1 < Sᶜ.ncard)
    (h_disc : Not ((G.induce Sᶜ).Connected)) :
    Exists fun T : Separation G => T.Proper ∧ T.OrderAtMost S.ncard := by
  obtain ⟨T, hproper, _hsubset, horder⟩ :=
    disconnected_deletion_has_proper_separation_subset (G := G) S hS_nontrivial h_disc
  exact ⟨T, hproper, horder⟩

theorem not_kplusone_connected_has_proper_small_separation
    [Fintype V]
    (k : Nat)
    (h_card : k + 1 < Nat.card V)
    (h_not : Not (IsKConnected G (k + 1))) :
    Exists fun S : Separation G => S.Proper ∧ S.OrderAtMost k := by
  classical
  obtain ⟨S, hS_card, hS_disc⟩ :=
    not_kplusone_connected_has_small_disconnected_deletion (G := G) k h_card h_not
  have h_compl_large : 1 < Sᶜ.ncard := by
    have hsum : S.ncard + Sᶜ.ncard = Nat.card V := by
      simpa [Set.ncard_univ] using Set.ncard_add_ncard_compl S
    omega
  obtain ⟨T, hT_proper, hT_order⟩ :=
    disconnected_deletion_has_proper_separation (G := G) S h_compl_large hS_disc
  exact ⟨T, hT_proper, T.orderAtMost_mono hT_order hS_card⟩

theorem isKConnected_no_proper_separation_orderAtMost
    [Fintype V]
    {k : Nat}
    (hG : IsKConnected G (k + 1))
    (S : Separation G)
    (hproper : S.Proper)
    (horder : S.OrderAtMost k) :
    False := by
  classical
  rcases hproper with ⟨⟨a, ha_left, ha_not_right⟩, ⟨b, hb_right, hb_not_left⟩⟩
  have ha_sep_compl : a ∈ S.separatorᶜ := by
    intro ha_sep
    exact ha_not_right ha_sep.2
  have hb_sep_compl : b ∈ S.separatorᶜ := by
    intro hb_sep
    exact hb_not_left hb_sep.1
  have hsep_card : S.separator.ncard <= k := by
    rcases horder with ⟨F, hF, hcard⟩
    rw [← hF, Set.ncard_coe_finset]
    exact hcard
  have hsep_lt : S.separator.ncard < k + 1 := Nat.lt_succ_of_le hsep_card
  have hconn : (G.induce S.separatorᶜ).Connected := hG.2 S.separator hsep_lt
  let a' : (S.separatorᶜ : Set V) := ⟨a, ha_sep_compl⟩
  let b' : (S.separatorᶜ : Set V) := ⟨b, hb_sep_compl⟩
  obtain ⟨p⟩ := hconn a' b'
  let LeftInComplement : Set (S.separatorᶜ : Set V) := {x | (x : V) ∈ S.left}
  have ha_mem : a' ∈ LeftInComplement := ha_left
  have hb_not_mem : b' ∉ LeftInComplement := hb_not_left
  obtain ⟨d, hd_mem, hd_left, hd_not_left⟩ :=
    p.exists_boundary_dart LeftInComplement ha_mem hb_not_mem
  have hfst_left : (d.fst : V) ∈ S.left := hd_left
  have hfst_not_right : (d.fst : V) ∉ S.right := by
    intro hright
    exact d.fst.2 ⟨hfst_left, hright⟩
  have hsnd_not_left : (d.snd : V) ∉ S.left := hd_not_left
  have hsnd_right : (d.snd : V) ∈ S.right := by
    have hcover : (d.snd : V) ∈ S.left ∪ S.right := by
      rw [S.covers]
      exact Set.mem_univ _
    rcases hcover with hsnd_left | hsnd_right
    · exact False.elim (hsnd_not_left hsnd_left)
    · exact hsnd_right
  exact S.no_cross hfst_left hfst_not_right hsnd_right hsnd_not_left d.2

theorem isFourConnected_no_proper_separation_orderAtMost_three
    [Fintype V]
    (hG : IsFourConnected G)
    (S : Separation G)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 3) :
    False :=
  isKConnected_no_proper_separation_orderAtMost
    (G := G) (k := 3) hG S hproper horder

theorem isThreeConnected_no_proper_separation_orderAtMost_two
    [Fintype V]
    (hG : IsThreeConnected G)
    (S : Separation G)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 2) :
    False :=
  isKConnected_no_proper_separation_orderAtMost
    (G := G) (k := 2) hG S hproper horder

theorem three_connected_of_no_proper_separation_orderAtMost_two
    [Fintype V]
    (hcard : 3 < Nat.card V)
    (hno_sep :
      forall S : Separation G, S.Proper -> S.OrderAtMost 2 -> False) :
    IsThreeConnected G := by
  classical
  refine ⟨hcard, ?_⟩
  by_contra hdelete
  have hnot : Not (IsKConnected G 3) := by
    intro hG
    exact hdelete hG.2
  obtain ⟨S, hproper, horder⟩ :=
    not_kplusone_connected_has_proper_small_separation
      (G := G) 2 hcard hnot
  exact hno_sep S hproper horder

theorem IsThreeConnected.no_nonempty_set_with_small_boundary
    [Fintype V]
    (hG : IsThreeConnected G)
    {C T : Set V}
    (hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b))
    (hdisj : Disjoint C T)
    (hC : C.Nonempty)
    (houtside : (C ∪ T)ᶜ.Nonempty)
    (hT : T.ncard < 3) :
    False := by
  classical
  let S : Separation G := Separation.ofSetBoundary C T hboundary
  have hproper : S.Proper := by
    simpa [S] using
      Separation.ofSetBoundary_proper
        (G := G) hboundary hC houtside
  have horder : S.OrderAtMost 2 := by
    have hT_le : T.ncard <= 2 := by omega
    simpa [S] using
      Separation.ofSetBoundary_orderAtMost
        (G := G) hboundary hdisj hT_le
  exact isThreeConnected_no_proper_separation_orderAtMost_two
    (G := G) hG S hproper horder

theorem IsThreeConnected.no_nonempty_set_with_boundary_pair
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    {C : Set V} {u v : V}
    (hboundary_pair :
      forall {a b : V}, a ∈ C -> b ∉ C -> G.Adj a b -> b = u ∨ b = v)
    (hdisj : Disjoint C ({u, v} : Set V))
    (hC : C.Nonempty)
    (houtside : (C ∪ ({u, v} : Set V))ᶜ.Nonempty) :
    False := by
  classical
  let T : Set V := ({u, v} : Set V)
  have hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b) := by
    intro a b ha hb_not hb_not_T hab
    rcases hboundary_pair ha hb_not hab with rfl | rfl
    · exact hb_not_T (by simp [T])
    · exact hb_not_T (by simp [T])
  have hTsmall : T.ncard < 3 := by
    have hTle : T.ncard <= 2 := by
      calc
        T.ncard = ({u, v} : Set V).ncard := rfl
        _ <= ({v} : Set V).ncard + 1 := by
          exact Set.ncard_insert_le u ({v} : Set V)
        _ = 2 := by simp
    omega
  exact hG.no_nonempty_set_with_small_boundary
    hboundary (by simpa [T] using hdisj) hC
    (by simpa [T] using houtside) hTsmall

theorem isFourConnected_delete_triple_connected
    [Fintype V]
    (hG : IsFourConnected G)
    (a b c : V) :
    (G.induce ({a, b, c} : Set V)ᶜ).Connected := by
  have hpair_card : ({b, c} : Set V).ncard <= 2 := by
    calc
      ({b, c} : Set V).ncard <= ({c} : Set V).ncard + 1 := by
        simpa using Set.ncard_insert_le b ({c} : Set V)
      _ = 2 := by simp
  have htriple_card : ({a, b, c} : Set V).ncard <= 3 := by
    calc
      ({a, b, c} : Set V).ncard <= ({b, c} : Set V).ncard + 1 := by
        simpa using Set.ncard_insert_le a ({b, c} : Set V)
      _ <= 3 := by omega
  exact hG.2 ({a, b, c} : Set V) (lt_of_le_of_lt htriple_card (by decide))

theorem isFourConnected_delete_triple_top_connected
    [Fintype V]
    (hG : IsFourConnected G)
    (a b c : V) :
    (((⊤ : G.Subgraph).deleteVerts ({a, b, c} : Set V)).coe).Connected := by
  exact (connected_deleteVerts_top_iff_induce_compl
    (G := G) ({a, b, c} : Set V)).mpr
      (isFourConnected_delete_triple_connected hG a b c)

end Schematic.Math.GraphTheory
