import Schematic.Math.GraphTheory.Basic

/-!
Small separations and separator bookkeeping. These are background facts used by
the induction proof, not named results of the paper.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

structure Separation (G : SimpleGraph V) where
  left : Set V
  right : Set V
  covers : left ∪ right = Set.univ
  no_cross :
    forall {a b : V},
      a ∈ left ->
      a ∉ right ->
      b ∈ right ->
      b ∉ left ->
      Not (G.Adj a b)

namespace Separation

def separator (S : Separation G) : Set V :=
  S.left ∩ S.right

def symm (S : Separation G) : Separation G where
  left := S.right
  right := S.left
  covers := by
    rw [Set.union_comm]
    exact S.covers
  no_cross := by
    intro a b ha han hb hbn hab
    exact S.no_cross hb hbn ha han hab.symm

def Proper (S : Separation G) : Prop :=
  (S.left \ S.right).Nonempty ∧ (S.right \ S.left).Nonempty

def OrderAtMost (S : Separation G) (t : Nat) : Prop :=
  Exists fun F : Finset V => (F : Set V) = S.separator ∧ F.card <= t

def OrderEq (S : Separation G) (t : Nat) : Prop :=
  Exists fun F : Finset V => (F : Set V) = S.separator ∧ F.card = t

theorem mem_left_or_right (S : Separation G) (v : V) :
    v ∈ S.left ∨ v ∈ S.right := by
  have hv : v ∈ S.left ∪ S.right := by
    rw [S.covers]
    exact Set.mem_univ v
  exact hv

theorem mem_right_of_not_mem_left (S : Separation G) {v : V}
    (hv : v ∉ S.left) :
    v ∈ S.right :=
  (S.mem_left_or_right v).resolve_left hv

theorem mem_left_of_not_mem_right (S : Separation G) {v : V}
    (hv : v ∉ S.right) :
    v ∈ S.left :=
  (S.mem_left_or_right v).resolve_right hv

def ofSetBoundary
    (C T : Set V)
    (hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b)) :
    Separation G where
  left := C ∪ T
  right := Cᶜ
  covers := by
    classical
    ext v
    constructor
    · intro _hv
      exact Set.mem_univ v
    · intro _hv
      by_cases hvC : v ∈ C
      · exact Or.inl (Or.inl hvC)
      · exact Or.inr hvC
  no_cross := by
    classical
    intro a b ha ha_not_right hb hb_not_left hab
    have haC : a ∈ C := by
      by_contra ha_not_C
      exact ha_not_right ha_not_C
    have hb_not_C : b ∉ C := hb
    have hb_not_T : b ∉ T := by
      intro hbT
      exact hb_not_left (Or.inr hbT)
    exact hboundary haC hb_not_C hb_not_T hab

theorem ofSetBoundary_separator_eq
    {C T : Set V}
    (hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b))
    (hdisj : Disjoint C T) :
    (ofSetBoundary (G := G) C T hboundary).separator = T := by
  classical
  ext v
  constructor
  · intro hv
    change v ∈ (C ∪ T) ∩ Cᶜ at hv
    rcases hv.1 with hvC | hvT
    · exact False.elim (hv.2 hvC)
    · exact hvT
  · intro hvT
    change v ∈ (C ∪ T) ∩ Cᶜ
    exact ⟨Or.inr hvT, by
      intro hvC
      exact Set.disjoint_left.mp hdisj hvC hvT⟩

theorem ofSetBoundary_proper
    {C T : Set V}
    (hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b))
    (hC : C.Nonempty)
    (houtside : (C ∪ T)ᶜ.Nonempty) :
    (ofSetBoundary (G := G) C T hboundary).Proper := by
  classical
  rcases hC with ⟨c, hc⟩
  rcases houtside with ⟨r, hr⟩
  refine ⟨?_, ?_⟩
  · refine ⟨c, ?_, ?_⟩
    · change c ∈ C ∪ T
      exact Or.inl hc
    · change c ∉ Cᶜ
      exact fun hc_not => hc_not hc
  · refine ⟨r, ?_, ?_⟩
    · change r ∈ Cᶜ
      exact fun hrC => hr (Or.inl hrC)
    · change r ∉ C ∪ T
      exact hr

theorem ofSetBoundary_orderAtMost
    [Fintype V]
    {C T : Set V} {k : Nat}
    (hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b))
    (hdisj : Disjoint C T)
    (hT : T.ncard <= k) :
    (ofSetBoundary (G := G) C T hboundary).OrderAtMost k := by
  classical
  refine ⟨T.toFinite.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact (ofSetBoundary_separator_eq (G := G) hboundary hdisj).symm
  · rwa [← Set.ncard_eq_toFinset_card T T.toFinite]

theorem proper_symm (S : Separation G) :
    S.symm.Proper ↔ S.Proper := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, h₁⟩

theorem separator_symm (S : Separation G) :
    S.symm.separator = S.separator := by
  ext v
  simp [separator, symm, and_comm]

theorem orderAtMost_mono {S : Separation G} {a b : Nat}
    (hS : S.OrderAtMost a)
    (hab : a <= b) :
    S.OrderAtMost b := by
  rcases hS with ⟨F, hF, hcard⟩
  exact ⟨F, hF, le_trans hcard hab⟩

theorem orderEq_orderAtMost {S : Separation G} {t : Nat}
    (hS : S.OrderEq t) :
    S.OrderAtMost t := by
  rcases hS with ⟨F, hF, hcard⟩
  exact ⟨F, hF, le_of_eq hcard⟩

theorem separator_ncard_le_of_orderAtMost
    (S : Separation G) {t : Nat}
    (hS : S.OrderAtMost t) :
    S.separator.ncard <= t := by
  rcases hS with ⟨F, hF, hcard⟩
  rw [← hF, Set.ncard_coe_finset]
  exact hcard

theorem orderAtMost_of_separator_ncard_le
    [Fintype V]
    (S : Separation G) {t : Nat}
    (hS : S.separator.ncard <= t) :
    S.OrderAtMost t := by
  classical
  refine ⟨S.separator.toFinite.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
  · rwa [← Set.ncard_eq_toFinset_card S.separator S.separator.toFinite]

theorem orderAtMost_iff_separator_ncard_le
    [Fintype V]
    (S : Separation G) {t : Nat} :
    S.OrderAtMost t ↔ S.separator.ncard <= t := by
  exact ⟨S.separator_ncard_le_of_orderAtMost,
    S.orderAtMost_of_separator_ncard_le⟩

theorem separator_ncard_ge_two_of_not_orderAtMost_one
    [Fintype V]
    (S : Separation G)
    (hnot : Not (S.OrderAtMost 1)) :
    2 <= S.separator.ncard := by
  by_contra hlt
  have hle : S.separator.ncard <= 1 := by omega
  exact hnot (S.orderAtMost_of_separator_ncard_le hle)

theorem separator_ncard_ge_three_of_not_orderAtMost_two
    [Fintype V]
    (S : Separation G)
    (hnot : Not (S.OrderAtMost 2)) :
    3 <= S.separator.ncard := by
  by_contra hlt
  have hle : S.separator.ncard <= 2 := by omega
  exact hnot (S.orderAtMost_of_separator_ncard_le hle)

theorem exists_left_only_ne_of_two_left_only
    [Fintype V]
    (S : Separation G)
    (x : V)
    (hcard : 2 <= (S.left \ S.right).ncard) :
    Exists fun v : V => v ∈ S.left \ S.right ∧ v ≠ x := by
  have hlt : 1 < (S.left \ S.right).ncard := by omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Set.one_lt_ncard (s := S.left \ S.right)).mp hlt
  by_cases hax : a = x
  · exact ⟨b, hb, by
      intro hbx
      exact hab (hax.trans hbx.symm)⟩
  · exact ⟨a, ha, hax⟩

theorem exists_left_only_ne_prefer_of_two_left_only
    [Fintype V]
    (S : Separation G)
    (avoid prefer : V)
    (hcard : 2 <= (S.left \ S.right).ncard)
    (hprefer_ne : prefer ≠ avoid) :
    Exists fun v : V =>
      v ∈ S.left \ S.right ∧ v ≠ avoid ∧
        (prefer ∈ S.left \ S.right -> v = prefer) := by
  by_cases hprefer : prefer ∈ S.left \ S.right
  · exact ⟨prefer, hprefer, hprefer_ne, by intro _; rfl⟩
  · obtain ⟨v, hv, hv_ne⟩ := S.exists_left_only_ne_of_two_left_only avoid hcard
    exact ⟨v, hv, hv_ne, by intro hp; exact False.elim (hprefer hp)⟩

theorem exists_right_only_ne_of_two_right_only
    [Fintype V]
    (S : Separation G)
    (x : V)
    (hcard : 2 <= (S.right \ S.left).ncard) :
    Exists fun v : V => v ∈ S.right \ S.left ∧ v ≠ x := by
  simpa [Separation.symm] using
    S.symm.exists_left_only_ne_of_two_left_only x hcard

theorem exists_separator_pair_of_orderAtMost_two_not_orderAtMost_one
    [Fintype V]
    (S : Separation G)
    (horder_two : S.OrderAtMost 2)
    (hnot_order_one : Not (S.OrderAtMost 1)) :
    Exists fun x : V =>
      Exists fun y : V => x ≠ y ∧ S.separator = ({x, y} : Set V) := by
  have hle_two : S.separator.ncard <= 2 :=
    S.separator_ncard_le_of_orderAtMost horder_two
  have hge_two : 2 <= S.separator.ncard :=
    S.separator_ncard_ge_two_of_not_orderAtMost_one hnot_order_one
  have hcard : S.separator.ncard = 2 := le_antisymm hle_two hge_two
  simpa using (Set.ncard_eq_two.mp hcard)

theorem exists_oriented_pair_avoiding_ordered_pair
    {v1 v2 x y : V}
    (hv12 : v1 ≠ v2)
    (hxy : x ≠ y) :
    Exists fun a : V =>
      Exists fun b : V =>
        a ≠ b ∧ ({a, b} : Set V) = ({x, y} : Set V) ∧
          v1 ≠ b ∧ v2 ≠ a := by
  classical
  by_cases h_v1_y : v1 = y
  · refine ⟨y, x, hxy.symm, ?_, ?_, ?_⟩
    · ext z
      simp [Set.mem_insert_iff, or_comm]
    · intro h_v1_x
      exact hxy (h_v1_x ▸ h_v1_y)
    · intro h_v2_y
      exact hv12 (h_v1_y.trans h_v2_y.symm)
  · by_cases h_v2_x : v2 = x
    · refine ⟨y, x, hxy.symm, ?_, ?_, ?_⟩
      · ext z
        simp [Set.mem_insert_iff, or_comm]
      · intro h_v1_x
        exact hv12 (h_v1_x.trans h_v2_x.symm)
      · intro h_v2_y
        exact hxy (h_v2_x ▸ h_v2_y)
    · exact ⟨x, y, hxy, rfl, h_v1_y, h_v2_x⟩

theorem exists_separator_triple_of_orderAtMost_three_not_orderAtMost_two
    [Fintype V]
    (S : Separation G)
    (horder_three : S.OrderAtMost 3)
    (hnot_order_two : Not (S.OrderAtMost 2)) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ S.separator = ({x, y, z} : Set V) := by
  have hle_three : S.separator.ncard <= 3 :=
    S.separator_ncard_le_of_orderAtMost horder_three
  have hge_three : 3 <= S.separator.ncard :=
    S.separator_ncard_ge_three_of_not_orderAtMost_two hnot_order_two
  have hcard : S.separator.ncard = 3 := le_antisymm hle_three hge_three
  simpa using (Set.ncard_eq_three.mp hcard)

theorem separator_subset_left (S : Separation G) :
    S.separator ⊆ S.left := by
  intro v hv
  exact hv.1

theorem separator_subset_right (S : Separation G) :
    S.separator ⊆ S.right := by
  intro v hv
  exact hv.2

theorem mem_separator_of_mem_pair
    (S : Separation G)
    {x y v : V}
    (hseparator : S.separator = ({x, y} : Set V))
    (hv : v = x ∨ v = y) :
    v ∈ S.separator := by
  rw [hseparator]
  simpa using hv

theorem mem_separator_of_mem_triple
    (S : Separation G)
    {x y z v : V}
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hv : v = x ∨ v = y ∨ v = z) :
    v ∈ S.separator := by
  rw [hseparator]
  simpa [Set.mem_insert_iff] using hv

theorem triple_vertices_mem_separator
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    x ∈ S.separator ∧ y ∈ S.separator ∧ z ∈ S.separator := by
  constructor
  · exact S.mem_separator_of_mem_triple hseparator (Or.inl rfl)
  constructor
  · exact S.mem_separator_of_mem_triple hseparator (Or.inr (Or.inl rfl))
  · exact S.mem_separator_of_mem_triple hseparator (Or.inr (Or.inr rfl))

theorem triple_vertices_mem_left
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    x ∈ S.left ∧ y ∈ S.left ∧ z ∈ S.left := by
  have hmem := S.triple_vertices_mem_separator hseparator
  exact ⟨hmem.1.1, hmem.2.1.1, hmem.2.2.1⟩

theorem triple_vertices_mem_right
    (S : Separation G)
    {x y z : V}
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    x ∈ S.right ∧ y ∈ S.right ∧ z ∈ S.right := by
  have hmem := S.triple_vertices_mem_separator hseparator
  exact ⟨hmem.1.2, hmem.2.1.2, hmem.2.2.2⟩

theorem exists_nonadjacent_separator_pair_of_not_clique
    (S : Separation G)
    (hnot_clique : Not (G.IsClique S.separator)) :
    Exists fun a : V =>
      a ∈ S.separator ∧
        Exists fun b : V =>
          b ∈ S.separator ∧ a ≠ b ∧ Not (G.Adj a b) := by
  classical
  by_contra hnone
  exact hnot_clique (by
    intro a ha b hb hne
    by_contra hnot_adj
    exact hnone ⟨a, ha, b, hb, hne, hnot_adj⟩)

theorem triple_separator_isClique_of_pairwise_adj
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hxy_adj : G.Adj x y)
    (hxz_adj : G.Adj x z)
    (hyz_adj : G.Adj y z) :
    G.IsClique S.separator := by
  intro a ha b hb hab
  have ha_tri : a = x ∨ a = y ∨ a = z := by
    have : a ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using ha
    simpa [Set.mem_insert_iff] using this
  have hb_tri : b = x ∨ b = y ∨ b = z := by
    have : b ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using hb
    simpa [Set.mem_insert_iff] using this
  rcases ha_tri with rfl | rfl | rfl <;>
    rcases hb_tri with rfl | rfl | rfl
  · exact False.elim (hab rfl)
  · exact hxy_adj
  · exact hxz_adj
  · exact hxy_adj.symm
  · exact False.elim (hab rfl)
  · exact hyz_adj
  · exact hxz_adj.symm
  · exact hyz_adj.symm
  · exact False.elim (hab rfl)

theorem exists_nonadjacent_pair_of_not_clique_triple
    (S : Separation G)
    {x y z : V}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hnot_clique : Not (G.IsClique S.separator)) :
    Not (G.Adj x y) ∨ Not (G.Adj x z) ∨ Not (G.Adj y z) := by
  classical
  by_cases hxy_adj : G.Adj x y
  · by_cases hxz_adj : G.Adj x z
    · by_cases hyz_adj : G.Adj y z
      · exact False.elim
          (hnot_clique
            (S.triple_separator_isClique_of_pairwise_adj
              hxy hxz hyz hseparator hxy_adj hxz_adj hyz_adj))
      · exact Or.inr (Or.inr hyz_adj)
    · exact Or.inr (Or.inl hxz_adj)
  · exact Or.inl hxy_adj

theorem separator_ncard_eq_of_orderEq
    (S : Separation G) {t : Nat}
    (hS : S.OrderEq t) :
    S.separator.ncard = t := by
  rcases hS with ⟨F, hF, hcard⟩
  rw [← hF, Set.ncard_coe_finset, hcard]

theorem orderAtMost_symm (S : Separation G) (t : Nat) :
    S.symm.OrderAtMost t ↔ S.OrderAtMost t := by
  constructor
  · rintro ⟨F, hF, hcard⟩
    exact ⟨F, by rw [← S.separator_symm]; exact hF, hcard⟩
  · rintro ⟨F, hF, hcard⟩
    exact ⟨F, by rw [S.separator_symm]; exact hF, hcard⟩

theorem no_cross_symm (S : Separation G)
    {a b : V}
    (ha : a ∈ S.left)
    (han : a ∉ S.right)
    (hb : b ∈ S.right)
    (hbn : b ∉ S.left) :
    Not (G.Adj b a) := by
  intro h
  exact S.no_cross ha han hb hbn h.symm

def ofCoreAndBoundary
    (K B : Set V)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b)) :
    Separation G where
  left := Kᶜ
  right := K ∪ B
  covers := by
    ext v
    by_cases hvK : v ∈ K <;> simp [hvK]
  no_cross := by
    intro a b ha han hb hbn hab
    have haK : a ∉ K := ha
    have haB : a ∉ B := by
      intro haB
      exact han (Or.inr haB)
    have hbK : b ∈ K := by
      by_contra hbK
      exact hbn hbK
    exact hclosed hbK haK haB hab.symm

theorem ofCoreAndBoundary_separator_subset_boundary
    (K B : Set V)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b)) :
    (ofCoreAndBoundary (G := G) K B hclosed).separator ⊆ B := by
  intro v hv
  rcases hv.2 with hvK | hvB
  · exact False.elim (hv.1 hvK)
  · exact hvB

theorem ofCoreAndBoundary_separator_eq_boundary_of_core_subset_compl
    (K B : Set V)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    (hKB : K ⊆ Bᶜ) :
    (ofCoreAndBoundary (G := G) K B hclosed).separator = B := by
  apply Set.Subset.antisymm
  · exact ofCoreAndBoundary_separator_subset_boundary (G := G) K B hclosed
  · intro v hvB
    constructor
    · intro hvK
      exact hKB hvK hvB
    · exact Or.inr hvB

theorem ofCoreAndBoundary_orderAtMost_boundary_ncard
    [Fintype V]
    (K B : Set V)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b)) :
    (ofCoreAndBoundary (G := G) K B hclosed).OrderAtMost B.ncard := by
  classical
  refine (ofCoreAndBoundary (G := G) K B hclosed).orderAtMost_of_separator_ncard_le ?_
  exact Set.ncard_le_ncard
    (ofCoreAndBoundary_separator_subset_boundary (G := G) K B hclosed)

theorem ofCoreAndBoundary_orderAtMost_of_boundary_ncard_le
    [Fintype V]
    (K B : Set V)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    {t : Nat}
    (hB : B.ncard <= t) :
    (ofCoreAndBoundary (G := G) K B hclosed).OrderAtMost t := by
  exact (ofCoreAndBoundary (G := G) K B hclosed).orderAtMost_mono
    (ofCoreAndBoundary_orderAtMost_boundary_ncard (G := G) K B hclosed) hB

theorem ofCoreAndBoundary_right_only_nonempty
    (K B : Set V)
    (hclosed :
      forall {a b : V}, a ∈ K -> b ∉ K -> b ∉ B -> Not (G.Adj a b))
    (hK : K.Nonempty) :
    ((ofCoreAndBoundary (G := G) K B hclosed).right \
      (ofCoreAndBoundary (G := G) K B hclosed).left).Nonempty := by
  rcases hK with ⟨v, hvK⟩
  exact ⟨v, Or.inl hvK, fun hv_notK => hv_notK hvK⟩

theorem finset_clique_subset_left_or_subset_right
    (S : Separation G)
    (L : Finset V)
    (h_clique : G.IsClique (L : Set V)) :
    (forall v : V, v ∈ L -> v ∈ S.left) ∨
      (forall v : V, v ∈ L -> v ∈ S.right) := by
  classical
  by_cases hleft : forall v : V, v ∈ L -> v ∈ S.left
  · exact Or.inl hleft
  · right
    push Not at hleft
    rcases hleft with ⟨x, hxL, hx_not_left⟩
    have hx_right : x ∈ S.right := by
      have hx_cover : x ∈ S.left ∪ S.right := by
        rw [S.covers]
        exact Set.mem_univ x
      exact hx_cover.resolve_left hx_not_left
    intro y hyL
    by_contra hy_not_right
    have hy_left : y ∈ S.left := by
      have hy_cover : y ∈ S.left ∪ S.right := by
        rw [S.covers]
        exact Set.mem_univ y
      exact hy_cover.resolve_right hy_not_right
    have hy_ne_x : y ≠ x := by
      intro hyx
      exact hy_not_right (by simpa [hyx] using hx_right)
    exact S.no_cross hy_left hy_not_right hx_right hx_not_left
      (h_clique hyL hxL hy_ne_x)

theorem natCard_left_lt_of_proper
    [Fintype V]
    (S : Separation G)
    (hproper : S.Proper) :
    Nat.card S.left < Nat.card V := by
  classical
  letI : Fintype S.left := S.left.toFinite.fintype
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rcases hproper.2 with ⟨x, _hx_right, hx_not_left⟩
  exact
    (Fintype.card_subtype_lt
      (p := fun v : V => v ∈ S.left) (x := x) hx_not_left)

theorem natCard_right_lt_of_proper
    [Fintype V]
    (S : Separation G)
    (hproper : S.Proper) :
    Nat.card S.right < Nat.card V := by
  classical
  letI : Fintype S.right := S.right.toFinite.fintype
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rcases hproper.1 with ⟨x, _hx_left, hx_not_right⟩
  exact
    (Fintype.card_subtype_lt
      (p := fun v : V => v ∈ S.right) (x := x) hx_not_right)

end Separation

end Schematic.Math.GraphTheory
