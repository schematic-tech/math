import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.FinalSplices

/-! Permutation, symmetry, and avoidance transport for three-linkages. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def ThreeVertexLinkage.toPartial
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right) :
    PartialThreeVertexLinkage G left right 3 where
  leftIndex i := i
  rightIndex i := L.targetEquiv i
  leftIndex_injective := by
    intro i j h
    exact h
  rightIndex_injective := by
    intro i j h
    exact L.targetEquiv.injective h
  path i := L.path i
  isPath i := L.isPath i
  pairwise_vertex_disjoint := L.pairwise_vertex_disjoint

theorem hasPartialThreeVertexLinkage_three_iff
    {left right : Fin 3 -> V} :
    HasPartialThreeVertexLinkage G left right 3 ↔
      HasThreeVertexLinkage G left right := by
  constructor
  · rintro ⟨L⟩
    exact L.hasThreeVertexLinkage
  · rintro ⟨L⟩
    exact ⟨L.toPartial⟩

def ThreeVertexLinkage.ofRightPermutationEq
    {left right : Fin 3 -> V}
    (e : Fin 3 ≃ Fin 3)
    (hmatch : forall i : Fin 3, left i = right (e i))
    (hleft : Function.Injective left) :
    ThreeVertexLinkage G left right where
  targetEquiv := e
  path i :=
    (SimpleGraph.Walk.nil : G.Walk (left i) (left i)).copy rfl (hmatch i)
  isPath i := by
    simp
  pairwise_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    have hvi_eq : v = left i := by
      simpa using hvi
    have hvj_eq : v = left j := by
      simpa using hvj
    exact hij (hleft (hvi_eq.symm.trans hvj_eq))

theorem hasThreeVertexLinkage_of_right_permutation_eq
    {left right : Fin 3 -> V}
    (e : Fin 3 ≃ Fin 3)
    (hmatch : forall i : Fin 3, left i = right (e i))
    (hleft : Function.Injective left) :
    HasThreeVertexLinkage G left right :=
  ⟨ThreeVertexLinkage.ofRightPermutationEq e hmatch hleft⟩

noncomputable def fin3EquivOfRangeEq
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    (hrange : Set.range left = Set.range right) :
    Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (fun i : Fin 3 => Function.invFun right (left i)) <| by
    constructor
    · intro i j hij
      apply hleft
      have hi : right (Function.invFun right (left i)) = left i := by
        apply Function.invFun_eq
        rw [← Set.mem_range, ← hrange]
        exact Set.mem_range_self i
      have hj : right (Function.invFun right (left j)) = left j := by
        apply Function.invFun_eq
        rw [← Set.mem_range, ← hrange]
        exact Set.mem_range_self j
      rw [← hi, ← hj]
      exact congrArg right hij
    · intro j
      refine ⟨Function.invFun left (right j), ?_⟩
      apply hright
      have hleft_inv : left (Function.invFun left (right j)) = right j := by
        apply Function.invFun_eq
        rw [← Set.mem_range, hrange]
        exact Set.mem_range_self j
      have hright_inv :
          right (Function.invFun right
              (left (Function.invFun left (right j)))) =
            left (Function.invFun left (right j)) := by
        apply Function.invFun_eq
        rw [← Set.mem_range, ← hrange]
        exact Set.mem_range_self (Function.invFun left (right j))
      rw [hright_inv, hleft_inv]

theorem hasThreeVertexLinkage_of_range_eq
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    (hrange : Set.range left = Set.range right) :
    HasThreeVertexLinkage G left right := by
  classical
  refine hasThreeVertexLinkage_of_right_permutation_eq
    (G := G)
    (fin3EquivOfRangeEq (left := left) (right := right)
      hleft hright hrange) ?_ hleft
  intro i
  change left i = right (Function.invFun right (left i))
  symm
  apply Function.invFun_eq
  rw [← Set.mem_range, ← hrange]
  exact Set.mem_range_self i

theorem fin3_range_eq_univ_of_injective_of_card
    [Fintype V]
    {f : Fin 3 -> V}
    (hf : Function.Injective f)
    (hcard : Fintype.card V = 3) :
    Set.range f = Set.univ := by
  classical
  apply Set.eq_of_subset_of_ncard_le (Set.subset_univ (Set.range f))
  have hrange : (Set.range f).ncard = 3 := by
    rw [Set.ncard_range_of_injective hf]
    simp
  have huniv : (Set.univ : Set V).ncard = 3 := by
    simp [Set.ncard_univ, hcard]
  omega

theorem hasThreeVertexLinkage_of_card_eq_three
    [Fintype V]
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    (hcard : Fintype.card V = 3) :
    HasThreeVertexLinkage G left right := by
  classical
  exact hasThreeVertexLinkage_of_range_eq
    (G := G) hleft hright
    ((fin3_range_eq_univ_of_injective_of_card
        (V := V) hleft hcard).trans
      (fin3_range_eq_univ_of_injective_of_card
        (V := V) hright hcard).symm)

theorem hasThreeVertexLinkage_refl
    {points : Fin 3 -> V}
    (hpoints : Function.Injective points) :
    HasThreeVertexLinkage G points points :=
  hasThreeVertexLinkage_of_right_permutation_eq
    (G := G) (Equiv.refl (Fin 3)) (fun _ => rfl) hpoints

theorem hasThreeVertexLinkage_of_equal_or_adjacent_permutation
    {left right : Fin 3 -> V}
    (e : Fin 3 ≃ Fin 3)
    (hstep :
      forall i : Fin 3,
        left i = right (e i) ∨ G.Adj (left i) (right (e i)))
    (hsupports :
      forall i j : Fin 3, i ≠ j ->
        Disjoint ({left i, right (e i)} : Set V)
          ({left j, right (e j)} : Set V)) :
    HasThreeVertexLinkage G left right := by
  classical
  let path : forall i : Fin 3, G.Walk (left i) (right (e i)) := fun i =>
    if h : left i = right (e i) then
      (SimpleGraph.Walk.nil : G.Walk (left i) (left i)).copy rfl h
    else
      ((hstep i).resolve_left h).toWalk
  refine ⟨{
    targetEquiv := e
    path := path
    isPath := ?_
    pairwise_vertex_disjoint := ?_
  }⟩
  · intro i
    by_cases h : left i = right (e i)
    · simp [path, h]
    · have hadj : G.Adj (left i) (right (e i)) := (hstep i).resolve_left h
      simp [path, h, SimpleGraph.Walk.IsPath.of_adj hadj]
  · intro i j hij
    rw [Set.disjoint_left]
    intro v hvi hvj
    have hvi_pair : v ∈ ({left i, right (e i)} : Set V) := by
      by_cases h : left i = right (e i)
      · simp [path, h] at hvi
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hvi]
      · simp [path, h, Set.mem_insert_iff, Set.mem_singleton_iff] at hvi ⊢
        exact hvi
    have hvj_pair : v ∈ ({left j, right (e j)} : Set V) := by
      by_cases h : left j = right (e j)
      · simp [path, h] at hvj
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hvj]
      · simp [path, h, Set.mem_insert_iff, Set.mem_singleton_iff] at hvj ⊢
        exact hvj
    exact Set.disjoint_left.mp (hsupports i j hij) hvi_pair hvj_pair

theorem hasThreeVertexLinkage_of_equal_or_adjacent
    {left right : Fin 3 -> V}
    (hstep : forall i : Fin 3, left i = right i ∨ G.Adj (left i) (right i))
    (hsupports :
      forall i j : Fin 3, i ≠ j ->
        Disjoint ({left i, right i} : Set V) ({left j, right j} : Set V)) :
    HasThreeVertexLinkage G left right :=
  hasThreeVertexLinkage_of_equal_or_adjacent_permutation
    (G := G) (Equiv.refl (Fin 3)) hstep (by simpa using hsupports)

def ThreeVertexLinkage.symm
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right) :
    ThreeVertexLinkage G right left where
  targetEquiv := L.targetEquiv.symm
  path i := ((L.path (L.targetEquiv.symm i)).reverse).copy (by simp) rfl
  isPath i := by
    simpa using (L.isPath (L.targetEquiv.symm i)).reverse
  pairwise_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hs :
        Disjoint {v : V | v ∈ (L.path (L.targetEquiv.symm i)).support}
          {v : V | v ∈ (L.path (L.targetEquiv.symm j)).support} := by
      apply L.pairwise_vertex_disjoint
      intro h
      exact hij (by simpa using congrArg L.targetEquiv h)
    exact Set.disjoint_left.mp hs
      (by simpa [SimpleGraph.Walk.support_reverse] using hxi)
      (by simpa [SimpleGraph.Walk.support_reverse] using hxj)

theorem HasThreeVertexLinkage.symm
    {left right : Fin 3 -> V}
    (h : HasThreeVertexLinkage G left right) :
    HasThreeVertexLinkage G right left := by
  rcases h with ⟨L⟩
  exact ⟨L.symm⟩

def ThreeVertexLinkage.reindexLeft
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right)
    (e : Fin 3 ≃ Fin 3) :
    ThreeVertexLinkage G (fun i => left (e i)) right where
  targetEquiv := e.trans L.targetEquiv
  path i := L.path (e i)
  isPath i := L.isPath (e i)
  pairwise_vertex_disjoint := by
    intro i j hij
    exact L.pairwise_vertex_disjoint (e i) (e j) (by
      intro h
      exact hij (e.injective h))

def ThreeVertexLinkage.reindexRight
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right)
    (e : Fin 3 ≃ Fin 3) :
    ThreeVertexLinkage G left (fun i => right (e i)) where
  targetEquiv := L.targetEquiv.trans e.symm
  path i := (L.path i).copy rfl (by simp)
  isPath i := by
    simpa using L.isPath i
  pairwise_vertex_disjoint := by
    intro i j hij
    simpa using L.pairwise_vertex_disjoint i j hij

def ThreeVertexLinkage.reindex
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right)
    (eLeft eRight : Fin 3 ≃ Fin 3) :
    ThreeVertexLinkage G (fun i => left (eLeft i)) (fun i => right (eRight i)) :=
  (L.reindexLeft eLeft).reindexRight eRight

theorem ThreeVertexLinkage.exists_path_avoiding_small_set
    [Fintype V]
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right)
    {S : Set V}
    (hS : S.ncard < 3) :
    Exists fun i : Fin 3 =>
      forall v : V, v ∈ (L.path i).support -> v ∉ S := by
  classical
  by_contra hnone
  have hhit :
      forall i : Fin 3,
        Exists fun v : V => v ∈ (L.path i).support ∧ v ∈ S := by
    intro i
    by_contra hmiss
    exact hnone ⟨i, by
      intro v hv hvS
      exact hmiss ⟨v, hv, hvS⟩⟩
  let f : Fin 3 -> S := fun i =>
    ⟨Classical.choose (hhit i), (Classical.choose_spec (hhit i)).2⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hij_ne
    have hi_support :
        (f i : V) ∈ (L.path i).support :=
      (Classical.choose_spec (hhit i)).1
    have hj_support :
        (f j : V) ∈ (L.path j).support := by
      have hj_support_original :
          (f j : V) ∈ (L.path j).support :=
        (Classical.choose_spec (hhit j)).1
      simpa using hj_support_original
    have hj_support_for_i :
        (f i : V) ∈ (L.path j).support := by
      have hval : (f i : V) = (f j : V) := congrArg Subtype.val hij
      simpa [hval] using hj_support
    exact Set.disjoint_left.mp
      (L.pairwise_vertex_disjoint i j hij_ne)
      hi_support hj_support_for_i
  have hcard : Fintype.card (Fin 3) <= Fintype.card S :=
    Fintype.card_le_of_injective f hf_inj
  have hScard : Fintype.card S = S.ncard :=
    Set.fintypeCard_eq_ncard S
  simp only [Fintype.card_fin] at hcard
  omega

/-- Among `n` pairwise vertex-disjoint paths, one avoids every vertex of a
set of cardinality less than `n`. -/
theorem PartialThreeVertexLinkage.exists_path_avoiding_set
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {S : Set V}
    (hS : S.ncard < n) :
    Exists fun i : Fin n =>
      forall v : V, v ∈ (L.path i).support -> v ∉ S := by
  classical
  by_contra hnone
  have hhit :
      forall i : Fin n,
        Exists fun v : V => v ∈ (L.path i).support ∧ v ∈ S := by
    intro i
    by_contra hmiss
    exact hnone ⟨i, by
      intro v hv hvS
      exact hmiss ⟨v, hv, hvS⟩⟩
  let f : Fin n -> S := fun i =>
    ⟨Classical.choose (hhit i), (Classical.choose_spec (hhit i)).2⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hij_ne
    have hi_support :
        (f i : V) ∈ (L.path i).support :=
      (Classical.choose_spec (hhit i)).1
    have hj_support :
        (f j : V) ∈ (L.path j).support :=
      (Classical.choose_spec (hhit j)).1
    have hj_support_for_i :
        (f i : V) ∈ (L.path j).support := by
      have hval : (f i : V) = (f j : V) :=
        congrArg Subtype.val hij
      simpa [hval] using hj_support
    exact Set.disjoint_left.mp
      (L.pairwise_vertex_disjoint i j hij_ne)
      hi_support hj_support_for_i
  have hcard : Fintype.card (Fin n) <= Fintype.card S :=
    Fintype.card_le_of_injective f hf_inj
  have hScard : Fintype.card S = S.ncard :=
    Set.fintypeCard_eq_ncard S
  simp only [Fintype.card_fin] at hcard
  omega


end Schematic.Math.GraphTheory
