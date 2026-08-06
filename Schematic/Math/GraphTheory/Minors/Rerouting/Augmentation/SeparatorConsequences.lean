import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.TargetSinks

/-! Residual separators, locked targets, and three-connectivity consequences. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.separates_by_splitResidualCutSet_of_not_splitResidualReaches
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hno : Not L.SplitResidualReachesUnusedRight) :
    SeparatesVertexTriplesByDeletion G L.splitResidualCutSet left right := by
  intro i j hli hrj hreach
  obtain ⟨p, _hp, hsupport⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := L.splitResidualCutSetᶜ)
      hli hrj hreach
  have hleftR :
      L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.out (left i)) :=
    L.left_splitOutReachable_of_not_mem_splitResidualCutSet hli
  have hrightR :
      L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.out (right j)) :=
    PartialThreeVertexLinkage.Walk.end_splitOutReachable_of_avoids_splitResidualCutSet
      L p hleftR (by
        intro v hv
        exact hsupport v hv)
  exact L.right_not_splitOutReachable_of_not_mem_splitResidualCutSet
    hno hrj hrightR

theorem PartialThreeVertexLinkage.splitResidualReachesUnusedRight_of_no_small_separator
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hn : n < 3)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTriplesByDeletion G S left right)) :
    L.SplitResidualReachesUnusedRight := by
  by_contra hno
  exact
    hnosep L.splitResidualCutSet
      (L.splitResidualCutSet_ncard_lt_three_of_lt_three hn)
      (L.separates_by_splitResidualCutSet_of_not_splitResidualReaches hno)

theorem PartialThreeVertexLinkage.separates_by_residualCutSet_of_not_residualReaches
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hno : Not L.ResidualReachesUnusedRight) :
    SeparatesVertexTriplesByDeletion G L.residualCutSet left right := by
  intro i j hli hrj hreach
  obtain ⟨p, _hp, hsupport⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := L.residualCutSetᶜ)
      hli hrj hreach
  have hleftR :
      L.ResidualReachableFromUnusedLeft (left i) :=
    L.left_residualReachable_of_not_mem_residualCutSet hli
  have havoidBoundary :
      forall v : V, v ∈ p.support -> v ∉ L.ResidualBoundary := by
    intro v hv hb
    exact hsupport v hv
      (PartialThreeVertexLinkage.ResidualBoundary.subset_residualCutSet L hb)
  have hrightR :
      L.ResidualReachableFromUnusedLeft (right j) :=
    PartialThreeVertexLinkage.Walk.end_residualReachable_of_avoids_boundary
      L p hleftR havoidBoundary
  exact L.right_not_residualReachable_of_not_mem_residualCutSet hno hrj hrightR

theorem HasThreeVertexLinkage.not_separates_by_small_deletion
    [Fintype V]
    {left right : Fin 3 -> V}
    (hlink : HasThreeVertexLinkage G left right)
    {S : Set V}
    (hS : S.ncard < 3) :
    Not (SeparatesVertexTriplesByDeletion G S left right) := by
  classical
  intro hsep
  rcases hlink with ⟨L⟩
  obtain ⟨i, havoid⟩ := L.exists_path_avoiding_small_set hS
  have hli : left i ∉ S :=
    havoid (left i) (L.path i).start_mem_support
  have hri : right (L.targetEquiv i) ∉ S :=
    havoid (right (L.targetEquiv i)) (L.path i).end_mem_support
  have hreach :
      (G.induce Sᶜ).Reachable
        ⟨left i, hli⟩ ⟨right (L.targetEquiv i), hri⟩ :=
    Walk.reachable_induce_of_support_subset (L.path i) (by
      intro v hv
      exact havoid v hv)
  exact hsep i (L.targetEquiv i) hli hri hreach

theorem HasThreeVertexLinkage.not_separates_from_target_set_by_small_deletion
    [Fintype V]
    {left right : Fin 3 -> V} {Y : Set V}
    (hlink : HasThreeVertexLinkage G left right)
    (hrightY : forall j : Fin 3, right j ∈ Y)
    {S : Set V}
    (hS : S.ncard < 3) :
    Not (SeparatesVertexTripleFromSetByDeletion G S left Y) := by
  intro hsep
  exact hlink.not_separates_by_small_deletion hS
    (hsep.to_triples hrightY)

def lockedOneTargetRight
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1) :
    Fin 3 -> V ⊕ Fin 2
  | 0 => Sum.inl (right (L.rightIndex 0))
  | 1 => Sum.inr 0
  | 2 => Sum.inr 1

def lockedTwoTargetRight
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2) :
    Fin 3 -> V ⊕ Fin 1
  | 0 => Sum.inl (right (L.rightIndex 0))
  | 1 => Sum.inl (right (L.rightIndex 1))
  | 2 => Sum.inr 0

theorem lockedOneTargetRight_injective
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1) :
    Function.Injective (lockedOneTargetRight L) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [lockedOneTargetRight] at hij ⊢

theorem lockedTwoTargetRight_injective
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2) :
    Function.Injective (lockedTwoTargetRight L) := by
  have hselected_ne :
      right (L.rightIndex 0) ≠ right (L.rightIndex 1) := by
    intro h
    have hend0 :
        right (L.rightIndex 0) ∈ (L.path 0).support :=
      (L.path 0).end_mem_support
    have hend1 :
        right (L.rightIndex 0) ∈ (L.path 1).support := by
      simp [h]
    exact
      (by decide : (0 : Fin 2) ≠ 1)
        (L.eq_of_mem_path_supports hend0 hend1)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [lockedTwoTargetRight] at hij ⊢
  · exact False.elim (hselected_ne hij)
  · exact False.elim (hselected_ne hij.symm)

/-- One selected target can be locked while two target-set sinks remain
available.

This is the one-endpoint case of GM IX `(2.2)`.  If at least one sink survives
a deletion of fewer than three vertices, a path of the existing full
target-set linkage avoids the deleted original vertices and reaches that sink.
If both sinks are deleted, no original vertex was deleted, so the selected
path reaches its locked target. -/
theorem lockedOneTarget_not_separates
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {left right fullRight : Fin 3 -> V} {Y : Set V}
    (Lselected : PartialThreeVertexLinkage G left right 1)
    (Lfull : ThreeVertexLinkage G left fullRight)
    (hfullY : forall i : Fin 3, fullRight i ∈ Y)
    {D : Set (V ⊕ Fin 2)}
    (hD : D.ncard < 3) :
    Not
      (SeparatesVertexTriplesByDeletion
        (finiteTargetSetSinkGraph G Y 2) D
        (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 2))
        (lockedOneTargetRight Lselected)) := by
  classical
  intro hsep
  let D0 : Set V := finiteTargetSetSinkOriginalDeleted D
  have hD0 : D0.ncard < 3 :=
    finiteTargetSetSinkOriginalDeleted_ncard_lt_three
      (V := V) (D := D) hD
  by_cases hs0 : (Sum.inr (0 : Fin 2) : V ⊕ Fin 2) ∈ D
  · by_cases hs1 : (Sum.inr (1 : Fin 2) : V ⊕ Fin 2) ∈ D
    · have hD0_empty : D0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hsubset :
            ({Sum.inl x, Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)} :
              Set (V ⊕ Fin 2)) ⊆ D := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · exact hx
          · exact hs0
          · exact hs1
        have hthree :
            ({Sum.inl x, Sum.inr (0 : Fin 2), Sum.inr (1 : Fin 2)} :
              Set (V ⊕ Fin 2)).ncard = 3 := by
          simp
        have hle :=
          Set.ncard_le_ncard hsubset
        omega
      have hsource :
          Sum.inl (left (Lselected.leftIndex 0)) ∉ D := by
        intro hmem
        have :
            left (Lselected.leftIndex 0) ∈ D0 := hmem
        simp [hD0_empty] at this
      have htarget :
          Sum.inl (right (Lselected.rightIndex 0)) ∉ D := by
        intro hmem
        have :
            right (Lselected.rightIndex 0) ∈ D0 := hmem
        simp [hD0_empty] at this
      have hreachG :
          (G.induce D0ᶜ).Reachable
            ⟨left (Lselected.leftIndex 0), by
              simpa [D0, finiteTargetSetSinkOriginalDeleted] using hsource⟩
            ⟨right (Lselected.rightIndex 0), by
              simpa [D0, finiteTargetSetSinkOriginalDeleted] using htarget⟩ :=
        Walk.reachable_induce_of_support_subset
          (Lselected.path 0) (by
            intro z _hz
            simp [hD0_empty])
      have hreach :=
        finiteTargetSetSinkGraph_reachable_original_after_delete
          (G := G) (Y := Y) (n := 2) hsource htarget hreachG
      exact
        hsep (Lselected.leftIndex 0) 0 hsource
          (by simpa [lockedOneTargetRight] using htarget)
          (by simpa [lockedOneTargetRight] using hreach)
    · obtain ⟨i, havoid⟩ :=
        Lfull.exists_path_avoiding_small_set hD0
      have hsource : Sum.inl (left i) ∉ D := by
        simpa [D0, finiteTargetSetSinkOriginalDeleted] using
          havoid (left i) (Lfull.path i).start_mem_support
      have htarget :
          Sum.inl (fullRight (Lfull.targetEquiv i)) ∉ D := by
        simpa [D0, finiteTargetSetSinkOriginalDeleted] using
          havoid _ (Lfull.path i).end_mem_support
      have hreachG :
          (G.induce D0ᶜ).Reachable
            ⟨left i, by
              simpa [D0, finiteTargetSetSinkOriginalDeleted] using hsource⟩
            ⟨fullRight (Lfull.targetEquiv i), by
              simpa [D0, finiteTargetSetSinkOriginalDeleted] using htarget⟩ :=
        Walk.reachable_induce_of_support_subset (Lfull.path i) (by
          intro z hz
          exact havoid z hz)
      have hreach :=
        finiteTargetSetSinkGraph_reachable_to_sink_after_delete
          (G := G) (Y := Y) (n := 2)
          hsource htarget hs1
          (hfullY (Lfull.targetEquiv i)) hreachG
      exact
        hsep i 2 hsource
          (by simpa [lockedOneTargetRight] using hs1)
          (by simpa [lockedOneTargetRight] using hreach)
  · obtain ⟨i, havoid⟩ :=
      Lfull.exists_path_avoiding_small_set hD0
    have hsource : Sum.inl (left i) ∉ D := by
      simpa [D0, finiteTargetSetSinkOriginalDeleted] using
        havoid (left i) (Lfull.path i).start_mem_support
    have htarget :
        Sum.inl (fullRight (Lfull.targetEquiv i)) ∉ D := by
      simpa [D0, finiteTargetSetSinkOriginalDeleted] using
        havoid _ (Lfull.path i).end_mem_support
    have hreachG :
        (G.induce D0ᶜ).Reachable
          ⟨left i, by
            simpa [D0, finiteTargetSetSinkOriginalDeleted] using hsource⟩
          ⟨fullRight (Lfull.targetEquiv i), by
            simpa [D0, finiteTargetSetSinkOriginalDeleted] using htarget⟩ :=
      Walk.reachable_induce_of_support_subset (Lfull.path i) (by
        intro z hz
        exact havoid z hz)
    have hreach :=
      finiteTargetSetSinkGraph_reachable_to_sink_after_delete
        (G := G) (Y := Y) (n := 2)
        hsource htarget hs0
        (hfullY (Lfull.targetEquiv i)) hreachG
    exact
      hsep i 1 hsource
        (by simpa [lockedOneTargetRight] using hs0)
        (by simpa [lockedOneTargetRight] using hreach)

/-- Two selected targets can be locked while one target-set sink remains
available.  This is the two-endpoint case of GM IX `(2.2)`. -/
theorem lockedTwoTarget_not_separates
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {left right fullRight : Fin 3 -> V} {Y : Set V}
    (Lselected : PartialThreeVertexLinkage G left right 2)
    (Lfull : ThreeVertexLinkage G left fullRight)
    (hfullY : forall i : Fin 3, fullRight i ∈ Y)
    {D : Set (V ⊕ Fin 1)}
    (hD : D.ncard < 3) :
    Not
      (SeparatesVertexTriplesByDeletion
        (finiteTargetSetSinkGraph G Y 1) D
        (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 1))
        (lockedTwoTargetRight Lselected)) := by
  classical
  intro hsep
  let D0 : Set V := finiteTargetSetSinkOriginalDeleted D
  have hD0 : D0.ncard < 3 :=
    finiteTargetSetSinkOriginalDeleted_ncard_lt_three
      (V := V) (D := D) hD
  by_cases hsink : (Sum.inr (0 : Fin 1) : V ⊕ Fin 1) ∈ D
  · have hD0_lt_two : D0.ncard < 2 := by
      let A : Set (V ⊕ Fin 1) :=
        Sum.inl '' D0
      have hsink_not_A :
          (Sum.inr (0 : Fin 1) : V ⊕ Fin 1) ∉ A := by
        simp [A]
      have hsubset :
          insert (Sum.inr (0 : Fin 1) : V ⊕ Fin 1) A ⊆ D := by
        intro z hz
        rcases hz with rfl | hzA
        · exact hsink
        · rcases hzA with ⟨x, hx, rfl⟩
          exact hx
      have hAcard : A.ncard = D0.ncard := by
        exact Set.ncard_image_of_injective D0 Sum.inl_injective
      have hinsert :
          (insert (Sum.inr (0 : Fin 1) : V ⊕ Fin 1) A).ncard =
            D0.ncard + 1 := by
        rw [Set.ncard_insert_of_notMem hsink_not_A, hAcard]
      have hle := Set.ncard_le_ncard hsubset
      omega
    obtain ⟨a, havoid⟩ :=
      Lselected.exists_path_avoiding_set hD0_lt_two
    have hsource :
        Sum.inl (left (Lselected.leftIndex a)) ∉ D := by
      simpa [D0, finiteTargetSetSinkOriginalDeleted] using
        havoid _ (Lselected.path a).start_mem_support
    have htarget :
        Sum.inl (right (Lselected.rightIndex a)) ∉ D := by
      simpa [D0, finiteTargetSetSinkOriginalDeleted] using
        havoid _ (Lselected.path a).end_mem_support
    have hreachG :
        (G.induce D0ᶜ).Reachable
          ⟨left (Lselected.leftIndex a), by
            simpa [D0, finiteTargetSetSinkOriginalDeleted] using hsource⟩
          ⟨right (Lselected.rightIndex a), by
            simpa [D0, finiteTargetSetSinkOriginalDeleted] using htarget⟩ :=
      Walk.reachable_induce_of_support_subset (Lselected.path a) (by
        intro z hz
        exact havoid z hz)
    have hreach :=
      finiteTargetSetSinkGraph_reachable_original_after_delete
        (G := G) (Y := Y) (n := 1) hsource htarget hreachG
    fin_cases a
    · exact
        hsep (Lselected.leftIndex 0) 0 hsource
          (by simpa [lockedTwoTargetRight] using htarget)
          (by simpa [lockedTwoTargetRight] using hreach)
    · exact
        hsep (Lselected.leftIndex 1) 1 hsource
          (by simpa [lockedTwoTargetRight] using htarget)
          (by simpa [lockedTwoTargetRight] using hreach)
  · obtain ⟨i, havoid⟩ :=
      Lfull.exists_path_avoiding_small_set hD0
    have hsource : Sum.inl (left i) ∉ D := by
      simpa [D0, finiteTargetSetSinkOriginalDeleted] using
        havoid (left i) (Lfull.path i).start_mem_support
    have htarget :
        Sum.inl (fullRight (Lfull.targetEquiv i)) ∉ D := by
      simpa [D0, finiteTargetSetSinkOriginalDeleted] using
        havoid _ (Lfull.path i).end_mem_support
    have hreachG :
        (G.induce D0ᶜ).Reachable
          ⟨left i, by
            simpa [D0, finiteTargetSetSinkOriginalDeleted] using hsource⟩
          ⟨fullRight (Lfull.targetEquiv i), by
            simpa [D0, finiteTargetSetSinkOriginalDeleted] using htarget⟩ :=
      Walk.reachable_induce_of_support_subset (Lfull.path i) (by
        intro z hz
        exact havoid z hz)
    have hreach :=
      finiteTargetSetSinkGraph_reachable_to_sink_after_delete
        (G := G) (Y := Y) (n := 1)
        hsource htarget hsink
        (hfullY (Lfull.targetEquiv i)) hreachG
    exact
      hsep i 2 hsource
        (by simpa [lockedTwoTargetRight] using hsink)
        (by simpa [lockedTwoTargetRight] using hreach)

theorem exists_path_between_fin3_triples_of_not_separates
    [DecidableEq V]
    {left right : Fin 3 -> V} {S : Set V}
    (hnot : Not (SeparatesVertexTriplesByDeletion G S left right)) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        Exists fun p : G.Walk (left i) (right j) =>
          left i ∉ S ∧ right j ∉ S ∧ p.IsPath ∧
            forall v : V, v ∈ p.support -> v ∉ S := by
  classical
  by_contra hnone
  apply hnot
  intro i j hli hrj hreach
  obtain ⟨p, hp, hsub⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := Sᶜ)
      (u := left i) (v := right j) hli hrj hreach
  exact hnone ⟨i, j, p, hli, hrj, hp, by
    intro v hv
    exact hsub v hv⟩

theorem exists_path_between_fin3_triples_of_not_separates_empty
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (hnot :
      Not (SeparatesVertexTriplesByDeletion G (∅ : Set V) left right)) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        Exists fun p : G.Walk (left i) (right j) =>
          p.IsPath := by
  classical
  obtain ⟨i, j, p, _hli, _hrj, hp, _havoid⟩ :=
    exists_path_between_fin3_triples_of_not_separates
      (G := G) (S := (∅ : Set V)) hnot
  exact ⟨i, j, p, hp⟩

theorem PartialThreeVertexLinkage.hasPartial_succ_of_usedVertices_small
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTriplesByDeletion G S left right))
    (hused : L.usedVertices.ncard < 3) :
    HasPartialThreeVertexLinkage G left right (n + 1) := by
  classical
  obtain ⟨i, j, p, hli, hrj, hp, havoid⟩ :=
    exists_path_between_fin3_triples_of_not_separates
      (G := G) (S := L.usedVertices) (hnosep L.usedVertices hused)
  have hi_unused : i ∉ Set.range L.leftIndex := by
    rintro ⟨k, rfl⟩
    exact hli (L.left_mem_usedVertices k)
  have hj_unused : j ∉ Set.range L.rightIndex := by
    rintro ⟨k, rfl⟩
    exact hrj (L.right_mem_usedVertices k)
  exact
    L.hasPartial_succ_of_path_avoids_usedVertices
      hi_unused hj_unused p hp havoid

theorem PartialThreeVertexLinkage.exists_ordinary_path_of_residualReaches
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hreach : L.ResidualReachesUnusedRight) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        i ∉ Set.range L.leftIndex ∧
          j ∉ Set.range L.rightIndex ∧
            Exists fun p : G.Walk (left i) (right j) =>
              p.IsPath := by
  classical
  rcases hreach with ⟨j, hj, i, hi, hres⟩
  have hGreach : G.Reachable (left i) (right j) :=
    PartialThreeVertexLinkage.ResidualStep.reachable hres
  rcases hGreach with ⟨p⟩
  exact ⟨i, j, hi, hj, p.toPath, p.toPath.property⟩

theorem exists_fin3_apply_not_mem_of_ncard_lt_three
    [Fintype V]
    {f : Fin 3 -> V} (hf : Function.Injective f) {S : Set V}
    (hS : S.ncard < 3) :
    Exists fun i : Fin 3 => f i ∉ S := by
  classical
  by_contra hnone
  have hall : forall i : Fin 3, f i ∈ S := by
    intro i
    by_contra hfi
    exact hnone ⟨i, hfi⟩
  let g : Fin 3 -> S := fun i => ⟨f i, hall i⟩
  have hg : Function.Injective g := by
    intro i j hij
    exact hf (congrArg Subtype.val hij)
  have hcard : Fintype.card (Fin 3) <= Fintype.card S :=
    Fintype.card_le_of_injective g hg
  have hScard : Fintype.card S = S.ncard := by
    exact Set.fintypeCard_eq_ncard S
  simp only [Fintype.card_fin] at hcard
  omega

theorem IsThreeConnected.exists_reachable_between_fin3_triples_outside_small_set
    [Fintype V]
    (hG : IsThreeConnected G)
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    {S : Set V}
    (hS : S.ncard < 3) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        Exists fun hli : left i ∉ S =>
          Exists fun hrj : right j ∉ S =>
            (G.induce Sᶜ).Reachable ⟨left i, hli⟩ ⟨right j, hrj⟩ := by
  obtain ⟨i, hi⟩ := exists_fin3_apply_not_mem_of_ncard_lt_three hleft hS
  obtain ⟨j, hj⟩ := exists_fin3_apply_not_mem_of_ncard_lt_three hright hS
  exact ⟨i, j, hi, hj, hG.2 S hS ⟨left i, hi⟩ ⟨right j, hj⟩⟩

theorem IsThreeConnected.not_separates_fin3_triples_by_small_deletion
    [Fintype V]
    (hG : IsThreeConnected G)
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    {S : Set V}
    (hS : S.ncard < 3) :
    Not (SeparatesVertexTriplesByDeletion G S left right) := by
  intro hsep
  obtain ⟨i, j, hi, hj, hreach⟩ :=
    hG.exists_reachable_between_fin3_triples_outside_small_set
      hleft hright hS
  exact hsep i j hi hj hreach

theorem IsThreeConnected.exists_path_between_fin3_triples_avoiding_small_set
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    {S : Set V}
    (hS : S.ncard < 3) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        Exists fun p : G.Walk (left i) (right j) =>
          p.IsPath ∧ forall v : V, v ∈ p.support -> v ∉ S := by
  obtain ⟨i, j, hi, hj, _hreach⟩ :=
    hG.exists_reachable_between_fin3_triples_outside_small_set
      hleft hright hS
  have hconn : (G.induce Sᶜ).Connected := hG.2 S hS
  obtain ⟨p, hp, hp_subset⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) hconn hi hj
  exact ⟨i, j, p, hp, by
    intro v hv
    exact hp_subset v hv⟩


end Schematic.Math.GraphTheory
