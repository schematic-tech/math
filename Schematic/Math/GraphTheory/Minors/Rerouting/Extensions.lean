import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualChains

/-! Augmenting partial set linkages to full three-linkages. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

namespace PartialSetLinkage

/-- A larger endpoint-clean linkage retaining all selected endpoint sets. -/
structure Extension
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (m : Nat) where
  linkage : PartialSetLinkage G X Y m
  sourceSet_subset : L.sourceSet ⊆ linkage.sourceSet
  targetSet_subset : L.targetSet ⊆ linkage.targetSet

/--
Augment an endpoint-clean partial set-linkage along a restricted residual
chain.

This is the reconstruction half of GM IX (2.2).  The older split-flow
decomposition supplies the new disjoint paths.  The extra work here proves
that the reconstructed paths still meet `X` and `Y` only at their respective
ends.  In particular, this theorem does not discard the source-clean
restriction encoded in `PartialSetLinkage.SplitResidualStep`.
-/
noncomputable def augmentOfRestrictedSplitResidualChain
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (left right : Fin 3 -> V)
    (leftIndex rightIndex : Fin n -> Fin 3)
    (hleftIndex : Function.Injective leftIndex)
    (hrightIndex : Function.Injective rightIndex)
    (hleft : forall i : Fin n, left (leftIndex i) = L.source i)
    (hright : forall i : Fin n, right (rightIndex i) = L.target i)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    (hiNew : iNew ∉ Set.range leftIndex)
    (hjNew : jNew ∉ Set.range rightIndex)
    (hsourceValuesInj :
      Function.Injective
        (fun a : Fin (n + 1) =>
          left ((Fin.snoc leftIndex iNew :
            Fin (n + 1) -> Fin 3) a)))
    (hiNewX : left iNew ∈ X)
    (hjNewY : right jNew ∈ Y)
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    Extension L (n + 1) := by
  classical
  let L' : PartialThreeVertexLinkage G left right n :=
    L.toPartialThreeVertexLinkage left right leftIndex rightIndex
      hleftIndex hrightIndex hleft hright
  have hchain' : l.IsChain L'.SplitResidualStep := by
    exact
      L.isChain_toPartialThreeVertexLinkage
        left right leftIndex rightIndex hleftIndex hrightIndex
        hleft hright hchain
  let sourceIndex : Fin (n + 1) -> Fin 3 :=
    Fin.snoc leftIndex iNew
  have hsourceIndexInj : Function.Injective sourceIndex := by
    simpa [sourceIndex] using
      (Fin.snoc_injective_iff.mpr ⟨hleftIndex, hiNew⟩)
  let oldData : forall k : Fin n,
      L'.SplitAugmentedSourceData l jNew (left (leftIndex k)) := fun k =>
    PartialThreeVertexLinkage.SplitAugmentedSourceData.fromOldLeft
      (L := L') (l := l) (jNew := jNew)
      hnodup hlast hchain' k
  let newData :
      L'.SplitAugmentedSourceData l jNew (left iNew) :=
    PartialThreeVertexLinkage.SplitAugmentedSourceData.fromNewLeft
      (L := L') (l := l) (iNew := iNew) (jNew := jNew)
      hnodup hhead hlast hchain'
  let data :
      forall a : Fin (n + 1),
        L'.SplitAugmentedSourceData l jNew (left (sourceIndex a)) := by
    intro a
    cases a using Fin.lastCases with
    | last =>
        simpa [sourceIndex] using newData
    | cast k =>
        simpa [sourceIndex] using oldData k
  let rightIndexNew : Fin (n + 1) -> Fin 3 := fun a =>
    if hnew :
        (data a).terminal =
          VertexSplitState.out (right jNew) then
      jNew
    else
      rightIndex
        (Classical.choose
          (show Exists fun k : Fin n =>
              (data a).terminal =
                VertexSplitState.out (right (rightIndex k)) from
            (Or.resolve_left (data a).terminal_classified hnew)))
  have hterminalRight :
      forall a : Fin (n + 1),
        (data a).terminal =
          VertexSplitState.out (right (rightIndexNew a)) := by
    intro a
    by_cases hnew :
        (data a).terminal =
          VertexSplitState.out (right jNew)
    · simp [rightIndexNew, hnew]
    · let k : Fin n :=
        Classical.choose
          (show Exists fun k : Fin n =>
              (data a).terminal =
                VertexSplitState.out (right (rightIndex k)) from
            Or.resolve_left (data a).terminal_classified hnew)
      have hk :
          (data a).terminal =
            VertexSplitState.out (right (rightIndex k)) :=
        Classical.choose_spec
          (show Exists fun k : Fin n =>
              (data a).terminal =
                VertexSplitState.out (right (rightIndex k)) from
            Or.resolve_left (data a).terminal_classified hnew)
      simpa [rightIndexNew, hnew, k] using hk
  have hrightIndexNewInj : Function.Injective rightIndexNew := by
    intro a b hab
    have hterminalEq : (data a).terminal = (data b).terminal := by
      calc
        (data a).terminal =
            VertexSplitState.out (right (rightIndexNew a)) :=
          hterminalRight a
        _ = VertexSplitState.out (right (rightIndexNew b)) := by
          rw [hab]
        _ = (data b).terminal := (hterminalRight b).symm
    have hsourceEq :
        VertexSplitState.inn (left (sourceIndex a)) =
          VertexSplitState.inn (left (sourceIndex b)) :=
      PartialThreeVertexLinkage.SplitAugmentedSourceData.source_eq_of_terminal_eq
        (L := L') (l := l) (jNew := jNew)
        hnodup hlast hchain' (data a) (data b) hterminalEq
    injection hsourceEq with hleftEq
    exact hsourceValuesInj (by simpa [sourceIndex] using hleftEq)
  have hrightRangeSubset :
      Set.range rightIndexNew ⊆
        Set.insert jNew (Set.range rightIndex) := by
    rintro j ⟨a, rfl⟩
    dsimp [rightIndexNew]
    split_ifs with hnew
    · exact Set.mem_insert jNew _
    · exact Set.mem_insert_iff.mpr
        (Or.inr ⟨Classical.choose
          (Or.resolve_left (data a).terminal_classified hnew), rfl⟩)
  have hrightRange :
      Set.range rightIndexNew =
        Set.insert jNew (Set.range rightIndex) := by
    apply Set.eq_of_subset_of_ncard_le hrightRangeSubset
    calc
      (Set.insert jNew (Set.range rightIndex)).ncard =
          (Set.range rightIndex).ncard + 1 :=
        Set.ncard_insert_of_notMem hjNew
      _ = n + 1 := by
        rw [Set.ncard_range_of_injective hrightIndex]
        simp
      _ ≤ (Set.range rightIndexNew).ncard := by
        rw [Set.ncard_range_of_injective hrightIndexNewInj]
        simpa only [Nat.card_fin] using Nat.le_refl (n + 1)
  have hdataDisjoint :
      forall a b : Fin (n + 1), a ≠ b ->
        Disjoint {z : V | z ∈ (data a).path.support}
          {z : V | z ∈ (data b).path.support} := by
    intro a b hab
    have hsourceNe :
        VertexSplitState.inn (left (sourceIndex a)) ≠
          VertexSplitState.inn (left (sourceIndex b)) := by
      intro hs
      injection hs with hs
      exact hab (hsourceValuesInj (by simpa [sourceIndex] using hs))
    exact
      PartialThreeVertexLinkage.SplitAugmentedSourceData.paths_disjoint
        (L := L') (l := l) (jNew := jNew)
        hnodup hlast hchain' (data a) (data b) hsourceNe
  let outputTarget : Fin (n + 1) -> V :=
    fun a => right (rightIndexNew a)
  let outputPath : forall a : Fin (n + 1),
      G.Walk (left (sourceIndex a)) (outputTarget a) :=
    fun a =>
      ((data a).path).copy rfl (by
        have hv :=
          congrArg VertexSplitState.vertex (hterminalRight a)
        simpa [outputTarget] using hv)
  let M : PartialSetLinkage G X Y (n + 1) := {
    source := fun a => left (sourceIndex a)
    target := outputTarget
    source_mem := by
      intro a
      cases a using Fin.lastCases with
      | last =>
          simpa [sourceIndex] using hiNewX
      | cast k =>
          simpa [sourceIndex, hleft k] using L.source_mem k
    target_mem := by
      intro a
      have hmem :
          rightIndexNew a ∈
            Set.insert jNew (Set.range rightIndex) := by
        rw [← hrightRange]
        exact ⟨a, rfl⟩
      rcases Set.mem_insert_iff.mp hmem with hnew | ⟨k, hk⟩
      · simpa [outputTarget, hnew] using hjNewY
      · simpa [outputTarget, ← hk, hright k] using L.target_mem k
    source_injective := by
      simpa [sourceIndex] using hsourceValuesInj
    target_injective := by
      intro a b hab
      have hterminalEq :
          (data a).terminal = (data b).terminal := by
        calc
          (data a).terminal =
              VertexSplitState.out (outputTarget a) := by
            simpa [outputTarget] using hterminalRight a
          _ = VertexSplitState.out (outputTarget b) := by
            rw [hab]
          _ = (data b).terminal := by
            simpa [outputTarget] using (hterminalRight b).symm
      have hsourceEq :
          VertexSplitState.inn (left (sourceIndex a)) =
            VertexSplitState.inn (left (sourceIndex b)) :=
        PartialThreeVertexLinkage.SplitAugmentedSourceData.source_eq_of_terminal_eq
          (L := L') (l := l) (jNew := jNew)
          hnodup hlast hchain' (data a) (data b) hterminalEq
      injection hsourceEq with hsourceEq
      exact hsourceValuesInj (by simpa [sourceIndex] using hsourceEq)
    path := outputPath
    isPath := by
      intro a
      simpa [outputPath] using (data a).path_isPath
    pairwise_vertex_disjoint := by
      intro a b hab
      simpa [outputPath] using hdataDisjoint a b hab
    source_clean := by
      intro a z hzPath hzX
      have hzData : z ∈ (data a).path.support := by
        simpa [outputPath] using hzPath
      obtain ⟨s, hsChain, hsVertex⟩ := (data a).path_support z hzData
      have hinn :
          VertexSplitState.inn z ∈ (data a).chain :=
        PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_vertex_mem_chain
          (L := L') (l := l) (m := (data a).chain)
          hchain' (data a).chain_head (data a).chain_aug hsChain hsVertex
      by_cases hzUnused : z ∉ L.usedVertices
      · have hreach :
            Relation.ReflTransGen (L'.SplitAugmentedArc l)
              (VertexSplitState.inn (left (sourceIndex a)))
              (VertexSplitState.inn z) :=
          reflTransGen_of_isChain_head?_mem
            (data a).chain_head (data a).chain_aug hinn
        have hstartEq :
            VertexSplitState.inn (left (sourceIndex a)) =
              VertexSplitState.inn z :=
          reflTransGen_eq_of_no_incoming
            (L.splitAugmentedArc_no_incoming_inn_of_unused_source
              left right leftIndex rightIndex
              hleftIndex hrightIndex hleft hright
              hchain hzX hzUnused)
            hreach
        injection hstartEq with hstartEq
        exact hstartEq.symm
      · have hzUsed : z ∈ L.usedVertices := by simpa using hzUnused
        have hzSelected : z ∈ L.sourceSet :=
          (Set.ext_iff.mp L.usedVertices_inter_sourceSet z).mp
            ⟨hzUsed, hzX⟩
        rcases hzSelected with ⟨k, hk⟩
        let b : Fin (n + 1) := Fin.castSucc k
        have hzOldData : z ∈ (data b).path.support := by
          have hstart :
              left (sourceIndex b) ∈ (data b).path.support :=
            (data b).path.start_mem_support
          simpa [b, sourceIndex, hleft k, ← hk] using hstart
        have hab : a = b := by
          by_contra hab
          exact
            Set.disjoint_left.mp (hdataDisjoint a b hab)
              hzData hzOldData
        calc
          z = L.source k := hk.symm
          _ = left (leftIndex k) := (hleft k).symm
          _ = left (sourceIndex b) := by
            simp [b, sourceIndex]
          _ = left (sourceIndex a) := by rw [hab]
    target_clean := by
      intro a z hzPath hzY
      have hzData : z ∈ (data a).path.support := by
        simpa [outputPath] using hzPath
      obtain ⟨s, hsChain, hsVertex⟩ := (data a).path_support z hzData
      have hinn :
          VertexSplitState.inn z ∈ (data a).chain :=
        PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_vertex_mem_chain
          (L := L') (l := l) (m := (data a).chain)
          hchain' (data a).chain_head (data a).chain_aug hsChain hsVertex
      have hout :
          VertexSplitState.out z ∈ (data a).chain :=
        PartialThreeVertexLinkage.SplitAugmentedArc.mem_out_of_mem_inn_chain
          (L := L') (l := l) (m := (data a).chain)
          hchain'
          (by simpa [outputTarget] using
            (show (data a).chain.getLast? =
                some (VertexSplitState.out (outputTarget a)) from by
              simpa [outputTarget] using
                (data a).chain_last.trans
                  (congrArg some (hterminalRight a))))
          (data a).chain_aug hinn
      by_cases hzUnused : z ∉ L.usedVertices
      · have hreach :
            Relation.ReflTransGen (L'.SplitAugmentedArc l)
              (VertexSplitState.out z)
              (VertexSplitState.out (outputTarget a)) :=
          reflTransGen_of_isChain_mem_getLast?
            (by simpa [outputTarget] using
              (show (data a).chain.getLast? =
                  some (VertexSplitState.out (outputTarget a)) from by
                simpa [outputTarget] using
                  (data a).chain_last.trans
                    (congrArg some (hterminalRight a))))
            (data a).chain_aug hout
        have hendEq :
            VertexSplitState.out z =
              VertexSplitState.out (outputTarget a) :=
          reflTransGen_eq_of_no_outgoing
            (L.splitAugmentedArc_no_outgoing_out_of_unused_target
              left right leftIndex rightIndex
              hleftIndex hrightIndex hleft hright
              hchain hzY hzUnused)
            hreach
        injection hendEq with hendEq
      · have hzUsed : z ∈ L.usedVertices := by simpa using hzUnused
        have hzSelected : z ∈ L.targetSet :=
          (Set.ext_iff.mp L.usedVertices_inter_targetSet z).mp
            ⟨hzUsed, hzY⟩
        rcases hzSelected with ⟨k, hk⟩
        have hOldIndex :
            rightIndex k ∈ Set.range rightIndexNew := by
          rw [hrightRange]
          exact Set.mem_insert_iff.mpr (Or.inr ⟨k, rfl⟩)
        rcases hOldIndex with ⟨b, hb⟩
        have hzOldData : z ∈ (data b).path.support := by
          have hterminalVertex :
              (data b).terminal.vertex = outputTarget b := by
            have hv :=
              congrArg VertexSplitState.vertex (hterminalRight b)
            simpa [outputTarget] using hv
          have hend :
              outputTarget b ∈ (data b).path.support := by
            rw [← hterminalVertex]
            exact (data b).path.end_mem_support
          simpa [outputTarget, hb, hright k, ← hk] using hend
        have hab : a = b := by
          by_contra hab
          exact
            Set.disjoint_left.mp (hdataDisjoint a b hab)
              hzData hzOldData
        subst b
        simp [outputTarget, hb, hright k, ← hk]
  }
  exact {
    linkage := M
    sourceSet_subset := by
      rintro z ⟨k, rfl⟩
      refine ⟨Fin.castSucc k, ?_⟩
      simp [M, sourceIndex, hleft k]
    targetSet_subset := by
      rintro z ⟨k, rfl⟩
      have hOldIndex :
          rightIndex k ∈ Set.range rightIndexNew := by
        rw [hrightRange]
        exact Set.mem_insert_iff.mpr (Or.inr ⟨k, rfl⟩)
      rcases hOldIndex with ⟨b, hb⟩
      refine ⟨b, ?_⟩
      simp [M, outputTarget, hb, hright k]
  }

/--
One endpoint-preserving augmentation step for a partial `X -> Y` linkage of
order less than three.

The full three-linkage is used only to exclude a residual separator of order
`n`.  The resulting shortest residual chain is then reconstructed by
`augmentOfRestrictedSplitResidualChain`.
-/
theorem exists_extensionOneOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n < 3)
    (F : ThreeSetLinkage G X Y) :
    Nonempty (Extension L (n + 1)) := by
  classical
  obtain ⟨x, y, hxX, hxUnused, hyY, hyUnused,
    l, hlNe, hlHead, hlLast, hlChain, hlMinimal⟩ :=
    (L.splitResidualReachesUnusedTarget_of_full_three hn F).exists_minimal_isChain_list
  have hlNodup : l.Nodup :=
    minimal_isChain_nodup
      hlNe hlHead hlLast hlChain hlMinimal
  have hnle : n <= 3 := Nat.le_of_lt hn
  let oldIndex : Fin n -> Fin 3 := Fin.castLE hnle
  let newIndex : Fin 3 := ⟨n, hn⟩
  let left : Fin 3 -> V := fun j =>
    if hj : (j : Nat) < n then
      L.source ⟨j, hj⟩
    else
      x
  let right : Fin 3 -> V := fun j =>
    if hj : (j : Nat) < n then
      L.target ⟨j, hj⟩
    else
      y
  have holdIndexInj : Function.Injective oldIndex :=
    Fin.castLE_injective hnle
  have hleftOld :
      forall i : Fin n, left (oldIndex i) = L.source i := by
    intro i
    simp [left, oldIndex, Fin.castLE]
  have hrightOld :
      forall i : Fin n, right (oldIndex i) = L.target i := by
    intro i
    simp [right, oldIndex, Fin.castLE]
  have hleftNew : left newIndex = x := by
    simp [left, newIndex]
  have hrightNew : right newIndex = y := by
    simp [right, newIndex]
  have hnewNotRange :
      newIndex ∉ Set.range oldIndex := by
    rintro ⟨i, hi⟩
    have hval := congrArg Fin.val hi
    simp [newIndex, oldIndex, Fin.castLE] at hval
    omega
  have hxNotRange : x ∉ Set.range L.source := by
    rintro ⟨i, hi⟩
    exact hxUnused (by
      rw [← hi]
      exact L.source_mem_usedVertices i)
  have hsourceSnocInj :
      Function.Injective (Fin.snoc L.source x) := by
    exact
      Fin.snoc_injective_iff.mpr
        ⟨L.source_injective, hxNotRange⟩
  have hsourceValuesInj :
      Function.Injective
        (fun a : Fin (n + 1) =>
          left ((Fin.snoc oldIndex newIndex :
            Fin (n + 1) -> Fin 3) a)) := by
    have hfun :
        (fun a : Fin (n + 1) =>
          left ((Fin.snoc oldIndex newIndex :
            Fin (n + 1) -> Fin 3) a)) =
          Fin.snoc L.source x := by
      funext a
      cases a using Fin.lastCases with
      | last =>
          simp [hleftNew]
      | cast i =>
          simp [hleftOld]
    rw [hfun]
    exact hsourceSnocInj
  exact ⟨
    L.augmentOfRestrictedSplitResidualChain
      left right oldIndex oldIndex holdIndexInj holdIndexInj
      hleftOld hrightOld
      hnewNotRange hnewNotRange hsourceValuesInj
      (by simpa [hleftNew] using hxX)
      (by simpa [hrightNew] using hyY)
      hlNodup
      (by simpa [hleftNew] using hlHead)
      (by simpa [hrightNew] using hlLast)
      hlChain⟩

/-- A chosen one-step endpoint-preserving augmentation. -/
noncomputable def extensionOneOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n < 3)
    (F : ThreeSetLinkage G X Y) :
    Extension L (n + 1) :=
  Classical.choice (L.exists_extensionOneOfFullThree hn F)

/-- The linkage supplied by one endpoint-preserving augmentation. -/
noncomputable def augmentOneOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n < 3)
    (F : ThreeSetLinkage G X Y) :
    PartialSetLinkage G X Y (n + 1) :=
  (L.extensionOneOfFullThree hn F).linkage

/-- One augmentation retains every source selected before the step. -/
theorem sourceSet_subset_augmentOneOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n < 3)
    (F : ThreeSetLinkage G X Y) :
    L.sourceSet ⊆ (L.augmentOneOfFullThree hn F).sourceSet := by
  exact (L.extensionOneOfFullThree hn F).sourceSet_subset

/-- One augmentation retains every target selected before the step. -/
theorem targetSet_subset_augmentOneOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n < 3)
    (F : ThreeSetLinkage G X Y) :
    L.targetSet ⊆ (L.augmentOneOfFullThree hn F).targetSet := by
  exact (L.extensionOneOfFullThree hn F).targetSet_subset

/-- The identity endpoint extension. -/
def Extension.refl
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    Extension L n where
  linkage := L
  sourceSet_subset := Set.Subset.rfl
  targetSet_subset := Set.Subset.rfl

/-- Endpoint-preserving extensions compose. -/
def Extension.trans
    {X Y : Set V} {n m k : Nat}
    {L : PartialSetLinkage G X Y n}
    (E₁ : Extension L m)
    (E₂ : Extension E₁.linkage k) :
    Extension L k where
  linkage := E₂.linkage
  sourceSet_subset := E₁.sourceSet_subset.trans E₂.sourceSet_subset
  targetSet_subset := E₁.targetSet_subset.trans E₂.targetSet_subset

/--
GM IX (2.2), specialized to the order-three case used in (2.4).

Any selected endpoint-clean linkage of order at most three extends to an
order-three endpoint-clean linkage whenever some order-three linkage exists.
Both selected endpoint sets are retained.
-/
theorem exists_extensionToThreeOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n <= 3)
    (F : ThreeSetLinkage G X Y) :
    Nonempty (Extension L 3) := by
  have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
    omega
  rcases hnCases with rfl | rfl | rfl | rfl
  · let E₁ : Extension L 1 :=
      L.extensionOneOfFullThree (by omega) F
    let E₂ : Extension E₁.linkage 2 :=
      E₁.linkage.extensionOneOfFullThree (by omega) F
    let E₃ : Extension E₂.linkage 3 :=
      E₂.linkage.extensionOneOfFullThree (by omega) F
    exact ⟨(E₁.trans E₂).trans E₃⟩
  · let E₁ : Extension L 2 :=
      L.extensionOneOfFullThree (by omega) F
    let E₂ : Extension E₁.linkage 3 :=
      E₁.linkage.extensionOneOfFullThree (by omega) F
    exact ⟨E₁.trans E₂⟩
  · let E : Extension L 3 :=
      L.extensionOneOfFullThree (by omega) F
    exact ⟨E⟩
  · exact ⟨Extension.refl L⟩

/-- A chosen endpoint-preserving completion to order three. -/
noncomputable def extensionToThreeOfFullThree
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n <= 3)
    (F : ThreeSetLinkage G X Y) :
    Extension L 3 :=
  Classical.choice (L.exists_extensionToThreeOfFullThree hn F)

def ofThreeSetLinkage
    {X Y : Set V}
    (L : ThreeSetLinkage G X Y) :
    PartialSetLinkage G X Y 3 where
  source := L.source
  target := L.target
  source_mem := L.source_mem
  target_mem := L.target_mem
  source_injective := L.source_injective
  target_injective := L.target_injective
  path := L.path
  isPath := L.isPath
  pairwise_vertex_disjoint := L.pairwise_vertex_disjoint
  source_clean := L.source_clean
  target_clean := L.target_clean

/-- Forget that an order-three partial linkage was built incrementally. -/
def toThreeSetLinkage
    {X Y : Set V}
    (L : PartialSetLinkage G X Y 3) :
    ThreeSetLinkage G X Y where
  source := L.source
  target := L.target
  source_mem := L.source_mem
  target_mem := L.target_mem
  source_injective := L.source_injective
  target_injective := L.target_injective
  path := L.path
  isPath := L.isPath
  pairwise_vertex_disjoint := L.pairwise_vertex_disjoint
  source_clean := L.source_clean
  target_clean := L.target_clean

/--
Public order-three form of GM IX (2.2): the returned linkage retains all
selected sources and targets.
-/
theorem exists_threeSetLinkage_extending
    [Fintype V] [DecidableEq V]
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n)
    (hn : n <= 3)
    (F : ThreeSetLinkage G X Y) :
    Exists fun M : ThreeSetLinkage G X Y =>
      L.sourceSet ⊆ Set.range M.source ∧
        L.targetSet ⊆ Set.range M.target := by
  let E := L.extensionToThreeOfFullThree hn F
  exact
    ⟨E.linkage.toThreeSetLinkage,
      E.sourceSet_subset,
      E.targetSet_subset⟩

def symm
    {X Y : Set V} {n : Nat}
    (L : PartialSetLinkage G X Y n) :
    PartialSetLinkage G Y X n where
  source := L.target
  target := L.source
  source_mem := L.target_mem
  target_mem := L.source_mem
  source_injective := L.target_injective
  target_injective := L.source_injective
  path i := (L.path i).reverse
  isPath i := (L.isPath i).reverse
  pairwise_vertex_disjoint := by
    intro i j hij
    simpa [SimpleGraph.Walk.support_reverse] using
      L.pairwise_vertex_disjoint i j hij
  source_clean := by
    intro i z hz hzY
    exact L.target_clean i z (by
      simpa [SimpleGraph.Walk.support_reverse] using hz) hzY
  target_clean := by
    intro i z hz hzX
    exact L.source_clean i z (by
      simpa [SimpleGraph.Walk.support_reverse] using hz) hzX

end PartialSetLinkage

end Schematic.Math.GraphTheory
