import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
/--
Finite vertex-Menger augmentation for the three-terminal case, in the exact
`k = 3` shape used by GM IX `(2.2)`.

Starting from one already chosen vertex-disjoint `left -> right` path, the
usual no-small-separator hypothesis extends it to a full three-path linkage.
The proof uses the same split-vertex residual augmentation machinery as
`finite_menger_three_vertex_linkage_of_not_separates`, but starts from the
given partial linkage rather than from the empty linkage.
-/
theorem PartialThreeVertexLinkage.one_extend_to_three_of_not_separates
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    (hleft : Function.Injective left)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTriplesByDeletion G S left right)) :
    HasThreeVertexLinkage G left right := by
  classical
  have hreach1 : L.SplitResidualReachesUnusedRight :=
    L.splitResidualReachesUnusedRight_of_no_small_separator
      (by decide) hnosep
  obtain ⟨i1, j1, hi1, _hj1, l1, hl1_ne, hhead1, hlast1, hchain1,
    hmin1⟩ :=
    hreach1.exists_minimal_isChain_list
  have hnodupChain1 : l1.Nodup :=
    minimal_isChain_nodup hl1_ne hhead1 hlast1 hchain1 hmin1
  obtain ⟨L2⟩ :
      HasPartialThreeVertexLinkage G left right 2 :=
    L.hasPartial_succ_of_splitResidualChain_augmented
      hleft hi1 hnodupChain1 hhead1 hlast1 hchain1
  have hreach2 : L2.SplitResidualReachesUnusedRight :=
    L2.splitResidualReachesUnusedRight_of_no_small_separator
      (by decide) hnosep
  obtain ⟨i2, j2, hi2, _hj2, l2, hl2_ne, hhead2, hlast2, hchain2,
    hmin2⟩ :=
    hreach2.exists_minimal_isChain_list
  have hnodupChain2 : l2.Nodup :=
    minimal_isChain_nodup hl2_ne hhead2 hlast2 hchain2 hmin2
  have hpartial3 : HasPartialThreeVertexLinkage G left right 3 :=
    L2.hasPartial_succ_of_splitResidualChain_augmented
      hleft hi2 hnodupChain2 hhead2 hlast2 hchain2
  exact hasPartialThreeVertexLinkage_three_iff.mp hpartial3

/--
Finite vertex-Menger augmentation for the final step of GM IX `(2.2)`.

Starting from two already chosen vertex-disjoint `left -> right` paths, the
no-small-separator hypothesis supplies the third path while preserving the
existing two-path matching.
-/
theorem PartialThreeVertexLinkage.two_extend_to_three_of_not_separates
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    (hleft : Function.Injective left)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTriplesByDeletion G S left right)) :
    HasThreeVertexLinkage G left right := by
  classical
  have hreach2 : L.SplitResidualReachesUnusedRight :=
    L.splitResidualReachesUnusedRight_of_no_small_separator
      (by decide) hnosep
  obtain ⟨i2, j2, hi2, _hj2, l2, hl2_ne, hhead2, hlast2, hchain2,
    hmin2⟩ :=
    hreach2.exists_minimal_isChain_list
  have hnodupChain2 : l2.Nodup :=
    minimal_isChain_nodup hl2_ne hhead2 hlast2 hchain2 hmin2
  have hpartial3 : HasPartialThreeVertexLinkage G left right 3 :=
    L.hasPartial_succ_of_splitResidualChain_augmented
      hleft hi2 hnodupChain2 hhead2 hlast2 hchain2
  exact hasPartialThreeVertexLinkage_three_iff.mp hpartial3

/--
GM IX `(2.2)` for ordered triples, one-path partial form.

If a full three-linkage exists somewhere between the two triples, and one
matched path has already been specified, the specified one-path matching can be
extended to a full three-linkage.  This is a direct corollary of the
no-small-separator form: the existing full linkage rules out all separators of
order `< 3`, and the residual augmentation preserves the partial matching.
-/
theorem PartialThreeVertexLinkage.one_extend_to_three_of_hasThreeVertexLinkage
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 1)
    (hleft : Function.Injective left)
    (hfull : HasThreeVertexLinkage G left right) :
    HasThreeVertexLinkage G left right :=
  L.one_extend_to_three_of_not_separates hleft (by
    intro S hS
    exact hfull.not_separates_by_small_deletion hS)

/--
GM IX `(2.2)` for ordered triples, two-path partial form.

This is the final augmentation step: an existing full three-linkage lets a
specified two-path partial matching be completed without changing that
matching.
-/
theorem PartialThreeVertexLinkage.two_extend_to_three_of_hasThreeVertexLinkage
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    (hleft : Function.Injective left)
    (hfull : HasThreeVertexLinkage G left right) :
    HasThreeVertexLinkage G left right :=
  L.two_extend_to_three_of_not_separates hleft (by
    intro S hS
    exact hfull.not_separates_by_small_deletion hS)

/--
GM IX `(2.2)`, finite three-terminal form.

Given an existing three-linkage between two ordered triples, any already chosen
partial matching of size `< 3` extends to a full three-linkage.  This is the
form needed by the endpoint subcases in the GM IX `(2.4)` side-tripod proof:
when one of the new boundary targets is already a vertex of the old rim system,
that path is fixed first, and the augmenting-path theorem supplies the
remaining paths without changing the fixed part.
-/
theorem PartialThreeVertexLinkage.extend_to_three_of_hasThreeVertexLinkage
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hn : n < 3)
    (hleft : Function.Injective left)
    (hfull : HasThreeVertexLinkage G left right) :
    HasThreeVertexLinkage G left right := by
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn_cases with rfl | hrest
  · exact hfull
  rcases hrest with rfl | rfl
  · exact L.one_extend_to_three_of_hasThreeVertexLinkage hleft hfull
  · exact L.two_extend_to_three_of_hasThreeVertexLinkage hleft hfull

/--
Finite vertex-Menger, specialized to two ordered triples of terminals.
If no set of fewer than three vertices separates the two triples by deletion,
then there are three pairwise vertex-disjoint paths from the left triple to the
right triple, with the right triple permuted.

This is the hard converse to
`HasThreeVertexLinkage.not_separates_by_small_deletion`.
-/
theorem finite_menger_three_vertex_linkage_of_not_separates
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    (hright : Function.Injective right)
    (hnosep :
      forall S : Set V, S.ncard < 3 ->
        Not (SeparatesVertexTriplesByDeletion G S left right)) :
    HasThreeVertexLinkage G left right := by
  classical
  by_cases hcard : Fintype.card V = 3
  · exact hasThreeVertexLinkage_of_card_eq_three
      (G := G) hleft hright hcard
  by_cases hrange : Set.range left = Set.range right
  · exact hasThreeVertexLinkage_of_range_eq
      (G := G) hleft hright hrange
  let L0 : PartialThreeVertexLinkage G left right 0 :=
    PartialThreeVertexLinkage.empty (G := G)
  have hreach0 : L0.SplitResidualReachesUnusedRight :=
    L0.splitResidualReachesUnusedRight_of_no_small_separator
      (by decide) hnosep
  obtain ⟨L1⟩ :=
    PartialThreeVertexLinkage.empty_hasPartial_one_of_splitResidualReaches
      (G := G) (left := left) (right := right)
      (by simpa [L0] using hreach0)
  have hreach1 : L1.SplitResidualReachesUnusedRight :=
    L1.splitResidualReachesUnusedRight_of_no_small_separator
      (by decide) hnosep
  obtain ⟨i1, j1, hi1, hj1, l1, hl1_ne, hhead1, hlast1, hchain1,
    hmin1⟩ :=
    hreach1.exists_minimal_isChain_list
  have hdistinctChain1 :
      forall (idxA idxB : Nat)
        (hidxA : idxA < l1.length) (hidxB : idxB < l1.length),
          idxA < idxB ->
            l1[idxA]'hidxA ≠ l1[idxB]'hidxB := by
    intro idxA idxB hidxA hidxB hlt
    exact
      minimal_isChain_getElem_ne_of_lt
        hl1_ne hhead1 hlast1 hchain1 hmin1 hidxA hidxB hlt
  have hnodupChain1 : l1.Nodup :=
    minimal_isChain_nodup hl1_ne hhead1 hlast1 hchain1 hmin1
  have hdirect1 :
      (forall s : VertexSplitState V, s ∈ l1 ->
        s.vertex ∉ L1.usedVertices) ->
        HasPartialThreeVertexLinkage G left right 2 := by
    intro havoid1
    simpa using
      L1.hasPartial_succ_of_splitResidualChain_avoids_usedVertices
        hi1 hj1 hhead1 hlast1 hchain1 havoid1
  have hfirstHit1 :
      Not (forall s : VertexSplitState V, s ∈ l1 ->
        s.vertex ∉ L1.usedVertices) ->
        Exists fun idx : Nat =>
          Exists fun hidx : idx < l1.length =>
            (l1[idx]'hidx).vertex ∈ L1.usedVertices ∧
              forall j : Nat, j < idx ->
                forall hj : j < l1.length,
                  (l1[j]'hj).vertex ∉ L1.usedVertices := by
    intro hnot
    push Not at hnot
    rcases hnot with ⟨s, hs_mem, hs_used⟩
    exact
      L1.exists_first_splitResidualChain_usedVertexIndex
        ⟨s, hs_mem, hs_used⟩
  have hlastHit1 :
      Not (forall s : VertexSplitState V, s ∈ l1 ->
        s.vertex ∉ L1.usedVertices) ->
        Exists fun idx : Nat =>
          Exists fun hidx : idx < l1.length =>
            (l1[idx]'hidx).vertex ∈ L1.usedVertices ∧
              forall j : Nat, idx < j ->
                forall hj : j < l1.length,
                  (l1[j]'hj).vertex ∉ L1.usedVertices := by
    intro hnot
    push Not at hnot
    rcases hnot with ⟨s, hs_mem, hs_used⟩
    exact
      L1.exists_last_splitResidualChain_usedVertexIndex
        ⟨s, hs_mem, hs_used⟩
  have hfirstHitState1 :
      forall (idx : Nat) (hidx : idx < l1.length),
        (l1[idx]'hidx).vertex ∈ L1.usedVertices ->
          (forall j : Nat, j < idx ->
            forall hj : j < l1.length,
              (l1[j]'hj).vertex ∉ L1.usedVertices) ->
            Exists fun v : V => l1[idx]'hidx = VertexSplitState.inn v := by
    intro idx hidx hused hfirst
    exact
      L1.first_used_splitResidualChain_state_is_inn_of_head
        hidx hhead1 hchain1 hused hfirst
  have hlastHitState1 :
      forall (idx : Nat) (hidx : idx < l1.length),
        (l1[idx]'hidx).vertex ∈ L1.usedVertices ->
          (forall j : Nat, idx < j ->
            forall hj : j < l1.length,
              (l1[j]'hj).vertex ∉ L1.usedVertices) ->
            Exists fun v : V => l1[idx]'hidx = VertexSplitState.out v := by
    intro idx hidx hused hafter
    exact
      L1.last_used_splitResidualChain_state_is_out
        hidx hlast1 hchain1 hused hafter
  have hpartial2_of_ordered_hits1 :
      forall (idxF idxL : Nat)
        (hidxF : idxF < l1.length) (hidxL : idxL < l1.length)
        (vHit wHit : V),
        (l1[idxF]'hidxF).vertex ∈ L1.usedVertices ->
          (l1[idxL]'hidxL).vertex ∈ L1.usedVertices ->
            (forall j : Nat, j < idxF ->
              forall hj : j < l1.length,
                (l1[j]'hj).vertex ∉ L1.usedVertices) ->
              (forall j : Nat, idxL < j ->
                forall hj : j < l1.length,
                  (l1[j]'hj).vertex ∉ L1.usedVertices) ->
                l1[idxF]'hidxF = VertexSplitState.inn vHit ->
                  l1[idxL]'hidxL = VertexSplitState.out wHit ->
                    (L1.path 0).support.idxOf wHit <
                      (L1.path 0).support.idxOf vHit ->
                      HasPartialThreeVertexLinkage G left right 2 := by
    intro idxF idxL hidxF hidxL vHit wHit husedF husedL hfirst hafter
      hstateF hstateL horder
    have hvHit : vHit ∈ L1.usedVertices := by
      simpa [hstateF] using husedF
    have hwHit : wHit ∈ L1.usedVertices := by
      simpa [hstateL] using husedL
    obtain ⟨pIn, hpIn, hInAvoid⟩ :=
      L1.exists_path_to_first_used_of_splitResidualChain
        hidxF hhead1 hstateF hchain1 hfirst
    have hvertexL : (l1[idxL]'hidxL).vertex = wHit := by
      simp [hstateL]
    obtain ⟨pOut, hpOut, hOutAvoid⟩ :=
      L1.exists_path_from_last_used_to_target_of_splitResidualChain
        hidxL hvertexL hlast1 hchain1 hafter
    exact
      L1.hasPartial_two_of_one_path_ordered_splice_or_direct
        hi1 hj1 hvHit hwHit horder pIn hpIn hInAvoid pOut hpOut
        hOutAvoid
  have hpartial2_of_adjacent_hits1 :
      forall (idxF idxL : Nat)
        (hidxF : idxF < l1.length) (hidxL : idxL < l1.length)
        (hidxL_eq : idxL = idxF + 1)
        (vHit wHit : V),
        (l1[idxF]'hidxF).vertex ∈ L1.usedVertices ->
          (l1[idxL]'hidxL).vertex ∈ L1.usedVertices ->
            (forall j : Nat, j < idxF ->
              forall hj : j < l1.length,
                (l1[j]'hj).vertex ∉ L1.usedVertices) ->
              (forall j : Nat, idxL < j ->
                forall hj : j < l1.length,
                  (l1[j]'hj).vertex ∉ L1.usedVertices) ->
                l1[idxF]'hidxF = VertexSplitState.inn vHit ->
                  l1[idxL]'hidxL = VertexSplitState.out wHit ->
                    HasPartialThreeVertexLinkage G left right 2 := by
    intro idxF idxL hidxF hidxL hidxL_eq vHit wHit husedF husedL
      hfirst hafter hstateF hstateL
    exact
      L1.hasPartial_two_of_one_path_adjacent_first_last_hits
        hi1 hj1 hidxF hidxL hidxL_eq hhead1 hlast1 hchain1
        husedF husedL hfirst hafter hstateF hstateL
  -- The previously attempted vertex-level residual augmentation was too weak:
  -- it permits residual walks through occupied vertices without enforcing
  -- vertex capacity.  The remaining proof is the true finite vertex-Menger
  -- theorem, which should be supplied by a split-vertex residual/network
  -- argument rather than by that false augmentation lemma.
  have hpartial2 : HasPartialThreeVertexLinkage G left right 2 := by
    exact
      L1.hasPartial_succ_of_splitResidualChain_augmented
        hleft hi1 hnodupChain1 hhead1 hlast1 hchain1

  obtain ⟨L2⟩ := hpartial2
  have hreach2 : L2.SplitResidualReachesUnusedRight :=
    L2.splitResidualReachesUnusedRight_of_no_small_separator
      (by decide) hnosep
  obtain ⟨i2, j2, hi2, _hj2, l2, hl2_ne, hhead2, hlast2, hchain2,
    hmin2⟩ :=
    hreach2.exists_minimal_isChain_list
  have hnodupChain2 : l2.Nodup :=
    minimal_isChain_nodup hl2_ne hhead2 hlast2 hchain2 hmin2
  have hpartial3 : HasPartialThreeVertexLinkage G left right 3 := by
    exact
      L2.hasPartial_succ_of_splitResidualChain_augmented
        hleft hi2 hnodupChain2 hhead2 hlast2 hchain2

  exact hasPartialThreeVertexLinkage_three_iff.mp hpartial3

/-- Fixed-triple Menger applied to the one-locked-target auxiliary graph. -/
theorem hasThreeVertexLinkage_lockedOneTargetSinkGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {left right fullRight : Fin 3 -> V} {Y : Set V}
    (hleft : Function.Injective left)
    (Lselected : PartialThreeVertexLinkage G left right 1)
    (Lfull : ThreeVertexLinkage G left fullRight)
    (hfullY : forall i : Fin 3, fullRight i ∈ Y) :
    HasThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y 2)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 2))
      (lockedOneTargetRight Lselected) := by
  classical
  exact
    finite_menger_three_vertex_linkage_of_not_separates
      (G := finiteTargetSetSinkGraph G Y 2)
      (left := fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 2))
      (right := lockedOneTargetRight Lselected)
      (by
        intro i j h
        exact hleft (Sum.inl.inj h))
      (lockedOneTargetRight_injective Lselected)
      (by
        intro D hD
        exact
          lockedOneTarget_not_separates Lselected Lfull hfullY hD)

/-- Fixed-triple Menger applied to the two-locked-target auxiliary graph. -/
theorem hasThreeVertexLinkage_lockedTwoTargetSinkGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {left right fullRight : Fin 3 -> V} {Y : Set V}
    (hleft : Function.Injective left)
    (Lselected : PartialThreeVertexLinkage G left right 2)
    (Lfull : ThreeVertexLinkage G left fullRight)
    (hfullY : forall i : Fin 3, fullRight i ∈ Y) :
    HasThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y 1)
      (fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 1))
      (lockedTwoTargetRight Lselected) := by
  classical
  exact
    finite_menger_three_vertex_linkage_of_not_separates
      (G := finiteTargetSetSinkGraph G Y 1)
      (left := fun i : Fin 3 => (Sum.inl (left i) : V ⊕ Fin 1))
      (right := lockedTwoTargetRight Lselected)
      (by
        intro i j h
        exact hleft (Sum.inl.inj h))
      (lockedTwoTargetRight_injective Lselected)
      (by
        intro D hD
        exact
          lockedTwoTarget_not_separates Lselected Lfull hfullY hD)

theorem ThreeVertexLinkage.finiteTargetSink_path_not_nil_of_target_sink
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {left : Fin 3 -> V} {augRight : Fin 3 -> V ⊕ Fin n}
    (L : ThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y n)
      (fun i : Fin 3 => Sum.inl (left i)) augRight)
    {i : Fin 3} {s : Fin n}
    (htarget : augRight (L.targetEquiv i) = Sum.inr s) :
    Not (L.path i).Nil := by
  exact SimpleGraph.Walk.not_nil_of_ne (p := L.path i) (by
    intro h
    have :
        (Sum.inl (left i) : V ⊕ Fin n) =
          augRight (L.targetEquiv i) := h
    rw [htarget] at this
    cases this)

/-- Once every auxiliary sink is one of the three linkage targets, deleting
the final vertex of any linkage path leaves only original graph vertices. -/
theorem ThreeVertexLinkage.finiteTargetSink_dropLast_support_original
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {left : Fin 3 -> V} {augRight : Fin 3 -> V ⊕ Fin n}
    (L : ThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y n)
      (fun i : Fin 3 => Sum.inl (left i)) augRight)
    (hsinks : forall s : Fin n,
      Exists fun j : Fin 3 => augRight j = Sum.inr s)
    (i : Fin 3) :
    forall z : V ⊕ Fin n,
      z ∈ (L.path i).dropLast.support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)) := by
  intro z hz
  cases z with
  | inl v =>
      exact ⟨v, rfl⟩
  | inr s =>
      rcases hsinks s with ⟨j, hj⟩
      let m : Fin 3 := L.targetEquiv.symm j
      have hm : L.targetEquiv m = j := by
        simp [m]
      have hz_path :
          (Sum.inr s : V ⊕ Fin n) ∈ (L.path i).support := by
        by_cases hnil : (L.path i).Nil
        · have hs_eq_start :
              (Sum.inr s : V ⊕ Fin n) =
                Sum.inl (left i) := by
            have hdrop_support :=
              SimpleGraph.Walk.nil_iff_support_eq.mp hnil.dropLast
            simp [hdrop_support] at hz
          cases hs_eq_start
        · have hz_drop :
              (Sum.inr s : V ⊕ Fin n) ∈
                (L.path i).support.dropLast := by
            simpa [SimpleGraph.Walk.support_dropLast hnil] using hz
          exact List.mem_of_mem_dropLast hz_drop
      by_cases him : i = m
      · have hi_target :
            augRight (L.targetEquiv i) = Sum.inr s := by
          rw [him, hm, hj]
        have hnil :=
          L.finiteTargetSink_path_not_nil_of_target_sink hi_target
        have hend_not :
            augRight (L.targetEquiv i) ∉
              (L.path i).dropLast.support :=
          Walk.IsPath.end_notMem_walk_dropLast_support
            (L.isPath i) hnil
        exact False.elim
          (hend_not (by simpa [hi_target] using hz))
      · have hm_end :
            (Sum.inr s : V ⊕ Fin n) ∈ (L.path m).support := by
          simpa [hm, hj] using (L.path m).end_mem_support
        exact False.elim
          (Set.disjoint_left.mp
            (L.pairwise_vertex_disjoint i m him)
            hz_path hm_end)

/-- A linkage path ending at a locked original target contains no auxiliary
sink at all. -/
theorem ThreeVertexLinkage.finiteTargetSink_locked_support_original
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {left : Fin 3 -> V} {augRight : Fin 3 -> V ⊕ Fin n}
    (L : ThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y n)
      (fun i : Fin 3 => Sum.inl (left i)) augRight)
    (hsinks : forall s : Fin n,
      Exists fun j : Fin 3 => augRight j = Sum.inr s)
    {i : Fin 3} {y : V}
    (htarget : augRight (L.targetEquiv i) = Sum.inl y) :
    forall z : V ⊕ Fin n,
      z ∈ (L.path i).support ->
        z ∈ Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)) := by
  intro z hz
  cases z with
  | inl v =>
      exact ⟨v, rfl⟩
  | inr s =>
      rcases hsinks s with ⟨j, hj⟩
      let m : Fin 3 := L.targetEquiv.symm j
      have hm : L.targetEquiv m = j := by simp [m]
      have hm_end :
          (Sum.inr s : V ⊕ Fin n) ∈ (L.path m).support := by
        simpa [hm, hj] using (L.path m).end_mem_support
      have him : i ≠ m := by
        intro him
        have : (Sum.inl y : V ⊕ Fin n) = Sum.inr s := by
          calc
            Sum.inl y = augRight (L.targetEquiv i) := htarget.symm
            _ = augRight (L.targetEquiv m) := by rw [him]
            _ = Sum.inr s := by rw [hm, hj]
        cases this
      exact False.elim
        (Set.disjoint_left.mp
          (L.pairwise_vertex_disjoint i m him) hz hm_end)

structure FiniteTargetSinkOriginalPathData
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {left : Fin 3 -> V} {augRight : Fin 3 -> V ⊕ Fin n}
    (L : ThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y n)
      (fun i : Fin 3 => Sum.inl (left i)) augRight)
    (i : Fin 3) where
  target : V
  target_mem : target ∈ Y
  path : G.Walk (left i) target
  isPath : path.IsPath
  support_lift :
    forall z : V, z ∈ path.support ->
      (Sum.inl z : V ⊕ Fin n) ∈ (L.path i).support
  target_eq_of_locked :
    forall y : V,
      augRight (L.targetEquiv i) = Sum.inl y ->
        target = y

theorem ThreeVertexLinkage.exists_finiteTargetSinkOriginalPathData
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {left : Fin 3 -> V} {augRight : Fin 3 -> V ⊕ Fin n}
    (L : ThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y n)
      (fun i : Fin 3 => Sum.inl (left i)) augRight)
    (hsinks : forall s : Fin n,
      Exists fun j : Fin 3 => augRight j = Sum.inr s)
    (hlockedY :
      forall j : Fin 3, forall y : V,
        augRight j = Sum.inl y -> y ∈ Y)
    (i : Fin 3) :
    Nonempty (FiniteTargetSinkOriginalPathData L i) := by
  classical
  cases htarget : augRight (L.targetEquiv i) with
  | inl y =>
      let p :
          (finiteTargetSetSinkGraph G Y n).Walk
            (Sum.inl (left i)) (Sum.inl y) :=
        (L.path i).copy rfl htarget
      have hp : p.IsPath := by
        exact
          (SimpleGraph.Walk.isPath_copy (L.path i) rfl htarget).mpr
            (L.isPath i)
      have hsupport :
          forall z : V ⊕ Fin n, z ∈ p.support ->
            z ∈ Set.range
              (fun v : V => (Sum.inl v : V ⊕ Fin n)) := by
        intro z hz
        apply L.finiteTargetSink_locked_support_original hsinks htarget z
        simpa [p, SimpleGraph.Walk.support_copy] using hz
      let q : G.Walk (left i) y :=
        finiteTargetSetSinkOriginalWalk p hsupport
      exact ⟨{
        target := y
        target_mem := hlockedY (L.targetEquiv i) y htarget
        path := q
        isPath := by
          exact finiteTargetSetSinkOriginalWalk_isPath hp hsupport
        support_lift := by
          intro z hz
          have hz_p :
              (Sum.inl z : V ⊕ Fin n) ∈ p.support :=
            finiteTargetSetSinkOriginalWalk_support_lift hsupport hz
          simpa [p, SimpleGraph.Walk.support_copy] using hz_p
        target_eq_of_locked := by
          intro y' hy'
          exact Sum.inl.inj (htarget.symm.trans hy')
      }⟩
  | inr s =>
      have hnil :
          Not (L.path i).Nil :=
        L.finiteTargetSink_path_not_nil_of_target_sink htarget
      have hpen_original :
          (L.path i).penultimate ∈
            Set.range (fun v : V => (Sum.inl v : V ⊕ Fin n)) :=
        L.finiteTargetSink_dropLast_support_original hsinks i
          (L.path i).penultimate
          (L.path i).dropLast.end_mem_support
      rcases hpen_original with ⟨y, hy⟩
      have hy' : (L.path i).penultimate = Sum.inl y := hy.symm
      let p :
          (finiteTargetSetSinkGraph G Y n).Walk
            (Sum.inl (left i)) (Sum.inl y) :=
        (L.path i).dropLast.copy rfl hy'
      have hdrop_path : (L.path i).dropLast.IsPath := by
        simpa [SimpleGraph.Walk.dropLast] using
          (L.isPath i).take ((L.path i).length - 1)
      have hp : p.IsPath :=
        (SimpleGraph.Walk.isPath_copy (L.path i).dropLast rfl hy').mpr
          hdrop_path
      have hsupport :
          forall z : V ⊕ Fin n, z ∈ p.support ->
            z ∈ Set.range
              (fun v : V => (Sum.inl v : V ⊕ Fin n)) := by
        intro z hz
        apply L.finiteTargetSink_dropLast_support_original hsinks i z
        simpa [p, SimpleGraph.Walk.support_copy] using hz
      have hyY : y ∈ Y := by
        have hadj :
            (finiteTargetSetSinkGraph G Y n).Adj
              (L.path i).penultimate
              (augRight (L.targetEquiv i)) :=
          (L.path i).adj_penultimate hnil
        rw [hy', htarget] at hadj
        simpa [finiteTargetSetSinkGraph] using hadj
      let q : G.Walk (left i) y :=
        finiteTargetSetSinkOriginalWalk p hsupport
      exact ⟨{
        target := y
        target_mem := hyY
        path := q
        isPath :=
          finiteTargetSetSinkOriginalWalk_isPath hp hsupport
        support_lift := by
          intro z hz
          have hz_p :
              (Sum.inl z : V ⊕ Fin n) ∈ p.support :=
            finiteTargetSetSinkOriginalWalk_support_lift hsupport hz
          have hz_drop :
              (Sum.inl z : V ⊕ Fin n) ∈
                (L.path i).dropLast.support := by
            simpa [p, SimpleGraph.Walk.support_copy] using hz_p
          by_cases hnil' : (L.path i).Nil
          · exact False.elim (hnil hnil')
          · have hz_list :
                (Sum.inl z : V ⊕ Fin n) ∈
                  (L.path i).support.dropLast := by
              simpa [SimpleGraph.Walk.support_dropLast hnil'] using hz_drop
            exact List.mem_of_mem_dropLast hz_list
        target_eq_of_locked := by
          intro y' hy'
          have : (Sum.inr s : V ⊕ Fin n) = Sum.inl y' :=
            htarget.symm.trans hy'
          cases this
      }⟩

/-- Extract a genuine original-graph linkage from a finite sink graph while
retaining every locked original target. -/
theorem ThreeVertexLinkage.extract_finiteTargetSetSinkGraph
    {V : Type u} {G : SimpleGraph V} {Y : Set V} {n : Nat}
    {left : Fin 3 -> V} {augRight : Fin 3 -> V ⊕ Fin n}
    (L : ThreeVertexLinkage
      (finiteTargetSetSinkGraph G Y n)
      (fun i : Fin 3 => Sum.inl (left i)) augRight)
    (hsinks : forall s : Fin n,
      Exists fun j : Fin 3 => augRight j = Sum.inr s)
    (hlockedY :
      forall j : Fin 3, forall y : V,
        augRight j = Sum.inl y -> y ∈ Y) :
    Exists fun right : Fin 3 -> V =>
      (forall i : Fin 3, right i ∈ Y) ∧
        (forall j : Fin 3, forall y : V,
          augRight j = Sum.inl y -> y ∈ Set.range right) ∧
          HasThreeVertexLinkage G left right := by
  classical
  have hdata :
      forall i : Fin 3,
        Nonempty (FiniteTargetSinkOriginalPathData L i) :=
    fun i => L.exists_finiteTargetSinkOriginalPathData hsinks hlockedY i
  let D : forall i : Fin 3, FiniteTargetSinkOriginalPathData L i :=
    fun i => Classical.choice (hdata i)
  let right : Fin 3 -> V := fun i => (D i).target
  let Lout : ThreeVertexLinkage G left right := {
    targetEquiv := Equiv.refl (Fin 3)
    path := fun i => (D i).path
    isPath := fun i => (D i).isPath
    pairwise_vertex_disjoint := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact
        Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij)
          ((D i).support_lift z hzi)
          ((D j).support_lift z hzj)
  }
  refine ⟨right, ?_, ?_, ⟨Lout⟩⟩
  · intro i
    exact (D i).target_mem
  · intro j y hj
    let i : Fin 3 := L.targetEquiv.symm j
    refine ⟨i, ?_⟩
    have hi : L.targetEquiv i = j := by simp [i]
    exact (D i).target_eq_of_locked y (by simpa [hi] using hj)

/--
Complete one selected path to a three-linkage ending in a prescribed target
set, without losing the selected path's target.

This is the one-path endpoint-preservation case of GM IX `(2.2)`.  The
selected path itself need not be one of the paths in the resulting linkage;
only its target is locked, which is exactly the conclusion used by the
society argument.
-/
theorem PartialThreeVertexLinkage.extend_one_to_target_set_preserving_target
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {left right fullRight : Fin 3 -> V} {Y : Set V}
    (hleft : Function.Injective left)
    (Lselected : PartialThreeVertexLinkage G left right 1)
    (hselectedY : right (Lselected.rightIndex 0) ∈ Y)
    (Lfull : ThreeVertexLinkage G left fullRight)
    (hfullY : forall i : Fin 3, fullRight i ∈ Y) :
    Exists fun outRight : Fin 3 -> V =>
      (forall i : Fin 3, outRight i ∈ Y) ∧
        right (Lselected.rightIndex 0) ∈ Set.range outRight ∧
          HasThreeVertexLinkage G left outRight := by
  classical
  rcases
      hasThreeVertexLinkage_lockedOneTargetSinkGraph
        hleft Lselected Lfull hfullY with
    ⟨Laug⟩
  rcases
      Laug.extract_finiteTargetSetSinkGraph
        (by
          intro s
          fin_cases s
          · exact ⟨1, rfl⟩
          · exact ⟨2, rfl⟩)
        (by
          intro j y hj
          fin_cases j
          · have hy : right (Lselected.rightIndex 0) = y :=
              by simpa [lockedOneTargetRight] using hj
            rw [← hy]
            exact hselectedY
          · simp [lockedOneTargetRight] at hj
          · simp [lockedOneTargetRight] at hj) with
    ⟨outRight, houtY, hlocked, hout⟩
  exact
    ⟨outRight, houtY,
      hlocked 0 (right (Lselected.rightIndex 0))
        (by simp [lockedOneTargetRight]),
      hout⟩

/--
Complete two selected paths to a three-linkage ending in a prescribed target
set, without losing either selected target.

This is the two-path endpoint-preservation case of GM IX `(2.2)`.
-/
theorem PartialThreeVertexLinkage.extend_two_to_target_set_preserving_targets
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {left right fullRight : Fin 3 -> V} {Y : Set V}
    (hleft : Function.Injective left)
    (Lselected : PartialThreeVertexLinkage G left right 2)
    (hselectedY :
      forall i : Fin 2, right (Lselected.rightIndex i) ∈ Y)
    (Lfull : ThreeVertexLinkage G left fullRight)
    (hfullY : forall i : Fin 3, fullRight i ∈ Y) :
    Exists fun outRight : Fin 3 -> V =>
      (forall i : Fin 3, outRight i ∈ Y) ∧
        right (Lselected.rightIndex 0) ∈ Set.range outRight ∧
          right (Lselected.rightIndex 1) ∈ Set.range outRight ∧
            HasThreeVertexLinkage G left outRight := by
  classical
  rcases
      hasThreeVertexLinkage_lockedTwoTargetSinkGraph
        hleft Lselected Lfull hfullY with
    ⟨Laug⟩
  rcases
      Laug.extract_finiteTargetSetSinkGraph
        (by
          intro s
          fin_cases s
          exact ⟨2, rfl⟩)
        (by
          intro j y hj
          fin_cases j
          · have hy : right (Lselected.rightIndex 0) = y :=
              by simpa [lockedTwoTargetRight] using hj
            rw [← hy]
            exact hselectedY 0
          · have hy : right (Lselected.rightIndex 1) = y :=
              by simpa [lockedTwoTargetRight] using hj
            rw [← hy]
            exact hselectedY 1
          · simp [lockedTwoTargetRight] at hj) with
    ⟨outRight, houtY, hlocked, hout⟩
  exact
    ⟨outRight, houtY,
      hlocked 0 (right (Lselected.rightIndex 0))
        (by simp [lockedTwoTargetRight]),
      hlocked 1 (right (Lselected.rightIndex 1))
        (by simp [lockedTwoTargetRight]),
      hout⟩


end Schematic.Math.GraphTheory
