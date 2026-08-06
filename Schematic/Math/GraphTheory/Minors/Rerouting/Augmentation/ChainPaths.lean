import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.ChainDisjointness

/-! Paths extracted from initial, final, and intermediate residual-chain blocks. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.exists_path_to_first_used_of_splitResidualChain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {iNew : Fin 3} {l : List (VertexSplitState V)} {idx : Nat}
    (hidx : idx < l.length)
    {vHit : V}
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hstate : l[idx]'hidx = VertexSplitState.inn vHit)
    (hchain : l.IsChain L.SplitResidualStep)
    (hfirst : forall j : Nat, j < idx ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun p : G.Walk (left iNew) vHit =>
      p.IsPath ∧ forall x : V, x ∈ p.support ->
        x ∉ L.usedVertices ∨ x = vHit := by
  classical
  let lp : List (VertexSplitState V) := l.take (idx + 1)
  let lv : List V := lp.map VertexSplitState.vertex
  have hchain_lp : lp.IsChain L.SplitResidualStep := by
    exact hchain.take (idx + 1)
  have hchain_v : lv.IsChain (fun u w : V => u = w ∨ G.Adj u w) := by
    change (lp.map VertexSplitState.vertex).IsChain
      (fun u w : V => u = w ∨ G.Adj u w)
    rw [List.isChain_map]
    exact hchain_lp.imp (fun {a b} h =>
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (a := a) (b := b) h)
  have hhead_lp : lp.head? =
      some (VertexSplitState.inn (left iNew)) := by
    dsimp [lp]
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_take]
    simp
    rwa [← List.head?_eq_getElem?]
  have hlast_lp : lp.getLast? = some (VertexSplitState.inn vHit) := by
    dsimp [lp]
    rw [List.getLast?_eq_getElem?]
    have hlen : (l.take (idx + 1)).length = idx + 1 := by
      rw [List.length_take]
      omega
    rw [hlen]
    rw [Nat.add_sub_cancel]
    rw [List.getElem?_take]
    have hidxopt : l[idx]? = some (l[idx]'hidx) :=
      List.getElem?_eq_getElem hidx
    simp [hidxopt, hstate]
  have hhead_v : lv.head? = some (left iNew) := by
    simp [lv, List.head?_map, hhead_lp]
  have hlast_v : lv.getLast? = some vHit := by
    simp [lv, List.getLast?_map, hlast_lp]
  have hA :
      forall x : V, x ∈ lv ->
        x ∈ (L.usedVerticesᶜ ∪ {vHit} : Set V) := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨s, hs_lp, rfl⟩
    rw [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [List.mem_take_iff_getElem] at hs_lp
    rcases hs_lp with ⟨j, hjmin, hget⟩
    have hjlen : j < l.length := by
      have : j < min (idx + 1) l.length := hjmin
      exact lt_of_lt_of_le this (min_le_right _ _)
    have hsj : s = l[j]'hjlen := by
      rw [← hget]
    by_cases hjidx : j < idx
    · exact Or.inl (by simpa [hsj] using hfirst j hjidx hjlen)
    · have hjeq : j = idx := by
        have hjle : j <= idx := by
          have : j < idx + 1 := lt_of_lt_of_le hjmin (min_le_left _ _)
          omega
        omega
      subst j
      exact Or.inr (by simp [hsj, hstate])
  have hreach_ind :
      (G.induce (L.usedVerticesᶜ ∪ {vHit} : Set V)).Reachable
        ⟨left iNew, by
          have hx : left iNew ∈ lv := by
            have hmem : left iNew ∈ lv.head? := by simp [hhead_v]
            exact List.mem_of_mem_head? hmem
          exact hA _ hx⟩
        ⟨vHit, by exact Or.inr rfl⟩ := by
    simpa [lv] using
      reachable_induce_of_isChain_eq_or_adj
        (G := G) (A := (L.usedVerticesᶜ ∪ {vHit} : Set V))
        hchain_v hhead_v hlast_v hA
  have hleftA : left iNew ∈ (L.usedVerticesᶜ ∪ {vHit} : Set V) := by
    have hx : left iNew ∈ lv := by
      have hmem : left iNew ∈ lv.head? := by simp [hhead_v]
      exact List.mem_of_mem_head? hmem
    exact hA _ hx
  have hvA : vHit ∈ (L.usedVerticesᶜ ∪ {vHit} : Set V) := Or.inr rfl
  obtain ⟨p, hp, hsupport⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := (L.usedVerticesᶜ ∪ {vHit} : Set V))
      (u := left iNew) (v := vHit)
      hleftA hvA hreach_ind
  exact ⟨p, hp, by
    intro x hx
    exact hsupport x hx⟩

theorem PartialThreeVertexLinkage.exists_path_to_first_used_of_splitResidualChain_support_subset
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {iNew : Fin 3} {l : List (VertexSplitState V)} {idx : Nat}
    (hidx : idx < l.length)
    {vHit : V}
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hstate : l[idx]'hidx = VertexSplitState.inn vHit)
    (hchain : l.IsChain L.SplitResidualStep)
    (hfirst : forall j : Nat, j < idx ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun p : G.Walk (left iNew) vHit =>
      p.IsPath ∧
        (forall x : V, x ∈ p.support ->
          x ∉ L.usedVertices ∨ x = vHit) ∧
          forall x : V, x ∈ p.support ->
            Exists fun m : Nat =>
              Exists fun hm : m < l.length =>
                m <= idx ∧ (l[m]'hm).vertex = x := by
  classical
  let lp : List (VertexSplitState V) := l.take (idx + 1)
  let lv : List V := lp.map VertexSplitState.vertex
  have hchain_lp : lp.IsChain L.SplitResidualStep := by
    exact hchain.take (idx + 1)
  have hchain_v : lv.IsChain (fun u w : V => u = w ∨ G.Adj u w) := by
    change (lp.map VertexSplitState.vertex).IsChain
      (fun u w : V => u = w ∨ G.Adj u w)
    rw [List.isChain_map]
    exact hchain_lp.imp (fun {a b} h =>
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (a := a) (b := b) h)
  have hhead_lp : lp.head? =
      some (VertexSplitState.inn (left iNew)) := by
    dsimp [lp]
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_take]
    simp
    rwa [← List.head?_eq_getElem?]
  have hlast_lp : lp.getLast? = some (VertexSplitState.inn vHit) := by
    dsimp [lp]
    rw [List.getLast?_eq_getElem?]
    have hlen : (l.take (idx + 1)).length = idx + 1 := by
      rw [List.length_take]
      omega
    rw [hlen]
    rw [Nat.add_sub_cancel]
    rw [List.getElem?_take]
    have hidxopt : l[idx]? = some (l[idx]'hidx) :=
      List.getElem?_eq_getElem hidx
    simp [hidxopt, hstate]
  have hhead_v : lv.head? = some (left iNew) := by
    simp [lv, List.head?_map, hhead_lp]
  have hlast_v : lv.getLast? = some vHit := by
    simp [lv, List.getLast?_map, hlast_lp]
  have hlv_ne : lv ≠ [] := by
    intro hnil
    simp [hnil] at hhead_v
  obtain ⟨p, hp, hsupport_lv⟩ :=
    exists_path_of_isChain_eq_or_adj
      (G := G) hlv_ne hchain_v hhead_v hlast_v
  refine ⟨p, hp, ?_, ?_⟩
  · intro x hx
    have hx_lv : x ∈ lv := hsupport_lv x hx
    rcases List.mem_map.mp hx_lv with ⟨s, hs_lp, hsx⟩
    rw [List.mem_take_iff_getElem] at hs_lp
    rcases hs_lp with ⟨m, hmmin, hget⟩
    have hm : m < l.length := by
      exact lt_of_lt_of_le hmmin (min_le_right _ _)
    have hsm : s = l[m]'hm := by
      rw [← hget]
    have hmle : m <= idx := by
      have : m < idx + 1 := lt_of_lt_of_le hmmin (min_le_left _ _)
      omega
    have hmx : (l[m]'hm).vertex = x := by
      simpa [hsm] using hsx
    by_cases hmi : m = idx
    · subst m
      exact Or.inr (by
        have hvx : vHit = x := by
          simpa [hstate] using hmx
        exact hvx.symm)
    · have hmlt : m < idx := lt_of_le_of_ne hmle hmi
      exact Or.inl (by
        simpa [hmx] using hfirst m hmlt hm)
  · intro x hx
    have hx_lv : x ∈ lv := hsupport_lv x hx
    rcases List.mem_map.mp hx_lv with ⟨s, hs_lp, hsx⟩
    rw [List.mem_take_iff_getElem] at hs_lp
    rcases hs_lp with ⟨m, hmmin, hget⟩
    have hm : m < l.length := by
      exact lt_of_lt_of_le hmmin (min_le_right _ _)
    have hsm : s = l[m]'hm := by
      rw [← hget]
    have hmle : m <= idx := by
      have : m < idx + 1 := lt_of_lt_of_le hmmin (min_le_left _ _)
      omega
    have hmx : (l[m]'hm).vertex = x := by
      simpa [hsm] using hsx
    exact ⟨m, hm, hmle, hmx⟩

theorem PartialThreeVertexLinkage.exists_path_from_last_used_to_target_of_splitResidualChain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {jNew : Fin 3} {l : List (VertexSplitState V)} {idx : Nat}
    (hidx : idx < l.length)
    {vHit : V}
    (hvertex : (l[idx]'hidx).vertex = vHit)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (hafter : forall m : Nat, idx < m ->
      forall hm : m < l.length,
        (l[m]'hm).vertex ∉ L.usedVertices) :
    Exists fun p : G.Walk vHit (right jNew) =>
      p.IsPath ∧ forall x : V, x ∈ p.support ->
        x ∉ L.usedVertices ∨ x = vHit := by
  classical
  let lp : List (VertexSplitState V) := l.drop idx
  let lv : List V := lp.map VertexSplitState.vertex
  have hchain_lp : lp.IsChain L.SplitResidualStep := by
    exact hchain.drop idx
  have hchain_v : lv.IsChain (fun u w : V => u = w ∨ G.Adj u w) := by
    change (lp.map VertexSplitState.vertex).IsChain
      (fun u w : V => u = w ∨ G.Adj u w)
    rw [List.isChain_map]
    exact hchain_lp.imp (fun {a b} h =>
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (a := a) (b := b) h)
  have hhead_lp : lp.head? = some (l[idx]'hidx) := by
    dsimp [lp]
    rw [List.head?_drop]
    exact List.getElem?_eq_getElem hidx
  have hlast_lp :
      lp.getLast? = some (VertexSplitState.out (right jNew)) := by
    dsimp [lp]
    rw [List.getLast?_drop]
    simp [Nat.not_le_of_lt hidx, hlast]
  have hhead_v : lv.head? = some vHit := by
    simp [lv, List.head?_map, hhead_lp, hvertex]
  have hlast_v : lv.getLast? = some (right jNew) := by
    simp [lv, List.getLast?_map, hlast_lp]
  have hA :
      forall x : V, x ∈ lv ->
        x ∈ (L.usedVerticesᶜ ∪ {vHit} : Set V) := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨s, hs_lp, rfl⟩
    rw [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [List.mem_drop_iff_getElem] at hs_lp
    rcases hs_lp with ⟨j, hjlen, hget⟩
    have hmLen : idx + j < l.length := by
      simpa [Nat.add_comm] using hjlen
    have hsj : s = l[idx + j]'hmLen := by
      rw [← hget]
    by_cases hj0 : j = 0
    · subst j
      exact Or.inr (by simpa [hsj] using hvertex)
    · have hlt : idx < idx + j := by
        omega
      exact Or.inl (by simpa [hsj] using hafter (idx + j) hlt hmLen)
  have hreach_ind :
      (G.induce (L.usedVerticesᶜ ∪ {vHit} : Set V)).Reachable
        ⟨vHit, by exact Or.inr rfl⟩
        ⟨right jNew, by
          have hx : right jNew ∈ lv := by
            have hmem : right jNew ∈ lv.getLast? := by simp [hlast_v]
            exact List.mem_of_mem_getLast? hmem
          exact hA _ hx⟩ := by
    simpa [lv] using
      reachable_induce_of_isChain_eq_or_adj
        (G := G) (A := (L.usedVerticesᶜ ∪ {vHit} : Set V))
        hchain_v hhead_v hlast_v hA
  have hvA : vHit ∈ (L.usedVerticesᶜ ∪ {vHit} : Set V) := Or.inr rfl
  have hrightA : right jNew ∈ (L.usedVerticesᶜ ∪ {vHit} : Set V) := by
    have hx : right jNew ∈ lv := by
      have hmem : right jNew ∈ lv.getLast? := by simp [hlast_v]
      exact List.mem_of_mem_getLast? hmem
    exact hA _ hx
  obtain ⟨p, hp, hsupport⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := (L.usedVerticesᶜ ∪ {vHit} : Set V))
      (u := vHit) (v := right jNew)
      hvA hrightA hreach_ind
  exact ⟨p, hp, by
    intro x hx
    exact hsupport x hx⟩

theorem PartialThreeVertexLinkage.exists_path_between_splitResidualChain_indices
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxA idxB : Nat}
    (hidxA : idxA < l.length)
    (hidxB : idxB < l.length)
    (hAB : idxA <= idxB)
    {a b : V}
    (hvertexA : (l[idxA]'hidxA).vertex = a)
    (hvertexB : (l[idxB]'hidxB).vertex = b)
    (hchain : l.IsChain L.SplitResidualStep)
    (hmiddle : forall m : Nat, idxA < m -> m < idxB ->
      forall hm : m < l.length,
        (l[m]'hm).vertex ∉ L.usedVertices) :
    Exists fun p : G.Walk a b =>
      p.IsPath ∧ forall x : V, x ∈ p.support ->
        x ∉ L.usedVertices ∨ x = a ∨ x = b := by
  classical
  let len : Nat := idxB - idxA + 1
  let seg : List (VertexSplitState V) := (l.drop idxA).take len
  let lv : List V := seg.map VertexSplitState.vertex
  have hlen_pos : 0 < len := by
    dsimp [len]
    omega
  have hseg_len : seg.length = len := by
    dsimp [seg, len]
    rw [List.length_take, List.length_drop]
    omega
  have hchain_seg : seg.IsChain L.SplitResidualStep := by
    exact (hchain.drop idxA).take len
  have hchain_v : lv.IsChain (fun u w : V => u = w ∨ G.Adj u w) := by
    change (seg.map VertexSplitState.vertex).IsChain
      (fun u w : V => u = w ∨ G.Adj u w)
    rw [List.isChain_map]
    exact hchain_seg.imp (fun {s t} h =>
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (a := s) (b := t) h)
  have hhead_seg : seg.head? = some (l[idxA]'hidxA) := by
    dsimp [seg]
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_take]
    have hdrop0 : (l.drop idxA)[0]? = some (l[idxA]'hidxA) := by
      rw [List.getElem?_drop]
      simp [List.getElem?_eq_getElem hidxA]
    simp [hlen_pos, hdrop0]
  have hlast_seg : seg.getLast? = some (l[idxB]'hidxB) := by
    dsimp [seg]
    rw [List.getLast?_eq_getElem?]
    rw [hseg_len]
    have hsub : len - 1 = idxB - idxA := by
      simp [len]
    rw [hsub]
    rw [List.getElem?_take]
    have hdrop :
        (l.drop idxA)[idxB - idxA]? = some (l[idxB]'hidxB) := by
      rw [List.getElem?_drop]
      have hadd : idxA + (idxB - idxA) = idxB := by omega
      rw [hadd]
      exact List.getElem?_eq_getElem hidxB
    have hlt_len : idxB - idxA < len := by
      dsimp [len]
      omega
    simp [hlt_len, hdrop]
  have hhead_v : lv.head? = some a := by
    simp [lv, List.head?_map, hhead_seg, hvertexA]
  have hlast_v : lv.getLast? = some b := by
    simp [lv, List.getLast?_map, hlast_seg, hvertexB]
  have hA :
      forall x : V, x ∈ lv ->
        x ∈ (L.usedVerticesᶜ ∪ ({a, b} : Set V)) := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨s, hs_seg, rfl⟩
    rw [Set.mem_union, Set.mem_compl_iff]
    dsimp [seg] at hs_seg
    rw [List.mem_take_iff_getElem] at hs_seg
    rcases hs_seg with ⟨j, hjmin, hget⟩
    have hj_drop_len : j < (l.drop idxA).length :=
      lt_of_lt_of_le hjmin (min_le_right _ _)
    have hmLen : idxA + j < l.length := by
      rw [List.length_drop] at hj_drop_len
      omega
    have hdrop_get :
        (l.drop idxA)[j]'hj_drop_len = l[idxA + j]'hmLen := by
      simp [
        (List.getElem_drop (xs := l) (i := idxA) (j := j)
          (h := hj_drop_len))]
    have hs_eq : s = l[idxA + j]'hmLen := by
      exact hget.symm.trans hdrop_get
    have hj_lt_len : j < len := lt_of_lt_of_le hjmin (min_le_left _ _)
    have hm_le_B : idxA + j <= idxB := by
      dsimp [len] at hj_lt_len
      omega
    by_cases hmA : idxA + j = idxA
    · exact Or.inr (by
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hs_eq, hmA,
          hvertexA])
    · by_cases hmB : idxA + j = idxB
      · exact Or.inr (by
          simp [Set.mem_insert_iff, Set.mem_singleton_iff, hs_eq, hmB,
            hvertexB])
      · exact Or.inl (by
          have hltA : idxA < idxA + j := lt_of_le_of_ne
            (Nat.le_add_right idxA j) (Ne.symm hmA)
          have hltB : idxA + j < idxB := lt_of_le_of_ne hm_le_B hmB
          simpa [hs_eq] using hmiddle (idxA + j) hltA hltB hmLen)
  have hreach_ind :
      (G.induce (L.usedVerticesᶜ ∪ ({a, b} : Set V))).Reachable
        ⟨a, by
          have ha_mem : a ∈ lv.head? := by simp [hhead_v]
          exact hA a (List.mem_of_mem_head? ha_mem)⟩
        ⟨b, by
          have hb_mem : b ∈ lv.getLast? := by simp [hlast_v]
          exact hA b (List.mem_of_mem_getLast? hb_mem)⟩ := by
    simpa [lv] using
      reachable_induce_of_isChain_eq_or_adj
        (G := G) (A := (L.usedVerticesᶜ ∪ ({a, b} : Set V)))
        hchain_v hhead_v hlast_v hA
  obtain ⟨p, hp, hsupport⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := (L.usedVerticesᶜ ∪ ({a, b} : Set V)))
      (u := a) (v := b)
      (by
        have ha_mem : a ∈ lv.head? := by simp [hhead_v]
        exact hA a (List.mem_of_mem_head? ha_mem))
      (by
        have hb_mem : b ∈ lv.getLast? := by simp [hlast_v]
        exact hA b (List.mem_of_mem_getLast? hb_mem))
      hreach_ind
  exact ⟨p, hp, by
    intro x hx
    rcases hsupport x hx with hx_not | hx_pair
    · exact Or.inl hx_not
    · simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_pair
      rcases hx_pair with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)⟩

theorem PartialThreeVertexLinkage.exists_path_between_splitResidualChain_indices_support_subset
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxA idxB : Nat}
    (hidxA : idxA < l.length)
    (hidxB : idxB < l.length)
    (hAB : idxA <= idxB)
    {a b : V}
    (hvertexA : (l[idxA]'hidxA).vertex = a)
    (hvertexB : (l[idxB]'hidxB).vertex = b)
    (hchain : l.IsChain L.SplitResidualStep) :
    Exists fun p : G.Walk a b =>
      p.IsPath ∧
        forall x : V, x ∈ p.support ->
          Exists fun idx : Nat =>
            Exists fun hidx : idx < l.length =>
              idxA <= idx ∧ idx <= idxB ∧
                (l[idx]'hidx).vertex = x := by
  classical
  let len : Nat := idxB - idxA + 1
  let seg : List (VertexSplitState V) := (l.drop idxA).take len
  let lv : List V := seg.map VertexSplitState.vertex
  have hlen_pos : 0 < len := by
    dsimp [len]
    omega
  have hseg_len : seg.length = len := by
    dsimp [seg, len]
    rw [List.length_take, List.length_drop]
    omega
  have hlv_ne : lv ≠ [] := by
    intro hnil
    have hlen_lv : lv.length = len := by
      simp [lv, hseg_len]
    simp [hnil] at hlen_lv
  have hchain_seg : seg.IsChain L.SplitResidualStep := by
    exact (hchain.drop idxA).take len
  have hchain_v : lv.IsChain (fun u w : V => u = w ∨ G.Adj u w) := by
    change (seg.map VertexSplitState.vertex).IsChain
      (fun u w : V => u = w ∨ G.Adj u w)
    rw [List.isChain_map]
    exact hchain_seg.imp (fun {s t} h =>
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (a := s) (b := t) h)
  have hhead_seg : seg.head? = some (l[idxA]'hidxA) := by
    dsimp [seg]
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_take]
    have hdrop0 : (l.drop idxA)[0]? = some (l[idxA]'hidxA) := by
      rw [List.getElem?_drop]
      simp [List.getElem?_eq_getElem hidxA]
    simp [hlen_pos, hdrop0]
  have hlast_seg : seg.getLast? = some (l[idxB]'hidxB) := by
    dsimp [seg]
    rw [List.getLast?_eq_getElem?]
    rw [hseg_len]
    have hsub : len - 1 = idxB - idxA := by
      simp [len]
    rw [hsub]
    rw [List.getElem?_take]
    have hdrop :
        (l.drop idxA)[idxB - idxA]? = some (l[idxB]'hidxB) := by
      rw [List.getElem?_drop]
      have hadd : idxA + (idxB - idxA) = idxB := by omega
      rw [hadd]
      exact List.getElem?_eq_getElem hidxB
    have hlt_len : idxB - idxA < len := by
      dsimp [len]
      omega
    simp [hlt_len, hdrop]
  have hhead_v : lv.head? = some a := by
    simp [lv, List.head?_map, hhead_seg, hvertexA]
  have hlast_v : lv.getLast? = some b := by
    simp [lv, List.getLast?_map, hlast_seg, hvertexB]
  obtain ⟨p, hp, hsupport_lv⟩ :=
    exists_path_of_isChain_eq_or_adj
      (G := G) hlv_ne hchain_v hhead_v hlast_v
  refine ⟨p, hp, ?_⟩
  intro x hx
  have hx_lv : x ∈ lv := hsupport_lv x hx
  rcases List.mem_map.mp hx_lv with ⟨s, hs_seg, hsx⟩
  dsimp [seg] at hs_seg
  rw [List.mem_take_iff_getElem] at hs_seg
  rcases hs_seg with ⟨j, hjmin, hget⟩
  have hj_drop_len : j < (l.drop idxA).length :=
    lt_of_lt_of_le hjmin (min_le_right _ _)
  have hmLen : idxA + j < l.length := by
    rw [List.length_drop] at hj_drop_len
    omega
  have hdrop_get :
      (l.drop idxA)[j]'hj_drop_len = l[idxA + j]'hmLen := by
    simp [
      (List.getElem_drop (xs := l) (i := idxA) (j := j)
        (h := hj_drop_len))]
  have hs_eq : s = l[idxA + j]'hmLen := by
    exact hget.symm.trans hdrop_get
  have hj_lt_len : j < len := lt_of_lt_of_le hjmin (min_le_left _ _)
  have hm_le_B : idxA + j <= idxB := by
    dsimp [len] at hj_lt_len
    omega
  exact ⟨idxA + j, hmLen, by omega, hm_le_B, by
    simpa [hs_eq] using hsx⟩

theorem PartialThreeVertexLinkage.exists_path_from_last_used_to_target_of_splitResidualChain_support_subset
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {jNew : Fin 3} {l : List (VertexSplitState V)} {idx : Nat}
    (hidx : idx < l.length)
    {vHit : V}
    (hvertex : (l[idx]'hidx).vertex = vHit)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (hafter : forall m : Nat, idx < m ->
      forall hm : m < l.length,
        (l[m]'hm).vertex ∉ L.usedVertices) :
    Exists fun p : G.Walk vHit (right jNew) =>
      p.IsPath ∧
        (forall x : V, x ∈ p.support ->
          x ∉ L.usedVertices ∨ x = vHit) ∧
          forall x : V, x ∈ p.support ->
            Exists fun m : Nat =>
              Exists fun hm : m < l.length =>
                idx <= m ∧ (l[m]'hm).vertex = x := by
  classical
  let idxLast : Nat := l.length - 1
  have hidxLast : idxLast < l.length := by
    dsimp [idxLast]
    omega
  have hidx_le_last : idx <= idxLast := by
    dsimp [idxLast]
    omega
  have hvertexLast : (l[idxLast]'hidxLast).vertex = right jNew := by
    have hgl : l.getLast? = some (l[idxLast]'hidxLast) := by
      rw [List.getLast?_eq_getElem?]
      simp [idxLast, List.getElem?_eq_getElem hidxLast]
    rw [hgl] at hlast
    injection hlast with hstateLast
    simp [hstateLast]
  obtain ⟨p, hp, hsupportIdx⟩ :=
    L.exists_path_between_splitResidualChain_indices_support_subset
      hidx hidxLast hidx_le_last hvertex hvertexLast hchain
  refine ⟨p, hp, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm, hidxm, _hmLast, hmx⟩ := hsupportIdx x hx
    by_cases hmi : m = idx
    · subst m
      exact Or.inr (by
        have hvx : vHit = x := by
          simpa [hvertex] using hmx
        exact hvx.symm)
    · have him : idx < m := lt_of_le_of_ne hidxm (Ne.symm hmi)
      exact Or.inl (by
        simpa [hmx] using hafter m him hm)
  · intro x hx
    obtain ⟨m, hm, hidxm, _hmLast, hmx⟩ := hsupportIdx x hx
    exact ⟨m, hm, hidxm, hmx⟩


end Schematic.Math.GraphTheory
