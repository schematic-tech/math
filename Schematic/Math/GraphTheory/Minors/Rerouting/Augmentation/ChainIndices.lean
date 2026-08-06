import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.TwoPathSplicing

/-! Used-vertex indices and state transitions along residual chains. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.empty_hasPartial_one_of_splitResidualReaches
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (hreach :
      (PartialThreeVertexLinkage.empty (G := G)
        (left := left) (right := right)).SplitResidualReachesUnusedRight) :
    HasPartialThreeVertexLinkage G left right 1 := by
  classical
  let L0 : PartialThreeVertexLinkage G left right 0 :=
    PartialThreeVertexLinkage.empty (G := G)
  obtain ⟨i, j, hi, hj, p, hp⟩ :=
    L0.exists_ordinary_path_of_splitResidualReaches hreach
  have havoid :
      forall v : V, v ∈ p.support -> v ∉ L0.usedVertices := by
    intro v _hv hused
    rcases hused with ⟨k, _hk⟩
    exact Fin.elim0 k
  simpa using
    L0.hasPartial_succ_of_path_avoids_usedVertices
      hi hj p hp havoid

theorem PartialThreeVertexLinkage.hasPartial_succ_of_splitResidualChain_avoids_usedVertices
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {iNew jNew : Fin 3} {l : List (VertexSplitState V)}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (havoid :
      forall s : VertexSplitState V, s ∈ l -> s.vertex ∉ L.usedVertices) :
    HasPartialThreeVertexLinkage G left right (n + 1) := by
  classical
  let lv : List V := l.map VertexSplitState.vertex
  have hchain_v : lv.IsChain (fun u v : V => u = v ∨ G.Adj u v) := by
    change (l.map VertexSplitState.vertex).IsChain
      (fun u v : V => u = v ∨ G.Adj u v)
    rw [List.isChain_map]
    exact hchain.imp (fun {a b} h =>
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (a := a) (b := b) h)
  have hhead_v : lv.head? = some (left iNew) := by
    simp [lv, List.head?_map, hhead]
  have hlast_v : lv.getLast? = some (right jNew) := by
    simp [lv, List.getLast?_map, hlast]
  have hA : forall v : V, v ∈ lv -> v ∈ (L.usedVertices)ᶜ := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨s, hs, rfl⟩
    exact havoid s hs
  have hreach_ind :
      (G.induce (L.usedVertices)ᶜ).Reachable
        ⟨left iNew, by
          have hs_head :
              VertexSplitState.inn (left iNew) ∈ l.head? := by
            simp [hhead]
          exact havoid _ (List.mem_of_mem_head? hs_head)⟩
        ⟨right jNew, by
          have hs_last :
              VertexSplitState.out (right jNew) ∈ l.getLast? := by
            simp [hlast]
          exact havoid _ (List.mem_of_mem_getLast? hs_last)⟩ := by
    simpa [lv] using
      reachable_induce_of_isChain_eq_or_adj
        (G := G) (A := (L.usedVertices)ᶜ)
        hchain_v hhead_v hlast_v hA
  have hleft_not_used : left iNew ∉ L.usedVertices := by
    have hs_head :
        VertexSplitState.inn (left iNew) ∈ l.head? := by
      simp [hhead]
    exact havoid _ (List.mem_of_mem_head? hs_head)
  have hright_not_used : right jNew ∉ L.usedVertices := by
    have hs_last :
        VertexSplitState.out (right jNew) ∈ l.getLast? := by
      simp [hlast]
    exact havoid _ (List.mem_of_mem_getLast? hs_last)
  obtain ⟨p, hp, hsupport⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) (A := (L.usedVertices)ᶜ)
      (u := left iNew) (v := right jNew)
      hleft_not_used hright_not_used hreach_ind
  exact
    L.hasPartial_succ_of_path_avoids_usedVertices
      hiNew hjNew p hp (by
        intro v hv
        exact hsupport v hv)

theorem PartialThreeVertexLinkage.exists_first_splitResidualChain_usedVertexIndex
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hused : Exists fun s : VertexSplitState V =>
      s ∈ l ∧ s.vertex ∈ L.usedVertices) :
    Exists fun idx : Nat =>
      Exists fun hidx : idx < l.length =>
        (l[idx]'hidx).vertex ∈ L.usedVertices ∧
          forall j : Nat, j < idx ->
            forall hj : j < l.length,
              (l[j]'hj).vertex ∉ L.usedVertices := by
  classical
  let pred : VertexSplitState V -> Bool := fun s =>
    decide (s.vertex ∈ L.usedVertices)
  generalize hfind : l.find? pred = o
  cases o with
  | none =>
      have hnone := List.find?_eq_none.mp hfind
      rcases hused with ⟨s, hs, hsused⟩
      have hs_pred : pred s = true := by
        simp [pred, hsused]
      exact False.elim (hnone s hs hs_pred)
  | some s =>
      have hspec := List.find?_eq_some_iff_getElem.mp hfind
      rcases hspec.2 with ⟨idx, hidx, hget, hmin⟩
      refine ⟨idx, hidx, ?_, ?_⟩
      · have htrue : pred (l[idx]'hidx) = true := by
          simpa [hget] using hspec.1
        simpa [pred] using htrue
      · intro j hjlt hjlen hjused
        have hnot := hmin j hjlt
        have htrue : pred (l[j]'hjlen) = true := by
          simp [pred, hjused]
        rw [htrue] at hnot
        simp at hnot

theorem PartialThreeVertexLinkage.exists_last_splitResidualChain_usedVertexIndex
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hused : Exists fun s : VertexSplitState V =>
      s ∈ l ∧ s.vertex ∈ L.usedVertices) :
    Exists fun idx : Nat =>
      Exists fun hidx : idx < l.length =>
        (l[idx]'hidx).vertex ∈ L.usedVertices ∧
          forall j : Nat, idx < j ->
            forall hj : j < l.length,
              (l[j]'hj).vertex ∉ L.usedVertices := by
  classical
  let D : Nat := l.length - 1
  let Hit : Nat -> Prop := fun d =>
    Exists fun idx : Nat =>
      Exists fun hidx : idx < l.length =>
        (l[idx]'hidx).vertex ∈ L.usedVertices ∧ D - idx = d
  have hHit : Exists Hit := by
    rcases hused with ⟨s, hs_mem, hs_used⟩
    rcases List.getElem_of_mem hs_mem with ⟨idx, hidx, hget⟩
    refine ⟨D - idx, idx, hidx, ?_, rfl⟩
    simpa [hget]
  let d0 : Nat := Nat.find hHit
  rcases Nat.find_spec hHit with ⟨idx, hidx, hidx_used, hidx_d⟩
  refine ⟨idx, hidx, hidx_used, ?_⟩
  intro j hlt hj hj_used
  have hcandidate : Hit (D - j) := ⟨j, hj, hj_used, rfl⟩
  have hmin : d0 <= D - j := Nat.find_min' hHit hcandidate
  have hidx_d0 : D - idx = d0 := by
    simpa [d0] using hidx_d
  have hidx_le_D : idx <= D := by
    dsimp [D]
    omega
  have hj_le_D : j <= D := by
    dsimp [D]
    omega
  have hltD : D - j < D - idx := by
    omega
  omega

theorem PartialThreeVertexLinkage.exists_next_splitResidualChain_usedVertexIndex
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx0 : Nat}
    (hused_after :
      Exists fun idx : Nat =>
        Exists fun hidx : idx < l.length =>
          idx0 < idx ∧ (l[idx]'hidx).vertex ∈ L.usedVertices) :
    Exists fun idx : Nat =>
      Exists fun hidx : idx < l.length =>
        idx0 < idx ∧
          (l[idx]'hidx).vertex ∈ L.usedVertices ∧
            forall j : Nat, idx0 < j -> j < idx ->
              forall hj : j < l.length,
                (l[j]'hj).vertex ∉ L.usedVertices := by
  classical
  let Hit : Nat -> Prop := fun idx =>
    Exists fun hidx : idx < l.length =>
      idx0 < idx ∧ (l[idx]'hidx).vertex ∈ L.usedVertices
  have hHit : Exists Hit := hused_after
  let idx : Nat := Nat.find hHit
  rcases Nat.find_spec hHit with ⟨hidx, hgt, hused⟩
  refine ⟨idx, hidx, hgt, hused, ?_⟩
  intro j hgtj hjlt hjlen hjused
  have hcandidate : Hit j := ⟨hjlen, hgtj, hjused⟩
  have hmin : idx <= j := Nat.find_min' hHit hcandidate
  omega

theorem PartialThreeVertexLinkage.exists_prev_splitResidualChain_usedVertexIndex
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx0 : Nat}
    (hused_before :
      Exists fun idx : Nat =>
        Exists fun hidx : idx < l.length =>
          idx < idx0 ∧ (l[idx]'hidx).vertex ∈ L.usedVertices) :
    Exists fun idx : Nat =>
      Exists fun hidx : idx < l.length =>
        idx < idx0 ∧
          (l[idx]'hidx).vertex ∈ L.usedVertices ∧
            forall j : Nat, idx < j -> j < idx0 ->
              forall hj : j < l.length,
                (l[j]'hj).vertex ∉ L.usedVertices := by
  classical
  let D : Nat := idx0 - 1
  let Hit : Nat -> Prop := fun d =>
    Exists fun idx : Nat =>
      Exists fun hidx : idx < l.length =>
        idx < idx0 ∧
          (l[idx]'hidx).vertex ∈ L.usedVertices ∧ D - idx = d
  have hHit : Exists Hit := by
    rcases hused_before with ⟨idx, hidx, hlt, hused⟩
    exact ⟨D - idx, idx, hidx, hlt, hused, rfl⟩
  let d0 : Nat := Nat.find hHit
  rcases Nat.find_spec hHit with ⟨idx, hidx, hlt, hused, hidx_d⟩
  refine ⟨idx, hidx, hlt, hused, ?_⟩
  intro j hij hj0 hjlen hjused
  have hcandidate : Hit (D - j) := ⟨j, hjlen, hj0, hjused, rfl⟩
  have hmin : d0 <= D - j := Nat.find_min' hHit hcandidate
  have hidx_d0 : D - idx = d0 := by
    simpa [d0] using hidx_d
  have hidx_le_D : idx <= D := by
    dsimp [D]
    omega
  have hj_le_D : j <= D := by
    dsimp [D]
    omega
  have hltD : D - j < D - idx := by
    omega
  omega

theorem PartialThreeVertexLinkage.first_used_index_le_last_used_index
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    {idxF idxL : Nat}
    (hidxL : idxL < l.length)
    (husedL : (l[idxL]'hidxL).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idxF ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    idxF <= idxL := by
  by_contra hnot
  have hlt : idxL < idxF := by omega
  exact hfirst idxL hlt hidxL husedL

theorem PartialThreeVertexLinkage.used_splitResidualChain_state_is_inn_of_prev_unused
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat} (hidx : idx < l.length)
    (hpos : 0 < idx)
    (hchain : l.IsChain L.SplitResidualStep)
    (hused : (l[idx]'hidx).vertex ∈ L.usedVertices)
    (hprev_unused :
      (l[idx - 1]'(by omega)).vertex ∉ L.usedVertices) :
    Exists fun v : V => l[idx]'hidx = VertexSplitState.inn v := by
  classical
  let j := idx - 1
  have hjlt : j < idx := by
    dsimp [j]
    omega
  have hjlen : j < l.length := lt_trans hjlt hidx
  have hprev_unused' : (l[j]'hjlen).vertex ∉ L.usedVertices := by
    simpa [j] using hprev_unused
  have hj_succ : j + 1 = idx := by
    dsimp [j]
    omega
  have hstep_raw := (List.isChain_iff_getElem.mp hchain) j (by
    rw [hj_succ]
    exact hidx)
  have hstep : L.SplitResidualStep (l[j]'hjlen) (l[idx]'hidx) := by
    simpa [hj_succ] using hstep_raw
  cases hcur : l[idx]'hidx with
  | inn v =>
      exact ⟨v, rfl⟩
  | out v =>
      have hvused : v ∈ L.usedVertices := by
        simpa [hcur] using hused
      cases hprev : l[j]'hjlen with
      | inn u =>
          have hstep' :
              ((u = v ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart v u) := by
            simpa [PartialThreeVertexLinkage.SplitResidualStep, hprev, hcur]
              using hstep
          rcases hstep' with hcap | hdart
          · exact False.elim (hcap.2 (by simpa [hcap.1] using hvused))
          · exact False.elim (hprev_unused' (by
              simpa [hprev] using hdart.snd_mem_usedVertices))
      | out u =>
          simp [PartialThreeVertexLinkage.SplitResidualStep, hprev, hcur] at hstep

theorem PartialThreeVertexLinkage.used_splitResidualChain_state_is_out_of_next_unused
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat} (hidx : idx < l.length)
    (hnext_len : idx + 1 < l.length)
    (hchain : l.IsChain L.SplitResidualStep)
    (hused : (l[idx]'hidx).vertex ∈ L.usedVertices)
    (hnext_unused :
      (l[idx + 1]'hnext_len).vertex ∉ L.usedVertices) :
    Exists fun v : V => l[idx]'hidx = VertexSplitState.out v := by
  classical
  have hstep := (List.isChain_iff_getElem.mp hchain) idx hnext_len
  cases hcur : l[idx]'hidx with
  | out v =>
      exact ⟨v, rfl⟩
  | inn u =>
      cases hnext : l[idx + 1]'hnext_len with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep, hcur, hnext] at hstep
      | out v =>
          have hstep' :
              ((u = v ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart v u) := by
            simpa [PartialThreeVertexLinkage.SplitResidualStep, hcur, hnext]
              using hstep
          have huused : u ∈ L.usedVertices := by
            simpa [hcur] using hused
          rcases hstep' with hcap | hdart
          · exact False.elim (hcap.2 huused)
          · exact False.elim (hnext_unused (by
              simpa [hnext] using hdart.fst_mem_usedVertices))

theorem PartialThreeVertexLinkage.next_used_after_out_splitResidualChain_state_is_inn
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxStart idxNext : Nat}
    (hidxStart : idxStart < l.length)
    (hidxNext : idxNext < l.length)
    (hSN : idxStart < idxNext)
    {w : V}
    (hstateStart : l[idxStart]'hidxStart = VertexSplitState.out w)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedNext : (l[idxNext]'hidxNext).vertex ∈ L.usedVertices)
    (hmiddle : forall j : Nat, idxStart < j -> j < idxNext ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun v : V => l[idxNext]'hidxNext = VertexSplitState.inn v := by
  classical
  by_cases hadj : idxNext = idxStart + 1
  · subst idxNext
    have hstep := (List.isChain_iff_getElem.mp hchain) idxStart hidxNext
    cases hcur : l[idxStart + 1]'hidxNext with
    | inn v =>
        exact ⟨v, rfl⟩
    | out v =>
        have hbad :
            L.SplitResidualStep (VertexSplitState.out w)
              (VertexSplitState.out v) := by
          simpa [hstateStart, hcur] using hstep
        simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
  · have hgap : idxStart + 1 < idxNext := by omega
    have hprev_lt : idxStart < idxNext - 1 := by omega
    have hprev_prev : idxNext - 1 < idxNext := by omega
    have hprev_len : idxNext - 1 < l.length := by omega
    have hprev_unused :
        (l[idxNext - 1]'hprev_len).vertex ∉ L.usedVertices :=
      hmiddle (idxNext - 1) hprev_lt hprev_prev hprev_len
    exact
      L.used_splitResidualChain_state_is_inn_of_prev_unused
        hidxNext (by omega) hchain husedNext (by
          simpa using hprev_unused)

theorem PartialThreeVertexLinkage.prev_used_before_inn_splitResidualChain_state_is_out
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxPrev idxInn : Nat}
    (hidxPrev : idxPrev < l.length)
    (hidxInn : idxInn < l.length)
    (hPI : idxPrev < idxInn)
    {v : V}
    (hstateInn : l[idxInn]'hidxInn = VertexSplitState.inn v)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedPrev : (l[idxPrev]'hidxPrev).vertex ∈ L.usedVertices)
    (hmiddle : forall j : Nat, idxPrev < j -> j < idxInn ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun w : V => l[idxPrev]'hidxPrev = VertexSplitState.out w := by
  classical
  by_cases hadj : idxInn = idxPrev + 1
  · subst idxInn
    have hstep := (List.isChain_iff_getElem.mp hchain) idxPrev hidxInn
    cases hprev : l[idxPrev]'hidxPrev with
    | out w =>
        exact ⟨w, rfl⟩
    | inn w =>
        have hbad :
            L.SplitResidualStep (VertexSplitState.inn w)
              (VertexSplitState.inn v) := by
          simpa [hprev, hstateInn] using hstep
        simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
  · have hgap : idxPrev + 1 < idxInn := by omega
    have hnext_len : idxPrev + 1 < l.length := by omega
    have hnext_unused :
        (l[idxPrev + 1]'hnext_len).vertex ∉ L.usedVertices :=
      hmiddle (idxPrev + 1) (by omega) hgap hnext_len
    exact
      L.used_splitResidualChain_state_is_out_of_next_unused
        hidxPrev hnext_len hchain husedPrev hnext_unused

theorem PartialThreeVertexLinkage.first_used_splitResidualChain_state_is_inn
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat} (hidx : idx < l.length)
    (hpos : 0 < idx)
    (hchain : l.IsChain L.SplitResidualStep)
    (hused : (l[idx]'hidx).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idx ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun v : V => l[idx]'hidx = VertexSplitState.inn v := by
  classical
  let j := idx - 1
  have hjlt : j < idx := by
    dsimp [j]
    omega
  have hjlen : j < l.length := lt_trans hjlt hidx
  have hprev_unused : (l[j]'hjlen).vertex ∉ L.usedVertices :=
    hfirst j hjlt hjlen
  have hj_succ : j + 1 = idx := by
    dsimp [j]
    omega
  have hstep_raw := (List.isChain_iff_getElem.mp hchain) j (by
    rw [hj_succ]
    exact hidx)
  have hstep : L.SplitResidualStep (l[j]'hjlen) (l[idx]'hidx) := by
    simpa [hj_succ] using hstep_raw
  cases hcur : l[idx]'hidx with
  | inn v =>
      exact ⟨v, rfl⟩
  | out v =>
      have hvused : v ∈ L.usedVertices := by
        simpa [hcur] using hused
      cases hprev : l[j]'hjlen with
      | inn u =>
          have hstep' :
              ((u = v ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart v u) := by
            simpa [PartialThreeVertexLinkage.SplitResidualStep, hprev, hcur]
              using hstep
          rcases hstep' with hcap | hdart
          · exact False.elim (hcap.2 (by simpa [hcap.1] using hvused))
          · exact False.elim (hprev_unused (by
              simpa [hprev] using hdart.snd_mem_usedVertices))
      | out u =>
          simp [PartialThreeVertexLinkage.SplitResidualStep, hprev, hcur] at hstep

theorem PartialThreeVertexLinkage.first_used_splitResidualChain_state_is_inn_of_head
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat} (hidx : idx < l.length)
    {source : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hchain : l.IsChain L.SplitResidualStep)
    (hused : (l[idx]'hidx).vertex ∈ L.usedVertices)
    (hfirst : forall j : Nat, j < idx ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun v : V => l[idx]'hidx = VertexSplitState.inn v := by
  classical
  by_cases hpos : 0 < idx
  · exact
      L.first_used_splitResidualChain_state_is_inn
        hidx hpos hchain hused hfirst
  · have hidx0 : idx = 0 := by omega
    subst idx
    have hget : l[0]? = some (l[0]'hidx) :=
      List.getElem?_eq_getElem hidx
    rw [List.head?_eq_getElem?, hget] at hhead
    injection hhead with hstate
    exact ⟨source, hstate⟩

theorem PartialThreeVertexLinkage.next_state_of_inn_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat}
    (hnext : idx + 1 < l.length)
    {v : V}
    (hstate : l[idx]'(lt_trans (Nat.lt_succ_self idx) hnext) =
      VertexSplitState.inn v)
    (hchain : l.IsChain L.SplitResidualStep) :
    Exists fun w : V =>
      l[idx + 1]'hnext = VertexSplitState.out w ∧
        L.SplitResidualStep (VertexSplitState.inn v)
          (VertexSplitState.out w) := by
  classical
  have hstep_raw := (List.isChain_iff_getElem.mp hchain) idx hnext
  cases hnext_state : l[idx + 1]'hnext with
  | inn w =>
      have hbad :
          L.SplitResidualStep (VertexSplitState.inn v)
            (VertexSplitState.inn w) := by
        simpa [hstate, hnext_state] using hstep_raw
      simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
  | out w =>
      refine ⟨w, rfl, ?_⟩
      simpa [hstate, hnext_state] using hstep_raw

theorem PartialThreeVertexLinkage.next_state_of_unused_inn_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat}
    (hnext : idx + 1 < l.length)
    {v : V}
    (hstate : l[idx]'(lt_trans (Nat.lt_succ_self idx) hnext) =
      VertexSplitState.inn v)
    (hchain : l.IsChain L.SplitResidualStep)
    (hunused : v ∉ L.usedVertices) :
    l[idx + 1]'hnext = VertexSplitState.out v := by
  classical
  obtain ⟨w, hstateW, hstep⟩ :=
    L.next_state_of_inn_splitResidualChain hnext hstate hchain
  have hstep' :
      (v = w ∧ v ∉ L.usedVertices) ∨ L.ForwardPathDart w v := by
    simpa [PartialThreeVertexLinkage.SplitResidualStep, hstate, hstateW]
      using hstep
  rcases hstep' with hcap | hdart
  · simpa [hcap.1] using hstateW
  · exact False.elim (hunused hdart.snd_mem_usedVertices)

theorem PartialThreeVertexLinkage.first_used_splitResidualChain_backward_block
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxF idxL : Nat}
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hFL : idxF < idxL)
    {vHit : V}
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hchain : l.IsChain L.SplitResidualStep)
    {k : Fin n}
    (hv : vHit ∈ (L.path k).support) :
    Exists fun w : V =>
      l[idxF + 1]'(by omega) = VertexSplitState.out w ∧
        w ∈ (L.path k).support ∧
          (L.path k).support.idxOf w <
            (L.path k).support.idxOf vHit := by
  classical
  have hnext : idxF + 1 < l.length := by omega
  obtain ⟨w, hstateW, hstep⟩ :=
    L.next_state_of_inn_splitResidualChain hnext hstateF hchain
  refine ⟨w, hstateW, ?_, ?_⟩
  · exact
      PartialThreeVertexLinkage.SplitResidualStep.out_mem_same_path_of_inn_out
        (G := G) L hstep hv
  · exact
      PartialThreeVertexLinkage.SplitResidualStep.idxOf_out_lt_inn_of_inn_out
        (G := G) L hstep hv

theorem PartialThreeVertexLinkage.prev_state_of_out_splitResidualChain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat}
    (hidx : idx < l.length)
    (hpos : 0 < idx)
    {w : V}
    (hstate : l[idx]'hidx = VertexSplitState.out w)
    (hchain : l.IsChain L.SplitResidualStep)
    {k : Fin n}
    (hw : w ∈ (L.path k).support) :
    Exists fun v : V =>
      l[idx - 1]'(by omega) = VertexSplitState.inn v ∧
        v ∈ (L.path k).support ∧
          (L.path k).support.idxOf w <
            (L.path k).support.idxOf v := by
  classical
  let prev := idx - 1
  have hprev_idx : prev < l.length := by
    dsimp [prev]
    omega
  have hprev_succ : prev + 1 = idx := by
    dsimp [prev]
    omega
  have hstep_raw := (List.isChain_iff_getElem.mp hchain) prev (by
    rw [hprev_succ]
    exact hidx)
  cases hprev_state : l[prev]'hprev_idx with
  | out u =>
      have hbad :
          L.SplitResidualStep (VertexSplitState.out u)
            (VertexSplitState.out w) := by
        simpa [hprev_succ, hprev_state, hstate] using hstep_raw
      simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
  | inn v =>
      have hstep :
          L.SplitResidualStep (VertexSplitState.inn v)
            (VertexSplitState.out w) := by
        simpa [hprev_succ, hprev_state, hstate] using hstep_raw
      have hv : v ∈ (L.path k).support := by
        have hstep_cases := hstep
        simp [PartialThreeVertexLinkage.SplitResidualStep] at hstep_cases
        rcases hstep_cases with hcap | hdart
        · simpa [hcap.1] using hw
        · exact hdart.snd_mem_path_of_fst_mem hw
      refine ⟨v, ?_, hv, ?_⟩
      · rfl
      · exact
          PartialThreeVertexLinkage.SplitResidualStep.idxOf_out_lt_inn_of_inn_out
            (G := G) L hstep hv

theorem PartialThreeVertexLinkage.prev_state_of_unused_out_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat}
    (hidx : idx < l.length)
    (hpos : 0 < idx)
    {w : V}
    (hstate : l[idx]'hidx = VertexSplitState.out w)
    (hchain : l.IsChain L.SplitResidualStep)
    (hunused : w ∉ L.usedVertices) :
    l[idx - 1]'(by omega) = VertexSplitState.inn w := by
  classical
  let prev := idx - 1
  have hprev_idx : prev < l.length := by
    dsimp [prev]
    omega
  have hprev_succ : prev + 1 = idx := by
    dsimp [prev]
    omega
  have hstep_raw := (List.isChain_iff_getElem.mp hchain) prev (by
    rw [hprev_succ]
    exact hidx)
  cases hprev_state : l[prev]'hprev_idx with
  | out u =>
      have hbad :
          L.SplitResidualStep (VertexSplitState.out u)
            (VertexSplitState.out w) := by
        simpa [hprev_succ, hprev_state, hstate] using hstep_raw
      simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
  | inn u =>
      have hstep :
          L.SplitResidualStep (VertexSplitState.inn u)
            (VertexSplitState.out w) := by
        simpa [hprev_succ, hprev_state, hstate] using hstep_raw
      have hstep' :
          (u = w ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart w u := by
        simpa [PartialThreeVertexLinkage.SplitResidualStep] using hstep
      rcases hstep' with hcap | hdart
      · exact congrArg VertexSplitState.inn hcap.1
      · exact False.elim (hunused hdart.fst_mem_usedVertices)

theorem PartialThreeVertexLinkage.splitResidualChain_unused_vertex_no_repeat_of_gap
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    (hchain : l.IsChain L.SplitResidualStep)
    {idxA idxB : Nat}
    (hidxA : idxA < l.length)
    (hidxB : idxB < l.length)
    (hgap : idxA + 1 < idxB)
    {x : V}
    (hA : (l[idxA]'hidxA).vertex = x)
    (hB : (l[idxB]'hidxB).vertex = x)
    (hunused : x ∉ L.usedVertices)
    (hheadOut :
      l[idxA]'hidxA = VertexSplitState.out x -> 0 < idxA) :
    False := by
  classical
  have hne_of_lt :
      forall {i j : Nat} (hi : i < l.length) (hj : j < l.length),
        i < j -> l[i]'hi ≠ l[j]'hj := by
    intro i j hi hj hij heq
    have hsome_i : l[i]? = some (l[i]'hi) :=
      List.getElem?_eq_getElem hi
    have hsome_j : l[j]? = some (l[j]'hj) :=
      List.getElem?_eq_getElem hj
    have hneq :=
      (List.nodup_iff_getElem?_ne_getElem?.mp hnodup) i j hij hj
    exact hneq (by
      rw [hsome_i, hsome_j]
      simp [heq])
  cases hstateA : l[idxA]'hidxA with
    | inn a =>
        have hax : a = x := by
          simpa [hstateA] using hA
        subst a
        cases hstateB : l[idxB]'hidxB with
        | inn b =>
            have hbx : b = x := by
              simpa [hstateB] using hB
            subst b
            exact
              (hne_of_lt hidxA hidxB (by omega))
                (by simp [hstateA, hstateB])
        | out b =>
            have hbx : b = x := by
              simpa [hstateB] using hB
            subst b
            have hnextA : idxA + 1 < l.length := by omega
            have hstateNext :
                l[idxA + 1]'hnextA = VertexSplitState.out x :=
              L.next_state_of_unused_inn_splitResidualChain
                hnextA (by simp [hstateA]) hchain hunused
            exact
              (hne_of_lt hnextA hidxB (by omega))
                (by simp [hstateNext, hstateB])
    | out a =>
        have hax : a = x := by
          simpa [hstateA] using hA
        subst a
        have hposA : 0 < idxA := hheadOut (by simp [hstateA])
        have hprevAidx : idxA - 1 < l.length := by omega
        have hstatePrev :
            l[idxA - 1]'hprevAidx = VertexSplitState.inn x := by
          simpa using
            L.prev_state_of_unused_out_splitResidualChain
              hidxA hposA (by simp [hstateA]) hchain hunused
        cases hstateB : l[idxB]'hidxB with
        | inn b =>
            have hbx : b = x := by
              simpa [hstateB] using hB
            subst b
            exact
              (hne_of_lt hprevAidx hidxB (by omega))
                (by simp [hstatePrev, hstateB])
        | out b =>
            have hbx : b = x := by
              simpa [hstateB] using hB
            subst b
            exact
              (hne_of_lt hidxA hidxB (by omega))
                (by simp [hstateA, hstateB])


end Schematic.Math.GraphTheory
