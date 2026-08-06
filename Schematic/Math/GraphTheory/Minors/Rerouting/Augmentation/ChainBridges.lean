import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.ChainPaths

/-! Bridge paths between successive used vertices of a residual chain. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.exists_bridge_to_next_used_of_out_splitResidualChain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxOut idxNext : Nat}
    (hidxOut : idxOut < l.length)
    (hidxNext : idxNext < l.length)
    (hON : idxOut < idxNext)
    {w : V}
    (hstateOut : l[idxOut]'hidxOut = VertexSplitState.out w)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedNext : (l[idxNext]'hidxNext).vertex ∈ L.usedVertices)
    (hmiddle : forall j : Nat, idxOut < j -> j < idxNext ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun vNext : V =>
      l[idxNext]'hidxNext = VertexSplitState.inn vNext ∧
        Exists fun p : G.Walk w vNext =>
          p.IsPath ∧ forall x : V, x ∈ p.support ->
            x ∉ L.usedVertices ∨ x = w ∨ x = vNext := by
  classical
  obtain ⟨vNext, hstateNext⟩ :=
    L.next_used_after_out_splitResidualChain_state_is_inn
      hidxOut hidxNext hON hstateOut hchain husedNext hmiddle
  have hvertexOut : (l[idxOut]'hidxOut).vertex = w := by
    simp [hstateOut]
  have hvertexNext : (l[idxNext]'hidxNext).vertex = vNext := by
    simp [hstateNext]
  obtain ⟨p, hp, havoid⟩ :=
    L.exists_path_between_splitResidualChain_indices
      hidxOut hidxNext (by omega) hvertexOut hvertexNext hchain hmiddle
  exact ⟨vNext, hstateNext, p, hp, havoid⟩

theorem PartialThreeVertexLinkage.exists_bridge_to_next_used_of_out_splitResidualChain_support_subset
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxOut idxNext : Nat}
    (hidxOut : idxOut < l.length)
    (hidxNext : idxNext < l.length)
    (hON : idxOut < idxNext)
    {w : V}
    (hstateOut : l[idxOut]'hidxOut = VertexSplitState.out w)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedNext : (l[idxNext]'hidxNext).vertex ∈ L.usedVertices)
    (hmiddle : forall j : Nat, idxOut < j -> j < idxNext ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun vNext : V =>
      l[idxNext]'hidxNext = VertexSplitState.inn vNext ∧
        Exists fun p : G.Walk w vNext =>
          p.IsPath ∧
            (forall x : V, x ∈ p.support ->
              x ∉ L.usedVertices ∨ x = w ∨ x = vNext) ∧
              forall x : V, x ∈ p.support ->
                Exists fun m : Nat =>
                  Exists fun hm : m < l.length =>
                    idxOut <= m ∧ m <= idxNext ∧
                      (l[m]'hm).vertex = x := by
  classical
  obtain ⟨vNext, hstateNext⟩ :=
    L.next_used_after_out_splitResidualChain_state_is_inn
      hidxOut hidxNext hON hstateOut hchain husedNext hmiddle
  have hvertexOut : (l[idxOut]'hidxOut).vertex = w := by
    simp [hstateOut]
  have hvertexNext : (l[idxNext]'hidxNext).vertex = vNext := by
    simp [hstateNext]
  obtain ⟨p, hp, hsupportIdx⟩ :=
    L.exists_path_between_splitResidualChain_indices_support_subset
      hidxOut hidxNext (by omega) hvertexOut hvertexNext hchain
  refine ⟨vNext, hstateNext, p, hp, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm, hOutm, hmNext, hmx⟩ := hsupportIdx x hx
    by_cases hmOut : m = idxOut
    · subst m
      exact Or.inr (Or.inl (by
        have hwx : w = x := by
          simpa [hstateOut] using hmx
        exact hwx.symm))
    · by_cases hmN : m = idxNext
      · subst m
        exact Or.inr (Or.inr (by
          have hvx : vNext = x := by
            simpa [hstateNext] using hmx
          exact hvx.symm))
      · have hOut_lt_m : idxOut < m := lt_of_le_of_ne hOutm (Ne.symm hmOut)
        have hm_lt_N : m < idxNext := lt_of_le_of_ne hmNext hmN
        exact Or.inl (by
          simpa [hmx] using hmiddle m hOut_lt_m hm_lt_N hm)
  · intro x hx
    exact hsupportIdx x hx

theorem PartialThreeVertexLinkage.exists_bridge_from_prev_used_to_inn_splitResidualChain
    [DecidableEq V]
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
    Exists fun wPrev : V =>
      l[idxPrev]'hidxPrev = VertexSplitState.out wPrev ∧
        Exists fun pBridge : G.Walk wPrev v =>
          pBridge.IsPath ∧ forall x : V, x ∈ pBridge.support ->
            x ∉ L.usedVertices ∨ x = wPrev ∨ x = v := by
  classical
  obtain ⟨wPrev, hstatePrev⟩ :=
    L.prev_used_before_inn_splitResidualChain_state_is_out
      hidxPrev hidxInn hPI hstateInn hchain husedPrev hmiddle
  have hvertexPrev : (l[idxPrev]'hidxPrev).vertex = wPrev := by
    simp [hstatePrev]
  have hvertexInn : (l[idxInn]'hidxInn).vertex = v := by
    simp [hstateInn]
  obtain ⟨p, hp, havoid⟩ :=
    L.exists_path_between_splitResidualChain_indices
      hidxPrev hidxInn (by omega) hvertexPrev hvertexInn hchain hmiddle
  exact ⟨wPrev, hstatePrev, p, hp, havoid⟩

theorem PartialThreeVertexLinkage.exists_bridge_from_prev_used_to_inn_splitResidualChain_support_subset
    [DecidableEq V]
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
    Exists fun wPrev : V =>
      l[idxPrev]'hidxPrev = VertexSplitState.out wPrev ∧
        Exists fun pBridge : G.Walk wPrev v =>
          pBridge.IsPath ∧
            (forall x : V, x ∈ pBridge.support ->
              x ∉ L.usedVertices ∨ x = wPrev ∨ x = v) ∧
              forall x : V, x ∈ pBridge.support ->
                Exists fun m : Nat =>
                  Exists fun hm : m < l.length =>
                    idxPrev <= m ∧ m <= idxInn ∧
                      (l[m]'hm).vertex = x := by
  classical
  obtain ⟨wPrev, hstatePrev⟩ :=
    L.prev_used_before_inn_splitResidualChain_state_is_out
      hidxPrev hidxInn hPI hstateInn hchain husedPrev hmiddle
  have hvertexPrev : (l[idxPrev]'hidxPrev).vertex = wPrev := by
    simp [hstatePrev]
  have hvertexInn : (l[idxInn]'hidxInn).vertex = v := by
    simp [hstateInn]
  obtain ⟨p, hp, hsupportIdx⟩ :=
    L.exists_path_between_splitResidualChain_indices_support_subset
      hidxPrev hidxInn (by omega) hvertexPrev hvertexInn hchain
  refine ⟨wPrev, hstatePrev, p, hp, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm, hPrevm, hmInn, hmx⟩ := hsupportIdx x hx
    by_cases hmPrev : m = idxPrev
    · subst m
      exact Or.inr (Or.inl (by
        have hwx : wPrev = x := by
          simpa [hstatePrev] using hmx
        exact hwx.symm))
    · by_cases hmI : m = idxInn
      · subst m
        exact Or.inr (Or.inr (by
          have hvx : v = x := by
            simpa [hstateInn] using hmx
          exact hvx.symm))
      · have hPrev_lt_m : idxPrev < m :=
          lt_of_le_of_ne hPrevm (Ne.symm hmPrev)
        have hm_lt_I : m < idxInn := lt_of_le_of_ne hmInn hmI
        exact Or.inl (by
          simpa [hmx] using hmiddle m hPrev_lt_m hm_lt_I hm)
  · intro x hx
    exact hsupportIdx x hx

theorem PartialThreeVertexLinkage.exists_first_multiblock_bridge
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxF idxL : Nat}
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hFL : idxF < idxL)
    (hnot_adj : idxL ≠ idxF + 1)
    {vHit : V}
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedL : (l[idxL]'hidxL).vertex ∈ L.usedVertices)
    {k : Fin n}
    (hv : vHit ∈ (L.path k).support) :
    Exists fun wExit : V =>
      Exists fun hidxOut : idxF + 1 < l.length =>
        l[idxF + 1]'hidxOut = VertexSplitState.out wExit ∧
          wExit ∈ (L.path k).support ∧
            (L.path k).support.idxOf wExit <
              (L.path k).support.idxOf vHit ∧
              Exists fun idxN : Nat =>
                Exists fun hidxN : idxN < l.length =>
                  idxF + 1 < idxN ∧
                    (l[idxN]'hidxN).vertex ∈ L.usedVertices ∧
                      (forall j : Nat, idxF + 1 < j -> j < idxN ->
                        forall hj : j < l.length,
                          (l[j]'hj).vertex ∉ L.usedVertices) ∧
                        Exists fun vNext : V =>
                          l[idxN]'hidxN = VertexSplitState.inn vNext ∧
                            Exists fun pBridge : G.Walk wExit vNext =>
                              pBridge.IsPath ∧
                                forall x : V, x ∈ pBridge.support ->
                                  x ∉ L.usedVertices ∨
                                    x = wExit ∨ x = vNext := by
  classical
  have hidxOut : idxF + 1 < l.length := by omega
  obtain ⟨wExit, hstateOut, hwExit, horderExit⟩ :=
    L.first_used_splitResidualChain_backward_block
      hidxF hidxL hFL hstateF hchain hv
  have hOutBeforeL : idxF + 1 < idxL := by omega
  have hused_after :
      Exists fun idx : Nat =>
        Exists fun hidx : idx < l.length =>
          idxF + 1 < idx ∧
            (l[idx]'hidx).vertex ∈ L.usedVertices :=
    ⟨idxL, hidxL, hOutBeforeL, husedL⟩
  obtain ⟨idxN, hidxN, hOutN, husedN, hmiddle⟩ :=
    L.exists_next_splitResidualChain_usedVertexIndex hused_after
  obtain ⟨vNext, hstateNext, pBridge, hpBridge, hBridgeAvoid⟩ :=
    L.exists_bridge_to_next_used_of_out_splitResidualChain
      hidxOut hidxN hOutN hstateOut hchain husedN hmiddle
  exact
    ⟨wExit, hidxOut, hstateOut, hwExit, horderExit, idxN, hidxN,
      hOutN, husedN, hmiddle, vNext, hstateNext, pBridge, hpBridge,
      hBridgeAvoid⟩

theorem PartialThreeVertexLinkage.exists_first_multiblock_bridge_support_subset
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxF idxL : Nat}
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hFL : idxF < idxL)
    (hnot_adj : idxL ≠ idxF + 1)
    {vHit : V}
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedL : (l[idxL]'hidxL).vertex ∈ L.usedVertices)
    {k : Fin n}
    (hv : vHit ∈ (L.path k).support) :
    Exists fun wExit : V =>
      Exists fun hidxOut : idxF + 1 < l.length =>
        l[idxF + 1]'hidxOut = VertexSplitState.out wExit ∧
          wExit ∈ (L.path k).support ∧
            (L.path k).support.idxOf wExit <
              (L.path k).support.idxOf vHit ∧
              Exists fun idxN : Nat =>
                Exists fun hidxN : idxN < l.length =>
                  idxF + 1 < idxN ∧
                    (l[idxN]'hidxN).vertex ∈ L.usedVertices ∧
                      (forall j : Nat, idxF + 1 < j -> j < idxN ->
                        forall hj : j < l.length,
                          (l[j]'hj).vertex ∉ L.usedVertices) ∧
                        Exists fun vNext : V =>
                          l[idxN]'hidxN = VertexSplitState.inn vNext ∧
                            Exists fun pBridge : G.Walk wExit vNext =>
                              pBridge.IsPath ∧
                                (forall x : V, x ∈ pBridge.support ->
                                  x ∉ L.usedVertices ∨
                                    x = wExit ∨ x = vNext) ∧
                                  forall x : V, x ∈ pBridge.support ->
                                    Exists fun m : Nat =>
                                      Exists fun hm : m < l.length =>
                                        idxF + 1 <= m ∧ m <= idxN ∧
                                          (l[m]'hm).vertex = x := by
  classical
  have hidxOut : idxF + 1 < l.length := by omega
  obtain ⟨wExit, hstateOut, hwExit, horderExit⟩ :=
    L.first_used_splitResidualChain_backward_block
      hidxF hidxL hFL hstateF hchain hv
  have hOutBeforeL : idxF + 1 < idxL := by omega
  have hused_after :
      Exists fun idx : Nat =>
        Exists fun hidx : idx < l.length =>
          idxF + 1 < idx ∧
            (l[idx]'hidx).vertex ∈ L.usedVertices :=
    ⟨idxL, hidxL, hOutBeforeL, husedL⟩
  obtain ⟨idxN, hidxN, hOutN, husedN, hmiddle⟩ :=
    L.exists_next_splitResidualChain_usedVertexIndex hused_after
  obtain ⟨vNext, hstateNext, pBridge, hpBridge, hBridgeAvoid,
    hBridgeSupport⟩ :=
    L.exists_bridge_to_next_used_of_out_splitResidualChain_support_subset
      hidxOut hidxN hOutN hstateOut hchain husedN hmiddle
  exact
    ⟨wExit, hidxOut, hstateOut, hwExit, horderExit, idxN, hidxN,
      hOutN, husedN, hmiddle, vNext, hstateNext, pBridge, hpBridge,
      hBridgeAvoid, hBridgeSupport⟩

theorem PartialThreeVertexLinkage.exists_last_multiblock_bridge_support_subset
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idxF idxL : Nat}
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hFL : idxF < idxL)
    (hnot_adj : idxL ≠ idxF + 1)
    {wHit : V}
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit)
    (hchain : l.IsChain L.SplitResidualStep)
    (husedF : (l[idxF]'hidxF).vertex ∈ L.usedVertices)
    {k : Fin n}
    (hw : wHit ∈ (L.path k).support) :
    Exists fun vEnter : V =>
      Exists fun hidxInn : idxL - 1 < l.length =>
        l[idxL - 1]'hidxInn = VertexSplitState.inn vEnter ∧
          vEnter ∈ (L.path k).support ∧
            (L.path k).support.idxOf wHit <
              (L.path k).support.idxOf vEnter ∧
              Exists fun idxP : Nat =>
                Exists fun hidxP : idxP < l.length =>
                  idxP < idxL - 1 ∧
                    (l[idxP]'hidxP).vertex ∈ L.usedVertices ∧
                      (forall j : Nat, idxP < j -> j < idxL - 1 ->
                        forall hj : j < l.length,
                          (l[j]'hj).vertex ∉ L.usedVertices) ∧
                        Exists fun wPrev : V =>
                          l[idxP]'hidxP = VertexSplitState.out wPrev ∧
                            Exists fun pBridge : G.Walk wPrev vEnter =>
                              pBridge.IsPath ∧
                                (forall x : V, x ∈ pBridge.support ->
                                  x ∉ L.usedVertices ∨
                                    x = wPrev ∨ x = vEnter) ∧
                                  forall x : V, x ∈ pBridge.support ->
                                    Exists fun m : Nat =>
                                      Exists fun hm : m < l.length =>
                                        idxP <= m ∧ m <= idxL - 1 ∧
                                          (l[m]'hm).vertex = x := by
  classical
  have hidxInn : idxL - 1 < l.length := by omega
  obtain ⟨vEnter, hstateInn, hvEnter, horderEnter⟩ :=
    L.prev_state_of_out_splitResidualChain
      hidxL (by omega) hstateL hchain hw
  have hF_before_inn : idxF < idxL - 1 := by omega
  have hused_before :
      Exists fun idx : Nat =>
        Exists fun hidx : idx < l.length =>
          idx < idxL - 1 ∧
            (l[idx]'hidx).vertex ∈ L.usedVertices :=
    ⟨idxF, hidxF, hF_before_inn, husedF⟩
  obtain ⟨idxP, hidxP, hPInn, husedP, hmiddle⟩ :=
    L.exists_prev_splitResidualChain_usedVertexIndex hused_before
  obtain ⟨wPrev, hstatePrev, pBridge, hpBridge, hBridgeAvoid,
    hBridgeSupport⟩ :=
    L.exists_bridge_from_prev_used_to_inn_splitResidualChain_support_subset
      hidxP hidxInn hPInn hstateInn hchain husedP hmiddle
  exact
    ⟨vEnter, hidxInn, hstateInn, hvEnter, horderEnter, idxP, hidxP,
      hPInn, husedP, hmiddle, wPrev, hstatePrev, pBridge, hpBridge,
      hBridgeAvoid, hBridgeSupport⟩


end Schematic.Math.GraphTheory
