import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.ChainIndices

/-! Disjointness between residual-chain prefixes, bridges, and suffixes. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.prefix_support_disjoint_bridge_of_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    (hchain : l.IsChain L.SplitResidualStep)
    {source : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    {idxF idxB : Nat}
    (hidxF : idxF < l.length)
    (hidxOut : idxF + 1 < l.length)
    {vHit wExit vNext : V}
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateOut : l[idxF + 1]'hidxOut = VertexSplitState.out wExit)
    (hvHitUsed : vHit ∈ L.usedVertices)
    (hwExitUsed : wExit ∈ L.usedVertices)
    (hvNextUsed : vNext ∈ L.usedVertices)
    (hneHitExit : vHit ≠ wExit)
    (hneHitNext : vHit ≠ vNext)
    {a b c d : V}
    (pPrefix : G.Walk a b)
    (pBridge : G.Walk c d)
    (hPrefixAvoid :
      forall x : V, x ∈ pPrefix.support ->
        x ∉ L.usedVertices ∨ x = vHit)
    (hBridgeAvoid :
      forall x : V, x ∈ pBridge.support ->
        x ∉ L.usedVertices ∨ x = wExit ∨ x = vNext)
    (hPrefixSupport :
      forall x : V, x ∈ pPrefix.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            m <= idxF ∧ (l[m]'hm).vertex = x)
    (hBridgeSupport :
      forall x : V, x ∈ pBridge.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxF + 1 <= m ∧ m <= idxB ∧
              (l[m]'hm).vertex = x) :
    Disjoint {x : V | x ∈ pPrefix.support}
      {x : V | x ∈ pBridge.support} := by
  classical
  rw [Set.disjoint_left]
  intro x hxPrefix hxBridge
  simp only [Set.mem_setOf_eq] at hxPrefix hxBridge
  rcases hPrefixAvoid x hxPrefix with hxPrefixUnused | hxHit
  · rcases hBridgeAvoid x hxBridge with hxBridgeUnused | hxBridgeEnd
    · obtain ⟨idxA, hidxA, hA_le, hAvertex⟩ :=
        hPrefixSupport x hxPrefix
      obtain ⟨idxC, hidxC, hC_ge, _hC_le, hCvertex⟩ :=
        hBridgeSupport x hxBridge
      have hA_lt_F : idxA < idxF := by
        by_contra hnot
        have hEq : idxA = idxF := by omega
        subst idxA
        have hxv : x = vHit := by
          have hvx : vHit = x := by
            simpa [hstateF] using hAvertex
          exact hvx.symm
        exact hxPrefixUnused (by simpa [hxv] using hvHitUsed)
      have hOut_lt_C : idxF + 1 < idxC := by
        by_contra hnot
        have hEq : idxC = idxF + 1 := by omega
        subst idxC
        have hxw : x = wExit := by
          have hwx : wExit = x := by
            simpa [hstateOut] using hCvertex
          exact hwx.symm
        exact hxPrefixUnused (by simpa [hxw] using hwExitUsed)
      exact
        L.splitResidualChain_unused_vertex_no_repeat_of_gap
          hnodup hchain hidxA hidxC (by omega) hAvertex hCvertex
          hxPrefixUnused (by
            intro hout
            by_contra hnot_pos
            have hidxA0 : idxA = 0 := by omega
            subst idxA
            have hget0 : l[0]? = some (l[0]'hidxA) :=
              List.getElem?_eq_getElem hidxA
            rw [List.head?_eq_getElem?, hget0] at hhead
            injection hhead with h0
            have hbad :
                VertexSplitState.inn source = VertexSplitState.out x := by
              exact h0.symm.trans (by simpa using hout)
            cases hbad)
    · rcases hxBridgeEnd with hxw | hxvNext
      · subst x
        exact hxPrefixUnused hwExitUsed
      · subst x
        exact hxPrefixUnused hvNextUsed
  · subst x
    rcases hBridgeAvoid vHit hxBridge with hvUnused | hvEnd
    · exact hvUnused hvHitUsed
    · rcases hvEnd with hvw | hvn
      · exact hneHitExit hvw
      · exact hneHitNext hvn

theorem PartialThreeVertexLinkage.prefix_support_disjoint_later_bridge_of_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    (hchain : l.IsChain L.SplitResidualStep)
    {source : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    {idxF idxA idxB : Nat}
    (hidxF : idxF < l.length)
    (hidxA : idxA < l.length)
    (hFA : idxF < idxA)
    {vHit wA vB : V}
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateA : l[idxA]'hidxA = VertexSplitState.out wA)
    (hvHitUsed : vHit ∈ L.usedVertices)
    (hwAUsed : wA ∈ L.usedVertices)
    (hvBUsed : vB ∈ L.usedVertices)
    (hneHitA : vHit ≠ wA)
    (hneHitB : vHit ≠ vB)
    {a b c d : V}
    (pPrefix : G.Walk a b)
    (pBridge : G.Walk c d)
    (hPrefixAvoid :
      forall x : V, x ∈ pPrefix.support ->
        x ∉ L.usedVertices ∨ x = vHit)
    (hBridgeAvoid :
      forall x : V, x ∈ pBridge.support ->
        x ∉ L.usedVertices ∨ x = wA ∨ x = vB)
    (hPrefixSupport :
      forall x : V, x ∈ pPrefix.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            m <= idxF ∧ (l[m]'hm).vertex = x)
    (hBridgeSupport :
      forall x : V, x ∈ pBridge.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxA <= m ∧ m <= idxB ∧ (l[m]'hm).vertex = x) :
    Disjoint {x : V | x ∈ pPrefix.support}
      {x : V | x ∈ pBridge.support} := by
  classical
  rw [Set.disjoint_left]
  intro x hxPrefix hxBridge
  simp only [Set.mem_setOf_eq] at hxPrefix hxBridge
  rcases hPrefixAvoid x hxPrefix with hxPrefixUnused | hxHit
  · rcases hBridgeAvoid x hxBridge with hxBridgeUnused | hxBridgeEnd
    · obtain ⟨idxP, hidxP, hP_le_F, hPvertex⟩ :=
        hPrefixSupport x hxPrefix
      obtain ⟨idxC, hidxC, hA_le_C, _hC_le_B, hCvertex⟩ :=
        hBridgeSupport x hxBridge
      have hP_lt_F : idxP < idxF := by
        by_contra hnot
        have hEq : idxP = idxF := by omega
        subst idxP
        have hxv : x = vHit := by
          have hvx : vHit = x := by
            simpa [hstateF] using hPvertex
          exact hvx.symm
        exact hxPrefixUnused (by simpa [hxv] using hvHitUsed)
      have hA_lt_C : idxA < idxC := by
        by_contra hnot
        have hEq : idxC = idxA := by omega
        subst idxC
        have hxw : x = wA := by
          have hwx : wA = x := by
            simpa [hstateA] using hCvertex
          exact hwx.symm
        exact hxPrefixUnused (by simpa [hxw] using hwAUsed)
      exact
        L.splitResidualChain_unused_vertex_no_repeat_of_gap
          hnodup hchain hidxP hidxC (by omega) hPvertex hCvertex
          hxPrefixUnused (by
            intro hout
            by_contra hnot_pos
            have hidxP0 : idxP = 0 := by omega
            subst idxP
            have hget0 : l[0]? = some (l[0]'hidxP) :=
              List.getElem?_eq_getElem hidxP
            rw [List.head?_eq_getElem?, hget0] at hhead
            injection hhead with h0
            have hbad :
                VertexSplitState.inn source = VertexSplitState.out x := by
              exact h0.symm.trans (by simpa using hout)
            cases hbad)
    · rcases hxBridgeEnd with hxA | hxB
      · subst x
        exact hxPrefixUnused hwAUsed
      · subst x
        exact hxPrefixUnused hvBUsed
  · subst x
    rcases hBridgeAvoid vHit hxBridge with hvUnused | hvEnd
    · exact hvUnused hvHitUsed
    · rcases hvEnd with hvA | hvB
      · exact hneHitA hvA
      · exact hneHitB hvB

theorem PartialThreeVertexLinkage.bridge_support_disjoint_suffix_of_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    (hchain : l.IsChain L.SplitResidualStep)
    {idxA idxB idxL : Nat}
    (hidxA_pos : 0 < idxA)
    (hidxB : idxB < l.length)
    (hidxL : idxL < l.length)
    (hBL : idxB < idxL)
    {wExit vNext wHit : V}
    (hstateB : l[idxB]'hidxB = VertexSplitState.inn vNext)
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit)
    (hwExitUsed : wExit ∈ L.usedVertices)
    (hvNextUsed : vNext ∈ L.usedVertices)
    (hwHitUsed : wHit ∈ L.usedVertices)
    (hneExitHit : wExit ≠ wHit)
    (hneNextHit : vNext ≠ wHit)
    {a b c d : V}
    (pBridge : G.Walk a b)
    (pSuffix : G.Walk c d)
    (hBridgeAvoid :
      forall x : V, x ∈ pBridge.support ->
        x ∉ L.usedVertices ∨ x = wExit ∨ x = vNext)
    (hSuffixAvoid :
      forall x : V, x ∈ pSuffix.support ->
        x ∉ L.usedVertices ∨ x = wHit)
    (hBridgeSupport :
      forall x : V, x ∈ pBridge.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxA <= m ∧ m <= idxB ∧ (l[m]'hm).vertex = x)
    (hSuffixSupport :
      forall x : V, x ∈ pSuffix.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxL <= m ∧ (l[m]'hm).vertex = x) :
    Disjoint {x : V | x ∈ pBridge.support}
      {x : V | x ∈ pSuffix.support} := by
  classical
  rw [Set.disjoint_left]
  intro x hxBridge hxSuffix
  simp only [Set.mem_setOf_eq] at hxBridge hxSuffix
  rcases hBridgeAvoid x hxBridge with hxBridgeUnused | hxBridgeEnd
  · rcases hSuffixAvoid x hxSuffix with hxSuffixUnused | hxHit
    · obtain ⟨idxC, hidxC, hA_le_C, hC_le_B, hCvertex⟩ :=
        hBridgeSupport x hxBridge
      obtain ⟨idxD, hidxD, hL_le_D, hDvertex⟩ :=
        hSuffixSupport x hxSuffix
      have hC_lt_B : idxC < idxB := by
        by_contra hnot
        have hEq : idxC = idxB := by omega
        subst idxC
        have hxv : x = vNext := by
          have hvx : vNext = x := by
            simpa [hstateB] using hCvertex
          exact hvx.symm
        exact hxBridgeUnused (by simpa [hxv] using hvNextUsed)
      have hL_lt_D : idxL < idxD := by
        by_contra hnot
        have hEq : idxD = idxL := by omega
        subst idxD
        have hxw : x = wHit := by
          have hwx : wHit = x := by
            simpa [hstateL] using hDvertex
          exact hwx.symm
        exact hxBridgeUnused (by simpa [hxw] using hwHitUsed)
      exact
        L.splitResidualChain_unused_vertex_no_repeat_of_gap
          hnodup hchain hidxC hidxD (by omega) hCvertex hDvertex
          hxBridgeUnused (by
            intro _hout
            omega)
    · subst x
      exact hxBridgeUnused hwHitUsed
  · rcases hSuffixAvoid x hxSuffix with hxSuffixUnused | hxHit
    · rcases hxBridgeEnd with hxExit | hxNext
      · subst x
        exact hxSuffixUnused hwExitUsed
      · subst x
        exact hxSuffixUnused hvNextUsed
    · subst x
      rcases hxBridgeEnd with hxExit | hxNext
      · exact hneExitHit hxExit.symm
      · exact hneNextHit hxNext.symm

theorem PartialThreeVertexLinkage.bridge_support_disjoint_later_bridge_of_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    (hchain : l.IsChain L.SplitResidualStep)
    {idxA idxB idxC idxD : Nat}
    (hidxA_pos : 0 < idxA)
    (hidxB : idxB < l.length)
    (hidxC : idxC < l.length)
    (hBC : idxB < idxC)
    {wA vB wC vD : V}
    (hstateB : l[idxB]'hidxB = VertexSplitState.inn vB)
    (hstateC : l[idxC]'hidxC = VertexSplitState.out wC)
    (hwAUsed : wA ∈ L.usedVertices)
    (hvBUsed : vB ∈ L.usedVertices)
    (hwCUsed : wC ∈ L.usedVertices)
    (hvDUsed : vD ∈ L.usedVertices)
    (hneAC : wA ≠ wC)
    (hneAD : wA ≠ vD)
    (hneBC : vB ≠ wC)
    (hneBD : vB ≠ vD)
    {a b c d : V}
    (pBridgeA : G.Walk a b)
    (pBridgeB : G.Walk c d)
    (hBridgeAAvoid :
      forall x : V, x ∈ pBridgeA.support ->
        x ∉ L.usedVertices ∨ x = wA ∨ x = vB)
    (hBridgeBAvoid :
      forall x : V, x ∈ pBridgeB.support ->
        x ∉ L.usedVertices ∨ x = wC ∨ x = vD)
    (hBridgeASupport :
      forall x : V, x ∈ pBridgeA.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxA <= m ∧ m <= idxB ∧ (l[m]'hm).vertex = x)
    (hBridgeBSupport :
      forall x : V, x ∈ pBridgeB.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxC <= m ∧ m <= idxD ∧ (l[m]'hm).vertex = x) :
    Disjoint {x : V | x ∈ pBridgeA.support}
      {x : V | x ∈ pBridgeB.support} := by
  classical
  rw [Set.disjoint_left]
  intro x hxA hxB
  simp only [Set.mem_setOf_eq] at hxA hxB
  rcases hBridgeAAvoid x hxA with hxAUnused | hxAEnd
  · rcases hBridgeBAvoid x hxB with hxBUnused | hxBEnd
    · obtain ⟨idxA', hidxA', hA_le, hA'_le_B, hAvertex⟩ :=
        hBridgeASupport x hxA
      obtain ⟨idxC', hidxC', hC_le, _hC'_le_D, hCvertex⟩ :=
        hBridgeBSupport x hxB
      have hA'_lt_B : idxA' < idxB := by
        by_contra hnot
        have hEq : idxA' = idxB := by omega
        subst idxA'
        have hxv : x = vB := by
          have hvx : vB = x := by
            simpa [hstateB] using hAvertex
          exact hvx.symm
        exact hxAUnused (by simpa [hxv] using hvBUsed)
      have hC_lt_C' : idxC < idxC' := by
        by_contra hnot
        have hEq : idxC' = idxC := by omega
        subst idxC'
        have hxw : x = wC := by
          have hwx : wC = x := by
            simpa [hstateC] using hCvertex
          exact hwx.symm
        exact hxAUnused (by simpa [hxw] using hwCUsed)
      have hA'_succ_lt_C' : idxA' + 1 < idxC' := by omega
      exact
        L.splitResidualChain_unused_vertex_no_repeat_of_gap
          hnodup hchain hidxA' hidxC' hA'_succ_lt_C' hAvertex hCvertex
          hxAUnused (by
            intro _hout
            exact lt_of_lt_of_le hidxA_pos hA_le)
    · rcases hxBEnd with hxC | hxD
      · subst x
        exact hxAUnused hwCUsed
      · subst x
        exact hxAUnused hvDUsed
  · rcases hBridgeBAvoid x hxB with hxBUnused | hxBEnd
    · rcases hxAEnd with hxA' | hxB'
      · subst x
        exact hxBUnused hwAUsed
      · subst x
        exact hxBUnused hvBUsed
    · rcases hxAEnd with hxA' | hxB'
      · subst x
        rcases hxBEnd with hxC | hxD
        · exact hneAC hxC
        · exact hneAD hxD
      · subst x
        rcases hxBEnd with hxC | hxD
        · exact hneBC hxC
        · exact hneBD hxD

theorem PartialThreeVertexLinkage.prefix_support_disjoint_suffix_of_splitResidualChain
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    (hchain : l.IsChain L.SplitResidualStep)
    {source : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    {idxF idxL : Nat}
    (hidxF : idxF < l.length)
    (hidxL : idxL < l.length)
    (hFL : idxF < idxL)
    {vHit wHit : V}
    (hstateF : l[idxF]'hidxF = VertexSplitState.inn vHit)
    (hstateL : l[idxL]'hidxL = VertexSplitState.out wHit)
    (hvHitUsed : vHit ∈ L.usedVertices)
    (hwHitUsed : wHit ∈ L.usedVertices)
    (hneHit : vHit ≠ wHit)
    {a b c d : V}
    (pPrefix : G.Walk a b)
    (pSuffix : G.Walk c d)
    (hPrefixAvoid :
      forall x : V, x ∈ pPrefix.support ->
        x ∉ L.usedVertices ∨ x = vHit)
    (hSuffixAvoid :
      forall x : V, x ∈ pSuffix.support ->
        x ∉ L.usedVertices ∨ x = wHit)
    (hPrefixSupport :
      forall x : V, x ∈ pPrefix.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            m <= idxF ∧ (l[m]'hm).vertex = x)
    (hSuffixSupport :
      forall x : V, x ∈ pSuffix.support ->
        Exists fun m : Nat =>
          Exists fun hm : m < l.length =>
            idxL <= m ∧ (l[m]'hm).vertex = x) :
    Disjoint {x : V | x ∈ pPrefix.support}
      {x : V | x ∈ pSuffix.support} := by
  classical
  rw [Set.disjoint_left]
  intro x hxPrefix hxSuffix
  simp only [Set.mem_setOf_eq] at hxPrefix hxSuffix
  rcases hPrefixAvoid x hxPrefix with hxPrefixUnused | hxHit
  · rcases hSuffixAvoid x hxSuffix with hxSuffixUnused | hxSuffixHit
    · obtain ⟨idxA, hidxA, hA_le_F, hAvertex⟩ :=
        hPrefixSupport x hxPrefix
      obtain ⟨idxB, hidxB, hL_le_B, hBvertex⟩ :=
        hSuffixSupport x hxSuffix
      have hA_lt_F : idxA < idxF := by
        by_contra hnot
        have hEq : idxA = idxF := by omega
        subst idxA
        have hxv : x = vHit := by
          have hvx : vHit = x := by
            simpa [hstateF] using hAvertex
          exact hvx.symm
        exact hxPrefixUnused (by simpa [hxv] using hvHitUsed)
      have hL_lt_B : idxL < idxB := by
        by_contra hnot
        have hEq : idxB = idxL := by omega
        subst idxB
        have hxw : x = wHit := by
          have hwx : wHit = x := by
            simpa [hstateL] using hBvertex
          exact hwx.symm
        exact hxPrefixUnused (by simpa [hxw] using hwHitUsed)
      have hgap : idxA + 1 < idxB := by omega
      exact
        L.splitResidualChain_unused_vertex_no_repeat_of_gap
          hnodup hchain hidxA hidxB hgap hAvertex hBvertex
          hxPrefixUnused (by
            intro hout
            by_contra hnot_pos
            have hidxA0 : idxA = 0 := by omega
            subst idxA
            have hget0 : l[0]? = some (l[0]'hidxA) :=
              List.getElem?_eq_getElem hidxA
            rw [List.head?_eq_getElem?, hget0] at hhead
            injection hhead with h0
            have hbad :
                VertexSplitState.inn source = VertexSplitState.out x := by
              exact h0.symm.trans (by simpa using hout)
            cases hbad)
    · subst x
      exact hxPrefixUnused hwHitUsed
  · subst x
    rcases hSuffixAvoid vHit hxSuffix with hvUnused | hvHit
    · exact hvUnused hvHitUsed
    · exact hneHit hvHit

theorem PartialThreeVertexLinkage.last_used_splitResidualChain_state_is_out
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat} (hidx : idx < l.length)
    {target : V}
    (hlast : l.getLast? = some (VertexSplitState.out target))
    (hchain : l.IsChain L.SplitResidualStep)
    (hused : (l[idx]'hidx).vertex ∈ L.usedVertices)
    (hafter : forall j : Nat, idx < j ->
      forall hj : j < l.length,
        (l[j]'hj).vertex ∉ L.usedVertices) :
    Exists fun v : V => l[idx]'hidx = VertexSplitState.out v := by
  classical
  by_cases hlast_idx : idx + 1 = l.length
  · have hgl : l.getLast? = some (l[idx]'hidx) := by
      rw [List.getLast?_eq_getElem?]
      have hidx_eq : l.length - 1 = idx := by omega
      rw [hidx_eq]
      exact List.getElem?_eq_getElem hidx
    rw [hgl] at hlast
    injection hlast with hout
    exact ⟨target, hout⟩
  · have hnext_len : idx + 1 < l.length := by omega
    have hstep := (List.isChain_iff_getElem.mp hchain) idx hnext_len
    have hnext_unused : (l[idx + 1]'hnext_len).vertex ∉ L.usedVertices :=
      hafter (idx + 1) (by omega) hnext_len
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


end Schematic.Math.GraphTheory
