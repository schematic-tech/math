import Schematic.Math.GraphTheory.Minors.Rerouting.Augmentation.OnePathSplicing

/-! Augmenting a two-path linkage by ordered splices. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem PartialThreeVertexLinkage.hasPartial_three_of_spliceFirstOfTwo_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOldToNew : G.Walk (left (L.leftIndex 0)) (right jNew))
    (pNewToOld : G.Walk (left iNew) (right (L.rightIndex 0)))
    (hdisjNew : Disjoint {v : V | v ∈ pOldToNew.support}
      {v : V | v ∈ pNewToOld.support})
    (hdisjOldToOther : Disjoint {v : V | v ∈ (L.path 1).support}
      {v : V | v ∈ pOldToNew.support})
    (hdisjNewToOther : Disjoint {v : V | v ∈ (L.path 1).support}
      {v : V | v ∈ pNewToOld.support}) :
    HasPartialThreeVertexLinkage G left right 3 := by
  refine ⟨L.spliceFirstOfTwoPaths hiNew hjNew
    (pOldToNew.toPath : G.Walk (left (L.leftIndex 0)) (right jNew))
    pOldToNew.toPath.property
    (pNewToOld.toPath : G.Walk (left iNew) (right (L.rightIndex 0)))
    pNewToOld.toPath.property ?_ ?_ ?_⟩
  · exact Walk.toPath_support_disjoint (G := G) hdisjNew
  · exact Walk.toPath_support_disjoint_right (G := G) hdisjOldToOther
  · exact Walk.toPath_support_disjoint_right (G := G) hdisjNewToOther

theorem PartialThreeVertexLinkage.hasPartial_three_of_spliceSecondOfTwo_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOldToNew : G.Walk (left (L.leftIndex 1)) (right jNew))
    (pNewToOld : G.Walk (left iNew) (right (L.rightIndex 1)))
    (hdisjNew : Disjoint {v : V | v ∈ pOldToNew.support}
      {v : V | v ∈ pNewToOld.support})
    (hdisjOldToOther : Disjoint {v : V | v ∈ (L.path 0).support}
      {v : V | v ∈ pOldToNew.support})
    (hdisjNewToOther : Disjoint {v : V | v ∈ (L.path 0).support}
      {v : V | v ∈ pNewToOld.support}) :
    HasPartialThreeVertexLinkage G left right 3 := by
  refine ⟨L.spliceSecondOfTwoPaths hiNew hjNew
    (pOldToNew.toPath : G.Walk (left (L.leftIndex 1)) (right jNew))
    pOldToNew.toPath.property
    (pNewToOld.toPath : G.Walk (left iNew) (right (L.rightIndex 1)))
    pNewToOld.toPath.property ?_ ?_ ?_⟩
  · exact Walk.toPath_support_disjoint (G := G) hdisjNew
  · exact Walk.toPath_support_disjoint_right (G := G) hdisjOldToOther
  · exact Walk.toPath_support_disjoint_right (G := G) hdisjNewToOther

theorem PartialThreeVertexLinkage.hasPartial_three_of_replaced_first_path_and_new_path_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOld : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)))
    (pNew : G.Walk (left iNew) (right jNew))
    (hOldNew : Disjoint {v : V | v ∈ pOld.support}
      {v : V | v ∈ pNew.support})
    (hOtherOld : Disjoint {v : V | v ∈ (L.path 1).support}
      {v : V | v ∈ pOld.support})
    (hOtherNew : Disjoint {v : V | v ∈ (L.path 1).support}
      {v : V | v ∈ pNew.support}) :
    HasPartialThreeVertexLinkage G left right 3 := by
  classical
  let Lother : PartialThreeVertexLinkage G left right 1 :=
    PartialThreeVertexLinkage.ofOnePath (G := G)
      (left := left) (right := right) (i := L.leftIndex 1)
      (j := L.rightIndex 1) (L.path 1) (L.isPath 1)
  have hiOld : L.leftIndex 0 ∉ Set.range Lother.leftIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    have heq : L.leftIndex 0 = L.leftIndex 1 := by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk.symm
    have h01 : (0 : Fin 2) = 1 := L.leftIndex_injective heq
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have hjOld : L.rightIndex 0 ∉ Set.range Lother.rightIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    have heq : L.rightIndex 0 = L.rightIndex 1 := by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk.symm
    have h01 : (0 : Fin 2) = 1 := L.rightIndex_injective heq
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  let Ltwo : PartialThreeVertexLinkage G left right 2 :=
    Lother.snocPath hiOld hjOld
      (pOld.toPath : G.Walk (left (L.leftIndex 0)) (right (L.rightIndex 0)))
      pOld.toPath.property (by
        intro k
        have hk0 : k = 0 := Subsingleton.elim k 0
        simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using
          Walk.toPath_support_disjoint_right (G := G) hOtherOld)
  have hiNewTwo : iNew ∉ Set.range Ltwo.leftIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hiNew ⟨0, by simpa [Ltwo, Fin.snoc_last] using hk⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        exact hiNew ⟨1, by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk⟩
  have hjNewTwo : jNew ∉ Set.range Ltwo.rightIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hjNew ⟨0, by simpa [Ltwo, Fin.snoc_last] using hk⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        exact hjNew ⟨1, by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk⟩
  refine ⟨Ltwo.snocPath hiNewTwo hjNewTwo
    (pNew.toPath : G.Walk (left iNew) (right jNew))
    pNew.toPath.property ?_⟩
  intro k
  cases k using Fin.lastCases with
  | last =>
      exact Walk.toPath_support_disjoint (G := G) hOldNew
  | cast k0 =>
      have hk00 : k0 = 0 := Subsingleton.elim k0 0
      simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
        PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc] using
        Walk.toPath_support_disjoint_right (G := G) hOtherNew

theorem PartialThreeVertexLinkage.hasPartial_three_of_replaced_second_path_and_new_path_walks
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pOld : G.Walk (left (L.leftIndex 1)) (right (L.rightIndex 1)))
    (pNew : G.Walk (left iNew) (right jNew))
    (hOldNew : Disjoint {v : V | v ∈ pOld.support}
      {v : V | v ∈ pNew.support})
    (hOtherOld : Disjoint {v : V | v ∈ (L.path 0).support}
      {v : V | v ∈ pOld.support})
    (hOtherNew : Disjoint {v : V | v ∈ (L.path 0).support}
      {v : V | v ∈ pNew.support}) :
    HasPartialThreeVertexLinkage G left right 3 := by
  classical
  let Lother : PartialThreeVertexLinkage G left right 1 :=
    PartialThreeVertexLinkage.ofOnePath (G := G)
      (left := left) (right := right) (i := L.leftIndex 0)
      (j := L.rightIndex 0) (L.path 0) (L.isPath 0)
  have hiOld : L.leftIndex 1 ∉ Set.range Lother.leftIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    have heq : L.leftIndex 1 = L.leftIndex 0 := by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk.symm
    have h10 : (1 : Fin 2) = 0 := L.leftIndex_injective heq
    exact (by decide : (1 : Fin 2) ≠ 0) h10
  have hjOld : L.rightIndex 1 ∉ Set.range Lother.rightIndex := by
    rintro ⟨k, hk⟩
    have hk0 : k = 0 := Subsingleton.elim k 0
    have heq : L.rightIndex 1 = L.rightIndex 0 := by
      simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using hk.symm
    have h10 : (1 : Fin 2) = 0 := L.rightIndex_injective heq
    exact (by decide : (1 : Fin 2) ≠ 0) h10
  let Ltwo : PartialThreeVertexLinkage G left right 2 :=
    Lother.snocPath hiOld hjOld
      (pOld.toPath : G.Walk (left (L.leftIndex 1)) (right (L.rightIndex 1)))
      pOld.toPath.property (by
        intro k
        have hk0 : k = 0 := Subsingleton.elim k 0
        simpa [Lother, PartialThreeVertexLinkage.ofOnePath, hk0] using
          Walk.toPath_support_disjoint_right (G := G) hOtherOld)
  have hiNewTwo : iNew ∉ Set.range Ltwo.leftIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hiNew ⟨1, by simpa [Ltwo, Fin.snoc_last] using hk⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        exact hiNew ⟨0, by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk⟩
  have hjNewTwo : jNew ∉ Set.range Ltwo.rightIndex := by
    rintro ⟨k, hk⟩
    cases k using Fin.lastCases with
    | last =>
        exact hjNew ⟨1, by simpa [Ltwo, Fin.snoc_last] using hk⟩
    | cast k0 =>
        have hk00 : k0 = 0 := Subsingleton.elim k0 0
        exact hjNew ⟨0, by
          simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
            PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc]
            using hk⟩
  refine ⟨Ltwo.snocPath hiNewTwo hjNewTwo
    (pNew.toPath : G.Walk (left iNew) (right jNew))
    pNew.toPath.property ?_⟩
  intro k
  cases k using Fin.lastCases with
  | last =>
      exact Walk.toPath_support_disjoint (G := G) hOldNew
  | cast k0 =>
      have hk00 : k0 = 0 := Subsingleton.elim k0 0
      simpa [Ltwo, Lother, PartialThreeVertexLinkage.snocPath,
        PartialThreeVertexLinkage.ofOnePath, hk00, Fin.snoc_castSucc] using
        Walk.toPath_support_disjoint_right (G := G) hOtherNew

theorem PartialThreeVertexLinkage.hasPartial_three_of_first_path_ordered_splice_or_direct
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {vHit wHit : V}
    (hv0 : vHit ∈ (L.path 0).support)
    (hw0 : wHit ∈ (L.path 0).support)
    (horder :
      (L.path 0).support.idxOf wHit < (L.path 0).support.idxOf vHit)
    (pIn : G.Walk (left iNew) vHit)
    (hpIn : pIn.IsPath)
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (pOut : G.Walk wHit (right jNew))
    (hpOut : pOut.IsPath)
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit) :
    HasPartialThreeVertexLinkage G left right 3 := by
  have hvUsed : vHit ∈ L.usedVertices := ⟨0, hv0⟩
  have hwUsed : wHit ∈ L.usedVertices := ⟨0, hw0⟩
  by_cases hOutIn :
      Disjoint {x : V | x ∈ pOut.support}
        {x : V | x ∈ pIn.support}
  · let q := L.path 0
    have hqpath : q.IsPath := by simpa [q] using L.isPath 0
    let oldToW : G.Walk (left (L.leftIndex 0)) wHit :=
      q.takeUntil wHit (by simpa [q] using hw0)
    let vToOld : G.Walk vHit (right (L.rightIndex 0)) :=
      q.dropUntil vHit (by simpa [q] using hv0)
    have hdisjNew :
        Disjoint {x : V | x ∈ (oldToW.append pOut).support}
          {x : V | x ∈ (pIn.append vToOld).support} := by
      have htake_used :
          forall x : V, x ∈ oldToW.support -> x ∈ L.usedVertices := by
        intro x hx
        exact ⟨0, by
          simpa [q, oldToW] using
            SimpleGraph.Walk.support_takeUntil_subset q
              (by simpa [q] using hw0) hx⟩
      have hdrop_used :
          forall x : V, x ∈ vToOld.support -> x ∈ L.usedVertices := by
        intro x hx
        exact ⟨0, by
          simpa [q, vToOld] using
            SimpleGraph.Walk.support_dropUntil_subset q
              (by simpa [q] using hv0) hx⟩
      have hv_not_oldToW : vHit ∉ oldToW.support := by
        dsimp [oldToW]
        exact Walk.not_mem_takeUntil_of_idxOf_lt
          (G := G) (by simpa [q] using hw0)
          (by simpa [q] using horder)
      have hw_not_vToOld : wHit ∉ vToOld.support := by
        dsimp [vToOld]
        exact Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
          (G := G) hqpath (by simpa [q] using hv0)
          (by simpa [q] using hw0) (by simpa [q] using horder)
      have h_old_in :
          Disjoint {x : V | x ∈ oldToW.support}
            {x : V | x ∈ pIn.support} := by
        rw [disjoint_comm]
        exact L.walk_support_disjoint_of_avoids_usedVertices
          hInAvoid htake_used hv_not_oldToW
      have h_old_drop :
          Disjoint {x : V | x ∈ oldToW.support}
            {x : V | x ∈ vToOld.support} := by
        dsimp [oldToW, vToOld]
        exact Walk.IsPath.takeUntil_support_disjoint_dropUntil_of_idxOf_lt
          (G := G) hqpath (by simpa [q] using hw0)
          (by simpa [q] using hv0) (by simpa [q] using horder)
      have h_out_drop :
          Disjoint {x : V | x ∈ pOut.support}
            {x : V | x ∈ vToOld.support} := by
        exact L.walk_support_disjoint_of_avoids_usedVertices
          hOutAvoid hdrop_used hw_not_vToOld
      exact Walk.support_append_disjoint_append
        (G := G) h_old_in h_old_drop hOutIn h_out_drop
    have hother_old :
        Disjoint {x : V | x ∈ (L.path 1).support}
          {x : V | x ∈ (oldToW.append pOut).support} := by
      rw [Set.disjoint_left]
      intro x hxOther hxAppend
      simp only [Set.mem_setOf_eq] at hxOther hxAppend
      rw [SimpleGraph.Walk.mem_support_append_iff] at hxAppend
      rcases hxAppend with hxOld | hxOut
      · have hx0 : x ∈ (L.path 0).support := by
          simpa [q, oldToW] using
            SimpleGraph.Walk.support_takeUntil_subset q
              (by simpa [q] using hw0) hxOld
        exact Set.disjoint_left.mp
          (L.pairwise_vertex_disjoint 1 0 (by decide)) hxOther hx0
      · rcases hOutAvoid x hxOut with hxNot | hxw
        · exact hxNot ⟨1, hxOther⟩
        · subst x
          exact Set.disjoint_left.mp
            (L.pairwise_vertex_disjoint 1 0 (by decide)) hxOther hw0
    have hother_new :
        Disjoint {x : V | x ∈ (L.path 1).support}
          {x : V | x ∈ (pIn.append vToOld).support} := by
      rw [Set.disjoint_left]
      intro x hxOther hxAppend
      simp only [Set.mem_setOf_eq] at hxOther hxAppend
      rw [SimpleGraph.Walk.mem_support_append_iff] at hxAppend
      rcases hxAppend with hxIn | hxOld
      · rcases hInAvoid x hxIn with hxNot | hxv
        · exact hxNot ⟨1, hxOther⟩
        · subst x
          exact Set.disjoint_left.mp
            (L.pairwise_vertex_disjoint 1 0 (by decide)) hxOther hv0
      · have hx0 : x ∈ (L.path 0).support := by
          simpa [q, vToOld] using
            SimpleGraph.Walk.support_dropUntil_subset q
              (by simpa [q] using hv0) hxOld
        exact Set.disjoint_left.mp
          (L.pairwise_vertex_disjoint 1 0 (by decide)) hxOther hx0
    exact L.hasPartial_three_of_spliceFirstOfTwo_walks hiNew hjNew
      (oldToW.append pOut) (pIn.append vToOld)
      hdisjNew hother_old hother_new
  · rw [Set.not_disjoint_iff] at hOutIn
    rcases hOutIn with ⟨x, hxOut, hxIn⟩
    simp only [Set.mem_setOf_eq] at hxOut hxIn
    have hx_not_used : x ∉ L.usedVertices := by
      rcases hInAvoid x hxIn with hxNot | hxv
      · exact hxNot
      rcases hOutAvoid x hxOut with hxNot | hxw
      · exact hxNot
      have hvw : vHit = wHit := hxv.symm.trans hxw
      have hbad :
          (L.path 0).support.idxOf wHit <
            (L.path 0).support.idxOf wHit := by
        rw [hvw] at horder
        exact horder
      exact False.elim (Nat.lt_irrefl _ hbad)
    have hx_ne_v : x ≠ vHit := by
      intro hxv
      exact hx_not_used (by simpa [hxv] using hvUsed)
    have hx_ne_w : x ≠ wHit := by
      intro hxw
      exact hx_not_used (by simpa [hxw] using hwUsed)
    let pDirect : G.Walk (left iNew) (right jNew) :=
      (pIn.takeUntil x hxIn).append (pOut.dropUntil x hxOut)
    have hdirect_avoid :
        forall y : V, y ∈ pDirect.support -> y ∉ L.usedVertices := by
      intro y hy
      dsimp [pDirect] at hy
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy
      rcases hy with hyIn | hyOut
      · have hyFull : y ∈ pIn.support :=
          SimpleGraph.Walk.support_takeUntil_subset pIn hxIn hyIn
        rcases hInAvoid y hyFull with hyNot | hyv
        · exact hyNot
        · subst y
          exact False.elim
            ((SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              hpIn hxIn hx_ne_v.symm) hyIn)
      · have hyFull : y ∈ pOut.support :=
          SimpleGraph.Walk.support_dropUntil_subset pOut hxOut hyOut
        rcases hOutAvoid y hyFull with hyNot | hyw
        · exact hyNot
        · subst y
          exact False.elim
            ((Walk.IsPath.start_not_mem_dropUntil_support_of_ne
              hpOut hxOut hx_ne_w) hyOut)
    exact L.hasPartial_succ_of_path_avoids_usedVertices hiNew hjNew
      (pDirect.toPath : G.Walk (left iNew) (right jNew))
      pDirect.toPath.property (by
        intro y hy
        exact hdirect_avoid y
          (SimpleGraph.Walk.support_toPath_subset pDirect hy))

theorem PartialThreeVertexLinkage.hasPartial_three_of_second_path_ordered_splice_or_direct
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (L : PartialThreeVertexLinkage G left right 2)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    {vHit wHit : V}
    (hv1 : vHit ∈ (L.path 1).support)
    (hw1 : wHit ∈ (L.path 1).support)
    (horder :
      (L.path 1).support.idxOf wHit < (L.path 1).support.idxOf vHit)
    (pIn : G.Walk (left iNew) vHit)
    (hpIn : pIn.IsPath)
    (hInAvoid :
      forall x : V, x ∈ pIn.support -> x ∉ L.usedVertices ∨ x = vHit)
    (pOut : G.Walk wHit (right jNew))
    (hpOut : pOut.IsPath)
    (hOutAvoid :
      forall x : V, x ∈ pOut.support -> x ∉ L.usedVertices ∨ x = wHit) :
    HasPartialThreeVertexLinkage G left right 3 := by
  have hvUsed : vHit ∈ L.usedVertices := ⟨1, hv1⟩
  have hwUsed : wHit ∈ L.usedVertices := ⟨1, hw1⟩
  by_cases hOutIn :
      Disjoint {x : V | x ∈ pOut.support}
        {x : V | x ∈ pIn.support}
  · let q := L.path 1
    have hqpath : q.IsPath := by simpa [q] using L.isPath 1
    let oldToW : G.Walk (left (L.leftIndex 1)) wHit :=
      q.takeUntil wHit (by simpa [q] using hw1)
    let vToOld : G.Walk vHit (right (L.rightIndex 1)) :=
      q.dropUntil vHit (by simpa [q] using hv1)
    have hdisjNew :
        Disjoint {x : V | x ∈ (oldToW.append pOut).support}
          {x : V | x ∈ (pIn.append vToOld).support} := by
      have htake_used :
          forall x : V, x ∈ oldToW.support -> x ∈ L.usedVertices := by
        intro x hx
        exact ⟨1, by
          simpa [q, oldToW] using
            SimpleGraph.Walk.support_takeUntil_subset q
              (by simpa [q] using hw1) hx⟩
      have hdrop_used :
          forall x : V, x ∈ vToOld.support -> x ∈ L.usedVertices := by
        intro x hx
        exact ⟨1, by
          simpa [q, vToOld] using
            SimpleGraph.Walk.support_dropUntil_subset q
              (by simpa [q] using hv1) hx⟩
      have hv_not_oldToW : vHit ∉ oldToW.support := by
        dsimp [oldToW]
        exact Walk.not_mem_takeUntil_of_idxOf_lt
          (G := G) (by simpa [q] using hw1)
          (by simpa [q] using horder)
      have hw_not_vToOld : wHit ∉ vToOld.support := by
        dsimp [vToOld]
        exact Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
          (G := G) hqpath (by simpa [q] using hv1)
          (by simpa [q] using hw1) (by simpa [q] using horder)
      have h_old_in :
          Disjoint {x : V | x ∈ oldToW.support}
            {x : V | x ∈ pIn.support} := by
        rw [disjoint_comm]
        exact L.walk_support_disjoint_of_avoids_usedVertices
          hInAvoid htake_used hv_not_oldToW
      have h_old_drop :
          Disjoint {x : V | x ∈ oldToW.support}
            {x : V | x ∈ vToOld.support} := by
        dsimp [oldToW, vToOld]
        exact Walk.IsPath.takeUntil_support_disjoint_dropUntil_of_idxOf_lt
          (G := G) hqpath (by simpa [q] using hw1)
          (by simpa [q] using hv1) (by simpa [q] using horder)
      have h_out_drop :
          Disjoint {x : V | x ∈ pOut.support}
            {x : V | x ∈ vToOld.support} := by
        exact L.walk_support_disjoint_of_avoids_usedVertices
          hOutAvoid hdrop_used hw_not_vToOld
      exact Walk.support_append_disjoint_append
        (G := G) h_old_in h_old_drop hOutIn h_out_drop
    have hother_old :
        Disjoint {x : V | x ∈ (L.path 0).support}
          {x : V | x ∈ (oldToW.append pOut).support} := by
      rw [Set.disjoint_left]
      intro x hxOther hxAppend
      simp only [Set.mem_setOf_eq] at hxOther hxAppend
      rw [SimpleGraph.Walk.mem_support_append_iff] at hxAppend
      rcases hxAppend with hxOld | hxOut
      · have hx1 : x ∈ (L.path 1).support := by
          simpa [q, oldToW] using
            SimpleGraph.Walk.support_takeUntil_subset q
              (by simpa [q] using hw1) hxOld
        exact Set.disjoint_left.mp
          (L.pairwise_vertex_disjoint 0 1 (by decide)) hxOther hx1
      · rcases hOutAvoid x hxOut with hxNot | hxw
        · exact hxNot ⟨0, hxOther⟩
        · subst x
          exact Set.disjoint_left.mp
            (L.pairwise_vertex_disjoint 0 1 (by decide)) hxOther hw1
    have hother_new :
        Disjoint {x : V | x ∈ (L.path 0).support}
          {x : V | x ∈ (pIn.append vToOld).support} := by
      rw [Set.disjoint_left]
      intro x hxOther hxAppend
      simp only [Set.mem_setOf_eq] at hxOther hxAppend
      rw [SimpleGraph.Walk.mem_support_append_iff] at hxAppend
      rcases hxAppend with hxIn | hxOld
      · rcases hInAvoid x hxIn with hxNot | hxv
        · exact hxNot ⟨0, hxOther⟩
        · subst x
          exact Set.disjoint_left.mp
            (L.pairwise_vertex_disjoint 0 1 (by decide)) hxOther hv1
      · have hx1 : x ∈ (L.path 1).support := by
          simpa [q, vToOld] using
            SimpleGraph.Walk.support_dropUntil_subset q
              (by simpa [q] using hv1) hxOld
        exact Set.disjoint_left.mp
          (L.pairwise_vertex_disjoint 0 1 (by decide)) hxOther hx1
    exact L.hasPartial_three_of_spliceSecondOfTwo_walks hiNew hjNew
      (oldToW.append pOut) (pIn.append vToOld)
      hdisjNew hother_old hother_new
  · rw [Set.not_disjoint_iff] at hOutIn
    rcases hOutIn with ⟨x, hxOut, hxIn⟩
    simp only [Set.mem_setOf_eq] at hxOut hxIn
    have hx_not_used : x ∉ L.usedVertices := by
      rcases hInAvoid x hxIn with hxNot | hxv
      · exact hxNot
      rcases hOutAvoid x hxOut with hxNot | hxw
      · exact hxNot
      have hvw : vHit = wHit := hxv.symm.trans hxw
      have hbad :
          (L.path 1).support.idxOf wHit <
            (L.path 1).support.idxOf wHit := by
        rw [hvw] at horder
        exact horder
      exact False.elim (Nat.lt_irrefl _ hbad)
    have hx_ne_v : x ≠ vHit := by
      intro hxv
      exact hx_not_used (by simpa [hxv] using hvUsed)
    have hx_ne_w : x ≠ wHit := by
      intro hxw
      exact hx_not_used (by simpa [hxw] using hwUsed)
    let pDirect : G.Walk (left iNew) (right jNew) :=
      (pIn.takeUntil x hxIn).append (pOut.dropUntil x hxOut)
    have hdirect_avoid :
        forall y : V, y ∈ pDirect.support -> y ∉ L.usedVertices := by
      intro y hy
      dsimp [pDirect] at hy
      rw [SimpleGraph.Walk.mem_support_append_iff] at hy
      rcases hy with hyIn | hyOut
      · have hyFull : y ∈ pIn.support :=
          SimpleGraph.Walk.support_takeUntil_subset pIn hxIn hyIn
        rcases hInAvoid y hyFull with hyNot | hyv
        · exact hyNot
        · subst y
          exact False.elim
            ((SimpleGraph.Walk.endpoint_notMem_support_takeUntil
              hpIn hxIn hx_ne_v.symm) hyIn)
      · have hyFull : y ∈ pOut.support :=
          SimpleGraph.Walk.support_dropUntil_subset pOut hxOut hyOut
        rcases hOutAvoid y hyFull with hyNot | hyw
        · exact hyNot
        · subst y
          exact False.elim
            ((Walk.IsPath.start_not_mem_dropUntil_support_of_ne
              hpOut hxOut hx_ne_w) hyOut)
    exact L.hasPartial_succ_of_path_avoids_usedVertices hiNew hjNew
      (pDirect.toPath : G.Walk (left iNew) (right jNew))
      pDirect.toPath.property (by
        intro y hy
        exact hdirect_avoid y
          (SimpleGraph.Walk.support_toPath_subset pDirect hy))


end Schematic.Math.GraphTheory
