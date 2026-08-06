import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.SplitCuts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
def PartialThreeVertexLinkage.ResidualReachableFromUnusedLeft
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (v : V) : Prop :=
  Exists fun i : Fin 3 =>
    i ∉ Set.range L.leftIndex ∧
      Relation.ReflTransGen L.ResidualStep (left i) v

def PartialThreeVertexLinkage.ResidualReachableSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Set V :=
  {v : V | L.ResidualReachableFromUnusedLeft v}

def PartialThreeVertexLinkage.ResidualReachesUnusedRight
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Prop :=
  Exists fun j : Fin 3 =>
    j ∉ Set.range L.rightIndex ∧
      L.ResidualReachableFromUnusedLeft (right j)

theorem PartialThreeVertexLinkage.ResidualReachableFromUnusedLeft.reachable
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {v : V}
    (h : L.ResidualReachableFromUnusedLeft v) :
    Exists fun i : Fin 3 =>
      i ∉ Set.range L.leftIndex ∧ G.Reachable (left i) v := by
  rcases h with ⟨i, hi, hreach⟩
  exact ⟨i, hi, PartialThreeVertexLinkage.ResidualStep.reachable hreach⟩

def PartialThreeVertexLinkage.ResidualBoundary
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Set V :=
  {v : V | v ∈ L.usedVertices ∧
    Not (L.ResidualReachableFromUnusedLeft v) ∧
      Exists fun u : V => L.ResidualReachableFromUnusedLeft u ∧ G.Adj u v}

theorem PartialThreeVertexLinkage.unused_left_residualReachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {i : Fin 3} (hi : i ∉ Set.range L.leftIndex) :
    L.ResidualReachableFromUnusedLeft (left i) :=
  ⟨i, hi, Relation.ReflTransGen.refl⟩

theorem PartialThreeVertexLinkage.not_residualReachable_unused_right_of_not_reaches
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hno : Not L.ResidualReachesUnusedRight)
    {j : Fin 3} (hj : j ∉ Set.range L.rightIndex) :
    Not (L.ResidualReachableFromUnusedLeft (right j)) := by
  intro hreach
  exact hno ⟨j, hj, hreach⟩

theorem PartialThreeVertexLinkage.ResidualBoundary.subset_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.ResidualBoundary ⊆ L.usedVertices := by
  intro v hv
  exact hv.1

theorem PartialThreeVertexLinkage.ResidualBoundary.not_reachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {v : V} (hv : v ∈ L.ResidualBoundary) :
    Not (L.ResidualReachableFromUnusedLeft v) :=
  hv.2.1

theorem PartialThreeVertexLinkage.ResidualReachableFromUnusedLeft.step
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (hu : L.ResidualReachableFromUnusedLeft u)
    (huv : L.ResidualStep u v) :
    L.ResidualReachableFromUnusedLeft v := by
  rcases hu with ⟨i, hi, hreach⟩
  exact ⟨i, hi, hreach.trans (Relation.ReflTransGen.single huv)⟩

theorem PartialThreeVertexLinkage.forwardPathDart_of_adj_not_residualStep
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (huv : G.Adj u v)
    (hnot : Not (L.ResidualStep u v)) :
    L.ForwardPathDart u v := by
  by_contra hforward
  exact hnot (Or.inl ⟨huv, hforward⟩)

theorem PartialThreeVertexLinkage.residualReachable_or_boundary_of_adj
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (hu : L.ResidualReachableFromUnusedLeft u)
    (huv : G.Adj u v) :
    L.ResidualReachableFromUnusedLeft v ∨ v ∈ L.ResidualBoundary := by
  classical
  by_cases hstep : L.ResidualStep u v
  · exact Or.inl (hu.step hstep)
  · have hforward : L.ForwardPathDart u v :=
      L.forwardPathDart_of_adj_not_residualStep huv hstep
    by_cases hv : L.ResidualReachableFromUnusedLeft v
    · exact Or.inl hv
    · exact Or.inr ⟨hforward.snd_mem_usedVertices, hv, ⟨u, hu, huv⟩⟩

theorem PartialThreeVertexLinkage.residualReachable_of_forwardPathDart_target
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (hforward : L.ForwardPathDart u v)
    (hv : L.ResidualReachableFromUnusedLeft v) :
    L.ResidualReachableFromUnusedLeft u :=
  hv.step (Or.inr hforward)

theorem PartialThreeVertexLinkage.Walk.support_residualReachable_of_end_reachable_of_darts_subset
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n)
    {a b : V} (q : G.Walk a b)
    (hsub : q.darts ⊆ (L.path k).darts)
    (hb : L.ResidualReachableFromUnusedLeft b) :
    forall x : V, x ∈ q.support -> L.ResidualReachableFromUnusedLeft x := by
  induction q with
  | nil =>
      intro x hx
      simp at hx
      subst x
      exact hb
  | cons huv q ih =>
      have hsub_tail : q.darts ⊆ (L.path k).darts := by
        intro d hd
        exact hsub (by
          simp [SimpleGraph.Walk.darts_cons, hd])
      have htail :=
        ih hsub_tail hb
      have hv : L.ResidualReachableFromUnusedLeft _ :=
        htail _ q.start_mem_support
      intro x hx
      simp [SimpleGraph.Walk.support_cons] at hx
      rcases hx with rfl | hx
      · apply L.residualReachable_of_forwardPathDart_target
        · refine ⟨k, huv, hsub ?_⟩
          simp [SimpleGraph.Walk.darts_cons]
        · exact hv
      · exact htail x hx

noncomputable def PartialThreeVertexLinkage.residualCutVertex
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n) : V := by
  classical
  exact
    match (L.path k).support.find?
        (fun v => ! decide (L.ResidualReachableFromUnusedLeft v)) with
    | some v => v
    | none => right (L.rightIndex k)

def PartialThreeVertexLinkage.residualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Set V :=
  Set.range L.residualCutVertex

theorem PartialThreeVertexLinkage.residualCutSet_ncard_le
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.residualCutSet.ncard <= n := by
  classical
  have hcard :
      Fintype.card (Set.range L.residualCutVertex) <=
        Fintype.card (Fin n) :=
    Fintype.card_range_le L.residualCutVertex
  rw [Set.fintypeCard_eq_ncard] at hcard
  simpa [PartialThreeVertexLinkage.residualCutSet] using hcard

theorem PartialThreeVertexLinkage.residualCutVertex_mem_support
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n) :
    L.residualCutVertex k ∈ (L.path k).support := by
  classical
  unfold PartialThreeVertexLinkage.residualCutVertex
  generalize hfind :
      (L.path k).support.find?
        (fun v => ! decide (L.ResidualReachableFromUnusedLeft v)) = o
  cases o with
  | none =>
      simp
  | some v =>
      have hsome :=
        (List.find?_eq_some_iff_getElem.mp hfind).2
      rcases hsome with ⟨i, hi, hget, _hmin⟩
      rw [← hget]
      exact List.getElem_mem hi

theorem PartialThreeVertexLinkage.residualCutSet_subset_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.residualCutSet ⊆ L.usedVertices := by
  intro v hv
  rcases hv with ⟨k, rfl⟩
  exact ⟨k, L.residualCutVertex_mem_support k⟩

theorem PartialThreeVertexLinkage.residualCutVertex_eq_left_of_left_not_reachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n)
    (hleft :
      Not (L.ResidualReachableFromUnusedLeft (left (L.leftIndex k)))) :
    L.residualCutVertex k = left (L.leftIndex k) := by
  classical
  unfold PartialThreeVertexLinkage.residualCutVertex
  have hfind :
      (L.path k).support.find?
          (fun v => ! decide (L.ResidualReachableFromUnusedLeft v)) =
        some (left (L.leftIndex k)) := by
    let l := (L.path k).support
    have hl_ne : l ≠ [] := by
      simp [l]
    have hhead :
        l.head hl_ne = left (L.leftIndex k) := by
      simp [l]
    have hpred :
        (fun v => ! decide (L.ResidualReachableFromUnusedLeft v))
          (l.head hl_ne) = true := by
      simp [hhead, hleft]
    change l.find? (fun v => ! decide (L.ResidualReachableFromUnusedLeft v)) =
      some (left (L.leftIndex k))
    rw [← List.cons_head_tail hl_ne]
    simpa [hhead] using
      (List.find?_cons_of_pos
        (p := fun v => ! decide (L.ResidualReachableFromUnusedLeft v))
        (a := l.head hl_ne) (l := l.tail) hpred)
  simp [hfind]

theorem PartialThreeVertexLinkage.residualCutVertex_eq_right_of_right_reachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n)
    (hright :
      L.ResidualReachableFromUnusedLeft (right (L.rightIndex k))) :
    L.residualCutVertex k = right (L.rightIndex k) := by
  classical
  have hall :
      forall x : V, x ∈ (L.path k).support ->
        L.ResidualReachableFromUnusedLeft x :=
    PartialThreeVertexLinkage.Walk.support_residualReachable_of_end_reachable_of_darts_subset
      L
      k (L.path k) (by intro d hd; exact hd) hright
  unfold PartialThreeVertexLinkage.residualCutVertex
  have hnone :
      (L.path k).support.find?
          (fun v => ! decide (L.ResidualReachableFromUnusedLeft v)) =
        none := by
    rw [List.find?_eq_none]
    intro x hx
    simp [hall x hx]
  simp [hnone]

theorem PartialThreeVertexLinkage.left_residualReachable_of_not_mem_residualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {i : Fin 3}
    (hi : left i ∉ L.residualCutSet) :
    L.ResidualReachableFromUnusedLeft (left i) := by
  classical
  by_cases hi_used : i ∈ Set.range L.leftIndex
  · rcases hi_used with ⟨k, rfl⟩
    by_contra hnot
    exact hi ⟨k, L.residualCutVertex_eq_left_of_left_not_reachable k hnot⟩
  · exact L.unused_left_residualReachable hi_used

theorem PartialThreeVertexLinkage.right_not_residualReachable_of_not_mem_residualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hno : Not L.ResidualReachesUnusedRight)
    {j : Fin 3}
    (hj : right j ∉ L.residualCutSet) :
    Not (L.ResidualReachableFromUnusedLeft (right j)) := by
  classical
  by_cases hj_used : j ∈ Set.range L.rightIndex
  · rcases hj_used with ⟨k, rfl⟩
    intro hreach
    exact hj ⟨k,
      L.residualCutVertex_eq_right_of_right_reachable k hreach⟩
  · exact L.not_residualReachable_unused_right_of_not_reaches hno hj_used

theorem PartialThreeVertexLinkage.residualCutVertex_eq_of_forwardPathDart_boundary
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {u v : V}
    (huv : L.ForwardPathDart u v)
    (hu : L.ResidualReachableFromUnusedLeft u)
    (hv : Not (L.ResidualReachableFromUnusedLeft v)) :
    Exists fun k : Fin n => L.residualCutVertex k = v := by
  classical
  rcases huv with ⟨k, hadj, hdart⟩
  let p := L.path k
  obtain ⟨m, hm, hget⟩ := List.getElem_of_mem hdart
  have hm_len : m < p.length := by
    simpa [p, SimpleGraph.Walk.length_darts] using hm
  have hsupport_idx : m + 1 < p.support.length := by
    simpa [p.length_support] using Nat.succ_lt_succ hm_len
  have hfst_get : p.getVert m = u := by
    have hdget := p.darts_getElem_eq_getVert m hm
    have hfst :
        (p.darts[m]'hm).fst = u := by
      simp [p, hget]
    rw [hdget] at hfst
    simpa using hfst
  have hsnd_get : p.support[m + 1]'hsupport_idx = v := by
    have hdget := p.darts_getElem_eq_getVert m hm
    have hsnd :
        (p.darts[m]'hm).snd = v := by
      simp [p, hget]
    rw [hdget] at hsnd
    have hgetVert_succ : p.getVert (m + 1) = v := by
      simpa using hsnd
    rw [← p.getVert_eq_support_getElem
      (n := m + 1) (Nat.succ_le_of_lt hm_len)]
    exact hgetVert_succ
  have hR_get : L.ResidualReachableFromUnusedLeft (p.getVert m) := by
    simpa [hfst_get] using hu
  have hsub_take : (p.take m).darts ⊆ p.darts := by
    intro d hd
    rw [SimpleGraph.Walk.darts_take] at hd
    exact List.take_subset m p.darts hd
  have hprefix :
      forall x : V, x ∈ (p.take m).support ->
        L.ResidualReachableFromUnusedLeft x :=
    PartialThreeVertexLinkage.Walk.support_residualReachable_of_end_reachable_of_darts_subset
      L k (p.take m) (by
        intro d hd
        exact hsub_take hd) hR_get
  have hfind :
      p.support.find?
          (fun w => ! decide (L.ResidualReachableFromUnusedLeft w)) =
        some v := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨?_, ?_⟩
    · simp [hv]
    · refine ⟨m + 1, hsupport_idx, hsnd_get, ?_⟩
      intro j hj
      have hj_le_m : j <= m := Nat.lt_succ_iff.mp hj
      have hj_support_len : j < p.support.length := lt_of_lt_of_le hj
        (Nat.le_of_lt hsupport_idx)
      have hj_take_len :
          j < (p.support.take (m + 1)).length := by
        rw [List.length_take]
        exact lt_min (Nat.lt_succ_of_le hj_le_m) hj_support_len
      have hj_mem_take :
          p.support[j]'hj_support_len ∈ p.support.take (m + 1) := by
        convert List.getElem_mem hj_take_len using 1
        exact (List.getElem_take (xs := p.support)
          (j := m + 1) (i := j) (h := hj_take_len)).symm
      have hj_mem_take_walk :
          p.support[j]'hj_support_len ∈ (p.take m).support := by
        simpa [SimpleGraph.Walk.take_support_eq_support_take_succ]
          using hj_mem_take
      have hRj :
          L.ResidualReachableFromUnusedLeft
            (p.support[j]'hj_support_len) :=
        hprefix _ hj_mem_take_walk
      simp [hRj]
  have hcut : L.residualCutVertex k = v := by
    unfold PartialThreeVertexLinkage.residualCutVertex
    simp [p, hfind]
  exact ⟨k, hcut⟩

theorem PartialThreeVertexLinkage.ResidualBoundary.subset_residualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.ResidualBoundary ⊆ L.residualCutSet := by
  intro v hv
  rcases hv with ⟨_hused, hnot, u, hu, huv⟩
  have hnot_step : Not (L.ResidualStep u v) := by
    intro hstep
    exact hnot (hu.step hstep)
  have hforward : L.ForwardPathDart u v :=
    L.forwardPathDart_of_adj_not_residualStep huv hnot_step
  obtain ⟨k, hk⟩ :=
    L.residualCutVertex_eq_of_forwardPathDart_boundary
      hforward hu hnot
  exact ⟨k, hk⟩

theorem PartialThreeVertexLinkage.residualCutSet_ncard_lt_three_of_lt_three
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hn : n < 3) :
    L.residualCutSet.ncard < 3 :=
  lt_of_le_of_lt L.residualCutSet_ncard_le hn

theorem PartialThreeVertexLinkage.Walk.end_residualReachable_of_avoids_boundary
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {a b : V} (p : G.Walk a b)
    (ha : L.ResidualReachableFromUnusedLeft a)
    (havoid : forall v : V, v ∈ p.support -> v ∉ L.ResidualBoundary) :
    L.ResidualReachableFromUnusedLeft b := by
  induction p with
  | nil =>
      exact ha
  | cons huv p ih =>
      refine ih ?_ ?_
      ·
        rcases L.residualReachable_or_boundary_of_adj ha huv with hreach | hboundary
        · exact hreach
        · exact False.elim (havoid _ (by
            simp [SimpleGraph.Walk.support_cons]) hboundary)
      ·
        intro v hvp hvboundary
        exact havoid v (by
          simp [SimpleGraph.Walk.support_cons, hvp]) hvboundary

theorem PartialThreeVertexLinkage.exists_leftIndex_not_used_of_lt_three
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hn : n < 3) :
    Exists fun i : Fin 3 => i ∉ Set.range L.leftIndex := by
  classical
  by_contra hnone
  have hall : (Set.univ : Set (Fin 3)) ⊆ Set.range L.leftIndex := by
    intro i _hi
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hEq : Set.range L.leftIndex = (Set.univ : Set (Fin 3)) := by
    exact (Set.eq_univ_iff_forall).mpr (fun i => hall trivial)
  have hcard_range : (Set.range L.leftIndex).ncard = n := by
    rw [Set.ncard_range_of_injective L.leftIndex_injective]
    simp
  rw [hEq] at hcard_range
  have hcard_univ : (Set.univ : Set (Fin 3)).ncard = 3 := by
    simp
  omega

theorem PartialThreeVertexLinkage.exists_rightIndex_not_used_of_lt_three
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hn : n < 3) :
    Exists fun i : Fin 3 => i ∉ Set.range L.rightIndex := by
  classical
  by_contra hnone
  have hall : (Set.univ : Set (Fin 3)) ⊆ Set.range L.rightIndex := by
    intro i _hi
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hEq : Set.range L.rightIndex = (Set.univ : Set (Fin 3)) := by
    exact (Set.eq_univ_iff_forall).mpr (fun i => hall trivial)
  have hcard_range : (Set.range L.rightIndex).ncard = n := by
    rw [Set.ncard_range_of_injective L.rightIndex_injective]
    simp
  rw [hEq] at hcard_range
  have hcard_univ : (Set.univ : Set (Fin 3)).ncard = 3 := by
    simp
  omega

noncomputable def PartialThreeVertexLinkage.snocPath
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hjNew : jNew ∉ Set.range L.rightIndex)
    (pNew : G.Walk (left iNew) (right jNew))
    (hpNew : pNew.IsPath)
    (hdisj :
      forall k : Fin n,
        Disjoint {v : V | v ∈ (L.path k).support}
          {v : V | v ∈ pNew.support}) :
    PartialThreeVertexLinkage G left right (n + 1) where
  leftIndex := Fin.snoc L.leftIndex iNew
  rightIndex := Fin.snoc L.rightIndex jNew
  leftIndex_injective := by
    exact Fin.snoc_injective_iff.mpr ⟨L.leftIndex_injective, hiNew⟩
  rightIndex_injective := by
    exact Fin.snoc_injective_iff.mpr ⟨L.rightIndex_injective, hjNew⟩
  path k := by
    cases k using Fin.lastCases with
    | last =>
        exact pNew.copy (by simp [Fin.snoc_last]) (by simp [Fin.snoc_last])
    | cast i =>
        exact (L.path i).copy
          (by simp [Fin.snoc_castSucc])
          (by simp [Fin.snoc_castSucc])
  isPath k := by
    cases k using Fin.lastCases with
    | last => simpa using hpNew
    | cast i => simpa using L.isPath i
  pairwise_vertex_disjoint := by
    intro a b hab
    cases a using Fin.lastCases with
    | last =>
        cases b using Fin.lastCases with
        | last => exact False.elim (hab rfl)
        | cast j =>
            rw [disjoint_comm]
            simpa using hdisj j
    | cast i =>
        cases b using Fin.lastCases with
        | last =>
            simpa using hdisj i
        | cast j =>
            have hij : i ≠ j := by
              intro h
              exact hab (by simp [h])
            simpa using L.pairwise_vertex_disjoint i j hij


end Schematic.Math.GraphTheory
