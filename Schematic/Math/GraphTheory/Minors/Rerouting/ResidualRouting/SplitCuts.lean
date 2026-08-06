import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.AugmentedSources

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
def PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (s : VertexSplitState V) : Prop :=
  Exists fun i : Fin 3 =>
    i ∉ Set.range L.leftIndex ∧
      Relation.ReflTransGen L.SplitResidualStep
        (VertexSplitState.inn (left i)) s

def PartialThreeVertexLinkage.SplitResidualReachesUnusedRight
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Prop :=
  Exists fun j : Fin 3 =>
    j ∉ Set.range L.rightIndex ∧
      L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.out (right j))

theorem PartialThreeVertexLinkage.unused_left_splitResidualReachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {i : Fin 3} (hi : i ∉ Set.range L.leftIndex) :
    L.SplitResidualReachableFromUnusedLeft
      (VertexSplitState.inn (left i)) :=
  ⟨i, hi, Relation.ReflTransGen.refl⟩

theorem PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.exists_isChain_list
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {s : VertexSplitState V}
    (hreach : L.SplitResidualReachableFromUnusedLeft s) :
    Exists fun i : Fin 3 =>
      i ∉ Set.range L.leftIndex ∧
        Exists fun l : List (VertexSplitState V) =>
          l ≠ [] ∧
            l.head? = some (VertexSplitState.inn (left i)) ∧
              l.getLast? = some s ∧
                l.IsChain L.SplitResidualStep := by
  rcases hreach with ⟨i, hi, hrtg⟩
  rcases reflTransGen_exists_isChain_list hrtg with
    ⟨l, hne, hhead, hlast, hchain⟩
  exact ⟨i, hi, l, hne, hhead, hlast, hchain⟩

theorem PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.exists_minimal_isChain_list
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {s : VertexSplitState V}
    (hreach : L.SplitResidualReachableFromUnusedLeft s) :
    Exists fun i : Fin 3 =>
      i ∉ Set.range L.leftIndex ∧
        Exists fun l : List (VertexSplitState V) =>
          l ≠ [] ∧
            l.head? = some (VertexSplitState.inn (left i)) ∧
              l.getLast? = some s ∧
                l.IsChain L.SplitResidualStep ∧
                  forall m : List (VertexSplitState V),
                    m ≠ [] ->
                      m.head? = some (VertexSplitState.inn (left i)) ->
                        m.getLast? = some s ->
                          m.IsChain L.SplitResidualStep ->
                            l.length <= m.length := by
  rcases hreach with ⟨i, hi, hrtg⟩
  rcases reflTransGen_exists_minimal_isChain_list hrtg with
    ⟨l, hne, hhead, hlast, hchain, hmin⟩
  exact ⟨i, hi, l, hne, hhead, hlast, hchain, hmin⟩

theorem PartialThreeVertexLinkage.SplitResidualReachesUnusedRight.exists_isChain_list
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    (hreach : L.SplitResidualReachesUnusedRight) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        i ∉ Set.range L.leftIndex ∧
          j ∉ Set.range L.rightIndex ∧
            Exists fun l : List (VertexSplitState V) =>
              l ≠ [] ∧
                l.head? = some (VertexSplitState.inn (left i)) ∧
                  l.getLast? = some (VertexSplitState.out (right j)) ∧
                    l.IsChain L.SplitResidualStep := by
  rcases hreach with ⟨j, hj, hfrom⟩
  rcases hfrom.exists_isChain_list with ⟨i, hi, l, hne, hhead, hlast, hchain⟩
  exact ⟨i, j, hi, hj, l, hne, hhead, hlast, hchain⟩

theorem PartialThreeVertexLinkage.SplitResidualReachesUnusedRight.exists_minimal_isChain_list
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    (hreach : L.SplitResidualReachesUnusedRight) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        i ∉ Set.range L.leftIndex ∧
          j ∉ Set.range L.rightIndex ∧
            Exists fun l : List (VertexSplitState V) =>
              l ≠ [] ∧
                l.head? = some (VertexSplitState.inn (left i)) ∧
                  l.getLast? = some (VertexSplitState.out (right j)) ∧
                    l.IsChain L.SplitResidualStep ∧
                      forall m : List (VertexSplitState V),
                        m ≠ [] ->
                          m.head? = some (VertexSplitState.inn (left i)) ->
                            m.getLast? =
                              some (VertexSplitState.out (right j)) ->
                              m.IsChain L.SplitResidualStep ->
                                l.length <= m.length := by
  rcases hreach with ⟨j, hj, hfrom⟩
  rcases hfrom.exists_minimal_isChain_list with
    ⟨i, hi, l, hne, hhead, hlast, hchain, hmin⟩
  exact ⟨i, j, hi, hj, l, hne, hhead, hlast, hchain, hmin⟩

theorem PartialThreeVertexLinkage.exists_ordinary_path_of_splitResidualReaches
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hreach : L.SplitResidualReachesUnusedRight) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        i ∉ Set.range L.leftIndex ∧
          j ∉ Set.range L.rightIndex ∧
            Exists fun p : G.Walk (left i) (right j) =>
              p.IsPath := by
  classical
  rcases hreach with ⟨j, hj, i, hi, hres⟩
  have hGreach : G.Reachable (left i) (right j) :=
    PartialThreeVertexLinkage.SplitResidualStep.reachable_vertex
      (L := L) hres
  rcases hGreach with ⟨p⟩
  exact ⟨i, j, hi, hj, p.toPath, p.toPath.property⟩

def PartialThreeVertexLinkage.SplitResidualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Set V :=
  {v : V |
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.inn v) ∧
      Not (L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out v))}

theorem PartialThreeVertexLinkage.SplitResidualCutSet.subset_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.SplitResidualCutSet ⊆ L.usedVertices := by
  intro v hv
  rcases hv with ⟨hin, hout⟩
  by_contra hv_unused
  rcases hin with ⟨i, hi, hreach⟩
  have hstep :
      L.SplitResidualStep
        (VertexSplitState.inn v) (VertexSplitState.out v) := by
    exact Or.inl ⟨rfl, hv_unused⟩
  exact hout ⟨i, hi, hreach.trans (Relation.ReflTransGen.single hstep)⟩

theorem PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.in_of_out_used
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {v : V}
    (hv : v ∈ L.usedVertices)
    (hout :
      L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out v)) :
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.inn v) := by
  rcases hout with ⟨i, hi, hreach⟩
  have hstep :
      L.SplitResidualStep
        (VertexSplitState.out v) (VertexSplitState.inn v) := by
    exact Or.inl ⟨rfl, hv⟩
  exact ⟨i, hi, hreach.trans (Relation.ReflTransGen.single hstep)⟩

theorem PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.out_of_in_forwardPathDart
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (hdart : L.ForwardPathDart u v)
    (hin :
      L.SplitResidualReachableFromUnusedLeft (VertexSplitState.inn v)) :
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out u) := by
  rcases hin with ⟨i, hi, hreach⟩
  have hstep :
      L.SplitResidualStep
        (VertexSplitState.inn v) (VertexSplitState.out u) := by
    exact Or.inr hdart
  exact ⟨i, hi, hreach.trans (Relation.ReflTransGen.single hstep)⟩

theorem PartialThreeVertexLinkage.Walk.start_splitOutReachable_of_end_splitOutReachable_of_darts_subset
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n)
    {a b : V} (q : G.Walk a b)
    (hsub : q.darts ⊆ (L.path k).darts)
    (hb :
      L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out b)) :
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out a) := by
  induction q with
  | nil =>
      exact hb
  | @cons u v w huv q ih =>
      have hsub_tail : q.darts ⊆ (L.path k).darts := by
        intro d hd
        exact hsub (by
          simp [SimpleGraph.Walk.darts_cons, hd])
      have hv_out :=
        ih hsub_tail hb
      exact by
        refine
          PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.out_of_in_forwardPathDart
            (L := L)
            (u := u)
            (v := v)
            (hdart := ?_) ?_
        · refine ⟨k, huv, hsub ?_⟩
          simp [SimpleGraph.Walk.darts_cons]
        · refine
            PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.in_of_out_used
              (L := L) ?_ hv_out
          exact (show L.ForwardPathDart u v from by
            refine ⟨k, huv, hsub ?_⟩
            simp [SimpleGraph.Walk.darts_cons]).snd_mem_usedVertices

theorem PartialThreeVertexLinkage.Walk.start_splitOutReachable_of_end_splitInReachable_of_darts_subset
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n)
    {a b : V} (q : G.Walk a b)
    (hnil : Not q.Nil)
    (hsub : q.darts ⊆ (L.path k).darts)
    (hb :
      L.SplitResidualReachableFromUnusedLeft (VertexSplitState.inn b)) :
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out a) := by
  induction q with
  | nil =>
      exact False.elim (hnil SimpleGraph.Walk.nil_nil)
  | @cons u v w huv q ih =>
      have hforward : L.ForwardPathDart u v := by
        refine ⟨k, huv, hsub ?_⟩
        simp [SimpleGraph.Walk.darts_cons]
      have hv_in :
          L.SplitResidualReachableFromUnusedLeft
            (VertexSplitState.inn v) := by
        by_cases hqnil : q.Nil
        · have hvw : v = w := hqnil.eq
          simpa [hvw] using hb
        · have hsub_tail : q.darts ⊆ (L.path k).darts := by
            intro d hd
            exact hsub (by
              simp [SimpleGraph.Walk.darts_cons, hd])
          have hv_out :
              L.SplitResidualReachableFromUnusedLeft
                (VertexSplitState.out v) :=
            ih hqnil hsub_tail hb
          exact
            PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.in_of_out_used
              hforward.snd_mem_usedVertices hv_out
      exact
        PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.out_of_in_forwardPathDart
          hforward hv_in

theorem PartialThreeVertexLinkage.path_getVert_splitOutReachable_of_later_splitInReachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n)
    {m r : Nat}
    (hmr : m < r)
    (hr : r <= (L.path k).length)
    (hin :
      L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.inn ((L.path k).getVert r))) :
    L.SplitResidualReachableFromUnusedLeft
      (VertexSplitState.out ((L.path k).getVert m)) := by
  classical
  let p := L.path k
  let q : G.Walk (p.getVert m) (p.getVert r) :=
    ((p.drop m).take (r - m)).copy rfl (by
      rw [SimpleGraph.Walk.drop_getVert]
      congr 1
      omega)
  have hq_len : q.length = r - m := by
    have hle : r - m <= p.length - m := by
      dsimp [p]
      omega
    simp [q, p, hle]
  have hq_not_nil : Not q.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    rw [hq_len]
    omega
  have hsub : q.darts ⊆ (L.path k).darts := by
    intro d hd
    have hd_take :
        d ∈ ((p.drop m).take (r - m)).darts := by
      simpa [q] using hd
    rw [SimpleGraph.Walk.darts_take] at hd_take
    have hd_drop : d ∈ (p.drop m).darts :=
      List.take_subset (r - m) (p.drop m).darts hd_take
    rw [SimpleGraph.Walk.darts_drop] at hd_drop
    exact List.drop_subset m p.darts hd_drop
  exact
    PartialThreeVertexLinkage.Walk.start_splitOutReachable_of_end_splitInReachable_of_darts_subset
      L k q hq_not_nil (by
        simpa [p] using hsub) (by
          simpa [q, p] using hin)

noncomputable def PartialThreeVertexLinkage.splitResidualCutVertex
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n) : V := by
  classical
  exact
    match (L.path k).support.find?
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedLeft
                (VertexSplitState.out v))) with
    | some v => v
    | none => right (L.rightIndex k)

def PartialThreeVertexLinkage.splitResidualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) : Set V :=
  Set.range L.splitResidualCutVertex

theorem PartialThreeVertexLinkage.splitResidualCutSet_ncard_le
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.splitResidualCutSet.ncard <= n := by
  classical
  have hcard :
      Fintype.card (Set.range L.splitResidualCutVertex) <=
        Fintype.card (Fin n) :=
    Fintype.card_range_le L.splitResidualCutVertex
  rw [Set.fintypeCard_eq_ncard] at hcard
  simpa [PartialThreeVertexLinkage.splitResidualCutSet] using hcard

theorem PartialThreeVertexLinkage.splitResidualCutVertex_mem_support
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n) :
    L.splitResidualCutVertex k ∈ (L.path k).support := by
  classical
  unfold PartialThreeVertexLinkage.splitResidualCutVertex
  generalize hfind :
      (L.path k).support.find?
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedLeft
                (VertexSplitState.out v))) = o
  cases o with
  | none =>
      simp
  | some v =>
      have hsome :=
        (List.find?_eq_some_iff_getElem.mp hfind).2
      rcases hsome with ⟨i, hi, hget, _hmin⟩
      rw [← hget]
      exact List.getElem_mem hi

theorem PartialThreeVertexLinkage.splitResidualCutSet_subset_usedVertices
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.splitResidualCutSet ⊆ L.usedVertices := by
  intro v hv
  rcases hv with ⟨k, rfl⟩
  exact ⟨k, L.splitResidualCutVertex_mem_support k⟩

theorem PartialThreeVertexLinkage.splitResidualCutVertex_eq_right_of_right_out_reachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n)
    (hright :
      L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.out (right (L.rightIndex k)))) :
    L.splitResidualCutVertex k = right (L.rightIndex k) := by
  classical
  have hall :
      forall x : V, x ∈ (L.path k).support ->
        L.SplitResidualReachableFromUnusedLeft
          (VertexSplitState.out x) := by
    intro x hx
    exact
      PartialThreeVertexLinkage.Walk.start_splitOutReachable_of_end_splitOutReachable_of_darts_subset
        L k ((L.path k).dropUntil x hx)
        ((L.path k).darts_dropUntil_subset hx) hright
  unfold PartialThreeVertexLinkage.splitResidualCutVertex
  have hnone :
      (L.path k).support.find?
          (fun v =>
            ! decide
                (L.SplitResidualReachableFromUnusedLeft
                  (VertexSplitState.out v))) =
        none := by
    rw [List.find?_eq_none]
    intro x hx
    simp [hall x hx]
  simp [hnone]

theorem PartialThreeVertexLinkage.not_splitOutReachable_unused_right_of_not_reaches
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hno : Not L.SplitResidualReachesUnusedRight)
    {j : Fin 3} (hj : j ∉ Set.range L.rightIndex) :
    Not
      (L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.out (right j))) := by
  intro hreach
  exact hno ⟨j, hj, hreach⟩

theorem PartialThreeVertexLinkage.right_not_splitOutReachable_of_not_mem_splitResidualCutSet
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hno : Not L.SplitResidualReachesUnusedRight)
    {j : Fin 3} (hj : right j ∉ L.splitResidualCutSet) :
    Not
      (L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.out (right j))) := by
  classical
  by_cases hj_used : j ∈ Set.range L.rightIndex
  · rcases hj_used with ⟨k, rfl⟩
    intro hreach
    exact hj ⟨k,
      L.splitResidualCutVertex_eq_right_of_right_out_reachable k hreach⟩
  · exact L.not_splitOutReachable_unused_right_of_not_reaches hno hj_used

theorem PartialThreeVertexLinkage.splitResidualCutSet_ncard_lt_three_of_lt_three
    [Fintype V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (hn : n < 3) :
    L.splitResidualCutSet.ncard < 3 :=
  lt_of_le_of_lt L.splitResidualCutSet_ncard_le hn

theorem PartialThreeVertexLinkage.SplitResidualCutSet.subset_splitResidualCutSet
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    L.SplitResidualCutSet ⊆ L.splitResidualCutSet := by
  classical
  intro v hv
  have hv_used : v ∈ L.usedVertices :=
    PartialThreeVertexLinkage.SplitResidualCutSet.subset_usedVertices L hv
  rcases hv_used with ⟨k, hv_support⟩
  refine ⟨k, ?_⟩
  let p := L.path k
  let pred : V -> Bool := fun w =>
    ! decide
        (L.SplitResidualReachableFromUnusedLeft
          (VertexSplitState.out w))
  have hv_out_not :
      Not
        (L.SplitResidualReachableFromUnusedLeft
          (VertexSplitState.out v)) := hv.2
  have hv_in :
      L.SplitResidualReachableFromUnusedLeft
        (VertexSplitState.inn v) := hv.1
  unfold PartialThreeVertexLinkage.splitResidualCutVertex
  change
    (match p.support.find? pred with
      | some w => w
      | none => right (L.rightIndex k)) = v
  generalize hfind : p.support.find? pred = o
  cases o with
  | none =>
      have hpred_v_not_true :
          Not (pred v = true) :=
        (List.find?_eq_none.mp hfind) v (by simpa [p] using hv_support)
      have hpred_v_true : pred v = true := by
        simp [pred, hv_out_not]
      exact False.elim (hpred_v_not_true hpred_v_true)
  | some c =>
      have hfind_spec := List.find?_eq_some_iff_getElem.mp hfind
      have hpred_c_true : pred c = true := hfind_spec.1
      rcases hfind_spec.2 with ⟨idx, hidx, hget, hmin⟩
      have hc_mem : c ∈ p.support := by
        rw [← hget]
        exact List.getElem_mem hidx
      have hc_out_not :
          Not
            (L.SplitResidualReachableFromUnusedLeft
              (VertexSplitState.out c)) := by
        simpa [pred] using hpred_c_true
      let r := p.support.idxOf v
      have hr_lt : r < p.support.length :=
        List.idxOf_lt_length_of_mem (by simpa [p] using hv_support)
      have hr_le_len : r <= p.length := by
        have hs : p.support.length = p.length + 1 := by
          exact p.length_support
        omega
      have hidx_le_len : idx <= p.length := by
        have hs : p.support.length = p.length + 1 := by
          exact p.length_support
        omega
      have hget_r : p.support[r]'hr_lt = v := by
        exact List.getElem_idxOf hr_lt
      have hp_get_r : p.getVert r = v := by
        simpa [r] using p.getVert_support_idxOf (by simpa [p] using hv_support)
      have hp_get_idx : p.getVert idx = c := by
        rw [p.getVert_eq_support_getElem hidx_le_len]
        exact hget
      have hidxOf_c : p.support.idxOf c = idx := by
        have hnodup := (L.isPath k).support_nodup
        simpa [p, hget] using hnodup.idxOf_getElem idx hidx
      by_cases hr_idx : r < idx
      · have hpred_r_not_true :
            Not (pred (p.support[r]'hr_lt) = true) := by
          have hmin_r := hmin r hr_idx
          intro htrue
          rw [htrue] at hmin_r
          simp at hmin_r
        have hpred_r_true : pred (p.support[r]'hr_lt) = true := by
          simp [hget_r, pred, hv_out_not]
        exact False.elim (hpred_r_not_true hpred_r_true)
      · have hidx_le_r : idx <= r := le_of_not_gt hr_idx
        by_cases hidx_r : idx = r
        · have hidx_eq :
              p.support.idxOf c = p.support.idxOf v := by
            rw [hidxOf_c, hidx_r]
          exact (List.idxOf_inj hc_mem).mp hidx_eq
        · have hidx_lt_r : idx < r := lt_of_le_of_ne hidx_le_r hidx_r
          have hc_out :
              L.SplitResidualReachableFromUnusedLeft
                (VertexSplitState.out c) := by
            have hin_r :
                L.SplitResidualReachableFromUnusedLeft
                  (VertexSplitState.inn ((L.path k).getVert r)) := by
              change
                L.SplitResidualReachableFromUnusedLeft
                  (VertexSplitState.inn (p.getVert r))
              simpa [hp_get_r] using hv_in
            have hreach_idx :
                L.SplitResidualReachableFromUnusedLeft
                  (VertexSplitState.out (p.getVert idx)) :=
              PartialThreeVertexLinkage.path_getVert_splitOutReachable_of_later_splitInReachable
                L k hidx_lt_r hr_le_len hin_r
            simpa [hp_get_idx] using hreach_idx
          exact False.elim (hc_out_not hc_out)

theorem PartialThreeVertexLinkage.SplitResidualReachableFromUnusedLeft.splitStep
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {u v : VertexSplitState V}
    (hu : L.SplitResidualReachableFromUnusedLeft u)
    (huv : L.SplitResidualStep u v) :
    L.SplitResidualReachableFromUnusedLeft v := by
  rcases hu with ⟨i, hi, hreach⟩
  exact ⟨i, hi, hreach.trans (Relation.ReflTransGen.single huv)⟩

theorem PartialThreeVertexLinkage.splitOutReachable_of_splitInReachable_of_not_mem_splitResidualCutSet
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {v : V}
    (hin :
      L.SplitResidualReachableFromUnusedLeft (VertexSplitState.inn v))
    (hv : v ∉ L.splitResidualCutSet) :
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out v) := by
  by_contra hout
  have hraw : v ∈ L.SplitResidualCutSet := ⟨hin, hout⟩
  exact hv
    (PartialThreeVertexLinkage.SplitResidualCutSet.subset_splitResidualCutSet
      L hraw)

theorem PartialThreeVertexLinkage.splitResidualCutVertex_eq_left_of_left_out_not_reachable
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (k : Fin n)
    (hleft :
      Not
        (L.SplitResidualReachableFromUnusedLeft
          (VertexSplitState.out (left (L.leftIndex k))))) :
    L.splitResidualCutVertex k = left (L.leftIndex k) := by
  classical
  unfold PartialThreeVertexLinkage.splitResidualCutVertex
  have hfind :
      (L.path k).support.find?
          (fun v =>
            ! decide
                (L.SplitResidualReachableFromUnusedLeft
                  (VertexSplitState.out v))) =
        some (left (L.leftIndex k)) := by
    let l := (L.path k).support
    have hl_ne : l ≠ [] := by
      simp [l]
    have hhead :
        l.head hl_ne = left (L.leftIndex k) := by
      simp [l]
    have hpred :
        (fun v =>
            ! decide
                (L.SplitResidualReachableFromUnusedLeft
                  (VertexSplitState.out v)))
          (l.head hl_ne) = true := by
      simp [hhead, hleft]
    change l.find?
        (fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedLeft
                (VertexSplitState.out v))) =
      some (left (L.leftIndex k))
    rw [← List.cons_head_tail hl_ne]
    simpa [hhead] using
      (List.find?_cons_of_pos
        (p := fun v =>
          ! decide
              (L.SplitResidualReachableFromUnusedLeft
                (VertexSplitState.out v)))
        (a := l.head hl_ne) (l := l.tail) hpred)
  simp [hfind]

theorem PartialThreeVertexLinkage.left_splitOutReachable_of_not_mem_splitResidualCutSet
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {i : Fin 3}
    (hi : left i ∉ L.splitResidualCutSet) :
    L.SplitResidualReachableFromUnusedLeft
      (VertexSplitState.out (left i)) := by
  classical
  by_cases hi_used : i ∈ Set.range L.leftIndex
  · rcases hi_used with ⟨k, rfl⟩
    by_contra hnot
    exact hi ⟨k,
      L.splitResidualCutVertex_eq_left_of_left_out_not_reachable k hnot⟩
  · have hin :
        L.SplitResidualReachableFromUnusedLeft
          (VertexSplitState.inn (left i)) :=
      L.unused_left_splitResidualReachable hi_used
    exact
      PartialThreeVertexLinkage.splitOutReachable_of_splitInReachable_of_not_mem_splitResidualCutSet
        hin hi

theorem PartialThreeVertexLinkage.Walk.end_splitOutReachable_of_avoids_splitResidualCutSet
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {a b : V} (p : G.Walk a b)
    (ha :
      L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out a))
    (havoid :
      forall v : V, v ∈ p.support -> v ∉ L.splitResidualCutSet) :
    L.SplitResidualReachableFromUnusedLeft (VertexSplitState.out b) := by
  induction p with
  | nil =>
      exact ha
  | @cons u v w huv p ih =>
      have hv_in :
          L.SplitResidualReachableFromUnusedLeft
            (VertexSplitState.inn v) := by
        exact ha.splitStep (by
          exact Or.inr huv)
      have hv_not_cut : v ∉ L.splitResidualCutSet := by
        exact havoid v (by simp [SimpleGraph.Walk.support_cons])
      have hv_out :
          L.SplitResidualReachableFromUnusedLeft
            (VertexSplitState.out v) :=
        PartialThreeVertexLinkage.splitOutReachable_of_splitInReachable_of_not_mem_splitResidualCutSet
          hv_in hv_not_cut
      exact ih hv_out (by
        intro x hx
        exact havoid x (by
          simp [SimpleGraph.Walk.support_cons, hx]))


end Schematic.Math.GraphTheory
