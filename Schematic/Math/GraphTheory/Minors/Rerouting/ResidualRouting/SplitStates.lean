import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.ForwardSteps

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/--
The vertex-splitting state space for the capacity-respecting residual network
used by the true vertex version of finite Menger.  `inn v` and `out v` are the
two sides of the unit-capacity vertex arc for `v`.
-/
inductive VertexSplitState (V : Type u) where
  | inn : V -> VertexSplitState V
  | out : V -> VertexSplitState V
deriving DecidableEq

namespace VertexSplitState

def equivSum (V : Type u) : VertexSplitState V ≃ V ⊕ V where
  toFun
    | inn v => Sum.inl v
    | out v => Sum.inr v
  invFun
    | Sum.inl v => inn v
    | Sum.inr v => out v
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro s
    cases s <;> rfl

instance instFintype [Fintype V] : Fintype (VertexSplitState V) :=
  Fintype.ofEquiv (V ⊕ V) (equivSum V).symm

def vertex : VertexSplitState V -> V
  | inn v => v
  | out v => v

@[simp] theorem vertex_inn (v : V) :
    (VertexSplitState.inn v).vertex = v := rfl

@[simp] theorem vertex_out (v : V) :
    (VertexSplitState.out v).vertex = v := rfl

end VertexSplitState

/--
Capacity-respecting residual steps for a partial vertex linkage.

The four clauses are the standard split-vertex residual network:
* an unused vertex may be crossed from `inn v` to `out v`;
* a used vertex capacity arc may be traversed backward from `out v` to `inn v`;
* any graph dart may be traversed from `out u` to `inn v`;
* a current path dart may be traversed backward from `inn v` to `out u`.

This relation is intentionally separate from `ResidualStep`, whose vertex-only
form is useful for some cut bookkeeping but is too coarse for augmentation.
-/
def PartialThreeVertexLinkage.SplitResidualStep
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    VertexSplitState V -> VertexSplitState V -> Prop
  | .inn u, .out v =>
      (u = v ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart v u
  | .out u, .inn v =>
      (u = v ∧ u ∈ L.usedVertices) ∨ G.Adj u v
  | _, _ => False

theorem PartialThreeVertexLinkage.SplitResidualStep.not_self
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    (s : VertexSplitState V) :
    Not (L.SplitResidualStep s s) := by
  cases s <;> simp [PartialThreeVertexLinkage.SplitResidualStep]

theorem PartialThreeVertexLinkage.splitResidualChain_getElem_ne_succ
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {l : List (VertexSplitState V)} {idx : Nat}
    (hnext : idx + 1 < l.length)
    (hchain : l.IsChain L.SplitResidualStep) :
    l[idx]'(lt_trans (Nat.lt_succ_self idx) hnext) ≠
      l[idx + 1]'hnext := by
  intro hEq
  have hstep := (List.isChain_iff_getElem.mp hchain) idx hnext
  exact
    PartialThreeVertexLinkage.SplitResidualStep.not_self
      (L := L) (l[idx]'(lt_trans (Nat.lt_succ_self idx) hnext))
      (by simpa [hEq] using hstep)

theorem PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b : VertexSplitState V}
    (h : L.SplitResidualStep a b) :
    a.vertex = b.vertex ∨ G.Adj a.vertex b.vertex := by
  cases a with
  | inn u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep] at h
      | out v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep] at h
          rcases h with hcap | hdart
          · exact Or.inl hcap.1
          · exact Or.inr hdart.adj.symm
  | out u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep] at h
          rcases h with hcap | hedge
          · exact Or.inl hcap.1
          · exact Or.inr hedge
      | out v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep] at h

theorem PartialThreeVertexLinkage.SplitResidualStep.no_outgoing_left_inn
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n) :
    forall a : VertexSplitState V,
      Not (L.SplitResidualStep
        (VertexSplitState.inn (left (L.leftIndex k))) a) := by
  intro a h
  cases a with
  | inn v =>
      simp [PartialThreeVertexLinkage.SplitResidualStep] at h
  | out v =>
      simp [PartialThreeVertexLinkage.SplitResidualStep] at h
      rcases h with hcap | hdart
      · exact hcap.2 (by
          simpa [hcap.1] using L.left_mem_usedVertices k)
      · exact L.not_forwardPathDart_to_left k hdart

theorem PartialThreeVertexLinkage.SplitResidualStep.no_incoming_right_out
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n) :
    forall a : VertexSplitState V,
      Not (L.SplitResidualStep a
        (VertexSplitState.out (right (L.rightIndex k)))) := by
  intro a h
  cases a with
  | inn u =>
      simp [PartialThreeVertexLinkage.SplitResidualStep] at h
      rcases h with hcap | hdart
      · exact hcap.2 (by
          simpa [hcap.1] using L.right_mem_usedVertices k)
      · exact L.not_forwardPathDart_from_right k hdart
  | out u =>
      simp [PartialThreeVertexLinkage.SplitResidualStep] at h

theorem PartialThreeVertexLinkage.SplitResidualStep.idxOf_out_lt_inn_of_inn_out
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {v w : V}
    (hstep :
      L.SplitResidualStep (VertexSplitState.inn v) (VertexSplitState.out w))
    {k : Fin n}
    (hv : v ∈ (L.path k).support) :
    (L.path k).support.idxOf w < (L.path k).support.idxOf v := by
  have hv_used : v ∈ L.usedVertices := ⟨k, hv⟩
  simp [PartialThreeVertexLinkage.SplitResidualStep] at hstep
  rcases hstep with hcap | hdart
  · exact False.elim (hcap.2 (by simpa [hcap.1] using hv_used))
  · exact
      hdart.idxOf_fst_lt_idxOf_snd_of_snd_mem hv

theorem PartialThreeVertexLinkage.SplitResidualStep.out_mem_same_path_of_inn_out
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {v w : V}
    (hstep :
      L.SplitResidualStep (VertexSplitState.inn v) (VertexSplitState.out w))
    {k : Fin n}
    (hv : v ∈ (L.path k).support) :
    w ∈ (L.path k).support := by
  have hv_used : v ∈ L.usedVertices := ⟨k, hv⟩
  simp [PartialThreeVertexLinkage.SplitResidualStep] at hstep
  rcases hstep with hcap | hdart
  · exact False.elim (hcap.2 (by simpa [hcap.1] using hv_used))
  · rcases hdart with ⟨i, hwi, hdart⟩
    by_cases hik : i = k
    · subst k
      exact (L.path i).dart_fst_mem_support_of_mem_darts
        (d := (⟨(w, v), hwi⟩ : G.Dart)) hdart
    · have hvi : v ∈ (L.path i).support :=
        (L.path i).dart_snd_mem_support_of_mem_darts
          (d := (⟨(w, v), hwi⟩ : G.Dart)) hdart
      exact False.elim
        (Set.disjoint_left.mp (L.pairwise_vertex_disjoint i k hik) hvi hv)

theorem PartialThreeVertexLinkage.SplitResidualStep.reachable_vertex
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b : VertexSplitState V}
    (h : Relation.ReflTransGen L.SplitResidualStep a b) :
    G.Reachable a.vertex b.vertex := by
  classical
  have hproj :
      Relation.ReflTransGen
        (fun u v : V => u = v ∨ G.Adj u v) a.vertex b.vertex :=
    Relation.ReflTransGen.lift
      (fun s : VertexSplitState V => s.vertex)
      (fun x y hxy =>
        PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
          (L := L) hxy)
      h
  rw [SimpleGraph.reachable_eq_reflTransGen]
  exact
    Relation.ReflTransGen.trans_induction_on hproj
      (fun _ => Relation.ReflTransGen.refl)
      (fun {u v} hstep => by
        rcases hstep with hEq | hAdj
        · simpa [hEq] using
            (Relation.ReflTransGen.refl :
              Relation.ReflTransGen G.Adj u u)
        · exact Relation.ReflTransGen.single hAdj)
      (fun _ _ huv hvw => huv.trans hvw)

def List.Consecutive {α : Type u} (l : List α) (a b : α) : Prop :=
  Exists fun idx : Nat =>
    Exists fun hnext : idx + 1 < l.length =>
      l[idx]'(lt_trans (Nat.lt_succ_self idx) hnext) = a ∧
        l[idx + 1]'hnext = b

theorem List.Consecutive.snd_unique_of_fst
    {α : Type u} {l : List α} (hnodup : l.Nodup)
    {a b c : α}
    (hab : List.Consecutive l a b)
    (hac : List.Consecutive l a c) :
    b = c := by
  rcases hab with ⟨i, hi, hia, hib⟩
  rcases hac with ⟨j, hj, hja, hjc⟩
  have hij : i = j := by
    have hsame :
        l[i]'(lt_trans (Nat.lt_succ_self i) hi) =
          l[j]'(lt_trans (Nat.lt_succ_self j) hj) := by
      rw [hia, hja]
    exact hnodup.getElem_inj_iff.mp hsame
  subst j
  exact hib.symm.trans hjc

theorem List.Consecutive.fst_unique_of_snd
    {α : Type u} {l : List α} (hnodup : l.Nodup)
    {a b c : α}
    (hac : List.Consecutive l a c)
    (hbc : List.Consecutive l b c) :
    a = b := by
  rcases hac with ⟨i, hi, hia, hic⟩
  rcases hbc with ⟨j, hj, hjb, hjc⟩
  have hij : i = j := by
    have hsame :
        l[i + 1]'hi = l[j + 1]'hj := by
      rw [hic, hjc]
    have hsucc : i + 1 = j + 1 :=
      hnodup.getElem_inj_iff.mp hsame
    omega
  subst j
  exact hia.symm.trans hjb

theorem List.Consecutive.rel_of_isChain
    {α : Type u} {r : α -> α -> Prop} {l : List α}
    (hchain : l.IsChain r) {a b : α}
    (hab : List.Consecutive l a b) :
    r a b := by
  rcases hab with ⟨idx, hnext, ha, hb⟩
  have hstep := (List.isChain_iff_getElem.mp hchain) idx hnext
  simpa [ha, hb] using hstep

theorem List.not_consecutive_to_head_of_nodup
    {α : Type u} {l : List α} (hnodup : l.Nodup)
    {a b : α} (hhead : l.head? = some b) :
    Not (List.Consecutive l a b) := by
  intro h
  rcases h with ⟨idx, hnext, _ha, hb⟩
  have h0len : 0 < l.length := by omega
  have hget0 : l[0]? = some (l[0]'h0len) :=
    List.getElem?_eq_getElem h0len
  rw [List.head?_eq_getElem?, hget0] at hhead
  injection hhead with hhead_state
  have hsame :
      l[0]'h0len = l[idx + 1]'hnext := by
    rw [hhead_state, hb]
  have hidx : 0 = idx + 1 :=
    hnodup.getElem_inj_iff.mp hsame
  omega

theorem List.not_consecutive_from_last_of_nodup
    {α : Type u} {l : List α} (hnodup : l.Nodup)
    {a b : α} (hlast : l.getLast? = some a) :
    Not (List.Consecutive l a b) := by
  intro h
  rcases h with ⟨idx, hnext, ha, _hb⟩
  have hlast_get : l.getLast? = some (l[idx]'(lt_trans
      (Nat.lt_succ_self idx) hnext)) := by
    rw [ha]
    exact hlast
  have hidx_last : idx = l.length - 1 := by
    have hgetLast :
        l.getLast? =
          some (l[l.length - 1]'(by omega)) := by
      rw [List.getLast?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)
    rw [hgetLast] at hlast_get
    injection hlast_get with hsame
    exact hnodup.getElem_inj_iff.mp hsame.symm
  omega

theorem List.exists_consecutive_from_head_of_head_ne_last
    {α : Type u} {l : List α} {a b : α}
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hne : a ≠ b) :
    Exists fun c : α => List.Consecutive l a c := by
  cases l with
  | nil =>
      simp at hhead
  | cons x xs =>
      cases xs with
      | nil =>
          have hxa : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          exact False.elim (hne (hxa.symm.trans hxb))
      | cons y ys =>
          refine ⟨y, 0, by simp, ?_, by simp⟩
          simpa using hhead

theorem List.exists_consecutive_to_last_of_head_ne_last
    {α : Type u} {l : List α} {a b : α}
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hne : a ≠ b) :
    Exists fun c : α => List.Consecutive l c b := by
  cases l with
  | nil =>
      simp at hhead
  | cons x xs =>
      cases xs with
      | nil =>
          have hxa : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          exact False.elim (hne (hxa.symm.trans hxb))
      | cons y ys =>
          let l' : List α := x :: y :: ys
          let idx : Nat := l'.length - 2
          have hidxNext : idx + 1 < l'.length := by
            dsimp [idx, l']
            omega
          have hidx : idx < l'.length :=
            lt_trans (Nat.lt_succ_self idx) hidxNext
          have hlast_state : l'[idx + 1]'hidxNext = b := by
            have hgetLast :
                l'.getLast? = some (l'[idx + 1]'hidxNext) := by
              rw [List.getLast?_eq_getElem?]
              have hidxsucc : idx + 1 = l'.length - 1 := by
                dsimp [idx, l']
                omega
              simp [hidxsucc]
            have hlast' : l'.getLast? = some b := by
              simpa [l'] using hlast
            rw [hgetLast] at hlast'
            exact Option.some.inj hlast'
          exact ⟨l'[idx]'hidx, idx, hidxNext, rfl, hlast_state⟩

theorem List.exists_consecutive_from_of_mem_of_getLast_ne
    {α : Type u} {l : List α} {s t : α}
    (hs : s ∈ l)
    (hlast : l.getLast? = some t)
    (hst : s ≠ t) :
    Exists fun c : α => List.Consecutive l s c := by
  rcases List.getElem_of_mem hs with ⟨idx, hidx, hget⟩
  have hnext : idx + 1 < l.length := by
    by_contra hnot
    have hidx_last : idx = l.length - 1 := by omega
    have hgetLast : l.getLast? = some (l[idx]'hidx) := by
      rw [List.getLast?_eq_getElem?]
      simp [hidx_last]
    rw [hgetLast] at hlast
    exact hst (hget.symm.trans (Option.some.inj hlast))
  exact ⟨l[idx + 1]'hnext, idx, hnext, hget, rfl⟩

theorem List.Consecutive.not_swap_of_nodup
    {α : Type u} {l : List α} (hnodup : l.Nodup)
    {a b : α}
    (hab : List.Consecutive l a b)
    (hba : List.Consecutive l b a) :
    False := by
  rcases hab with ⟨i, hi, hia, hib⟩
  rcases hba with ⟨j, hj, hjb, hja⟩
  have hi_len : i < l.length := lt_trans (Nat.lt_succ_self i) hi
  have hj_len : j < l.length := lt_trans (Nat.lt_succ_self j) hj
  have h_b :
      l[i + 1]'hi = l[j]'hj_len := by
    rw [hib, hjb]
  have h_a :
      l[i]'hi_len = l[j + 1]'hj := by
    rw [hia, hja]
  have hsucc_eq : i + 1 = j :=
    hnodup.getElem_inj_iff.mp h_b
  have hprev_eq : i = j + 1 :=
    hnodup.getElem_inj_iff.mp h_a
  omega

theorem exists_relation_incoming_terminal_of_chain_from_nonterminal_source
    {α : Type u} {r : α -> α -> Prop}
    {m : List α} {source terminal : α}
    (hhead : m.head? = some source)
    (hlast : m.getLast? = some terminal)
    (hchain : m.IsChain r)
    (hsource_out : Exists fun u : α => r source u)
    (hterminal : Not (Exists fun u : α => r terminal u)) :
    Exists fun a : α => r a terminal := by
  have hne : source ≠ terminal := by
    intro hEq
    rcases hsource_out with ⟨u, hsu⟩
    exact hterminal ⟨u, by simpa [hEq] using hsu⟩
  obtain ⟨a, hcon⟩ :=
    List.exists_consecutive_to_last_of_head_ne_last hhead hlast hne
  exact ⟨a, List.Consecutive.rel_of_isChain hchain hcon⟩

theorem reflTransGen_eq_of_no_incoming
    {α : Type u} {r : α -> α -> Prop} {a b : α}
    (hno_in : forall c : α, Not (r c b))
    (h : Relation.ReflTransGen r a b) :
    a = b := by
  rcases Relation.ReflTransGen.cases_tail h with hEq | hstep
  · exact hEq.symm
  · rcases hstep with ⟨c, _hac, hcb⟩
    exact False.elim (hno_in c hcb)

theorem reflTransGen_of_isChain_head?_getLast?
    {α : Type u} {r : α -> α -> Prop}
    {m : List α} {source terminal : α}
    (hm_ne : m ≠ [])
    (hhead : m.head? = some source)
    (hlast : m.getLast? = some terminal)
    (hchain : m.IsChain r) :
    Relation.ReflTransGen r source terminal := by
  cases m with
  | nil =>
      exact False.elim (hm_ne rfl)
  | cons x xs =>
      have hx : x = source := by
        simpa using hhead
      have hlast_eq :
          (x :: xs).getLast (List.cons_ne_nil x xs) = terminal := by
        have hgl :
            (x :: xs).getLast? =
              some ((x :: xs).getLast (List.cons_ne_nil x xs)) :=
          List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil x xs)
        rw [hgl] at hlast
        exact Option.some.inj hlast
      subst x
      simpa [hlast_eq] using
        List.relationReflTransGen_of_exists_isChain_cons xs hchain hlast_eq

theorem relation_sources_eq_of_same_terminal_of_left_unique
    {α : Type u} {r : α -> α -> Prop} {source₁ source₂ terminal : α}
    (hleft : Relator.LeftUnique r)
    (hsource₁ : forall a : α, Not (r a source₁))
    (hsource₂ : forall a : α, Not (r a source₂))
    (hreach₁ : Relation.ReflTransGen r source₁ terminal)
    (hreach₂ : Relation.ReflTransGen r source₂ terminal) :
    source₁ = source₂ := by
  have hcomp :
      Relation.ReflTransGen (flip r) source₁ source₂ ∨
        Relation.ReflTransGen (flip r) source₂ source₁ :=
    Relation.ReflTransGen.total_of_right_unique hleft.flip
      hreach₁.swap hreach₂.swap
  rcases hcomp with h12 | h21
  · exact
      (reflTransGen_eq_of_no_incoming
        (r := r) (a := source₂) (b := source₁) hsource₁
        (by simpa [Function.swap, flip] using h12.swap)).symm
  · exact
      reflTransGen_eq_of_no_incoming
        (r := r) (a := source₁) (b := source₂) hsource₂
        (by simpa [Function.swap, flip] using h21.swap)

theorem relation_sources_eq_of_same_terminal_chains_of_left_unique
    {α : Type u} {r : α -> α -> Prop}
    {m₁ m₂ : List α} {source₁ source₂ terminal : α}
    (hleft : Relator.LeftUnique r)
    (hsource₁ : forall a : α, Not (r a source₁))
    (hsource₂ : forall a : α, Not (r a source₂))
    (hm₁_ne : m₁ ≠ [])
    (hhead₁ : m₁.head? = some source₁)
    (hlast₁ : m₁.getLast? = some terminal)
    (hchain₁ : m₁.IsChain r)
    (hm₂_ne : m₂ ≠ [])
    (hhead₂ : m₂.head? = some source₂)
    (hlast₂ : m₂.getLast? = some terminal)
    (hchain₂ : m₂.IsChain r) :
    source₁ = source₂ := by
  exact
    relation_sources_eq_of_same_terminal_of_left_unique
      hleft hsource₁ hsource₂
      (reflTransGen_of_isChain_head?_getLast?
        hm₁_ne hhead₁ hlast₁ hchain₁)
      (reflTransGen_of_isChain_head?_getLast?
        hm₂_ne hhead₂ hlast₂ hchain₂)

theorem PartialThreeVertexLinkage.SplitResidualStep.no_chain_incoming_left
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3}
    (k : Fin n)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    forall a : VertexSplitState V,
      Not (List.Consecutive l a
        (VertexSplitState.inn (left (L.leftIndex k)))) := by
  intro a hcon
  rcases hcon with ⟨idx, hnext, _ha, hb⟩
  by_cases hlast_idx : idx + 1 = l.length - 1
  · have hgetLast :
        l.getLast? = some (l[idx + 1]'hnext) := by
      rw [List.getLast?_eq_getElem?]
      simp [hlast_idx]
    rw [hgetLast] at hlast
    injection hlast with hstate
    have hbad :
        VertexSplitState.inn (left (L.leftIndex k)) =
          VertexSplitState.out (right jNew) := hb.symm.trans hstate
    cases hbad
  · have hnextnext : idx + 2 < l.length := by omega
    have hstep :=
      (List.isChain_iff_getElem.mp hchain) (idx + 1) hnextnext
    exact
      PartialThreeVertexLinkage.SplitResidualStep.no_outgoing_left_inn
        (L := L) k (l[idx + 2]'hnextnext) (by
          simpa [hb] using hstep)

theorem PartialThreeVertexLinkage.SplitResidualStep.no_chain_outgoing_right
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {iNew : Fin 3}
    (k : Fin n)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    forall a : VertexSplitState V,
      Not (List.Consecutive l
        (VertexSplitState.out (right (L.rightIndex k))) a) := by
  intro a hcon
  rcases hcon with ⟨idx, hnext, ha, _hb⟩
  by_cases hidx0 : idx = 0
  · subst idx
    have h0len : 0 < l.length := by omega
    have hget0 : l[0]? = some (l[0]'h0len) :=
      List.getElem?_eq_getElem h0len
    rw [List.head?_eq_getElem?, hget0] at hhead
    injection hhead with hstate
    have hbad :
        VertexSplitState.out (right (L.rightIndex k)) =
          VertexSplitState.inn (left iNew) := ha.symm.trans hstate
    cases hbad
  · let prev : Nat := idx - 1
    have hprevNext : prev + 1 < l.length := by
      dsimp [prev]
      omega
    have hprevLen : prev < l.length := by
      exact lt_trans (Nat.lt_succ_self prev) hprevNext
    have hprevSucc : prev + 1 = idx := by
      dsimp [prev]
      omega
    have hstep :=
      (List.isChain_iff_getElem.mp hchain) prev hprevNext
    exact
      PartialThreeVertexLinkage.SplitResidualStep.no_incoming_right_out
        (L := L) k (l[prev]'hprevLen) (by
          simpa [hprevSucc, ha] using hstep)

theorem relation_exists_terminal_reachable_of_finite_right_unique
    {α : Type u} [Fintype α]
    {r : α -> α -> Prop} {source : α}
    (hright : forall {a b c : α}, r a c -> r b c -> a = b)
    (hsource : forall a : α, Not (r a source)) :
    Exists fun terminal : α =>
      Relation.ReflTransGen r source terminal ∧
        Not (Exists fun u : α => r terminal u) := by
  classical
  by_contra hnot
  push Not at hnot
  let Reach := {x : α // Relation.ReflTransGen r source x}
  letI : Fintype Reach := Fintype.ofFinite Reach
  have hsucc : forall x : Reach, Exists fun y : Reach => r x.1 y.1 := by
    intro x
    obtain ⟨y, hxy⟩ := hnot x.1 x.2
    exact ⟨⟨y, x.2.tail hxy⟩, hxy⟩
  let f : Reach -> Reach := fun x => Classical.choose (hsucc x)
  have hfstep : forall x : Reach, r x.1 (f x).1 := by
    intro x
    exact (Classical.choose_spec (hsucc x))
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hy : r y.1 (f x).1 := by
      have hval : (f y).1 = (f x).1 := by
        exact congrArg Subtype.val hxy.symm
      simpa [hval] using hfstep y
    exact hright (hfstep x) hy
  have hsurj : Function.Surjective f :=
    hfinj.bijective_of_finite.2
  let sourceReach : Reach :=
    ⟨source, Relation.ReflTransGen.refl⟩
  obtain ⟨x, hx⟩ := hsurj sourceReach
  have hxsource : r x.1 source := by
    have hval : (f x).1 = source := by
      exact congrArg Subtype.val hx
    simpa [hval] using hfstep x
  exact hsource x.1 hxsource

end Schematic.Math.GraphTheory
