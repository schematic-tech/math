import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem PartialThreeVertexLinkage.ForwardPathDart.idxOf_fst_lt_idxOf_snd_of_snd_mem
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ForwardPathDart u v)
    {k : Fin n}
    (hv : v ∈ (L.path k).support) :
    (L.path k).support.idxOf u < (L.path k).support.idxOf v := by
  exact h.idxOf_fst_lt_idxOf_snd_of_fst_mem (h.fst_mem_path_of_snd_mem hv)

theorem PartialThreeVertexLinkage.exists_forwardPathDart_from_of_mem_path_not_right
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {k : Fin n} {u : V}
    (hu : u ∈ (L.path k).support)
    (hu_ne_right : u ≠ right (L.rightIndex k)) :
    Exists fun v : V => L.ForwardPathDart u v := by
  classical
  let p := L.path k
  let idx : Nat := p.support.idxOf u
  have hidx_support : idx < p.support.length :=
    List.idxOf_lt_length_of_mem (by simpa [p] using hu)
  have hidx_lt_len : idx < p.length := by
    by_contra hnot
    have hidx_eq : idx = p.length := by
      rw [p.length_support] at hidx_support
      omega
    have hu_get : p.support[idx]'hidx_support = u := by
      simp [idx]
    have hright_get :
        p.support[idx]'hidx_support = right (L.rightIndex k) := by
      have hlast : p.support[p.length]'(by
          rw [p.length_support]
          exact Nat.lt_succ_self p.length) = right (L.rightIndex k) := by
        simp [p]
      simp [hidx_eq, hlast]
    exact hu_ne_right (hu_get ▸ hright_get)
  have hidx_darts : idx < p.darts.length := by
    simpa [p, SimpleGraph.Walk.length_darts] using hidx_lt_len
  let d : G.Dart := p.darts[idx]'hidx_darts
  have hfst_get : (p.darts[idx]'hidx_darts).fst = u := by
    have hdget := p.darts_getElem_eq_getVert idx hidx_darts
    have hgetVert : p.getVert idx = u := by
      simpa [idx, p] using p.getVert_support_idxOf (by simpa [p] using hu)
    rw [hdget]
    simp [hgetVert]
  have hfst : d.fst = u := by
    simpa [d] using hfst_get
  have hadj : G.Adj u d.snd := by
    simpa [hfst] using d.adj
  have hdmem : d ∈ p.darts := List.getElem_mem hidx_darts
  have hdmem' : (⟨(u, d.snd), hadj⟩ : G.Dart) ∈ p.darts := by
    convert hdmem using 1
    ext <;> simp [d, hfst]
  exact ⟨d.snd, k, hadj, by simpa [p] using hdmem'⟩

theorem PartialThreeVertexLinkage.exists_forwardPathDart_to_of_mem_path_not_left
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    {k : Fin n} {v : V}
    (hv : v ∈ (L.path k).support)
    (hv_ne_left : v ≠ left (L.leftIndex k)) :
    Exists fun u : V => L.ForwardPathDart u v := by
  classical
  let p := L.path k
  let idx : Nat := p.support.idxOf v
  have hidx_support : idx < p.support.length :=
    List.idxOf_lt_length_of_mem (by simpa [p] using hv)
  have hidx_pos : 0 < idx := by
    by_contra hnot
    have hidx_eq : idx = 0 := by omega
    have hv_get : p.support[idx]'hidx_support = v := by
      simp [idx]
    have hleft_get :
        p.support[idx]'hidx_support = left (L.leftIndex k) := by
      have hfirst : p.support[0]'(by
          rw [p.length_support]
          exact Nat.succ_pos p.length) = left (L.leftIndex k) := by
        simp [p]
      simp [hidx_eq, hfirst]
    exact hv_ne_left (hv_get ▸ hleft_get)
  let pred : Nat := idx - 1
  have hpred_darts : pred < p.darts.length := by
    have hidx_le_len : idx <= p.length := by
      rw [p.length_support] at hidx_support
      omega
    dsimp [pred]
    simpa [p, SimpleGraph.Walk.length_darts] using (by omega : idx - 1 < p.length)
  let d : G.Dart := p.darts[pred]'hpred_darts
  have hsnd_get : (p.darts[pred]'hpred_darts).snd = v := by
    have hdget := p.darts_getElem_eq_getVert pred hpred_darts
    have hpred_succ : pred + 1 = idx := by
      dsimp [pred]
      omega
    have hgetVert : p.getVert idx = v := by
      simpa [idx, p] using p.getVert_support_idxOf (by simpa [p] using hv)
    rw [hdget]
    have hsnd_get : p.getVert (pred + 1) = v := by
      simpa [hpred_succ] using hgetVert
    simp [hsnd_get]
  have hsnd : d.snd = v := by
    simpa [d] using hsnd_get
  have hadj : G.Adj d.fst v := by
    simpa [hsnd] using d.adj
  have hdmem : d ∈ p.darts := List.getElem_mem hpred_darts
  have hdmem' : (⟨(d.fst, v), hadj⟩ : G.Dart) ∈ p.darts := by
    convert hdmem using 1
    ext <;> simp [d, hsnd]
  exact ⟨d.fst, k, hadj, by simpa [p] using hdmem'⟩

theorem PartialThreeVertexLinkage.not_forwardPathDart_to_left
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n) {u : V} :
    Not (L.ForwardPathDart u (left (L.leftIndex k))) := by
  intro h
  have hlt :
      (L.path k).support.idxOf u <
        (L.path k).support.idxOf (left (L.leftIndex k)) :=
    h.idxOf_fst_lt_idxOf_snd_of_snd_mem
      (k := k) (L.path k).start_mem_support
  have hstart :
      (L.path k).support.idxOf (left (L.leftIndex k)) = 0 := by
    rw [List.idxOf_eq_zero_iff_head_eq (by simp)]
    simp
  omega

theorem PartialThreeVertexLinkage.not_forwardPathDart_from_right
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n) {v : V} :
    Not (L.ForwardPathDart (right (L.rightIndex k)) v) := by
  intro h
  have hv_mem : v ∈ (L.path k).support :=
    h.snd_mem_path_of_fst_mem (k := k) (L.path k).end_mem_support
  have hlt :
      (L.path k).support.idxOf (right (L.rightIndex k)) <
        (L.path k).support.idxOf v :=
    h.idxOf_fst_lt_idxOf_snd_of_fst_mem
      (k := k) (L.path k).end_mem_support
  have hend :
      (L.path k).support.idxOf (right (L.rightIndex k)) =
        (L.path k).support.length - 1 := by
    have hlast_not_drop :
        (L.path k).support.getLast (by simp) ∉ (L.path k).support.dropLast := by
      intro hmem
      have hnodup : (L.path k).support.Nodup := (L.isPath k).support_nodup
      have hsplit :
          (L.path k).support.dropLast ++
              [(L.path k).support.getLast (by simp)] =
            (L.path k).support :=
        List.dropLast_append_getLast (by simp)
      have hnodup_append :
          ((L.path k).support.dropLast ++
              [(L.path k).support.getLast (by simp)]).Nodup := by
        simpa [hsplit] using hnodup
      have hdisj :
          List.Disjoint (L.path k).support.dropLast
            [(L.path k).support.getLast (by simp)] :=
        List.disjoint_of_nodup_append hnodup_append
      exact hdisj hmem (by simp)
    simpa using
      List.idxOf_getLast
        (l := (L.path k).support) (by simp) hlast_not_drop
  have hv_lt :
      (L.path k).support.idxOf v < (L.path k).support.length :=
    List.idxOf_lt_length_of_mem hv_mem
  omega

def PartialThreeVertexLinkage.ResidualStep
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) (u v : V) : Prop :=
  (G.Adj u v ∧ Not (L.ForwardPathDart u v)) ∨
    L.ForwardPathDart v u

theorem PartialThreeVertexLinkage.ResidualStep.adj
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : L.ResidualStep u v) :
    G.Adj u v := by
  rcases h with h | h
  · exact h.1
  · exact h.adj.symm

theorem PartialThreeVertexLinkage.ResidualStep.reachable
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n} {u v : V}
    (h : Relation.ReflTransGen L.ResidualStep u v) :
    G.Reachable u v := by
  rw [SimpleGraph.reachable_eq_reflTransGen]
  exact h.mono (fun _a _b hab => hab.adj)

theorem reflTransGen_exists_isChain_list
    {α : Type u} {r : α -> α -> Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    Exists fun l : List α =>
      l ≠ [] ∧ l.head? = some a ∧ l.getLast? = some b ∧
        l.IsChain r := by
  induction h with
  | refl =>
      exact ⟨[a], by simp, by simp, by simp, by simp⟩
  | @tail b c _ hstep ih =>
      rcases ih with ⟨l, hne, hhead, hlast, hchain⟩
      refine ⟨l ++ [c], ?_, ?_, ?_, ?_⟩
      · simp [hne]
      · simpa [List.head?_append_of_ne_nil l hne] using hhead
      · simp
      · apply hchain.append
        · simp
        · intro x hx y hy
          simp at hy
          subst y
          have hxb : x = b := by
            simp [hlast] at hx
            exact hx.symm
          simpa [hxb] using hstep

theorem reflTransGen_exists_minimal_isChain_list
    {α : Type u} {r : α -> α -> Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) :
    Exists fun l : List α =>
      l ≠ [] ∧ l.head? = some a ∧ l.getLast? = some b ∧
        l.IsChain r ∧
          forall m : List α,
            m ≠ [] -> m.head? = some a -> m.getLast? = some b ->
              m.IsChain r -> l.length <= m.length := by
  classical
  let P : Nat -> Prop := fun len =>
    Exists fun l : List α =>
      l ≠ [] ∧ l.head? = some a ∧ l.getLast? = some b ∧
        l.IsChain r ∧ l.length = len
  have hP : Exists P := by
    obtain ⟨l, hne, hhead, hlast, hchain⟩ :=
      reflTransGen_exists_isChain_list h
    exact ⟨l.length, l, hne, hhead, hlast, hchain, rfl⟩
  let len0 : Nat := Nat.find hP
  rcases Nat.find_spec hP with ⟨l, hne, hhead, hlast, hchain, hlen⟩
  refine ⟨l, hne, hhead, hlast, hchain, ?_⟩
  intro m hmne hmhead hmlast hmchain
  have hmP : P m.length := ⟨m, hmne, hmhead, hmlast, hmchain, rfl⟩
  have hmin : len0 <= m.length := Nat.find_min' hP hmP
  omega

theorem minimal_isChain_getElem_ne_of_lt
    {α : Type u} {r : α -> α -> Prop} {a b : α}
    {l : List α}
    (hne : l ≠ [])
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hchain : l.IsChain r)
    (hmin :
      forall m : List α,
        m ≠ [] -> m.head? = some a -> m.getLast? = some b ->
          m.IsChain r -> l.length <= m.length)
    {i j : Nat}
    (hi : i < l.length)
    (hj : j < l.length)
    (hij : i < j) :
    l[i]'hi ≠ l[j]'hj := by
  classical
  intro heq
  let m : List α := l.take (i + 1) ++ l.drop (j + 1)
  have hmne : m ≠ [] := by
    dsimp [m]
    cases htake : l.take (i + 1) with
    | nil =>
        have hlen_take : (l.take (i + 1)).length = i + 1 := by
          rw [List.length_take]
          omega
        simp [htake] at hlen_take
    | cons x xs =>
        simp
  have hmhead : m.head? = some a := by
    dsimp [m]
    have htake_ne : l.take (i + 1) ≠ [] := by
      intro hnil
      have hlen_take : (l.take (i + 1)).length = i + 1 := by
        rw [List.length_take]
        omega
      simp [hnil] at hlen_take
    rw [List.head?_append_of_ne_nil _ htake_ne]
    have htake_head : (l.take (i + 1)).head? = l.head? := by
      cases l with
      | nil => simp at hi
      | cons x xs => simp
    simp [htake_head, hhead]
  have hmchain : m.IsChain r := by
    dsimp [m]
    apply (hchain.take (i + 1)).append
    · exact hchain.drop (j + 1)
    · intro x hx y hy
      have hxlast : x = l[i]'hi := by
        have hlast_take :
            (l.take (i + 1)).getLast? = some (l[i]'hi) := by
          rw [List.getLast?_eq_getElem?]
          have hlen_take : (l.take (i + 1)).length = i + 1 := by
            rw [List.length_take]
            omega
          rw [hlen_take, Nat.add_sub_cancel]
          rw [List.getElem?_take]
          simp [List.getElem?_eq_getElem hi]
        simpa [hlast_take] using hx.symm
      by_cases hdrop_empty : l.drop (j + 1) = []
      · simp [hdrop_empty] at hy
      · have hhead_drop :
            (l.drop (j + 1)).head? =
              some (l[j + 1]'(by
                by_contra hnot
                have hle : l.length <= j + 1 := by omega
                have hdrop_nil : l.drop (j + 1) = [] := by
                  apply List.eq_nil_of_length_eq_zero
                  rw [List.length_drop]
                  omega
                exact hdrop_empty hdrop_nil)) := by
          rw [List.head?_drop]
          exact List.getElem?_eq_getElem (by
            by_contra hnot
            have hle : l.length <= j + 1 := by omega
            have hdrop_nil : l.drop (j + 1) = [] := by
              apply List.eq_nil_of_length_eq_zero
              rw [List.length_drop]
              omega
            exact hdrop_empty hdrop_nil)
        have hyhead : y = l[j + 1]'(by
            by_contra hnot
            have hle : l.length <= j + 1 := by omega
            have hdrop_nil : l.drop (j + 1) = [] := by
              apply List.eq_nil_of_length_eq_zero
              rw [List.length_drop]
              omega
            exact hdrop_empty hdrop_nil) := by
          simpa [hhead_drop] using hy.symm
        have hstep := (List.isChain_iff_getElem.mp hchain) j (by
          by_contra hnot
          have hle : l.length <= j + 1 := by omega
          have hdrop_nil : l.drop (j + 1) = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [List.length_drop]
            omega
          exact hdrop_empty hdrop_nil)
        simpa [hxlast, hyhead, heq] using hstep
  have hmlast : m.getLast? = some b := by
    dsimp [m]
    by_cases hdrop_empty : l.drop (j + 1) = []
    · rw [hdrop_empty, List.append_nil]
      have hj_last : j + 1 = l.length := by
        have hlen_drop : (l.drop (j + 1)).length = 0 := by
          simp [hdrop_empty]
        rw [List.length_drop] at hlen_drop
        omega
      have hlast_take :
          (l.take (i + 1)).getLast? = some (l[i]'hi) := by
        rw [List.getLast?_eq_getElem?]
        have hlen_take : (l.take (i + 1)).length = i + 1 := by
          rw [List.length_take]
          omega
        rw [hlen_take, Nat.add_sub_cancel]
        rw [List.getElem?_take]
        simp [List.getElem?_eq_getElem hi]
      have hlast_l : l.getLast? = some (l[j]'hj) := by
        rw [List.getLast?_eq_getElem?]
        have hj_eq : l.length - 1 = j := by omega
        rw [hj_eq]
        exact List.getElem?_eq_getElem hj
      have hb : l[j]'hj = b := by
        rw [hlast_l] at hlast
        injection hlast
      simp [hlast_take, heq, hb]
    · rw [List.getLast?_append_of_ne_nil _ hdrop_empty]
      have hlast_drop : (l.drop (j + 1)).getLast? = some b := by
        have hj_succ_len : j + 1 < l.length := by
          by_contra hnot
          have hle : l.length <= j + 1 := by omega
          have hdrop_nil : l.drop (j + 1) = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [List.length_drop]
            omega
          exact hdrop_empty hdrop_nil
        rw [List.getLast?_drop]
        simp [hj_succ_len, hlast]
      exact hlast_drop
  have hmin_m : l.length <= m.length := hmin m hmne hmhead hmlast hmchain
  have hmlen : m.length = i + 1 + (l.length - (j + 1)) := by
    dsimp [m]
    rw [List.length_append, List.length_take, List.length_drop]
    have hmin_take : min (i + 1) l.length = i + 1 := by omega
    rw [hmin_take]
  have hshort : m.length < l.length := by
    rw [hmlen]
    omega
  omega

theorem minimal_isChain_nodup
    {α : Type u} {r : α -> α -> Prop} {a b : α}
    {l : List α}
    (hne : l ≠ [])
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hchain : l.IsChain r)
    (hmin :
      forall m : List α,
        m ≠ [] -> m.head? = some a -> m.getLast? = some b ->
          m.IsChain r -> l.length <= m.length) :
    l.Nodup := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  intro i j hij hj hEq
  have hi : i < l.length := lt_trans hij hj
  have hneij :
      l[i]'hi ≠ l[j]'hj :=
    minimal_isChain_getElem_ne_of_lt
      hne hhead hlast hchain hmin hi hj hij
  have hsome_i : l[i]? = some (l[i]'hi) :=
    List.getElem?_eq_getElem hi
  have hsome_j : l[j]? = some (l[j]'hj) :=
    List.getElem?_eq_getElem hj
  rw [hsome_i, hsome_j] at hEq
  injection hEq with h
  exact hneij h

theorem reachable_induce_of_isChain_eq_or_adj_cons
    {A : Set V} {xs : List V} {x b : V}
    (hchain : (x :: xs).IsChain (fun u v : V => u = v ∨ G.Adj u v))
    (hlast : (x :: xs).getLast? = some b)
    (hA : forall v : V, v ∈ x :: xs -> v ∈ A) :
    (G.induce A).Reachable
      ⟨x, hA x (by simp)⟩
      ⟨b, by
        have hb_last : b ∈ (x :: xs).getLast? := by
          simp [hlast]
        exact hA b (List.mem_of_mem_getLast? hb_last)⟩ := by
  induction xs generalizing x with
  | nil =>
      have hxb : x = b := by simpa using hlast
      subst b
      exact SimpleGraph.Reachable.refl _
  | cons y ys ih =>
      have hparts : (x = y ∨ G.Adj x y) ∧
          (y :: ys).IsChain (fun u v : V => u = v ∨ G.Adj u v) := by
        simpa using hchain
      have hxA : x ∈ A := hA x (by simp)
      have hyA : y ∈ A := hA y (by simp)
      have htailA : forall v : V, v ∈ y :: ys -> v ∈ A := by
        intro v hv
        exact hA v (by simp [hv])
      have htail :
          (G.induce A).Reachable
            ⟨y, hyA⟩
            ⟨b, by
              have hb_last : b ∈ (y :: ys).getLast? := by
                simpa using hlast
              exact htailA b (List.mem_of_mem_getLast? hb_last)⟩ :=
        ih hparts.2 (by simpa using hlast) htailA
      rcases hparts.1 with hxy | hxy
      · subst y
        simpa using htail
      · have hxy_ind : (G.induce A).Adj ⟨x, hxA⟩ ⟨y, hyA⟩ := by
          simpa using hxy
        exact hxy_ind.reachable.trans (by simpa using htail)

theorem reachable_induce_of_isChain_eq_or_adj
    {A : Set V} {l : List V} {a b : V}
    (hchain : l.IsChain (fun u v : V => u = v ∨ G.Adj u v))
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hA : forall v : V, v ∈ l -> v ∈ A) :
    (G.induce A).Reachable
      ⟨a, by
        have ha_head : a ∈ l.head? := by
          simp [hhead]
        exact hA a (List.mem_of_mem_head? ha_head)⟩
      ⟨b, by
        have hb_last : b ∈ l.getLast? := by
          simp [hlast]
        exact hA b (List.mem_of_mem_getLast? hb_last)⟩ := by
  cases l with
  | nil => simp at hhead
  | cons x xs =>
      have hxa : x = a := by simpa using hhead
      subst a
      simpa using
        reachable_induce_of_isChain_eq_or_adj_cons
          (G := G) (A := A) (xs := xs) (x := x) (b := b)
          hchain hlast hA

theorem exists_walk_of_isChain_eq_or_adj
    {l : List V} {a b : V}
    (hne : l ≠ [])
    (hchain : l.IsChain (fun u v : V => u = v ∨ G.Adj u v))
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b) :
    Exists fun p : G.Walk a b =>
      forall x : V, x ∈ p.support -> x ∈ l := by
  induction l generalizing a b with
  | nil =>
      exact False.elim (hne rfl)
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hxa : x = a := by simpa using hhead
          have hxb : x = b := by simpa using hlast
          subst a
          subst b
          refine ⟨SimpleGraph.Walk.nil, ?_⟩
          intro y hy
          simpa using hy
      | cons y ys =>
          have hxa : x = a := by simpa using hhead
          subst a
          have htail_ne : y :: ys ≠ [] := by simp
          have htail_chain :
              (y :: ys).IsChain (fun u v : V => u = v ∨ G.Adj u v) :=
            hchain.of_cons
          have htail_last : (y :: ys).getLast? = some b := by
            simpa using hlast
          obtain ⟨pTail, hpTail⟩ :=
            ih (a := y) (b := b) htail_ne htail_chain (by simp) htail_last
          have hrel : x = y ∨ G.Adj x y := hchain.rel
          rcases hrel with hxy | hxy
          · subst y
            refine ⟨pTail, ?_⟩
            intro z hz
            exact List.mem_cons_of_mem x (hpTail z hz)
          · refine ⟨SimpleGraph.Walk.cons hxy pTail, ?_⟩
            intro z hz
            simp [SimpleGraph.Walk.support_cons] at hz ⊢
            rcases hz with rfl | hz
            · exact Or.inl rfl
            · exact Or.inr (by simpa using hpTail z hz)

theorem exists_path_of_isChain_eq_or_adj
    [DecidableEq V]
    {l : List V} {a b : V}
    (hne : l ≠ [])
    (hchain : l.IsChain (fun u v : V => u = v ∨ G.Adj u v))
    (hhead : l.head? = some a)
    (hlast : l.getLast? = some b) :
    Exists fun p : G.Walk a b =>
      p.IsPath ∧ forall x : V, x ∈ p.support -> x ∈ l := by
  classical
  obtain ⟨p, hp⟩ :=
    exists_walk_of_isChain_eq_or_adj
      (G := G) hne hchain hhead hlast
  exact ⟨p.toPath, p.toPath.property, by
    intro x hx
    exact hp x (SimpleGraph.Walk.support_toPath_subset p hx)⟩

end Schematic.Math.GraphTheory
