import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.CurrentArcs

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/--
The directed arcs after augmenting a partial linkage by a split residual chain:
take the symmetric difference of the current linkage arcs and the chain arcs,
with opposite pairs cancelling.
-/
def PartialThreeVertexLinkage.SplitAugmentedArc
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (l : List (VertexSplitState V)) :
    VertexSplitState V -> VertexSplitState V -> Prop :=
  fun a b =>
    (L.SplitCurrentArc a b ∧ Not (List.Consecutive l b a)) ∨
      (List.Consecutive l a b ∧ Not (L.SplitCurrentArc b a))

theorem PartialThreeVertexLinkage.SplitAugmentedArc.forget_eq_or_adj
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)}
    (hchain : l.IsChain L.SplitResidualStep)
    {a b : VertexSplitState V}
    (h : L.SplitAugmentedArc l a b) :
    a.vertex = b.vertex ∨ G.Adj a.vertex b.vertex := by
  rcases h with hcur | hres
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.forget_eq_or_adj
        (L := L) hcur.1
  · exact
      PartialThreeVertexLinkage.SplitResidualStep.forget_eq_or_adj
        (L := L) (List.Consecutive.rel_of_isChain hchain hres.1)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.state_cases
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)}
    (hchain : l.IsChain L.SplitResidualStep)
    {a b : VertexSplitState V}
    (h : L.SplitAugmentedArc l a b) :
    (Exists fun u : V => Exists fun v : V =>
      a = VertexSplitState.inn u ∧ b = VertexSplitState.out v) ∨
      (Exists fun u : V => Exists fun v : V =>
        a = VertexSplitState.out u ∧ b = VertexSplitState.inn v) := by
  rcases h with hcur | hres
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.state_cases
        (L := L) hcur.1
  · exact
      PartialThreeVertexLinkage.SplitResidualStep.state_cases
        (L := L) (List.Consecutive.rel_of_isChain hchain hres.1)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.not_self
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)}
    (hnodup : l.Nodup)
    {s : VertexSplitState V}
    (h : L.SplitAugmentedArc l s s) :
    False := by
  rcases h with hcur | hchain
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.not_self
        (L := L) s hcur.1
  · rcases hchain.1 with ⟨idx, hnext, hstateA, hstateB⟩
    have hidx : idx < l.length := lt_trans (Nat.lt_succ_self idx) hnext
    have hsame :
        l[idx]'hidx = l[idx + 1]'hnext := by
      rw [hstateA, hstateB]
    have hidx_eq : idx = idx + 1 :=
      hnodup.getElem_inj_iff.mp hsame
    omega

theorem PartialThreeVertexLinkage.SplitAugmentedArc.left_unique
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source : V}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hchain : l.IsChain L.SplitResidualStep)
    {a b c : VertexSplitState V}
    (hab : L.SplitAugmentedArc l a b)
    (hac : L.SplitAugmentedArc l a c) :
    b = c := by
  classical
  rcases hab with hcurAB | hchainAB <;>
    rcases hac with hcurAC | hchainAC
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.left_unique
        (L := L) hcurAB.1 hcurAC.1
  · rcases
      PartialThreeVertexLinkage.SplitCurrentArc.chain_left_conflict
        (L := L) hhead hchain hcurAB.1 hchainAC.1
        with hEq | hConflict
    · exact hEq
    · rcases hConflict with hrev | hcurRev
      · exact False.elim (hcurAB.2 hrev)
      · exact False.elim (hchainAC.2 hcurRev)
  · rcases
      PartialThreeVertexLinkage.SplitCurrentArc.chain_left_conflict
        (L := L) hhead hchain hcurAC.1 hchainAB.1
        with hEq | hConflict
    · exact hEq.symm
    · rcases hConflict with hrev | hcurRev
      · exact False.elim (hcurAC.2 hrev)
      · exact False.elim (hchainAB.2 hcurRev)
  · exact List.Consecutive.snd_unique_of_fst hnodup hchainAB.1 hchainAC.1

theorem PartialThreeVertexLinkage.SplitCurrentArc.chain_right_conflict
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep)
    {a b c : VertexSplitState V}
    (hcur : L.SplitCurrentArc a c)
    (hstep : List.Consecutive l b c) :
    a = b ∨ List.Consecutive l c a ∨ L.SplitCurrentArc c b := by
  classical
  rcases hstep with ⟨idx, hidxNext, hstateB, hstateC⟩
  have hres_raw := (List.isChain_iff_getElem.mp hchain) idx hidxNext
  cases c with
  | out v =>
      cases a with
      | out u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
      | inn u =>
          have huv : u = v := hcur.1
          have huUsed : u ∈ L.usedVertices := hcur.2
          cases b with
          | out w =>
              have hbad :
                  L.SplitResidualStep (VertexSplitState.out w)
                    (VertexSplitState.out v) := by
                simpa [hstateB, hstateC] using hres_raw
              simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
          | inn w =>
              have hres :
                  L.SplitResidualStep (VertexSplitState.inn w)
                    (VertexSplitState.out v) := by
                simpa [hstateB, hstateC] using hres_raw
              have hcases :
                  (w = v ∧ w ∉ L.usedVertices) ∨
                    L.ForwardPathDart v w := by
                simpa [PartialThreeVertexLinkage.SplitResidualStep] using hres
              rcases hcases with hcap | hdart
              · have hvUsed : v ∈ L.usedVertices := by
                  simpa [huv] using huUsed
                have hvUnused : v ∉ L.usedVertices := by
                  simpa [hcap.1] using hcap.2
                exact False.elim (hvUnused hvUsed)
              · exact Or.inr (Or.inr (by
                  simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hdart))
  | inn v =>
      cases a with
      | inn u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
      | out u =>
          have hcurDart : L.ForwardPathDart u v := hcur
          cases b with
          | inn w =>
              have hbad :
                  L.SplitResidualStep (VertexSplitState.inn w)
                    (VertexSplitState.inn v) := by
                simpa [hstateB, hstateC] using hres_raw
              simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
          | out w =>
              have hres :
                  L.SplitResidualStep (VertexSplitState.out w)
                    (VertexSplitState.inn v) := by
                simpa [hstateB, hstateC] using hres_raw
              have hcases :
                  (w = v ∧ w ∈ L.usedVertices) ∨ G.Adj w v := by
                simpa [PartialThreeVertexLinkage.SplitResidualStep] using hres
              rcases hcases with hcap | hadj
              · have hvUsed : v ∈ L.usedVertices := by
                  simpa [hcap.1] using hcap.2
                exact Or.inr (Or.inr (by
                  simpa [PartialThreeVertexLinkage.SplitCurrentArc,
                    hcap.1.symm] using hvUsed))
              · by_cases huw : u = w
                · exact Or.inl (by simp [huw])
                · have hidxNextNext : idx + 2 < l.length := by
                    by_contra hnot
                    have hlast_index : l.length - 1 = idx + 1 := by
                      omega
                    have hgetLast :
                        l.getLast? = some (l[idx + 1]'hidxNext) := by
                      rw [List.getLast?_eq_getElem?]
                      rw [hlast_index]
                      exact List.getElem?_eq_getElem hidxNext
                    rw [hgetLast] at hlast
                    injection hlast with hlastState
                    have hbad :
                        VertexSplitState.inn v =
                          VertexSplitState.out sink := by
                      exact hstateC.symm.trans hlastState
                    cases hbad
                  have hnextStepRaw :=
                    (List.isChain_iff_getElem.mp hchain) (idx + 1)
                      hidxNextNext
                  cases hnextState : l[idx + 2]'hidxNextNext with
                  | inn t =>
                      have hbad :
                          L.SplitResidualStep (VertexSplitState.inn v)
                            (VertexSplitState.inn t) := by
                        simpa [hstateC, hnextState] using hnextStepRaw
                      simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
                  | out t =>
                      have hnextStep :
                          L.SplitResidualStep (VertexSplitState.inn v)
                            (VertexSplitState.out t) := by
                        simpa [hstateC, hnextState] using hnextStepRaw
                      have hnextCases :
                          (v = t ∧ v ∉ L.usedVertices) ∨
                            L.ForwardPathDart t v := by
                        simpa [PartialThreeVertexLinkage.SplitResidualStep]
                          using hnextStep
                      have ht_eq_u : t = u := by
                        rcases hnextCases with hcapNext | hdartNext
                        · exact False.elim
                            (hcapNext.2 (by
                              simpa [hcapNext.1] using
                                hcurDart.snd_mem_usedVertices))
                        · exact
                            PartialThreeVertexLinkage.ForwardPathDart.fst_unique_of_snd
                              (L := L) hdartNext hcurDart
                      have hcstate :
                          l[idx + 1]'(lt_trans
                            (Nat.lt_succ_self (idx + 1)) hidxNextNext) =
                            VertexSplitState.inn v := by
                        simpa using hstateC
                      have hastate :
                          l[(idx + 1) + 1]'hidxNextNext =
                            VertexSplitState.out u := by
                        simpa [Nat.add_assoc, ht_eq_u] using hnextState
                      exact Or.inr (Or.inl
                        ⟨idx + 1, hidxNextNext, hcstate, hastate⟩)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.right_unique
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep)
    {a b c : VertexSplitState V}
    (hac : L.SplitAugmentedArc l a c)
    (hbc : L.SplitAugmentedArc l b c) :
    a = b := by
  classical
  rcases hac with hcurAC | hchainAC <;>
    rcases hbc with hcurBC | hchainBC
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.right_unique
        (L := L) hcurAC.1 hcurBC.1
  · rcases
      PartialThreeVertexLinkage.SplitCurrentArc.chain_right_conflict
        (L := L) hlast hchain hcurAC.1 hchainBC.1
        with hEq | hConflict
    · exact hEq
    · rcases hConflict with hrev | hcurRev
      · exact False.elim (hcurAC.2 hrev)
      · exact False.elim (hchainBC.2 hcurRev)
  · rcases
      PartialThreeVertexLinkage.SplitCurrentArc.chain_right_conflict
        (L := L) hlast hchain hcurBC.1 hchainAC.1
        with hEq | hConflict
    · exact hEq.symm
    · rcases hConflict with hrev | hcurRev
      · exact False.elim (hcurBC.2 hrev)
      · exact False.elim (hchainAC.2 hcurRev)
  · exact List.Consecutive.fst_unique_of_snd hnodup hchainAC.1 hchainBC.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_terminal_reachable_of_no_incoming
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep)
    {source : VertexSplitState V}
    (hsource :
      forall a : VertexSplitState V, Not (L.SplitAugmentedArc l a source)) :
    Exists fun terminal : VertexSplitState V =>
      Relation.ReflTransGen (L.SplitAugmentedArc l) source terminal ∧
        Not (Exists fun u : VertexSplitState V =>
          L.SplitAugmentedArc l terminal u) := by
  classical
  exact
    relation_exists_terminal_reachable_of_finite_right_unique
      (r := L.SplitAugmentedArc l) (source := source)
      (fun hab hbc =>
        PartialThreeVertexLinkage.SplitAugmentedArc.right_unique
          (L := L) hnodup hlast hchain hab hbc)
      hsource

theorem PartialThreeVertexLinkage.exists_path_of_splitAugmentedChain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l m : List (VertexSplitState V)}
    {a b : VertexSplitState V}
    (hm_ne : m ≠ [])
    (hresChain : l.IsChain L.SplitResidualStep)
    (haugChain : m.IsChain (L.SplitAugmentedArc l))
    (hhead : m.head? = some a)
    (hlast : m.getLast? = some b) :
    Exists fun p : G.Walk a.vertex b.vertex =>
      p.IsPath ∧
        forall x : V, x ∈ p.support ->
          Exists fun s : VertexSplitState V => s ∈ m ∧ s.vertex = x := by
  classical
  let mv : List V := m.map VertexSplitState.vertex
  have hmv_ne : mv ≠ [] := by
    cases m with
    | nil => exact False.elim (hm_ne rfl)
    | cons s ss => simp [mv]
  have hchain_v :
      mv.IsChain (fun u v : V => u = v ∨ G.Adj u v) := by
    change (m.map VertexSplitState.vertex).IsChain
      (fun u v : V => u = v ∨ G.Adj u v)
    rw [List.isChain_map]
    exact haugChain.imp (fun {s t} h =>
      PartialThreeVertexLinkage.SplitAugmentedArc.forget_eq_or_adj
        (L := L) hresChain h)
  have hhead_v : mv.head? = some a.vertex := by
    simp [mv, List.head?_map, hhead]
  have hlast_v : mv.getLast? = some b.vertex := by
    simp [mv, List.getLast?_map, hlast]
  obtain ⟨p, hp, hsupport⟩ :=
    exists_path_of_isChain_eq_or_adj
      (G := G) hmv_ne hchain_v hhead_v hlast_v
  exact ⟨p, hp, by
    intro x hx
    have hxmv : x ∈ mv := hsupport x hx
    rcases List.mem_map.mp hxmv with ⟨s, hs, hsx⟩
    exact ⟨s, hs, hsx⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_terminal_chain_path_of_no_incoming
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep)
    {source : VertexSplitState V}
    (hsource :
      forall a : VertexSplitState V, Not (L.SplitAugmentedArc l a source)) :
    Exists fun terminal : VertexSplitState V =>
      Not (Exists fun u : VertexSplitState V =>
        L.SplitAugmentedArc l terminal u) ∧
        Exists fun m : List (VertexSplitState V) =>
          m ≠ [] ∧
            m.head? = some source ∧
              m.getLast? = some terminal ∧
                m.IsChain (L.SplitAugmentedArc l) ∧
                  Exists fun p : G.Walk source.vertex terminal.vertex =>
                    p.IsPath ∧
                      forall x : V, x ∈ p.support ->
                        Exists fun s : VertexSplitState V =>
                          s ∈ m ∧ s.vertex = x := by
  classical
  obtain ⟨terminal, hreach, hterminal⟩ :=
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_terminal_reachable_of_no_incoming
      (L := L) hnodup hlast hchain hsource
  obtain ⟨m, hm_ne, hhead, hlast_m, hchain_m⟩ :=
    reflTransGen_exists_isChain_list hreach
  obtain ⟨p, hp, hsupport⟩ :=
    PartialThreeVertexLinkage.exists_path_of_splitAugmentedChain
      (L := L) hm_ne hchain hchain_m hhead hlast_m
  exact
    ⟨terminal, hterminal, m, hm_ne, hhead, hlast_m, hchain_m,
      p, hp, hsupport⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_head_inn_of_unused
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source : V}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hsource_unused : source ∉ L.usedVertices) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l a (VertexSplitState.inn source)) := by
  classical
  intro a h
  rcases h with hcur | hchain
  · cases a with
    | inn u =>
        simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
    | out u =>
        exact hsource_unused hcur.1.snd_mem_usedVertices
  · exact List.not_consecutive_to_head_of_nodup hnodup hhead hchain.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_head_inn
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source sink : V}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l a (VertexSplitState.inn source)) := by
  classical
  intro a h
  rcases h with hcur | hchainIn
  · have hne : VertexSplitState.inn source ≠ VertexSplitState.out sink := by
      intro hbad
      cases hbad
    obtain ⟨c, hfirst⟩ :=
      List.exists_consecutive_from_head_of_head_ne_last hhead hlast hne
    have hres : L.SplitResidualStep (VertexSplitState.inn source) c :=
      List.Consecutive.rel_of_isChain hchain hfirst
    have hca : c = a := by
      cases a with
      | inn u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
      | out u =>
          have hcurDart : L.ForwardPathDart u source := by
            simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcur.1
          cases c with
          | inn w =>
              simp [PartialThreeVertexLinkage.SplitResidualStep] at hres
          | out w =>
              have hcases :
                  (source = w ∧ source ∉ L.usedVertices) ∨
                    L.ForwardPathDart w source := by
                simpa [PartialThreeVertexLinkage.SplitResidualStep] using hres
              rcases hcases with hcap | hdart
              · exact False.elim (hcap.2 hcurDart.snd_mem_usedVertices)
              · have hwu : w = u :=
                  PartialThreeVertexLinkage.ForwardPathDart.fst_unique_of_snd
                    (L := L) hdart hcurDart
                simp [hwu]
    exact hcur.2 (by simpa [hca] using hfirst)
  · exact List.not_consecutive_to_head_of_nodup hnodup hhead hchainIn.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_outgoing_last_out_of_unused
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hsink_unused : sink ∉ L.usedVertices) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l (VertexSplitState.out sink) a) := by
  classical
  intro a h
  rcases h with hcur | hchain
  · cases a with
    | inn v =>
        exact hsink_unused hcur.1.fst_mem_usedVertices
    | out v =>
        simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
  · exact List.not_consecutive_from_last_of_nodup hnodup hlast hchain.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_outgoing_last_out
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source sink : V}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l (VertexSplitState.out sink) a) := by
  classical
  intro a h
  rcases h with hcur | hchainOut
  · have hne : VertexSplitState.inn source ≠ VertexSplitState.out sink := by
      intro hbad
      cases hbad
    obtain ⟨c, hlastCon⟩ :=
      List.exists_consecutive_to_last_of_head_ne_last hhead hlast hne
    have hres : L.SplitResidualStep c (VertexSplitState.out sink) :=
      List.Consecutive.rel_of_isChain hchain hlastCon
    have hca : c = a := by
      cases a with
      | out u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
      | inn u =>
          have hcurDart : L.ForwardPathDart sink u := by
            simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcur.1
          cases c with
          | out w =>
              simp [PartialThreeVertexLinkage.SplitResidualStep] at hres
          | inn w =>
              have hcases :
                  (w = sink ∧ w ∉ L.usedVertices) ∨
                    L.ForwardPathDart sink w := by
                simpa [PartialThreeVertexLinkage.SplitResidualStep] using hres
              rcases hcases with hcap | hdart
              · exact False.elim (hcap.2 (by
                  simpa [hcap.1] using hcurDart.fst_mem_usedVertices))
              · have hwu : w = u :=
                  PartialThreeVertexLinkage.ForwardPathDart.snd_unique_of_fst
                    (L := L) hdart hcurDart
                simp [hwu]
    exact hcur.2 (by simpa [hca] using hlastCon)
  · exact
      List.not_consecutive_from_last_of_nodup hnodup hlast hchainOut.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_head_inn_of_unused
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source sink : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hsource_unused : source ∉ L.usedVertices) :
    Exists fun a : VertexSplitState V =>
      L.SplitAugmentedArc l (VertexSplitState.inn source) a := by
  cases l with
  | nil =>
      simp at hhead
  | cons s rest =>
      cases rest with
      | nil =>
          simp at hhead hlast
          have hbad :
              VertexSplitState.inn source = VertexSplitState.out sink :=
            hhead.symm.trans hlast
          cases hbad
      | cons t ts =>
          have hs : s = VertexSplitState.inn source := by
            simpa using hhead
          have hcon :
              List.Consecutive (s :: t :: ts)
                (VertexSplitState.inn source) t := by
            refine ⟨0, by simp, ?_, by simp⟩
            simpa using hs
          have hnotCurrent :
              Not (L.SplitCurrentArc t (VertexSplitState.inn source)) := by
            intro hcur
            cases t with
            | inn u =>
                simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
            | out u =>
                exact hsource_unused hcur.snd_mem_usedVertices
          exact ⟨t, Or.inr ⟨hcon, hnotCurrent⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_incoming_last_out_of_unused
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source sink : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hsink_unused : sink ∉ L.usedVertices) :
    Exists fun a : VertexSplitState V =>
      L.SplitAugmentedArc l a (VertexSplitState.out sink) := by
  cases l with
  | nil =>
      simp at hhead
  | cons s rest =>
      cases rest with
      | nil =>
          simp at hhead hlast
          have hbad :
              VertexSplitState.inn source = VertexSplitState.out sink :=
            hhead.symm.trans hlast
          cases hbad
      | cons t ts =>
          let l' : List (VertexSplitState V) := s :: t :: ts
          let idx : Nat := l'.length - 2
          have hidxNext : idx + 1 < l'.length := by
            dsimp [idx, l']
            omega
          have hidx : idx < l'.length :=
            lt_trans (Nat.lt_succ_self idx) hidxNext
          have hlast_state :
              l'[idx + 1]'hidxNext = VertexSplitState.out sink := by
            have hgetLast :
                l'.getLast? = some (l'[idx + 1]'hidxNext) := by
              rw [List.getLast?_eq_getElem?]
              have hidxsucc : idx + 1 = l'.length - 1 := by
                dsimp [idx, l']
                omega
              simp [hidxsucc]
            have hlast' :
                l'.getLast? = some (VertexSplitState.out sink) := by
              simpa [l'] using hlast
            rw [hgetLast] at hlast'
            exact Option.some.inj hlast'
          have hcon :
              List.Consecutive l' (l'[idx]'hidx)
                (VertexSplitState.out sink) :=
            ⟨idx, hidxNext, rfl, hlast_state⟩
          have hnotCurrent :
              Not (L.SplitCurrentArc (VertexSplitState.out sink) (l'[idx]'hidx)) := by
            intro hcur
            cases hstate : l'[idx]'hidx with
            | inn u =>
                have hdart : L.ForwardPathDart sink u := by
                  simpa [PartialThreeVertexLinkage.SplitCurrentArc, hstate]
                    using hcur
                exact hsink_unused hdart.fst_mem_usedVertices
            | out u =>
                simp [PartialThreeVertexLinkage.SplitCurrentArc, hstate] at hcur
          exact ⟨l'[idx]'hidx, Or.inr ⟨by simpa [l'] using hcon, hnotCurrent⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_head_inn
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source sink : V}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hlast : l.getLast? = some (VertexSplitState.out sink)) :
    Exists fun a : VertexSplitState V =>
      L.SplitAugmentedArc l (VertexSplitState.inn source) a := by
  classical
  have hne : VertexSplitState.inn source ≠ VertexSplitState.out sink := by
    intro h
    cases h
  obtain ⟨c, hfirst⟩ :=
    List.exists_consecutive_from_head_of_head_ne_last hhead hlast hne
  by_cases hcurBack :
      L.SplitCurrentArc c (VertexSplitState.inn source)
  · have hsourceUsed : source ∈ L.usedVertices := by
      cases c with
      | inn u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurBack
      | out u =>
          have hdart : L.ForwardPathDart u source := by
            simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcurBack
          exact hdart.snd_mem_usedVertices
    have hcurOut :
        L.SplitCurrentArc (VertexSplitState.inn source)
          (VertexSplitState.out source) := by
      simp [PartialThreeVertexLinkage.SplitCurrentArc, hsourceUsed]
    have hnotRev :
        Not (List.Consecutive l (VertexSplitState.out source)
          (VertexSplitState.inn source)) :=
      List.not_consecutive_to_head_of_nodup hnodup hhead
    exact ⟨VertexSplitState.out source, Or.inl ⟨hcurOut, hnotRev⟩⟩
  · exact ⟨c, Or.inr ⟨hfirst, hcurBack⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_incoming_last_out
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source sink : V}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hlast : l.getLast? = some (VertexSplitState.out sink)) :
    Exists fun a : VertexSplitState V =>
      L.SplitAugmentedArc l a (VertexSplitState.out sink) := by
  classical
  have hne : VertexSplitState.inn source ≠ VertexSplitState.out sink := by
    intro h
    cases h
  obtain ⟨c, hlastCon⟩ :=
    List.exists_consecutive_to_last_of_head_ne_last hhead hlast hne
  by_cases hcurBack :
      L.SplitCurrentArc (VertexSplitState.out sink) c
  · have hsinkUsed : sink ∈ L.usedVertices := by
      cases c with
      | inn u =>
          have hdart : L.ForwardPathDart sink u := by
            simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcurBack
          exact hdart.fst_mem_usedVertices
      | out u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurBack
    have hcurIn :
        L.SplitCurrentArc (VertexSplitState.inn sink)
          (VertexSplitState.out sink) := by
      simp [PartialThreeVertexLinkage.SplitCurrentArc, hsinkUsed]
    have hnotRev :
        Not (List.Consecutive l (VertexSplitState.out sink)
          (VertexSplitState.inn sink)) :=
      List.not_consecutive_from_last_of_nodup hnodup hlast
    exact ⟨VertexSplitState.inn sink, Or.inl ⟨hcurIn, hnotRev⟩⟩
  · exact ⟨c, Or.inr ⟨hlastCon, hcurBack⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_no_chain_incoming
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} (k : Fin n)
    (hnoChain :
      forall a : VertexSplitState V,
        Not (List.Consecutive l a (VertexSplitState.inn (left (L.leftIndex k))))) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l a
        (VertexSplitState.inn (left (L.leftIndex k)))) := by
  intro a h
  rcases h with hcur | hchain
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.no_incoming_left
        (L := L) k a hcur.1
  · exact hnoChain a hchain.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_outgoing_right_of_no_chain_outgoing
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} (k : Fin n)
    (hnoChain :
      forall a : VertexSplitState V,
        Not (List.Consecutive l (VertexSplitState.out (right (L.rightIndex k))) a)) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l
        (VertexSplitState.out (right (L.rightIndex k))) a) := by
  intro a h
  rcases h with hcur | hchain
  · exact
      PartialThreeVertexLinkage.SplitCurrentArc.no_outgoing_right
        (L := L) k a hcur.1
  · exact hnoChain a hchain.1

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_residual_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3}
    (k : Fin n)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l a
        (VertexSplitState.inn (left (L.leftIndex k)))) := by
  exact
    PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_no_chain_incoming
      (L := L) (l := l) k
      (PartialThreeVertexLinkage.SplitResidualStep.no_chain_incoming_left
        (L := L) (l := l) k hlast hchain)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.no_outgoing_right_of_residual_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {iNew : Fin 3}
    (k : Fin n)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    forall a : VertexSplitState V,
      Not (L.SplitAugmentedArc l
        (VertexSplitState.out (right (L.rightIndex k))) a) := by
  exact
    PartialThreeVertexLinkage.SplitAugmentedArc.no_outgoing_right_of_no_chain_outgoing
      (L := L) (l := l) k
      (PartialThreeVertexLinkage.SplitResidualStep.no_chain_outgoing_right
        (L := L) (l := l) k hhead hchain)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_terminal_chain_path_from_old_left
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (k : Fin n) :
    Exists fun terminal : VertexSplitState V =>
      Not (Exists fun u : VertexSplitState V =>
        L.SplitAugmentedArc l terminal u) ∧
        Exists fun m : List (VertexSplitState V) =>
          m ≠ [] ∧
            m.head? = some (VertexSplitState.inn (left (L.leftIndex k))) ∧
              m.getLast? = some terminal ∧
                m.IsChain (L.SplitAugmentedArc l) ∧
                  Exists fun p : G.Walk (left (L.leftIndex k)) terminal.vertex =>
                    p.IsPath ∧
                      forall x : V, x ∈ p.support ->
                        Exists fun s : VertexSplitState V =>
                          s ∈ m ∧ s.vertex = x := by
  exact
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_terminal_chain_path_of_no_incoming
      (L := L) hnodup hlast hchain
      (PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_residual_chain
        (L := L) (l := l) k hlast hchain)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_left_of_residual_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3}
    (k : Fin n)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    Exists fun a : VertexSplitState V =>
      L.SplitAugmentedArc l
        (VertexSplitState.inn (left (L.leftIndex k))) a := by
  refine ⟨VertexSplitState.out (left (L.leftIndex k)), Or.inl ?_⟩
  constructor
  · simp [PartialThreeVertexLinkage.SplitCurrentArc,
      L.left_mem_usedVertices k]
  · exact
      PartialThreeVertexLinkage.SplitResidualStep.no_chain_incoming_left
        (L := L) (l := l) k hlast hchain
        (VertexSplitState.out (left (L.leftIndex k)))

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_incoming_right_of_residual_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {iNew : Fin 3}
    (k : Fin n)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    Exists fun a : VertexSplitState V =>
      L.SplitAugmentedArc l a
        (VertexSplitState.out (right (L.rightIndex k))) := by
  refine ⟨VertexSplitState.inn (right (L.rightIndex k)), Or.inl ?_⟩
  constructor
  · simp [PartialThreeVertexLinkage.SplitCurrentArc,
      L.right_mem_usedVertices k]
  · exact
      PartialThreeVertexLinkage.SplitResidualStep.no_chain_outgoing_right
        (L := L) (l := l) k hhead hchain
        (VertexSplitState.inn (right (L.rightIndex k)))

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_inn_of_incoming
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink v : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hin :
      Exists fun a : VertexSplitState V =>
        L.SplitAugmentedArc l a (VertexSplitState.inn v)) :
    Exists fun u : VertexSplitState V =>
      L.SplitAugmentedArc l (VertexSplitState.inn v) u := by
  classical
  have hnotLast :
      VertexSplitState.inn v ≠ VertexSplitState.out sink := by
    intro h
    cases h
  rcases hin with ⟨a, ha⟩
  rcases ha with hcurIn | hchainIn
  · have hvUsed : v ∈ L.usedVertices := by
      cases a with
      | inn u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurIn
      | out u =>
          have hdart : L.ForwardPathDart u v := by
            simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcurIn.1
          exact hdart.snd_mem_usedVertices
    have hcurOut :
        L.SplitCurrentArc (VertexSplitState.inn v)
          (VertexSplitState.out v) := by
      simp [PartialThreeVertexLinkage.SplitCurrentArc, hvUsed]
    by_cases hrevCap :
        List.Consecutive l (VertexSplitState.out v)
          (VertexSplitState.inn v)
    · have hmem :
          VertexSplitState.inn v ∈ l := by
        rcases hrevCap with ⟨idx, hnext, _ha, hb⟩
        simpa [hb] using List.getElem_mem hnext
      obtain ⟨c, hnext⟩ :=
        List.exists_consecutive_from_of_mem_of_getLast_ne
          hmem hlast hnotLast
      by_cases hcurBack :
          L.SplitCurrentArc c (VertexSplitState.inn v)
      · have hac : a = c :=
          PartialThreeVertexLinkage.SplitCurrentArc.right_unique
            (L := L) hcurIn.1 hcurBack
        exact False.elim (hcurIn.2 (by simpa [hac] using hnext))
      · exact ⟨c, Or.inr ⟨hnext, hcurBack⟩⟩
    · exact ⟨VertexSplitState.out v, Or.inl ⟨hcurOut, hrevCap⟩⟩
  · have hmem :
        VertexSplitState.inn v ∈ l := by
      rcases hchainIn.1 with ⟨idx, hnext, _ha, hb⟩
      simpa [hb] using List.getElem_mem hnext
    obtain ⟨c, hnext⟩ :=
      List.exists_consecutive_from_of_mem_of_getLast_ne
        hmem hlast hnotLast
    by_cases hcurBack :
        L.SplitCurrentArc c (VertexSplitState.inn v)
    · have hvUsed : v ∈ L.usedVertices := by
        cases c with
        | inn u =>
            simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurBack
        | out u =>
            have hdart : L.ForwardPathDart u v := by
              simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcurBack
            exact hdart.snd_mem_usedVertices
      have hcurOut :
          L.SplitCurrentArc (VertexSplitState.inn v)
            (VertexSplitState.out v) := by
        simp [PartialThreeVertexLinkage.SplitCurrentArc, hvUsed]
      by_cases hrevCap :
          List.Consecutive l (VertexSplitState.out v)
            (VertexSplitState.inn v)
      · have ha_eq :
            a = VertexSplitState.out v :=
          List.Consecutive.fst_unique_of_snd hnodup hchainIn.1 hrevCap
        exact False.elim (hchainIn.2 (by simpa [ha_eq] using hcurOut))
      · exact ⟨VertexSplitState.out v, Or.inl ⟨hcurOut, hrevCap⟩⟩
    · exact ⟨c, Or.inr ⟨hnext, hcurBack⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_out_of_incoming_of_not_right
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink v : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hnot_sink : v ≠ sink)
    (hnot_right : forall k : Fin n, v ≠ right (L.rightIndex k))
    (hin :
      Exists fun a : VertexSplitState V =>
        L.SplitAugmentedArc l a (VertexSplitState.out v)) :
    Exists fun u : VertexSplitState V =>
      L.SplitAugmentedArc l (VertexSplitState.out v) u := by
  classical
  have hnotLast :
      VertexSplitState.out v ≠ VertexSplitState.out sink := by
    intro h
    injection h with hvs
    exact hnot_sink hvs
  have hcurrent_out_of_used :
      v ∈ L.usedVertices ->
        Exists fun w : V =>
          L.SplitCurrentArc (VertexSplitState.out v)
            (VertexSplitState.inn w) := by
    intro hvUsed
    rcases hvUsed with ⟨k, hvk⟩
    obtain ⟨w, hdart⟩ :=
      L.exists_forwardPathDart_from_of_mem_path_not_right
        (k := k) hvk (hnot_right k)
    exact ⟨w, by
      simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hdart⟩
  rcases hin with ⟨a, ha⟩
  rcases ha with hcurIn | hchainIn
  · have hvUsed : v ∈ L.usedVertices := by
      cases a with
      | inn u =>
          have hcap :
              u = v ∧ u ∈ L.usedVertices := by
            simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcurIn.1
          simpa [hcap.1] using hcap.2
      | out u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurIn
    obtain ⟨w, hcurOut⟩ := hcurrent_out_of_used hvUsed
    by_cases hrev :
        List.Consecutive l (VertexSplitState.inn w)
          (VertexSplitState.out v)
    · have hmem :
          VertexSplitState.out v ∈ l := by
        rcases hrev with ⟨idx, hnext, _ha, hb⟩
        simpa [hb] using List.getElem_mem hnext
      obtain ⟨c, hnext⟩ :=
        List.exists_consecutive_from_of_mem_of_getLast_ne
          hmem hlast hnotLast
      by_cases hcurBack :
          L.SplitCurrentArc c (VertexSplitState.out v)
      · have hac : a = c :=
          PartialThreeVertexLinkage.SplitCurrentArc.right_unique
            (L := L) hcurIn.1 hcurBack
        exact False.elim (hcurIn.2 (by simpa [hac] using hnext))
      · exact ⟨c, Or.inr ⟨hnext, hcurBack⟩⟩
    · exact ⟨VertexSplitState.inn w, Or.inl ⟨hcurOut, hrev⟩⟩
  · have hmem :
        VertexSplitState.out v ∈ l := by
      rcases hchainIn.1 with ⟨idx, hnext, _ha, hb⟩
      simpa [hb] using List.getElem_mem hnext
    obtain ⟨c, hnext⟩ :=
      List.exists_consecutive_from_of_mem_of_getLast_ne
        hmem hlast hnotLast
    by_cases hcurBack :
        L.SplitCurrentArc c (VertexSplitState.out v)
    · have hvUsed : v ∈ L.usedVertices := by
        cases c with
        | inn u =>
            have hcap :
                u = v ∧ u ∈ L.usedVertices := by
              simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcurBack
            simpa [hcap.1] using hcap.2
        | out u =>
            simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcurBack
      obtain ⟨w, hcurOut⟩ := hcurrent_out_of_used hvUsed
      by_cases hrev :
          List.Consecutive l (VertexSplitState.inn w)
            (VertexSplitState.out v)
      · have ha_eq :
            a = VertexSplitState.inn w :=
          List.Consecutive.fst_unique_of_snd hnodup hchainIn.1 hrev
        exact False.elim (hchainIn.2 (by simpa [ha_eq] using hcurOut))
      · exact ⟨VertexSplitState.inn w, Or.inl ⟨hcurOut, hrev⟩⟩
    · exact ⟨c, Or.inr ⟨hnext, hcurBack⟩⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.terminal_eq_out_right_of_incoming
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    {terminal : VertexSplitState V}
    (hin :
      Exists fun a : VertexSplitState V =>
        L.SplitAugmentedArc l a terminal)
    (hterminal :
      Not (Exists fun u : VertexSplitState V =>
        L.SplitAugmentedArc l terminal u)) :
    terminal = VertexSplitState.out sink ∨
      Exists fun k : Fin n =>
        terminal =
          VertexSplitState.out (right (L.rightIndex k)) := by
  classical
  cases terminal with
  | inn v =>
      exact False.elim
        (hterminal
          (PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_inn_of_incoming
            (L := L) hnodup hlast hin))
  | out v =>
      by_cases hvs : v = sink
      · exact Or.inl (by simp [hvs])
      · by_cases hright :
          Exists fun k : Fin n => v = right (L.rightIndex k)
        · rcases hright with ⟨k, hk⟩
          exact Or.inr ⟨k, by simp [hk]⟩
        · have hnot_right :
            forall k : Fin n, v ≠ right (L.rightIndex k) := by
            intro k hk
            exact hright ⟨k, hk⟩
          exact False.elim
            (hterminal
              (PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_out_of_incoming_of_not_right
                (L := L) hnodup hlast hvs hnot_right hin))

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_of_no_incoming
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {sink : V}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out sink))
    (hchain : l.IsChain L.SplitResidualStep)
    {source : VertexSplitState V}
    (hsource_no_in :
      forall a : VertexSplitState V, Not (L.SplitAugmentedArc l a source))
    (hsource_out :
      Exists fun u : VertexSplitState V => L.SplitAugmentedArc l source u) :
    Exists fun terminal : VertexSplitState V =>
      Not (Exists fun u : VertexSplitState V =>
        L.SplitAugmentedArc l terminal u) ∧
        (Exists fun a : VertexSplitState V =>
          L.SplitAugmentedArc l a terminal) ∧
          (terminal = VertexSplitState.out sink ∨
            Exists fun k : Fin n =>
              terminal =
                VertexSplitState.out (right (L.rightIndex k))) ∧
          Exists fun m : List (VertexSplitState V) =>
            m ≠ [] ∧
              m.head? = some source ∧
                m.getLast? = some terminal ∧
                  m.IsChain (L.SplitAugmentedArc l) ∧
                    Exists fun p : G.Walk source.vertex terminal.vertex =>
                      p.IsPath ∧
                        forall x : V, x ∈ p.support ->
                          Exists fun s : VertexSplitState V =>
                            s ∈ m ∧ s.vertex = x := by
  classical
  obtain ⟨terminal, hterminal, m, hm_ne, hhead_m, hlast_m, hchain_m,
    p, hp, hsupport⟩ :=
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_terminal_chain_path_of_no_incoming
      (L := L) hnodup hlast hchain hsource_no_in
  have hin_terminal :
      Exists fun a : VertexSplitState V =>
        L.SplitAugmentedArc l a terminal :=
    exists_relation_incoming_terminal_of_chain_from_nonterminal_source
      hhead_m hlast_m hchain_m hsource_out hterminal
  have hclassified :
      terminal = VertexSplitState.out sink ∨
        Exists fun k : Fin n =>
          terminal =
            VertexSplitState.out (right (L.rightIndex k)) :=
    PartialThreeVertexLinkage.SplitAugmentedArc.terminal_eq_out_right_of_incoming
      (L := L) hnodup hlast hin_terminal hterminal
  exact
    ⟨terminal, hterminal, hin_terminal, hclassified, m, hm_ne, hhead_m,
      hlast_m, hchain_m, p, hp, hsupport⟩

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_from_old_left
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {jNew : Fin 3}
    (hnodup : l.Nodup)
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    (k : Fin n) :
    Exists fun terminal : VertexSplitState V =>
      Not (Exists fun u : VertexSplitState V =>
        L.SplitAugmentedArc l terminal u) ∧
        (Exists fun a : VertexSplitState V =>
          L.SplitAugmentedArc l a terminal) ∧
          (terminal = VertexSplitState.out (right jNew) ∨
            Exists fun k : Fin n =>
              terminal =
                VertexSplitState.out (right (L.rightIndex k))) ∧
          Exists fun m : List (VertexSplitState V) =>
            m ≠ [] ∧
              m.head? =
                some (VertexSplitState.inn (left (L.leftIndex k))) ∧
                m.getLast? = some terminal ∧
                  m.IsChain (L.SplitAugmentedArc l) ∧
                    Exists fun p :
                      G.Walk (left (L.leftIndex k)) terminal.vertex =>
                      p.IsPath ∧
                        forall x : V, x ∈ p.support ->
                          Exists fun s : VertexSplitState V =>
                            s ∈ m ∧ s.vertex = x := by
  exact
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_of_no_incoming
      (L := L) hnodup hlast hchain
      (PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_residual_chain
        (L := L) (l := l) k hlast hchain)
      (PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_left_of_residual_chain
        (L := L) (l := l) k hlast hchain)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_from_new_left
    [Fintype V] [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {iNew jNew : Fin 3}
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep) :
    Exists fun terminal : VertexSplitState V =>
      Not (Exists fun u : VertexSplitState V =>
        L.SplitAugmentedArc l terminal u) ∧
        (Exists fun a : VertexSplitState V =>
          L.SplitAugmentedArc l a terminal) ∧
          (terminal = VertexSplitState.out (right jNew) ∨
            Exists fun k : Fin n =>
              terminal =
                VertexSplitState.out (right (L.rightIndex k))) ∧
          Exists fun m : List (VertexSplitState V) =>
            m ≠ [] ∧
              m.head? = some (VertexSplitState.inn (left iNew)) ∧
                m.getLast? = some terminal ∧
                  m.IsChain (L.SplitAugmentedArc l) ∧
                    Exists fun p : G.Walk (left iNew) terminal.vertex =>
                      p.IsPath ∧
                        forall x : V, x ∈ p.support ->
                          Exists fun s : VertexSplitState V =>
                            s ∈ m ∧ s.vertex = x := by
  exact
    PartialThreeVertexLinkage.SplitAugmentedArc.exists_classified_terminal_chain_path_of_no_incoming
      (L := L) hnodup hlast hchain
      (PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_head_inn
        (L := L) (l := l) hnodup hhead hlast hchain)
      (PartialThreeVertexLinkage.SplitAugmentedArc.exists_outgoing_head_inn
        (L := L) (l := l) hnodup hhead hlast)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.terminals_ne_from_new_and_old_left_one
    [DecidableEq V]
    {left right : Fin 3 -> V}
    (hleft : Function.Injective left)
    {L : PartialThreeVertexLinkage G left right 1}
    {l : List (VertexSplitState V)} {iNew jNew : Fin 3}
    (hiNew : iNew ∉ Set.range L.leftIndex)
    (hnodup : l.Nodup)
    (hhead : l.head? = some (VertexSplitState.inn (left iNew)))
    (hlast : l.getLast? = some (VertexSplitState.out (right jNew)))
    (hchain : l.IsChain L.SplitResidualStep)
    {terminalNew terminalOld : VertexSplitState V}
    {mNew mOld : List (VertexSplitState V)}
    (hmNew_ne : mNew ≠ [])
    (hheadNew : mNew.head? = some (VertexSplitState.inn (left iNew)))
    (hlastNew : mNew.getLast? = some terminalNew)
    (hchainNew : mNew.IsChain (L.SplitAugmentedArc l))
    (hmOld_ne : mOld ≠ [])
    (hheadOld :
      mOld.head? = some (VertexSplitState.inn (left (L.leftIndex 0))))
    (hlastOld : mOld.getLast? = some terminalOld)
    (hchainOld : mOld.IsChain (L.SplitAugmentedArc l)) :
    terminalNew ≠ terminalOld := by
  intro hterm
  have hsourceEq :
      VertexSplitState.inn (left iNew) =
        VertexSplitState.inn (left (L.leftIndex 0)) := by
    exact
      relation_sources_eq_of_same_terminal_chains_of_left_unique
        (r := L.SplitAugmentedArc l)
        (fun {_a _b _c} hac hbc =>
          PartialThreeVertexLinkage.SplitAugmentedArc.right_unique
            (L := L) (l := l) hnodup hlast hchain hac hbc)
        (PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_head_inn
          (L := L) (l := l) hnodup hhead hlast hchain)
        (PartialThreeVertexLinkage.SplitAugmentedArc.no_incoming_left_of_residual_chain
          (L := L) (l := l) 0 hlast hchain)
        hmNew_ne hheadNew hlastNew hchainNew
        hmOld_ne hheadOld (by simpa [hterm] using hlastOld) hchainOld
  injection hsourceEq with hleftEq
  have hi_eq : iNew = L.leftIndex 0 := hleft hleftEq
  exact hiNew ⟨0, hi_eq.symm⟩

theorem reflTransGen_of_isChain_head?_mem
    {α : Type u} {r : α -> α -> Prop}
    {m : List α} {source s : α}
    (hhead : m.head? = some source)
    (hchain : m.IsChain r)
    (hs : s ∈ m) :
    Relation.ReflTransGen r source s := by
  classical
  cases m with
  | nil =>
      simp at hs
  | cons a rest =>
      have ha : a = source := by simpa using hhead
      subst a
      have hs_cases : s = source ∨ s ∈ rest := by
        simpa using hs
      rcases hs_cases with hs_eq | hs_tail
      · simpa [hs_eq] using
          (Relation.ReflTransGen.refl :
            Relation.ReflTransGen r source source)
      · exact
          List.IsChain.cons_induction
            (r := r)
            (p := fun t => Relation.ReflTransGen r source t)
            rest hchain
            (fun {_x _y} hxy hx => hx.tail hxy)
            Relation.ReflTransGen.refl s hs_tail

theorem PartialThreeVertexLinkage.SplitAugmentedArc.inn_out_vertex_eq
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)}
    (hchain : l.IsChain L.SplitResidualStep)
    {u v : V}
    (h :
      L.SplitAugmentedArc l (VertexSplitState.inn u)
        (VertexSplitState.out v)) :
    u = v := by
  classical
  rcases h with hcur | hres
  · have hcap : u = v ∧ u ∈ L.usedVertices := by
      simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hcur.1
    exact hcap.1
  · have hstep :
        L.SplitResidualStep (VertexSplitState.inn u)
          (VertexSplitState.out v) :=
      List.Consecutive.rel_of_isChain hchain hres.1
    have hcases :
        (u = v ∧ u ∉ L.usedVertices) ∨ L.ForwardPathDart v u := by
      simpa [PartialThreeVertexLinkage.SplitResidualStep] using hstep
    rcases hcases with hcap | hdart
    · exact hcap.1
    · exact False.elim
        (hres.2 (by
          simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hdart))

theorem PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_mem_out_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l m : List (VertexSplitState V)}
    {source x : V}
    (hresChain : l.IsChain L.SplitResidualStep)
    (hhead : m.head? = some (VertexSplitState.inn source))
    (haugChain : m.IsChain (L.SplitAugmentedArc l))
    (hout : VertexSplitState.out x ∈ m) :
    VertexSplitState.inn x ∈ m := by
  classical
  obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hout
  by_cases hidx0 : idx = 0
  · subst idx
    have hget0 : m[0]? = some (m[0]'hidx) :=
      List.getElem?_eq_getElem hidx
    rw [List.head?_eq_getElem?, hget0] at hhead
    injection hhead with hbad
    have hstate : VertexSplitState.out x = VertexSplitState.inn source :=
      hget.symm.trans hbad
    cases hstate
  · let pred : Nat := idx - 1
    have hpredNext : pred + 1 < m.length := by
      dsimp [pred]
      omega
    have hpred : pred < m.length :=
      lt_trans (Nat.lt_succ_self pred) hpredNext
    have hpred_succ : pred + 1 = idx := by
      dsimp [pred]
      omega
    have hstep :=
      (List.isChain_iff_getElem.mp haugChain) pred hpredNext
    cases hprev : m[pred]'hpred with
    | inn u =>
        have haug :
            L.SplitAugmentedArc l (VertexSplitState.inn u)
              (VertexSplitState.out x) := by
          simpa [hpred_succ, hprev, hget] using hstep
        have hux : u = x :=
          PartialThreeVertexLinkage.SplitAugmentedArc.inn_out_vertex_eq
            (L := L) hresChain haug
        have hstate :
            m[pred]'hpred = VertexSplitState.inn x := by
          simpa [hux] using hprev
        exact hstate ▸ List.getElem_mem hpred
    | out u =>
        have hbad :
            L.SplitAugmentedArc l (VertexSplitState.out u)
              (VertexSplitState.out x) := by
          simpa [hpred_succ, hprev, hget] using hstep
        rcases
          PartialThreeVertexLinkage.SplitAugmentedArc.state_cases
            (L := L) hresChain hbad
          with hio | hoi
        · rcases hio with ⟨a, b, ha, _hb⟩
          cases ha
        · rcases hoi with ⟨a, b, _ha, hb⟩
          cases hb

theorem PartialThreeVertexLinkage.SplitAugmentedArc.mem_out_of_mem_inn_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l m : List (VertexSplitState V)}
    {sink x : V}
    (hresChain : l.IsChain L.SplitResidualStep)
    (hlast : m.getLast? = some (VertexSplitState.out sink))
    (haugChain : m.IsChain (L.SplitAugmentedArc l))
    (hinn : VertexSplitState.inn x ∈ m) :
    VertexSplitState.out x ∈ m := by
  classical
  obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hinn
  by_cases hlast_idx : idx = m.length - 1
  · have hlast_get : m.getLast? = some (m[idx]'hidx) := by
      rw [List.getLast?_eq_getElem?]
      simp [hlast_idx]
    rw [hlast_get] at hlast
    injection hlast with hbad
    have hstate : VertexSplitState.inn x = VertexSplitState.out sink :=
      hget.symm.trans hbad
    cases hstate
  · have hnext : idx + 1 < m.length := by omega
    have hstep :=
      (List.isChain_iff_getElem.mp haugChain) idx hnext
    cases hnextState : m[idx + 1]'hnext with
    | inn u =>
        have hbad :
            L.SplitAugmentedArc l (VertexSplitState.inn x)
              (VertexSplitState.inn u) := by
          simpa [hget, hnextState] using hstep
        rcases
          PartialThreeVertexLinkage.SplitAugmentedArc.state_cases
            (L := L) hresChain hbad
          with hio | hoi
        · rcases hio with ⟨a, b, _ha, hb⟩
          cases hb
        · rcases hoi with ⟨a, b, ha, _hb⟩
          cases ha
    | out u =>
        have haug :
            L.SplitAugmentedArc l (VertexSplitState.inn x)
              (VertexSplitState.out u) := by
          simpa [hget, hnextState] using hstep
        have hxu : x = u :=
          PartialThreeVertexLinkage.SplitAugmentedArc.inn_out_vertex_eq
            (L := L) hresChain haug
        have hstate :
            m[idx + 1]'hnext = VertexSplitState.out x := by
          simpa [hxu] using hnextState
        exact hstate ▸ List.getElem_mem hnext

theorem PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_vertex_mem_chain
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l m : List (VertexSplitState V)}
    {source x : V}
    (hresChain : l.IsChain L.SplitResidualStep)
    (hhead : m.head? = some (VertexSplitState.inn source))
    (haugChain : m.IsChain (L.SplitAugmentedArc l))
    {s : VertexSplitState V}
    (hs : s ∈ m)
    (hsx : s.vertex = x) :
    VertexSplitState.inn x ∈ m := by
  cases s with
  | inn v =>
      have hvx : v = x := by simpa using hsx
      simpa [hvx] using hs
  | out v =>
      have hvx : v = x := by simpa using hsx
      exact
        PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_mem_out_chain
          (L := L) (l := l) (m := m) hresChain hhead haugChain
          (by simpa [hvx] using hs)

theorem PartialThreeVertexLinkage.SplitAugmentedArc.paths_disjoint_of_sources_ne
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l m₁ m₂ : List (VertexSplitState V)}
    {source₁ source₂ sinkResidual : V}
    (hnodup : l.Nodup)
    (hlast_l : l.getLast? = some (VertexSplitState.out sinkResidual))
    (hresChain : l.IsChain L.SplitResidualStep)
    (hno₁ :
      forall a : VertexSplitState V,
        Not (L.SplitAugmentedArc l a (VertexSplitState.inn source₁)))
    (hno₂ :
      forall a : VertexSplitState V,
        Not (L.SplitAugmentedArc l a (VertexSplitState.inn source₂)))
    (hsource_ne : VertexSplitState.inn source₁ ≠ VertexSplitState.inn source₂)
    (hhead₁ : m₁.head? = some (VertexSplitState.inn source₁))
    (hchain₁ : m₁.IsChain (L.SplitAugmentedArc l))
    (hhead₂ : m₂.head? = some (VertexSplitState.inn source₂))
    (hchain₂ : m₂.IsChain (L.SplitAugmentedArc l))
    {a b c d : V}
    {p₁ : G.Walk a b} {p₂ : G.Walk c d}
    (hsupport₁ :
      forall x : V, x ∈ p₁.support ->
        Exists fun s : VertexSplitState V => s ∈ m₁ ∧ s.vertex = x)
    (hsupport₂ :
      forall x : V, x ∈ p₂.support ->
        Exists fun s : VertexSplitState V => s ∈ m₂ ∧ s.vertex = x) :
    Disjoint {x : V | x ∈ p₁.support} {x : V | x ∈ p₂.support} := by
  classical
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  simp only [Set.mem_setOf_eq] at hx₁ hx₂
  obtain ⟨s₁, hs₁, hs₁x⟩ := hsupport₁ x hx₁
  obtain ⟨s₂, hs₂, hs₂x⟩ := hsupport₂ x hx₂
  have hinn₁ : VertexSplitState.inn x ∈ m₁ :=
    PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_vertex_mem_chain
      (L := L) (l := l) (m := m₁) hresChain hhead₁ hchain₁
      hs₁ hs₁x
  have hinn₂ : VertexSplitState.inn x ∈ m₂ :=
    PartialThreeVertexLinkage.SplitAugmentedArc.mem_inn_of_vertex_mem_chain
      (L := L) (l := l) (m := m₂) hresChain hhead₂ hchain₂
      hs₂ hs₂x
  have hreach₁ :
      Relation.ReflTransGen (L.SplitAugmentedArc l)
        (VertexSplitState.inn source₁) (VertexSplitState.inn x) :=
    reflTransGen_of_isChain_head?_mem hhead₁ hchain₁ hinn₁
  have hreach₂ :
      Relation.ReflTransGen (L.SplitAugmentedArc l)
        (VertexSplitState.inn source₂) (VertexSplitState.inn x) :=
    reflTransGen_of_isChain_head?_mem hhead₂ hchain₂ hinn₂
  have hsource_eq :
      VertexSplitState.inn source₁ = VertexSplitState.inn source₂ :=
    relation_sources_eq_of_same_terminal_of_left_unique
      (r := L.SplitAugmentedArc l)
      (fun {_a _b _c} hac hbc =>
        PartialThreeVertexLinkage.SplitAugmentedArc.right_unique
          (L := L) (l := l) hnodup hlast_l hresChain hac hbc)
      hno₁ hno₂ hreach₁ hreach₂
  exact hsource_ne hsource_eq


end Schematic.Math.GraphTheory
