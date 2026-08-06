import Schematic.Math.GraphTheory.Minors.Rerouting.ResidualRouting.SplitStates

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/--
The directed arcs currently occupied by a partial linkage in the split-vertex
state graph.  A used vertex contributes its capacity arc `inn v -> out v`, and
each oriented dart of a current linkage path contributes `out u -> inn v`.
-/
def PartialThreeVertexLinkage.SplitCurrentArc
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n) :
    VertexSplitState V -> VertexSplitState V -> Prop
  | .inn u, .out v => u = v ∧ u ∈ L.usedVertices
  | .out u, .inn v => L.ForwardPathDart u v
  | _, _ => False

theorem PartialThreeVertexLinkage.SplitResidualStep.state_cases
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b : VertexSplitState V}
    (h : L.SplitResidualStep a b) :
    (Exists fun u : V => Exists fun v : V =>
      a = VertexSplitState.inn u ∧ b = VertexSplitState.out v) ∨
      (Exists fun u : V => Exists fun v : V =>
        a = VertexSplitState.out u ∧ b = VertexSplitState.inn v) := by
  cases a with
  | inn u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep] at h
      | out v =>
          exact Or.inl ⟨u, v, rfl, rfl⟩
  | out u =>
      cases b with
      | inn v =>
          exact Or.inr ⟨u, v, rfl, rfl⟩
      | out v =>
          simp [PartialThreeVertexLinkage.SplitResidualStep] at h

theorem PartialThreeVertexLinkage.SplitCurrentArc.state_cases
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b : VertexSplitState V}
    (h : L.SplitCurrentArc a b) :
    (Exists fun u : V => Exists fun v : V =>
      a = VertexSplitState.inn u ∧ b = VertexSplitState.out v) ∨
      (Exists fun u : V => Exists fun v : V =>
        a = VertexSplitState.out u ∧ b = VertexSplitState.inn v) := by
  cases a with
  | inn u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at h
      | out v =>
          exact Or.inl ⟨u, v, rfl, rfl⟩
  | out u =>
      cases b with
      | inn v =>
          exact Or.inr ⟨u, v, rfl, rfl⟩
      | out v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at h

theorem PartialThreeVertexLinkage.SplitCurrentArc.not_self
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (s : VertexSplitState V) :
    Not (L.SplitCurrentArc s s) := by
  cases s <;> simp [PartialThreeVertexLinkage.SplitCurrentArc]

theorem PartialThreeVertexLinkage.SplitCurrentArc.forget_eq_or_adj
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b : VertexSplitState V}
    (h : L.SplitCurrentArc a b) :
    a.vertex = b.vertex ∨ G.Adj a.vertex b.vertex := by
  cases a with
  | inn u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at h
      | out v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at h
          exact Or.inl h.1
  | out u =>
      cases b with
      | inn v =>
          exact Or.inr h.adj
      | out v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at h

theorem PartialThreeVertexLinkage.SplitCurrentArc.no_incoming_left
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n) :
    forall a : VertexSplitState V,
      Not (L.SplitCurrentArc a (VertexSplitState.inn (left (L.leftIndex k)))) := by
  intro a h
  cases a with
  | inn u =>
      simp [PartialThreeVertexLinkage.SplitCurrentArc] at h
  | out u =>
      exact L.not_forwardPathDart_to_left k h

theorem PartialThreeVertexLinkage.SplitCurrentArc.no_outgoing_right
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    (L : PartialThreeVertexLinkage G left right n)
    (k : Fin n) :
    forall a : VertexSplitState V,
      Not (L.SplitCurrentArc (VertexSplitState.out (right (L.rightIndex k))) a) := by
  intro a h
  cases a with
  | inn v =>
      exact L.not_forwardPathDart_from_right k h
  | out v =>
      simp [PartialThreeVertexLinkage.SplitCurrentArc] at h

theorem PartialThreeVertexLinkage.SplitCurrentArc.left_unique
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b c : VertexSplitState V}
    (hab : L.SplitCurrentArc a b)
    (hac : L.SplitCurrentArc a c) :
    b = c := by
  cases a with
  | inn u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hab
      | out v =>
          cases c with
          | inn w =>
              simp [PartialThreeVertexLinkage.SplitCurrentArc] at hac
          | out w =>
              simp [PartialThreeVertexLinkage.SplitCurrentArc] at hab hac ⊢
              exact hab.1.symm.trans hac.1
  | out u =>
      cases b with
      | inn v =>
          cases c with
          | inn w =>
              have hvw : v = w :=
                PartialThreeVertexLinkage.ForwardPathDart.snd_unique_of_fst
                  (L := L) hab hac
              simp [hvw]
          | out w =>
              simp [PartialThreeVertexLinkage.SplitCurrentArc] at hac
      | out v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hab

theorem PartialThreeVertexLinkage.SplitCurrentArc.right_unique
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {a b c : VertexSplitState V}
    (hac : L.SplitCurrentArc a c)
    (hbc : L.SplitCurrentArc b c) :
    a = b := by
  cases c with
  | inn v =>
      cases a with
      | inn u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hac
      | out u =>
          cases b with
          | inn w =>
              simp [PartialThreeVertexLinkage.SplitCurrentArc] at hbc
          | out w =>
              have huw : u = w :=
                PartialThreeVertexLinkage.ForwardPathDart.fst_unique_of_snd
                  (L := L) hac hbc
              simp [huw]
  | out v =>
      cases a with
      | inn u =>
          cases b with
          | inn w =>
              simp [PartialThreeVertexLinkage.SplitCurrentArc] at hac hbc ⊢
              exact hac.1.trans hbc.1.symm
          | out w =>
              simp [PartialThreeVertexLinkage.SplitCurrentArc] at hbc
      | out u =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hac

theorem PartialThreeVertexLinkage.SplitCurrentArc.chain_left_conflict
    [DecidableEq V]
    {left right : Fin 3 -> V} {n : Nat}
    {L : PartialThreeVertexLinkage G left right n}
    {l : List (VertexSplitState V)} {source : V}
    (hhead : l.head? = some (VertexSplitState.inn source))
    (hchain : l.IsChain L.SplitResidualStep)
    {a b c : VertexSplitState V}
    (hcur : L.SplitCurrentArc a b)
    (hstep : List.Consecutive l a c) :
    b = c ∨ List.Consecutive l b a ∨ L.SplitCurrentArc c a := by
  classical
  rcases hstep with ⟨idx, hidxNext, hstateA, hstateC⟩
  have hres_raw := (List.isChain_iff_getElem.mp hchain) idx hidxNext
  cases a with
  | inn u =>
      cases b with
      | inn v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
      | out v =>
          have huv : u = v := hcur.1
          have huUsed : u ∈ L.usedVertices := hcur.2
          cases c with
          | inn w =>
              have hbad :
                  L.SplitResidualStep (VertexSplitState.inn u)
                    (VertexSplitState.inn w) := by
                simpa [hstateA, hstateC] using hres_raw
              simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
          | out w =>
              have hres :
                  L.SplitResidualStep (VertexSplitState.inn u)
                    (VertexSplitState.out w) := by
                simpa [hstateA, hstateC] using hres_raw
              have hcases :
                  (u = w ∧ u ∉ L.usedVertices) ∨
                    L.ForwardPathDart w u := by
                simpa [PartialThreeVertexLinkage.SplitResidualStep] using hres
              rcases hcases with hcap | hdart
              · exact False.elim (hcap.2 huUsed)
              · exact Or.inr (Or.inr (by
                  simpa [PartialThreeVertexLinkage.SplitCurrentArc] using hdart))
  | out u =>
      cases b with
      | out v =>
          simp [PartialThreeVertexLinkage.SplitCurrentArc] at hcur
      | inn v =>
          have hcurDart : L.ForwardPathDart u v := hcur
          cases c with
          | out w =>
              have hbad :
                  L.SplitResidualStep (VertexSplitState.out u)
                    (VertexSplitState.out w) := by
                simpa [hstateA, hstateC] using hres_raw
              simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
          | inn w =>
              have hres :
                  L.SplitResidualStep (VertexSplitState.out u)
                    (VertexSplitState.inn w) := by
                simpa [hstateA, hstateC] using hres_raw
              have hcases :
                  (u = w ∧ u ∈ L.usedVertices) ∨ G.Adj u w := by
                simpa [PartialThreeVertexLinkage.SplitResidualStep] using hres
              rcases hcases with hcap | hadj
              · have hwUsed : w ∈ L.usedVertices := by
                  simpa [hcap.1.symm] using hcap.2
                exact Or.inr (Or.inr (by
                  simpa [PartialThreeVertexLinkage.SplitCurrentArc,
                    hcap.1.symm] using hwUsed))
              · by_cases hvw : v = w
                · exact Or.inl (by simp [hvw])
                · have hidx_pos : 0 < idx := by
                    by_contra hnot
                    have hidx0 : idx = 0 := by omega
                    subst idx
                    have h0len : 0 < l.length :=
                      lt_trans (Nat.lt_succ_self 0) hidxNext
                    have hget0 :
                        l[0]? = some (l[0]'h0len) :=
                      List.getElem?_eq_getElem h0len
                    rw [List.head?_eq_getElem?, hget0] at hhead
                    injection hhead with hheadState
                    have hbad :
                        VertexSplitState.inn source =
                          VertexSplitState.out u := by
                      exact hheadState.symm.trans (by simpa using hstateA)
                    cases hbad
                  let prev : Nat := idx - 1
                  have hprevLen : prev < l.length := by
                    dsimp [prev]
                    omega
                  have hprevNext : prev + 1 < l.length := by
                    dsimp [prev]
                    omega
                  have hprevSucc : prev + 1 = idx := by
                    dsimp [prev]
                    omega
                  have hprevStepRaw :=
                    (List.isChain_iff_getElem.mp hchain) prev hprevNext
                  cases hprevState : l[prev]'hprevLen with
                  | out t =>
                      have hbad :
                          L.SplitResidualStep (VertexSplitState.out t)
                            (VertexSplitState.out u) := by
                        simpa [hprevSucc, hprevState, hstateA] using
                          hprevStepRaw
                      simp [PartialThreeVertexLinkage.SplitResidualStep] at hbad
                  | inn t =>
                      have hprevStep :
                          L.SplitResidualStep (VertexSplitState.inn t)
                            (VertexSplitState.out u) := by
                        simpa [hprevSucc, hprevState, hstateA] using
                          hprevStepRaw
                      have hprevCases :
                          (t = u ∧ t ∉ L.usedVertices) ∨
                            L.ForwardPathDart u t := by
                        simpa [PartialThreeVertexLinkage.SplitResidualStep]
                          using hprevStep
                      have ht_eq_v : t = v := by
                        rcases hprevCases with hcapPrev | hdartPrev
                        · exact False.elim
                            (hcapPrev.2 (by
                              simpa [hcapPrev.1] using
                                hcurDart.fst_mem_usedVertices))
                        · symm
                          exact
                            PartialThreeVertexLinkage.ForwardPathDart.snd_unique_of_fst
                              (L := L) hcurDart hdartPrev
                      have hbstate :
                          l[prev]'(lt_trans (Nat.lt_succ_self prev)
                            hprevNext) = VertexSplitState.inn v := by
                        have hprevState' :
                            l[prev]'(lt_trans (Nat.lt_succ_self prev)
                              hprevNext) = VertexSplitState.inn t := by
                          simpa using hprevState
                        simpa [ht_eq_v] using hprevState'
                      have hastate :
                          l[prev + 1]'hprevNext =
                            VertexSplitState.out u := by
                        simpa [hprevSucc] using hstateA
                      exact Or.inr (Or.inl
                        ⟨prev, hprevNext, hbstate, hastate⟩)

end Schematic.Math.GraphTheory
