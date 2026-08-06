import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FaceRemainders.Reachability

/-! Non-selected face reachability through the cycle splice. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- A face orbit of the left summand which is not the selected cycle face is
unchanged by the carrier-level cycle splice. -/
theorem cycleSplicedHypermap_left_face_reachable_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    {e : OrientedEdge G₁}
    (he : ¬ CycleForwardDart (c.mapLe hC₁) e)
    (x : LeftBiasedDart G₁ G₂ C) :
    PermReachable
        (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face
        (Sum.inl e) x ↔
      match x with
      | Sum.inl f => PermReachable (R₁.toHypermap).face e f
      | Sum.inr _ => False := by
  classical
  let H :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  constructor
  · intro hreach
    have hcode :=
      cycleFaceRemainderCode_of_reachable
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hreach
    cases x with
    | inl f =>
        by_cases hf : CycleForwardDart (c.mapLe hC₁) f
        · rw [cycleFaceRemainderCode_inl_not_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e he,
            cycleFaceRemainderCode_inl_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ f hf] at hcode
          cases hcode
        · rw [cycleFaceRemainderCode_inl_not_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e he,
            cycleFaceRemainderCode_inl_not_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ f hf] at hcode
          exact Quotient.exact (congrArg Subtype.val (Sum.inl.inj hcode))
    | inr f =>
        have hf : ¬ CycleBackwardDart (c.mapLe hC₂) f.1 := by
          intro hback
          exact f.2 (common_adj_of_cycleBackwardDart hC₂ hback)
        rw [cycleFaceRemainderCode_inl_not_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e he,
            ← rightDartCode_of_not_common hC₁ f.1 f.2,
            cycleFaceRemainderCode_rightDartCode
              R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ f.1 hf] at hcode
        cases hcode
  · intro hreach
    cases x with
    | inl f =>
        exact cycleSplicedFace_left_reachable_of_old
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ he hreach
    | inr f => exact False.elim hreach

/-- A face orbit of the right summand which is not the selected reverse-cycle
face is exactly unchanged by the carrier-level cycle splice.  Common forward
cycle darts are represented by their left-biased copy, hence the existential
description through `rightDartCode`. -/
theorem cycleSplicedHypermap_right_face_reachable_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    {e : OrientedEdge G₂}
    (he : ¬ CycleBackwardDart (c.mapLe hC₂) e)
    (x : LeftBiasedDart G₁ G₂ C) :
    PermReachable
        (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face
        (rightDartCode hC₁ e) x ↔
      Exists fun f : OrientedEdge G₂ =>
        x = rightDartCode hC₁ f ∧
          PermReachable (R₂.toHypermap).face e f := by
  classical
  constructor
  · intro hreach
    have hcode :=
      cycleFaceRemainderCode_of_reachable
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hreach
    cases x with
    | inl f =>
        by_cases hf : CycleForwardDart (c.mapLe hC₁) f
        · let f₂ : OrientedEdge G₂ :=
            transferCommonDart hC₂ f
              (common_adj_of_cycleForwardDart hC₁ hf)
          have hf₂not : ¬ CycleBackwardDart (c.mapLe hC₂) f₂ :=
            cycleForwardDart_not_backward (hc.mapLe hC₂)
              (cycleForwardDart_transferCommonDart hC₁ hC₂ hf)
          rw [cycleFaceRemainderCode_rightDartCode
                R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e he,
              cycleFaceRemainderCode_inl_forward
                R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ f hf] at hcode
          refine ⟨f₂, ?_, ?_⟩
          · exact (rightDartCode_transferCommonDart hC₁ hC₂ f
              (common_adj_of_cycleForwardDart hC₁ hf)).symm
          · exact Quotient.exact
              (congrArg Subtype.val (Sum.inr.inj hcode))
        · rw [cycleFaceRemainderCode_rightDartCode
                R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e he,
              cycleFaceRemainderCode_inl_not_forward
                R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ f hf] at hcode
          cases hcode
    | inr f =>
        have hfnot : ¬ CycleBackwardDart (c.mapLe hC₂) f.1 := by
          intro hback
          exact f.2 (common_adj_of_cycleBackwardDart hC₂ hback)
        rw [cycleFaceRemainderCode_rightDartCode
              R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e he,
            ← rightDartCode_of_not_common hC₁ f.1 f.2,
            cycleFaceRemainderCode_rightDartCode
              R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ f.1 hfnot] at hcode
        refine ⟨f.1, (rightDartCode_of_not_common hC₁ f.1 f.2).symm, ?_⟩
        exact Quotient.exact
          (congrArg Subtype.val (Sum.inr.inj hcode))
  · rintro ⟨f, rfl, hef⟩
    exact cycleSplicedFace_right_reachable_of_old
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ he hef

/-- A dart of a cycle included into the left side of a graph union comes
from the left-biased copy of a unique dart of the original cycle. -/
theorem cycleForwardDart_mapLe_sup_iff_leftBiased
    {V : Type u} [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {r : V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (d : G₁.Walk r r)
    (e : OrientedEdge (G₁ ⊔ G₂)) :
    CycleForwardDart (d.mapLe le_sup_left) e ↔
      Exists fun f : OrientedEdge G₁ =>
        (leftBiasedSupEquiv hC₁ hcommon).symm e = Sum.inl f ∧
          CycleForwardDart d f := by
  constructor
  · rintro ⟨i, hi, htail, hhead⟩
    let f : OrientedEdge G₁ :=
      ⟨(d.getVert i, d.getVert (i + 1)), d.adj_getVert_succ (by
        simpa using hi)⟩
    refine ⟨f, ?_, ⟨i, by simpa using hi, rfl, rfl⟩⟩
    apply (leftBiasedSupEquiv hC₁ hcommon).injective
    rw [(leftBiasedSupEquiv hC₁ hcommon).apply_symm_apply]
    apply Subtype.ext
    exact Prod.ext (by simpa [f] using htail) (by simpa [f] using hhead)
  · rintro ⟨f, hleft, ⟨i, hi, htail, hhead⟩⟩
    have heq : e = leftBiasedSupEquiv hC₁ hcommon (Sum.inl f) := by
      calc
        e = leftBiasedSupEquiv hC₁ hcommon
              ((leftBiasedSupEquiv hC₁ hcommon).symm e) :=
          ((leftBiasedSupEquiv hC₁ hcommon).apply_symm_apply e).symm
        _ = leftBiasedSupEquiv hC₁ hcommon (Sum.inl f) :=
          congrArg (leftBiasedSupEquiv hC₁ hcommon) hleft
    refine ⟨i, by simpa using hi, ?_, ?_⟩
    · simpa [heq] using htail
    · simpa [heq] using hhead

/-- The left-biased union equivalence sends the encoded right dart to the
same ordered edge in the graph union. -/
theorem leftBiasedSupEquiv_rightDartCode
    {V : Type u} [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (e : OrientedEdge G₂) :
    leftBiasedSupEquiv hC₁ hcommon (rightDartCode hC₁ e) =
      ⟨(e.tail, e.head),
        (SimpleGraph.sup_adj G₁ G₂ e.tail e.head).mpr (Or.inr e.adj)⟩ := by
  classical
  by_cases heC : C.Adj e.tail e.head
  · rw [rightDartCode_of_common hC₁ e heC]
    apply Subtype.ext
    rfl
  · rw [rightDartCode_of_not_common hC₁ e heC]
    rfl

/-- A dart of a cycle included into the right side of a graph union comes
from the right-dart encoding of a unique dart of the original cycle. -/
theorem cycleForwardDart_mapLe_sup_iff_rightBiased
    {V : Type u} [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {r : V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (d : G₂.Walk r r)
    (e : OrientedEdge (G₁ ⊔ G₂)) :
    CycleForwardDart (d.mapLe le_sup_right) e ↔
      Exists fun f : OrientedEdge G₂ =>
        (leftBiasedSupEquiv hC₁ hcommon).symm e =
            rightDartCode hC₁ f ∧
          CycleForwardDart d f := by
  constructor
  · rintro ⟨i, hi, htail, hhead⟩
    let f : OrientedEdge G₂ :=
      ⟨(d.getVert i, d.getVert (i + 1)), d.adj_getVert_succ (by
        simpa using hi)⟩
    refine ⟨f, ?_, ⟨i, by simpa using hi, rfl, rfl⟩⟩
    apply (leftBiasedSupEquiv hC₁ hcommon).injective
    rw [(leftBiasedSupEquiv hC₁ hcommon).apply_symm_apply]
    rw [leftBiasedSupEquiv_rightDartCode hC₁ hcommon f]
    apply Subtype.ext
    exact Prod.ext (by simpa [f] using htail) (by simpa [f] using hhead)
  · rintro ⟨f, hright, ⟨i, hi, htail, hhead⟩⟩
    have heq :
        e = leftBiasedSupEquiv hC₁ hcommon (rightDartCode hC₁ f) := by
      calc
        e = leftBiasedSupEquiv hC₁ hcommon
              ((leftBiasedSupEquiv hC₁ hcommon).symm e) :=
          ((leftBiasedSupEquiv hC₁ hcommon).apply_symm_apply e).symm
        _ = leftBiasedSupEquiv hC₁ hcommon (rightDartCode hC₁ f) :=
          congrArg (leftBiasedSupEquiv hC₁ hcommon) hright
    refine ⟨i, by simpa using hi, ?_, ?_⟩
    · rw [heq, leftBiasedSupEquiv_rightDartCode]
      simpa using htail
    · rw [heq, leftBiasedSupEquiv_rightDartCode]
      simpa using hhead

/-- The first dart of a left cycle maps to the left-biased first dart in the
union carrier. -/
theorem cycleFirstDart_mapLe_sup
    {V : Type u} [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {r : V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (d : G₁.Walk r r) (hd : d.IsCycle) :
    cycleFirstDart (d.mapLe le_sup_left) (hd.mapLe le_sup_left) =
      leftBiasedSupEquiv hC₁ hcommon (Sum.inl (cycleFirstDart d hd)) := by
  rw [leftBiasedSupEquiv_inl]
  apply Subtype.ext
  change
    ((d.mapLe le_sup_left).getVert 0,
        (d.mapLe le_sup_left).getVert 1) =
      (d.getVert 0, d.getVert 1)
  exact Prod.ext
    (walkMapLe_getVert le_sup_left d 0)
    (walkMapLe_getVert le_sup_left d 1)

/-- The first dart of a right cycle maps to its right-dart encoding in the
left-biased union carrier. -/
theorem cycleFirstDart_mapLe_sup_right
    {V : Type u} [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {r : V}
    (hC₁ : C ≤ G₁)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (d : G₂.Walk r r) (hd : d.IsCycle) :
    cycleFirstDart (d.mapLe le_sup_right) (hd.mapLe le_sup_right) =
      leftBiasedSupEquiv hC₁ hcommon
        (rightDartCode hC₁ (cycleFirstDart d hd)) := by
  rw [leftBiasedSupEquiv_rightDartCode]
  apply Subtype.ext
  change
    ((d.mapLe le_sup_right).getVert 0,
        (d.mapLe le_sup_right).getVert 1) =
      (d.getVert 0, d.getVert 1)
  exact Prod.ext
    (walkMapLe_getVert le_sup_right d 0)
    (walkMapLe_getVert le_sup_right d 1)


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
