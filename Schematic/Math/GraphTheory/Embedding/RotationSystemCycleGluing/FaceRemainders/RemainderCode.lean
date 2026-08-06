import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FaceRemainders.SelectedFaces

/-! Face-orbit remainder codes for the cycle-splice carrier. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- Face orbits remaining after deleting the two facial disks that are
identified in a common-cycle sum. -/
abbrev CycleFaceRemainder
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle) :=
  Sum
    {o : (R₁.toHypermap).FaceOrbit //
      o ≠ selectedCycleFace R₁ (c.mapLe hC₁) (hc.mapLe hC₁)}
    {o : (R₂.toHypermap).FaceOrbit //
      o ≠ selectedCycleFace R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse}

/-- Assign a surviving old face orbit to each dart of the common-cycle
carrier. -/
noncomputable def cycleFaceRemainderCode
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse) :
    LeftBiasedDart G₁ G₂ C →
      CycleFaceRemainder R₁ R₂ hC₁ hC₂ c hc := by
  classical
  intro e
  cases e with
  | inl e =>
      by_cases heForward : CycleForwardDart (c.mapLe hC₁) e
      · let e₂ : OrientedEdge G₂ :=
          transferCommonDart hC₂ e
            (common_adj_of_cycleForwardDart hC₁ heForward)
        exact Sum.inr
          ⟨PermOrbit.of (R₂.toHypermap).face e₂, by
            intro heq
            have heReverseForward :
                CycleForwardDart (c.mapLe hC₂).reverse e₂ :=
              (faceOrbit_eq_selectedCycleFace_iff hfac₂ e₂).mp heq
            have heBackward :
                CycleBackwardDart (c.mapLe hC₂) e₂ :=
              (cycleForwardDart_reverse_iff_backward
                (c.mapLe hC₂) e₂).mp heReverseForward
            have heForward₂ :
                CycleForwardDart (c.mapLe hC₂) e₂ :=
              cycleForwardDart_transferCommonDart
                hC₁ hC₂ heForward
            exact cycleForwardDart_not_backward
              (hc.mapLe hC₂) heForward₂ heBackward⟩
      · exact Sum.inl
          ⟨PermOrbit.of (R₁.toHypermap).face e, by
            intro heq
            exact heForward
              ((faceOrbit_eq_selectedCycleFace_iff hfac₁ e).mp heq)⟩
  | inr e =>
      exact Sum.inr
        ⟨PermOrbit.of (R₂.toHypermap).face e.1, by
          intro heq
          have heReverseForward :
              CycleForwardDart (c.mapLe hC₂).reverse e.1 :=
            (faceOrbit_eq_selectedCycleFace_iff hfac₂ e.1).mp heq
          have heBackward :
              CycleBackwardDart (c.mapLe hC₂) e.1 :=
            (cycleForwardDart_reverse_iff_backward
              (c.mapLe hC₂) e.1).mp heReverseForward
          exact e.2 (common_adj_of_cycleBackwardDart hC₂ heBackward)⟩

theorem cycleFaceRemainderCode_inl_not_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : OrientedEdge G₁)
    (he : ¬ CycleForwardDart (c.mapLe hC₁) e) :
    cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
        (Sum.inl e) =
      Sum.inl
        ⟨PermOrbit.of (R₁.toHypermap).face e,
          fun heq => he
            ((faceOrbit_eq_selectedCycleFace_iff hfac₁ e).mp heq)⟩ := by
  classical
  simp [cycleFaceRemainderCode, he]

theorem cycleFaceRemainderCode_inl_forward
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (e : OrientedEdge G₁)
    (he : CycleForwardDart (c.mapLe hC₁) e) :
    cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
        (Sum.inl e) =
      Sum.inr
        ⟨PermOrbit.of (R₂.toHypermap).face
            (transferCommonDart hC₂ e
              (common_adj_of_cycleForwardDart hC₁ he)),
          faceOrbit_ne_selectedReverseFace_of_not_backward
            (hc := hc.mapLe hC₂) hfac₂
            (cycleForwardDart_not_backward (hc.mapLe hC₂)
              (cycleForwardDart_transferCommonDart hC₁ hC₂ he))⟩ := by
  classical
  simp only [cycleFaceRemainderCode, he, dite_true]

theorem cycleFaceRemainderCode_rightDartCode
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
    (e : OrientedEdge G₂)
    (he : ¬ CycleBackwardDart (c.mapLe hC₂) e) :
    cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
        (rightDartCode hC₁ e) =
      Sum.inr
        ⟨PermOrbit.of (R₂.toHypermap).face e,
          faceOrbit_ne_selectedReverseFace_of_not_backward
            (hc := hc.mapLe hC₂) hfac₂ he⟩ := by
  classical
  by_cases heC : C.Adj e.tail e.head
  · rcases cycleForward_or_backward_of_common hC₂ hspan e heC with
      heForward | heBackward
    · rw [rightDartCode_of_common hC₁ e heC]
      have heForward₁ :
          CycleForwardDart (c.mapLe hC₁)
            (transferCommonDart hC₁ e heC) :=
        cycleForwardDart_transferCommonDart hC₂ hC₁ heForward
      rw [cycleFaceRemainderCode_inl_forward
        R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
        (transferCommonDart hC₁ e heC) heForward₁]
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Quot.sound
      have hsame :
          transferCommonDart hC₂
              (transferCommonDart hC₁ e heC)
              (common_adj_of_cycleForwardDart hC₁ heForward₁) =
            e := by
        apply Subtype.ext
        rfl
      rw [hsame]
    · exact False.elim (he heBackward)
  · rw [rightDartCode_of_not_common hC₁ e heC]
    change Sum.inr _ = Sum.inr _
    apply congrArg Sum.inr
    apply Subtype.ext
    rfl

theorem cycleSplicedHypermap_face_rightDartCode_of_not_backward
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
    (e : OrientedEdge G₂)
    (he : ¬ CycleBackwardDart (c.mapLe hC₂) e) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
      hfac₁ hfac₂).face (rightDartCode hC₁ e) =
        rightDartCode hC₁ ((R₂.toHypermap).face e) := by
  classical
  by_cases heC : C.Adj e.tail e.head
  · rcases cycleForward_or_backward_of_common hC₂ hspan e heC with
      heForward | heBackward
    · rw [rightDartCode_of_common hC₁ e heC]
      have heForward₁ :
          CycleForwardDart (c.mapLe hC₁)
            (transferCommonDart hC₁ e heC) :=
        cycleForwardDart_transferCommonDart hC₂ hC₁ heForward
      rw [cycleSplicedHypermap_face_inl_forward
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
        (transferCommonDart hC₁ e heC) heForward₁]
      congr 2
    · exact False.elim (he heBackward)
  · rw [rightDartCode_of_not_common hC₁ e heC]
    exact cycleSplicedHypermap_face_inr
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ ⟨e, heC⟩

theorem cycleFaceRemainderCode_face
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
    (e : LeftBiasedDart G₁ G₂ C) :
    cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
        ((cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face e) =
      cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e := by
  classical
  cases e with
  | inl e =>
      by_cases heForward : CycleForwardDart (c.mapLe hC₁) e
      · let e₂ : OrientedEdge G₂ :=
          transferCommonDart hC₂ e
            (common_adj_of_cycleForwardDart hC₁ heForward)
        have he₂Forward :
            CycleForwardDart (c.mapLe hC₂) e₂ :=
          cycleForwardDart_transferCommonDart hC₁ hC₂ heForward
        have he₂NotBackward :
            ¬ CycleBackwardDart (c.mapLe hC₂) e₂ :=
          cycleForwardDart_not_backward (hc.mapLe hC₂) he₂Forward
        have hfaceNotBackward :
          ¬ CycleBackwardDart (c.mapLe hC₂)
              ((R₂.toHypermap).face e₂) :=
          hfac₂.not_backward_face_of_not_backward
            (hc := hc.mapLe hC₂) he₂NotBackward
        rw [cycleSplicedHypermap_face_inl_forward
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e heForward]
        rw [cycleFaceRemainderCode_rightDartCode
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
          ((R₂.toHypermap).face e₂) hfaceNotBackward]
        rw [cycleFaceRemainderCode_inl_forward
          R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e heForward]
        apply congrArg Sum.inr
        apply Subtype.ext
        exact PermOrbit.of_apply (R₂.toHypermap).face e₂
      · have hfaceNotForward :
            ¬ CycleForwardDart (c.mapLe hC₁)
              ((R₁.toHypermap).face e) :=
          hfac₁.not_forward_face_of_not_forward heForward
        rw [cycleSplicedHypermap_face_inl_not_forward
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e heForward]
        simp only [cycleFaceRemainderCode, heForward,
          hfaceNotForward, dite_false]
        apply congrArg Sum.inl
        apply Subtype.ext
        exact PermOrbit.of_apply (R₁.toHypermap).face e
  | inr e =>
      have heNotBackward :
          ¬ CycleBackwardDart (c.mapLe hC₂) e.1 := by
        intro heBackward
        exact e.2 (common_adj_of_cycleBackwardDart hC₂ heBackward)
      have hfaceNotBackward :
          ¬ CycleBackwardDart (c.mapLe hC₂)
            ((R₂.toHypermap).face e.1) :=
        hfac₂.not_backward_face_of_not_backward
          (hc := hc.mapLe hC₂) heNotBackward
      rw [cycleSplicedHypermap_face_inr
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e]
      rw [cycleFaceRemainderCode_rightDartCode
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
        ((R₂.toHypermap).face e.1) hfaceNotBackward]
      rw [← rightDartCode_of_not_common hC₁ e.1 e.2]
      rw [cycleFaceRemainderCode_rightDartCode
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e.1 heNotBackward]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact PermOrbit.of_apply (R₂.toHypermap).face e.1

theorem cycleFaceRemainderCode_of_link
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
    {e f : LeftBiasedDart G₁ G₂ C}
    (hef :
      PermLink
        (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face e f) :
    cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e =
      cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ f := by
  let H :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  cases hef with
  | forward =>
      exact
        (cycleFaceRemainderCode_face
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e).symm
  | backward =>
      have h :=
        cycleFaceRemainderCode_face
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ (H.face.symm e)
      rw [H.face.apply_symm_apply] at h
      exact h

theorem cycleFaceRemainderCode_of_reachable
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
    {e f : LeftBiasedDart G₁ G₂ C}
    (hef :
      PermReachable
        (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face e f) :
    cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e =
      cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ f :=
  hef.apply_eq
    (cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂)
    (fun {_ _} h => cycleFaceRemainderCode_of_link
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ h)


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
