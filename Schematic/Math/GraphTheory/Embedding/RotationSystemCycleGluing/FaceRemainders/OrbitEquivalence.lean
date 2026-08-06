import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FaceRemainders.Reachability

/-! Equivalence between spliced face orbits and old face remainders. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

noncomputable def cycleFaceOrbitToRemainder
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
        (hc.mapLe hC₂).reverse) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂).FaceOrbit →
      CycleFaceRemainder R₁ R₂ hC₁ hC₂ c hc :=
  Quotient.lift
    (cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂)
    (by
      intro e f hef
      exact cycleFaceRemainderCode_of_reachable
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hef)

noncomputable def cycleFaceRemainderToOrbit
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
        (hc.mapLe hC₂).reverse) :
    CycleFaceRemainder R₁ R₂ hC₁ hC₂ c hc →
      (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂).FaceOrbit
  | Sum.inl o =>
      PermOrbit.of
        (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face
        (Sum.inl (Quotient.out o.1))
  | Sum.inr o =>
      PermOrbit.of
        (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
          hfac₁ hfac₂).face
        (rightDartCode hC₁ (Quotient.out o.1))

theorem cycleFaceOrbitToRemainder_rightInverse
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
    (o : CycleFaceRemainder R₁ R₂ hC₁ hC₂ c hc) :
    cycleFaceOrbitToRemainder
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
        (cycleFaceRemainderToOrbit
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ o) =
      o := by
  classical
  cases o with
  | inl o =>
      let e : OrientedEdge G₁ := Quotient.out o.1
      have heOrbit :
          PermOrbit.of (R₁.toHypermap).face e = o.1 :=
        Quotient.out_eq o.1
      have heNotForward :
          ¬ CycleForwardDart (c.mapLe hC₁) e := by
        intro heForward
        apply o.2
        rw [← heOrbit]
        exact
          (faceOrbit_eq_selectedCycleFace_iff hfac₁ e).mpr heForward
      change
        cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
            (Sum.inl e) =
          Sum.inl o
      rw [cycleFaceRemainderCode_inl_not_forward
        R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e heNotForward]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact heOrbit
  | inr o =>
      let e : OrientedEdge G₂ := Quotient.out o.1
      have heOrbit :
          PermOrbit.of (R₂.toHypermap).face e = o.1 :=
        Quotient.out_eq o.1
      have heNotBackward :
          ¬ CycleBackwardDart (c.mapLe hC₂) e := by
        intro heBackward
        apply o.2
        rw [← heOrbit]
        exact
          (faceOrbit_eq_selectedCycleFace_iff hfac₂ e).mpr
            ((cycleForwardDart_reverse_iff_backward
              (c.mapLe hC₂) e).mpr heBackward)
      change
        cycleFaceRemainderCode R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂
            (rightDartCode hC₁ e) =
          Sum.inr o
      rw [cycleFaceRemainderCode_rightDartCode
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e heNotBackward]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact heOrbit

theorem cycleFaceOrbitToRemainder_leftInverse
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
    (o :
      (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂).FaceOrbit) :
    cycleFaceRemainderToOrbit
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
        (cycleFaceOrbitToRemainder
          R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ o) =
      o := by
  classical
  let H :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  induction o using Quotient.inductionOn with
  | h e =>
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
            let r : OrientedEdge G₂ :=
              Quotient.out (PermOrbit.of (R₂.toHypermap).face e₂)
            have hrOrbit :
                PermOrbit.of (R₂.toHypermap).face r =
                  PermOrbit.of (R₂.toHypermap).face e₂ :=
              Quotient.out_eq (PermOrbit.of (R₂.toHypermap).face e₂)
            have hrReach :
                PermReachable (R₂.toHypermap).face r e₂ :=
              Quotient.exact hrOrbit
            have hrNotBackward :
                ¬ CycleBackwardDart (c.mapLe hC₂) r :=
              hfac₂.not_backward_of_reachable_of_not_backward
                (hc := hc.mapLe hC₂) he₂NotBackward
                (PermReachable.symm (R₂.toHypermap).face hrReach)
            have hrightOut :
                PermReachable H.face
                  (rightDartCode hC₁ r) (rightDartCode hC₁ e₂) := by
              simpa [H] using
                cycleSplicedFace_right_reachable_of_old
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
                  hrNotBackward hrReach
            have hfaceOld :
                PermReachable (R₂.toHypermap).face
                  ((R₂.toHypermap).face e₂) e₂ := by
              simpa using
                PermReachable.backward (R₂.toHypermap).face
                  ((R₂.toHypermap).face e₂)
            have hrightFace :
                PermReachable H.face
                  (rightDartCode hC₁ ((R₂.toHypermap).face e₂))
                  (rightDartCode hC₁ e₂) := by
              simpa [H] using
                cycleSplicedFace_right_reachable_of_old
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
                  hfaceNotBackward hfaceOld
            have hcarrierFace :
                H.face (Sum.inl e) =
                  rightDartCode hC₁ ((R₂.toHypermap).face e₂) := by
              simpa [H] using
                cycleSplicedHypermap_face_inl_forward
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ e heForward
            have henter :
                PermReachable H.face (Sum.inl e)
                  (rightDartCode hC₁ ((R₂.toHypermap).face e₂)) := by
              simpa [hcarrierFace] using
                PermReachable.forward H.face (Sum.inl e)
            simp only [cycleFaceOrbitToRemainder, Quotient.lift_mk]
            rw [cycleFaceRemainderCode_inl_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e heForward]
            change
              PermOrbit.of H.face (rightDartCode hC₁ r) =
                PermOrbit.of H.face (Sum.inl e)
            apply PermOrbit.of_eq_of
            exact PermReachable.trans H.face hrightOut
              (PermReachable.symm H.face
                (PermReachable.trans H.face henter hrightFace))
          · let r : OrientedEdge G₁ :=
              Quotient.out (PermOrbit.of (R₁.toHypermap).face e)
            have hrOrbit :
                PermOrbit.of (R₁.toHypermap).face r =
                  PermOrbit.of (R₁.toHypermap).face e :=
              Quotient.out_eq (PermOrbit.of (R₁.toHypermap).face e)
            have hrReach :
                PermReachable (R₁.toHypermap).face r e :=
              Quotient.exact hrOrbit
            have hrNotForward :
                ¬ CycleForwardDart (c.mapLe hC₁) r :=
              hfac₁.not_forward_of_reachable_of_not_forward heForward
                (PermReachable.symm (R₁.toHypermap).face hrReach)
            have hleft :
                PermReachable H.face (Sum.inl r) (Sum.inl e) := by
              simpa [H] using
                cycleSplicedFace_left_reachable_of_old
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
                  hrNotForward hrReach
            simp only [cycleFaceOrbitToRemainder, Quotient.lift_mk]
            rw [cycleFaceRemainderCode_inl_not_forward
              R₁ R₂ hC₁ hC₂ c hc hfac₁ hfac₂ e heForward]
            change
              PermOrbit.of H.face (Sum.inl r) =
                PermOrbit.of H.face (Sum.inl e)
            exact PermOrbit.of_eq_of H.face hleft
      | inr e =>
          have heNotBackward :
              ¬ CycleBackwardDart (c.mapLe hC₂) e.1 := by
            intro heBackward
            exact e.2 (common_adj_of_cycleBackwardDart hC₂ heBackward)
          let r : OrientedEdge G₂ :=
            Quotient.out (PermOrbit.of (R₂.toHypermap).face e.1)
          have hrOrbit :
              PermOrbit.of (R₂.toHypermap).face r =
                PermOrbit.of (R₂.toHypermap).face e.1 :=
            Quotient.out_eq (PermOrbit.of (R₂.toHypermap).face e.1)
          have hrReach :
              PermReachable (R₂.toHypermap).face r e.1 :=
            Quotient.exact hrOrbit
          have hrNotBackward :
              ¬ CycleBackwardDart (c.mapLe hC₂) r :=
            hfac₂.not_backward_of_reachable_of_not_backward
              (hc := hc.mapLe hC₂) heNotBackward
              (PermReachable.symm (R₂.toHypermap).face hrReach)
          have hright :
              PermReachable H.face
                (rightDartCode hC₁ r) (rightDartCode hC₁ e.1) := by
            simpa [H] using
              cycleSplicedFace_right_reachable_of_old
                R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
                hrNotBackward hrReach
          simp only [cycleFaceOrbitToRemainder, Quotient.lift_mk]
          rw [← rightDartCode_of_not_common hC₁ e.1 e.2]
          rw [cycleFaceRemainderCode_rightDartCode
            R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
            e.1 heNotBackward]
          change
            PermOrbit.of H.face (rightDartCode hC₁ r) =
              PermOrbit.of H.face (rightDartCode hC₁ e.1)
          exact PermOrbit.of_eq_of H.face hright

noncomputable def cycleSplicedFaceOrbitEquiv
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
        (hc.mapLe hC₂).reverse) :
    (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂).FaceOrbit ≃
      CycleFaceRemainder R₁ R₂ hC₁ hC₂ c hc where
  toFun :=
    cycleFaceOrbitToRemainder
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  invFun :=
    cycleFaceRemainderToOrbit
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  left_inv :=
    cycleFaceOrbitToRemainder_leftInverse
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  right_inv :=
    cycleFaceOrbitToRemainder_rightInverse
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂



end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
