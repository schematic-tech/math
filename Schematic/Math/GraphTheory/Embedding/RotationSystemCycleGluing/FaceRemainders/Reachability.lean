import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FaceRemainders.RemainderCode

/-! Reachability of non-selected old faces after cycle splicing. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

theorem cycleSplicedFace_left_reachable_of_old
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
    {e f : OrientedEdge G₁}
    (he : ¬ CycleForwardDart (c.mapLe hC₁) e)
    (hef : PermReachable (R₁.toHypermap).face e f) :
    PermReachable
      (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂).face
      (Sum.inl e) (Sum.inl f) := by
  let H :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  induction hef with
  | refl =>
      exact PermReachable.refl H.face (Sum.inl e)
  | @tail b d hreach hlink ih =>
      have hb :
          ¬ CycleForwardDart (c.mapLe hC₁) b :=
        hfac₁.not_forward_of_reachable_of_not_forward he hreach
      exact PermReachable.trans H.face ih (by
        cases hlink with
        | forward =>
            have hface :
                H.face (Sum.inl b) =
                  Sum.inl ((R₁.toHypermap).face b) := by
              simpa [H] using
                cycleSplicedHypermap_face_inl_not_forward
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ b hb
            simpa [hface] using
              PermReachable.forward H.face (Sum.inl b)
        | backward =>
            have hd :
                ¬ CycleForwardDart (c.mapLe hC₁)
                  ((R₁.toHypermap).face.symm b) :=
              hfac₁.not_forward_of_reachable_of_not_forward he
                (PermReachable.trans (R₁.toHypermap).face hreach
                  (PermReachable.backward (R₁.toHypermap).face b))
            have hstep :=
              PermReachable.forward H.face
                (Sum.inl ((R₁.toHypermap).face.symm b))
            have hface :
                H.face
                    (Sum.inl ((R₁.toHypermap).face.symm b)) =
                  Sum.inl b := by
              simpa [H] using
                cycleSplicedHypermap_face_inl_not_forward
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
                  ((R₁.toHypermap).face.symm b) hd
            rw [hface] at hstep
            simpa using PermReachable.symm H.face hstep)

theorem cycleSplicedFace_right_reachable_of_old
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
    {e f : OrientedEdge G₂}
    (he : ¬ CycleBackwardDart (c.mapLe hC₂) e)
    (hef : PermReachable (R₂.toHypermap).face e f) :
    PermReachable
      (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂).face
      (rightDartCode hC₁ e) (rightDartCode hC₁ f) := by
  let H :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  induction hef with
  | refl =>
      exact PermReachable.refl H.face (rightDartCode hC₁ e)
  | @tail b d hreach hlink ih =>
      have hb :
          ¬ CycleBackwardDart (c.mapLe hC₂) b :=
        hfac₂.not_backward_of_reachable_of_not_backward
          (hc := hc.mapLe hC₂) he hreach
      exact PermReachable.trans H.face ih (by
        cases hlink with
        | forward =>
            have hface :
                H.face (rightDartCode hC₁ b) =
                  rightDartCode hC₁ ((R₂.toHypermap).face b) := by
              simpa [H] using
                cycleSplicedHypermap_face_rightDartCode_of_not_backward
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ b hb
            simpa [hface] using
              PermReachable.forward H.face (rightDartCode hC₁ b)
        | backward =>
            have hd :
                ¬ CycleBackwardDart (c.mapLe hC₂)
                  ((R₂.toHypermap).face.symm b) :=
              hfac₂.not_backward_of_reachable_of_not_backward
                (hc := hc.mapLe hC₂) he
                (PermReachable.trans (R₂.toHypermap).face hreach
                  (PermReachable.backward (R₂.toHypermap).face b))
            have hstep :=
              PermReachable.forward H.face
                (rightDartCode hC₁ ((R₂.toHypermap).face.symm b))
            have hface :
                H.face
                    (rightDartCode hC₁
                      ((R₂.toHypermap).face.symm b)) =
                  rightDartCode hC₁ b := by
              simpa [H] using
                cycleSplicedHypermap_face_rightDartCode_of_not_backward
                  R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
                  ((R₂.toHypermap).face.symm b) hd
            rw [hface] at hstep
            simpa using PermReachable.symm H.face hstep)


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
