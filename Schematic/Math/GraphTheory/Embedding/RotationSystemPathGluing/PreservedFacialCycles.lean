import Schematic.Math.GraphTheory.Embedding.RotationSystemPathGluing.CycleSumReachability
import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.Planarity

/-! Preservation of non-selected facial cycles by cycle-sum gluing. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- A non-selected facial cycle of the left summand remains facial after
gluing along the selected cycle.  The hypothesis is directional: sharing an
edge in the opposite orientation is allowed, which is exactly what is needed
for the auxiliary chord in facial-path gluing. -/
theorem cycleSum_isFacialCycle_of_left
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u r : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (hmeet :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support →
        v ∈ c.support)
    (d : G₁.Walk r r) (hd : d.IsCycle)
    (hdfacial : IsFacialCycle R₁ d hd)
    (hdisjoint :
      ∀ e : OrientedEdge G₁,
        CycleForwardDart d e →
          ¬ CycleForwardDart (c.mapLe hC₁) e) :
    IsFacialCycle
      (cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
        hfac₁ hfac₂ hmeet)
      (d.mapLe le_sup_left) (hd.mapLe le_sup_left) := by
  classical
  let E := leftBiasedSupEquiv hC₁ hcommon
  let H :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  let R :=
    cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet
  let φ :=
    cycleSplicedHypermapIsoCycleSum
      R₁ R₂ hC₁ hC₂ hcommon c hc hspan hfac₁ hfac₂ hmeet
  intro e
  rw [cycleForwardDart_mapLe_sup_iff_leftBiased hC₁ hcommon d e]
  have hfirst :
      cycleFirstDart (d.mapLe le_sup_left) (hd.mapLe le_sup_left) =
        E (Sum.inl (cycleFirstDart d hd)) :=
    cycleFirstDart_mapLe_sup hC₁ hcommon d hd
  rw [hfirst]
  have hiso :=
    (φ.faceReachable_iff
      (x := Sum.inl (cycleFirstDart d hd)) (y := E.symm e))
  have hEfirst :
      φ.toEquiv (Sum.inl (cycleFirstDart d hd)) =
        E (Sum.inl (cycleFirstDart d hd)) := by
    rfl
  have hEy : φ.toEquiv (E.symm e) = e := by
    change E (E.symm e) = e
    exact E.apply_symm_apply e
  rw [hEfirst, hEy] at hiso
  rw [← hiso]
  have hfirstNot :
      ¬ CycleForwardDart (c.mapLe hC₁) (cycleFirstDart d hd) :=
    hdisjoint _ (cycleForwardDart_first d hd)
  rw [cycleSplicedHypermap_left_face_reachable_iff
    R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hfirstNot]
  cases hx : E.symm e with
  | inl f =>
      simp only
      constructor
      · rintro ⟨g, hg, hgd⟩
        have hgf : g = f := by simpa using hg.symm
        subst g
        exact (hdfacial f).mp hgd
      · intro hf
        refine ⟨f, rfl, ?_⟩
        exact (hdfacial f).mpr hf
  | inr f => simp

/-- A non-selected facial cycle of the right summand remains facial after
gluing along the selected cycle.  The right selected face traverses the
common cycle backwards, so the directional disjointness condition excludes
backward darts of `c`. -/
theorem cycleSum_isFacialCycle_of_right
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u r : V}
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hC₁ : C ≤ G₁) (hC₂ : C ≤ G₂)
    (hcommon :
      ∀ ⦃x y : V⦄, G₁.Adj x y → G₂.Adj x y → C.Adj x y)
    (c : C.Walk u u) (hc : c.IsCycle)
    (hspan : c.toSubgraph.spanningCoe = C)
    (hfac₁ :
      IsFacialCycle R₁ (c.mapLe hC₁) (hc.mapLe hC₁))
    (hfac₂ :
      IsFacialCycle R₂ (c.mapLe hC₂).reverse
        (hc.mapLe hC₂).reverse)
    (hmeet :
      ∀ ⦃v : V⦄, v ∈ G₁.support → v ∈ G₂.support →
        v ∈ c.support)
    (d : G₂.Walk r r) (hd : d.IsCycle)
    (hdfacial : IsFacialCycle R₂ d hd)
    (hdisjoint :
      ∀ e : OrientedEdge G₂,
        CycleForwardDart d e →
          ¬ CycleBackwardDart (c.mapLe hC₂) e) :
    IsFacialCycle
      (cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
        hfac₁ hfac₂ hmeet)
      (d.mapLe le_sup_right) (hd.mapLe le_sup_right) := by
  classical
  let E := leftBiasedSupEquiv hC₁ hcommon
  let φ :=
    cycleSplicedHypermapIsoCycleSum
      R₁ R₂ hC₁ hC₂ hcommon c hc hspan hfac₁ hfac₂ hmeet
  intro e
  rw [cycleForwardDart_mapLe_sup_iff_rightBiased hC₁ hcommon d e]
  have hfirst :
      cycleFirstDart (d.mapLe le_sup_right) (hd.mapLe le_sup_right) =
        E (rightDartCode hC₁ (cycleFirstDart d hd)) :=
    cycleFirstDart_mapLe_sup_right hC₁ hcommon d hd
  rw [hfirst]
  have hiso :=
    (φ.faceReachable_iff
      (x := rightDartCode hC₁ (cycleFirstDart d hd))
      (y := E.symm e))
  have hEfirst :
      φ.toEquiv (rightDartCode hC₁ (cycleFirstDart d hd)) =
        E (rightDartCode hC₁ (cycleFirstDart d hd)) := by
    rfl
  have hEy : φ.toEquiv (E.symm e) = e := by
    change E (E.symm e) = e
    exact E.apply_symm_apply e
  rw [hEfirst, hEy] at hiso
  rw [← hiso]
  have hfirstNot :
      ¬ CycleBackwardDart (c.mapLe hC₂) (cycleFirstDart d hd) :=
    hdisjoint _ (cycleForwardDart_first d hd)
  rw [cycleSplicedHypermap_right_face_reachable_iff
    R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂ hfirstNot]
  constructor
  · rintro ⟨g, hg, hgd⟩
    exact ⟨g, hg, (hdfacial g).mp hgd⟩
  · rintro ⟨g, hg, hgd⟩
    exact ⟨g, hg, (hdfacial g).mpr hgd⟩


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
