import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.EulerCounts

/-! Connectivity and Euler planarity of cycle sums. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

/-- The carrier hypermap is the hypermap induced by the graph-level
`cycleSum`, up to the canonical dart equivalence. -/
noncomputable def cycleSplicedHypermapIsoCycleSum
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
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
        v ∈ c.support) :
    Hypermap.Iso
      (cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan
        hfac₁ hfac₂)
      ((cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
        hfac₁ hfac₂ hmeet).toHypermap) := by
  let E := leftBiasedSupEquiv hC₁ hcommon
  let N :=
    cycleSplicedNode R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  exact
    { toEquiv := E
      map_edge := by
        intro e
        change E (leftBiasedSymm e) = (E e).symm
        exact leftBiasedSupEquiv_symm hC₁ hcommon e
      map_node := by
        intro e
        change E (N e) = transportPerm E N (E e)
        simp
      map_face := by
        intro e
        change E (N.symm (leftBiasedSymm e)) =
          (transportPerm E N).symm (E e).symm
        calc
          E (N.symm (leftBiasedSymm e)) =
              (transportPerm E N).symm
                (E (leftBiasedSymm e)) := by
            simp [transportPerm]
          _ = (transportPerm E N).symm (E e).symm := by
            rw [leftBiasedSupEquiv_symm hC₁ hcommon e] }

theorem cycleSum_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
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
    (hconn₁ : (R₁.toHypermap).Connected)
    (hconn₂ : (R₂.toHypermap).Connected)
    (hplanar₁ : (R₁.toHypermap).EulerPlanar)
    (hplanar₂ : (R₂.toHypermap).EulerPlanar) :
    ((cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet).toHypermap).EulerPlanar := by
  let R :=
    cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet
  let K :=
    cycleSplicedHypermap R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  let φ :=
    cycleSplicedHypermapIsoCycleSum
      R₁ R₂ hC₁ hC₂ hcommon c hc hspan hfac₁ hfac₂ hmeet
  have hconnR : (R.toHypermap).Connected := by
    simpa [R] using
      cycleSum_connected
        R₁ R₂ hC₁ hC₂ hcommon c hc hspan hfac₁ hfac₂ hmeet
          hconn₁ hconn₂
  have hcomp₁ : (R₁.toHypermap).componentCount = 1 :=
    hconn₁.componentCount_eq_one
  have hcomp₂ : (R₂.toHypermap).componentCount = 1 :=
    hconn₂.componentCount_eq_one
  have hcompR : (R.toHypermap).componentCount = 1 :=
    hconnR.componentCount_eq_one
  have heuler₁ :
      (R₁.toHypermap).eulerLeft =
        (R₁.toHypermap).eulerRight :=
    Hypermap.euler_eq_of_evenGenus_planar
      (Hypermap.evenGenus R₁.toHypermap) hplanar₁
  have heuler₂ :
      (R₂.toHypermap).eulerLeft =
        (R₂.toHypermap).eulerRight :=
    Hypermap.euler_eq_of_evenGenus_planar
      (Hypermap.evenGenus R₂.toHypermap) hplanar₂
  have hdart₁ :
      Fintype.card (R₁.toHypermap).Dart =
        2 * (R₁.toHypermap).edgeOrbitCount :=
    Hypermap.Plain.card_dart_eq_two_mul_edgeOrbitCount
      (G := R₁.toHypermap) R₁.toHypermap_plain
  have hdart₂ :
      Fintype.card (R₂.toHypermap).Dart =
        2 * (R₂.toHypermap).edgeOrbitCount :=
    Hypermap.Plain.card_dart_eq_two_mul_edgeOrbitCount
      (G := R₂.toHypermap) R₂.toHypermap_plain
  have hdartR :
      Fintype.card (R.toHypermap).Dart =
        2 * (R.toHypermap).edgeOrbitCount :=
    Hypermap.Plain.card_dart_eq_two_mul_edgeOrbitCount
      (G := R.toHypermap) R.toHypermap_plain
  have hnormalized₁ :
      2 + 2 * (R₁.toHypermap).edgeOrbitCount =
        (R₁.toHypermap).edgeOrbitCount +
          (R₁.toHypermap).nodeOrbitCount +
          (R₁.toHypermap).faceOrbitCount := by
    simpa [Hypermap.eulerLeft, Hypermap.eulerRight,
      hcomp₁, hdart₁] using heuler₁
  have hnormalized₂ :
      2 + 2 * (R₂.toHypermap).edgeOrbitCount =
        (R₂.toHypermap).edgeOrbitCount +
          (R₂.toHypermap).nodeOrbitCount +
          (R₂.toHypermap).faceOrbitCount := by
    simpa [Hypermap.eulerLeft, Hypermap.eulerRight,
      hcomp₂, hdart₂] using heuler₂
  have hfaceK :
      K.faceOrbitCount + 2 =
        (R₁.toHypermap).faceOrbitCount +
          (R₂.toHypermap).faceOrbitCount := by
    simpa [K] using
      cycleSplicedHypermap_faceOrbitCount
        R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂
  have hfaceIso :
      K.faceOrbitCount = (R.toHypermap).faceOrbitCount := by
    simpa [K, R, φ] using φ.faceOrbitCount_eq
  have hface :
      (R.toHypermap).faceOrbitCount + 2 =
        (R₁.toHypermap).faceOrbitCount +
          (R₂.toHypermap).faceOrbitCount := by
    omega
  have hbalance :
      (R.toHypermap).edgeOrbitCount +
            (R₁.toHypermap).nodeOrbitCount +
            (R₂.toHypermap).nodeOrbitCount =
        (R₁.toHypermap).edgeOrbitCount +
          (R₂.toHypermap).edgeOrbitCount +
          (R.toHypermap).nodeOrbitCount := by
    simpa [R] using
      cycleSum_edgeNodeBalance
        R₁ R₂ hC₁ hC₂ hcommon c hc hspan hfac₁ hfac₂ hmeet
  have hnormalizedR :
      2 + 2 * (R.toHypermap).edgeOrbitCount =
        (R.toHypermap).edgeOrbitCount +
          (R.toHypermap).nodeOrbitCount +
          (R.toHypermap).faceOrbitCount := by
    omega
  apply Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight
  have heq :
      (R.toHypermap).eulerLeft =
        (R.toHypermap).eulerRight := by
    simpa [Hypermap.eulerLeft, Hypermap.eulerRight,
      hcompR, hdartR] using hnormalizedR
  exact heq.le

theorem cycleSum_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G₁ G₂ C : SimpleGraph V} {u : V}
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
    (hconn₁ : (R₁.toHypermap).Connected)
    (hconn₂ : (R₂.toHypermap).Connected)
    (hplanar₁ : (R₁.toHypermap).dual.EulerPlanar)
    (hplanar₂ : (R₂.toHypermap).dual.EulerPlanar) :
    ((cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet).toHypermap).dual.EulerPlanar := by
  rw [Hypermap.dual_eulerPlanar_iff] at hplanar₁ hplanar₂ ⊢
  exact cycleSum_eulerPlanar
    R₁ R₂ hC₁ hC₂ hcommon c hc hspan hfac₁ hfac₂ hmeet
      hconn₁ hconn₂ hplanar₁ hplanar₂


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
