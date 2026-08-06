import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FaceRemainders

/-! Orbit counts and Euler balances for cycle sums. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

theorem cycleSplicedHypermap_faceOrbitCount
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
        hfac₁ hfac₂).faceOrbitCount + 2 =
      (R₁.toHypermap).faceOrbitCount +
        (R₂.toHypermap).faceOrbitCount := by
  classical
  unfold Hypermap.faceOrbitCount
  rw [Nat.card_congr
    (cycleSplicedFaceOrbitEquiv
      R₁ R₂ hC₁ hC₂ c hc hspan hfac₁ hfac₂)]
  have hleft :
      Nat.card
          {o : (R₁.toHypermap).FaceOrbit //
            o ≠ selectedCycleFace R₁
              (c.mapLe hC₁) (hc.mapLe hC₁)} + 1 =
        Nat.card (R₁.toHypermap).FaceOrbit := by
    simpa using
      Nat.card_congr
        (Equiv.optionSubtypeNe
          (selectedCycleFace R₁ (c.mapLe hC₁) (hc.mapLe hC₁)))
  have hright :
      Nat.card
          {o : (R₂.toHypermap).FaceOrbit //
            o ≠ selectedCycleFace R₂ (c.mapLe hC₂).reverse
              (hc.mapLe hC₂).reverse} + 1 =
        Nat.card (R₂.toHypermap).FaceOrbit := by
    simpa using
      Nat.card_congr
        (Equiv.optionSubtypeNe
          (selectedCycleFace R₂ (c.mapLe hC₂).reverse
            (hc.mapLe hC₂).reverse))
  simp only [Nat.card_sum]
  omega

theorem edgeFinset_card_eq_support_card_of_isCycles
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcycles : G.IsCycles) :
    G.edgeFinset.card = Fintype.card G.support := by
  classical
  have hdegree :
      ∀ v : V, v ∈ G.support → G.degree v = 2 := by
    intro v hv
    have hnonempty : (G.neighborSet v).Nonempty :=
      G.degree_pos_iff_nonempty.mp
        ((G.degree_pos_iff_mem_support v).mpr hv)
    rw [← G.card_neighborSet_eq_degree]
    simpa [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
      hcycles hnonempty
  have hsum := G.sum_degrees_support_eq_twice_card_edges
  have hdouble :
      2 * G.support.toFinset.card =
        2 * G.edgeFinset.card := by
    calc
      2 * G.support.toFinset.card =
          ∑ v ∈ G.support, 2 := by
            simp [Nat.mul_comm]
      _ = ∑ v ∈ G.support, G.degree v := by
            apply Finset.sum_congr rfl
            intro v hv
            exact (hdegree v (by simpa using hv)).symm
      _ = 2 * G.edgeFinset.card := hsum
  rw [Set.toFinset_card] at hdouble
  omega

theorem cycleSum_edgeNodeBalance
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
    ((cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
        hfac₁ hfac₂ hmeet).toHypermap).edgeOrbitCount +
          (R₁.toHypermap).nodeOrbitCount +
          (R₂.toHypermap).nodeOrbitCount =
      (R₁.toHypermap).edgeOrbitCount +
        (R₂.toHypermap).edgeOrbitCount +
        ((cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
          hfac₁ hfac₂ hmeet).toHypermap).nodeOrbitCount := by
  classical
  let R :=
    cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet
  have hinf : G₁ ⊓ G₂ = C := by
    apply le_antisymm
    · intro x y hxy
      exact hcommon hxy.1 hxy.2
    · exact le_inf hC₁ hC₂
  have hedge :
      (G₁ ⊔ G₂).edgeFinset.card + C.edgeFinset.card =
        G₁.edgeFinset.card + G₂.edgeFinset.card := by
    have hinter :
        G₁.edgeFinset ∩ G₂.edgeFinset = C.edgeFinset := by
      apply Finset.coe_injective
      simp only [Finset.coe_inter, SimpleGraph.coe_edgeFinset]
      rw [← SimpleGraph.edgeSet_inf, hinf]
    rw [SimpleGraph.edgeFinset_sup, ← hinter]
    exact
      Finset.card_union_add_card_inter
        G₁.edgeFinset G₂.edgeFinset
  have hsupportInter :
      G₁.support.toFinset ∩ G₂.support.toFinset =
        c.support.toFinset := by
    ext v
    simp only [Finset.mem_inter, Set.mem_toFinset, List.mem_toFinset]
    constructor
    · rintro ⟨hv₁, hv₂⟩
      exact hmeet hv₁ hv₂
    · intro hv
      have hvC : v ∈ C.support :=
        SimpleGraph.mem_support_of_mem_walk_support c hc.not_nil hv
      exact
        ⟨SimpleGraph.support_mono hC₁ hvC,
          SimpleGraph.support_mono hC₂ hvC⟩
  have hsupportUnion :
      (G₁ ⊔ G₂).support.toFinset =
        G₁.support.toFinset ∪ G₂.support.toFinset := by
    ext v
    simp only [Set.mem_toFinset, Finset.mem_union]
    constructor
    · intro hv
      rcases (SimpleGraph.mem_support (G := G₁ ⊔ G₂)).mp hv with
        ⟨w, hvw⟩
      rcases (SimpleGraph.sup_adj G₁ G₂ v w).mp hvw with hvw₁ | hvw₂
      · exact Or.inl
          ((SimpleGraph.mem_support (G := G₁)).mpr ⟨w, hvw₁⟩)
      · exact Or.inr
          ((SimpleGraph.mem_support (G := G₂)).mpr ⟨w, hvw₂⟩)
    · rintro (hv | hv)
      · exact SimpleGraph.support_mono le_sup_left hv
      · exact SimpleGraph.support_mono le_sup_right hv
  have hcycleSupport :
      C.support.toFinset = c.support.toFinset := by
    apply Finset.Subset.antisymm
    · intro v hv
      have hvC : v ∈ C.support := by simpa using hv
      rcases (SimpleGraph.mem_support (G := C)).mp hvC with ⟨w, hvw⟩
      have hvw' :
          c.toSubgraph.spanningCoe.Adj v w := by
        simpa [hspan] using hvw
      rw [SimpleGraph.Subgraph.spanningCoe_adj,
        SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] at hvw'
      exact List.mem_toFinset.mpr
        (c.fst_mem_support_of_mem_edges hvw')
    · intro v hv
      have hv' : v ∈ c.support := by simpa using hv
      exact Set.mem_toFinset.mpr
        (SimpleGraph.mem_support_of_mem_walk_support c hc.not_nil hv')
  have hsupport :
      Fintype.card (G₁ ⊔ G₂).support + Fintype.card C.support =
        Fintype.card G₁.support + Fintype.card G₂.support := by
    rw [← Set.toFinset_card, ← Set.toFinset_card,
      ← Set.toFinset_card, ← Set.toFinset_card,
      hsupportUnion, hcycleSupport, ← hsupportInter]
    exact
      Finset.card_union_add_card_inter
        G₁.support.toFinset G₂.support.toFinset
  have hcycleGraph : C.IsCycles := by
    rw [← hspan]
    exact hc.isCycles_spanningCoe_toSubgraph
  have hcycleCard :
      C.edgeFinset.card = Fintype.card C.support :=
    edgeFinset_card_eq_support_card_of_isCycles C hcycleGraph
  have hbalance :
      (G₁ ⊔ G₂).edgeFinset.card +
            Fintype.card G₁.support + Fintype.card G₂.support =
        G₁.edgeFinset.card + G₂.edgeFinset.card +
          Fintype.card (G₁ ⊔ G₂).support := by
    calc
      (G₁ ⊔ G₂).edgeFinset.card +
              Fintype.card G₁.support + Fintype.card G₂.support =
          (G₁ ⊔ G₂).edgeFinset.card +
            (Fintype.card G₁.support + Fintype.card G₂.support) := by
              omega
      _ = (G₁ ⊔ G₂).edgeFinset.card +
            (Fintype.card (G₁ ⊔ G₂).support +
              Fintype.card C.support) := by
              rw [← hsupport]
      _ = ((G₁ ⊔ G₂).edgeFinset.card +
              Fintype.card C.support) +
            Fintype.card (G₁ ⊔ G₂).support := by
              omega
      _ = ((G₁ ⊔ G₂).edgeFinset.card + C.edgeFinset.card) +
            Fintype.card (G₁ ⊔ G₂).support := by
              rw [hcycleCard]
      _ = (G₁.edgeFinset.card + G₂.edgeFinset.card) +
            Fintype.card (G₁ ⊔ G₂).support := by
              rw [hedge]
  rw [R.edgeOrbitCount_eq_edgeFinset_card,
    R.nodeOrbitCount_eq_support_card,
    R₁.edgeOrbitCount_eq_edgeFinset_card,
    R₂.edgeOrbitCount_eq_edgeFinset_card,
    R₁.nodeOrbitCount_eq_support_card,
    R₂.nodeOrbitCount_eq_support_card]
  simpa using hbalance

theorem cycleSum_connected
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
    (hconn₂ : (R₂.toHypermap).Connected) :
    ((cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet).toHypermap).Connected := by
  let R :=
    cycleSum R₁ R₂ hC₁ hC₂ hcommon c hc hspan
      hfac₁ hfac₂ hmeet
  let a : OrientedEdge C := cycleFirstDart c hc
  let a₁ : OrientedEdge G₁ := liftOrientedEdge hC₁ a
  let a₂ : OrientedEdge G₂ := liftOrientedEdge hC₂ a
  let aU : OrientedEdge (G₁ ⊔ G₂) :=
    liftOrientedEdge (hC₁.trans le_sup_left) a
  letI : Nonempty (OrientedEdge (G₁ ⊔ G₂)) := ⟨aU⟩
  apply R.toHypermap_connected_of_tail_reachable
  intro e f
  rcases (SimpleGraph.sup_adj G₁ G₂ e.tail e.head).mp e.adj with he₁ | he₂
  · let e₁ : OrientedEdge G₁ := ⟨(e.tail, e.head), he₁⟩
    rcases (SimpleGraph.sup_adj G₁ G₂ f.tail f.head).mp f.adj with hf₁ | hf₂
    · let f₁ : OrientedEdge G₁ := ⟨(f.tail, f.head), hf₁⟩
      have hreach :
          G₁.Reachable e₁.tail f₁.tail :=
        R₁.toHypermap_reachable_tail_reachable
          (hconn₁.reachable R₁.toHypermap e₁ f₁)
      exact hreach.mono le_sup_left
    · let f₂ : OrientedEdge G₂ := ⟨(f.tail, f.head), hf₂⟩
      have hleft :
          G₁.Reachable e₁.tail a₁.tail :=
        R₁.toHypermap_reachable_tail_reachable
          (hconn₁.reachable R₁.toHypermap e₁ a₁)
      have hright :
          G₂.Reachable a₂.tail f₂.tail :=
        R₂.toHypermap_reachable_tail_reachable
          (hconn₂.reachable R₂.toHypermap a₂ f₂)
      exact (hleft.mono le_sup_left).trans (by
        simpa [a₁, a₂, liftOrientedEdge_tail] using
          hright.mono le_sup_right)
  · let e₂ : OrientedEdge G₂ := ⟨(e.tail, e.head), he₂⟩
    rcases (SimpleGraph.sup_adj G₁ G₂ f.tail f.head).mp f.adj with hf₁ | hf₂
    · let f₁ : OrientedEdge G₁ := ⟨(f.tail, f.head), hf₁⟩
      have hleft :
          G₂.Reachable e₂.tail a₂.tail :=
        R₂.toHypermap_reachable_tail_reachable
          (hconn₂.reachable R₂.toHypermap e₂ a₂)
      have hright :
          G₁.Reachable a₁.tail f₁.tail :=
        R₁.toHypermap_reachable_tail_reachable
          (hconn₁.reachable R₁.toHypermap a₁ f₁)
      exact (hleft.mono le_sup_right).trans (by
        simpa [a₁, a₂, liftOrientedEdge_tail] using
          hright.mono le_sup_left)
    · let f₂ : OrientedEdge G₂ := ⟨(f.tail, f.head), hf₂⟩
      have hreach :
          G₂.Reachable e₂.tail f₂.tail :=
        R₂.toHypermap_reachable_tail_reachable
          (hconn₂.reachable R₂.toHypermap e₂ f₂)
      exact hreach.mono le_sup_right


end RotationSystemGluing

end FourColor

end Schematic.Math.GraphTheory
