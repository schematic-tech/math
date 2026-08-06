import Schematic.Math.GraphTheory.Embedding.RotationSystemEdgeGluing.DartEquivalence

/-! Node-orbit reachability after collapsing the duplicate edge. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemEdgeGluing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
variable {x y : V}

private theorem twoPointSum_node_reachable_inl_inr
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hattach : forall ⦃v : V⦄,
      v ∈ G₁.support -> v ∈ G₂.support -> v = x ∨ v = y)
    (e : OrientedEdge G₁) (f : OrientedEdge G₂)
    (hef : e.tail = f.tail) :
    PermReachable (twoPointSum R₁ R₂ hxy₁ hxy₂).node
      (Sum.inl e) (Sum.inr f) := by
  let H₁ := R₁.toHypermap
  let H₂ := R₂.toHypermap
  let B := Hypermap.disjointSum H₁ H₂
  let p : B.Dart := Sum.inl (markerForward hxy₁)
  let q : B.Dart := Sum.inr (markerForward hxy₂)
  let K := firstPointSum R₁ R₂ hxy₁ hxy₂
  let a : K.Dart := leftYPoint R₁ R₂ hxy₁ hxy₂
  let b : K.Dart := rightYPoint R₁ R₂ hxy₁ hxy₂
  have hsepX : ¬ PermReachable B.node p q :=
    Hypermap.disjointSum_node_pivots_separate H₁ H₂
      (markerForward hxy₁) (markerForward hxy₂)
  have hsepY : ¬ PermReachable K.node a b :=
    firstPointSum_yPoints_node_separate R₁ R₂ hxy₁ hxy₂
  have hwhere : e.tail = x ∨ e.tail = y :=
    hattach e.adj.left_mem_support
      (hef ▸ f.adj.left_mem_support)
  rcases hwhere with hex | hey
  · have heP : PermReachable B.node (Sum.inl e) p :=
      permSum_reachable_inl R₁.node R₂.node
        (R₁.node_orbit_of_same_tail e (markerForward hxy₁) hex)
    have hqF : PermReachable B.node q (Sum.inr f) :=
      permSum_reachable_inr R₁.node R₂.node
        (R₂.node_orbit_of_same_tail (markerForward hxy₂) f
          (hex.symm.trans hef))
    have heP' :=
      permSplice_reachable_of_old_reachable B.node p q hsepX heP
    have hpQ := permSplice_left_reachable_right B.node p q hsepX
    have hqF' :=
      permSplice_reachable_of_old_reachable B.node p q hsepX hqF
    exact permSplice_reachable_of_old_reachable K.node a b hsepY
      (PermReachable.trans K.node heP'
        (PermReachable.trans K.node hpQ hqF'))
  · have heAOld :
        PermReachable B.node (Sum.inl e)
          (Sum.inl (H₁.face (markerForward hxy₁))) :=
      permSum_reachable_inl R₁.node R₂.node
        (R₁.node_orbit_of_same_tail e
          (H₁.face (markerForward hxy₁))
          (hey.trans (leftYPoint_tail R₁ hxy₁).symm))
    have hbFOld :
        PermReachable B.node
          (Sum.inr (H₂.face (markerForward hxy₂))) (Sum.inr f) :=
      permSum_reachable_inr R₁.node R₂.node
        (R₂.node_orbit_of_same_tail
          (H₂.face (markerForward hxy₂)) f
          ((rightYPoint_tail R₂ hxy₂).trans
            (hey.symm.trans hef)))
    have heA :=
      permSplice_reachable_of_old_reachable B.node p q hsepX heAOld
    have hbF :=
      permSplice_reachable_of_old_reachable B.node p q hsepX hbFOld
    have heA' :=
      permSplice_reachable_of_old_reachable K.node a b hsepY heA
    have haB := permSplice_left_reachable_right K.node a b hsepY
    have hbF' :=
      permSplice_reachable_of_old_reachable K.node a b hsepY hbF
    exact PermReachable.trans _ heA'
      (PermReachable.trans _ haB hbF')

/-- After the two endpoint merges, all summand darts with a common tail lie
in one node orbit. -/
theorem twoPointSum_node_reachable_of_same_tail
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hattach : forall ⦃v : V⦄,
      v ∈ G₁.support -> v ∈ G₂.support -> v = x ∨ v = y)
    (e f : (twoPointSum R₁ R₂ hxy₁ hxy₂).Dart)
    (hef : RotationSystemGluing.sumTail e =
      RotationSystemGluing.sumTail f) :
    PermReachable (twoPointSum R₁ R₂ hxy₁ hxy₂).node e f := by
  let H₁ := R₁.toHypermap
  let H₂ := R₂.toHypermap
  let B := Hypermap.disjointSum H₁ H₂
  let p : B.Dart := Sum.inl (markerForward hxy₁)
  let q : B.Dart := Sum.inr (markerForward hxy₂)
  let K := firstPointSum R₁ R₂ hxy₁ hxy₂
  let a : K.Dart := leftYPoint R₁ R₂ hxy₁ hxy₂
  let b : K.Dart := rightYPoint R₁ R₂ hxy₁ hxy₂
  have hsepX : ¬ PermReachable B.node p q :=
    Hypermap.disjointSum_node_pivots_separate H₁ H₂
      (markerForward hxy₁) (markerForward hxy₂)
  have hsepY : ¬ PermReachable K.node a b :=
    firstPointSum_yPoints_node_separate R₁ R₂ hxy₁ hxy₂
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          apply permSplice_reachable_of_old_reachable K.node a b hsepY
          apply permSplice_reachable_of_old_reachable B.node p q hsepX
          exact permSum_reachable_inl R₁.node R₂.node
            (R₁.node_orbit_of_same_tail e f hef)
      | inr f =>
          exact twoPointSum_node_reachable_inl_inr R₁ R₂
            hxy₁ hxy₂ hattach e f hef
  | inr e =>
      cases f with
      | inl f =>
          exact PermReachable.symm _
            (twoPointSum_node_reachable_inl_inr R₁ R₂
              hxy₁ hxy₂ hattach f e hef.symm)
      | inr f =>
          apply permSplice_reachable_of_old_reachable K.node a b hsepY
          apply permSplice_reachable_of_old_reachable B.node p q hsepX
          exact permSum_reachable_inr R₁.node R₂.node
            (R₂.node_orbit_of_same_tail e f hef)

theorem collapsedHypermap_node_reachable_of_same_tail
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hattach : forall ⦃v : V⦄,
      v ∈ G₁.support -> v ∈ G₂.support -> v = x ∨ v = y)
    (e f : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart)
    (hef : RotationSystemGluing.sumTail e.1.1 =
      RotationSystemGluing.sumTail f.1.1) :
    PermReachable (collapsedHypermap R₁ R₂ hxy₁ hxy₂).node e f := by
  let K := twoPointSum R₁ R₂ hxy₁ hxy₂
  let z := duplicateMarker R₁ R₂ hxy₁ hxy₂
  let L := K.walkupF z
  let u := duplicateOpposite R₁ R₂ hxy₁ hxy₂
  have hK : PermReachable K.node e.1.1 f.1.1 :=
    twoPointSum_node_reachable_of_same_tail R₁ R₂
      hxy₁ hxy₂ hattach e.1.1 f.1.1 hef
  have hL : PermReachable L.node e.1 f.1 := by
    change PermReachable (PermSkip.skip K.node z) e.1 f.1
    exact PermSkip.skip_permReachable_of_permReachable K.node hK
  change PermReachable (PermSkip.skip L.node u) e f
  exact PermSkip.skip_permReachable_of_permReachable L.node hL

noncomputable def collapsedNode
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x)) :
    Equiv.Perm (OrientedEdge (G₁ ⊔ G₂)) :=
  let E := collapsedDartEquiv R₁ R₂ hxy₁ hxy₂ hcommon
  ((E.symm.trans (collapsedHypermap R₁ R₂ hxy₁ hxy₂).node).trans E)


end RotationSystemEdgeGluing
end FourColor
end Schematic.Math.GraphTheory
