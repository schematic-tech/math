import Schematic.Math.GraphTheory.Embedding.RotationSystemEdgeGluing.PointSum

/-! Planarity and marker-edge collapse for the two-point hypermap sum. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemEdgeGluing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
variable {x y : V}

theorem twoPointSum_connected
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hR₁ : R₁.toHypermap.Connected)
    (hR₂ : R₂.toHypermap.Connected) :
    (twoPointSum R₁ R₂ hxy₁ hxy₂).Connected := by
  apply Hypermap.nodeSplice_connected
  · exact Hypermap.onePointSum_connected _ _ _ _ hR₁ hR₂
  · exact firstPointSum_yPoints_node_separate R₁ R₂ hxy₁ hxy₂

theorem twoPointSum_eulerPlanar
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hR₁conn : R₁.toHypermap.Connected)
    (hR₂conn : R₂.toHypermap.Connected)
    (hR₁ : R₁.toHypermap.EulerPlanar)
    (hR₂ : R₂.toHypermap.EulerPlanar) :
    (twoPointSum R₁ R₂ hxy₁ hxy₂).EulerPlanar := by
  apply Hypermap.nodeSplice_eulerPlanar
  · exact Hypermap.onePointSum_connected _ _ _ _ hR₁conn hR₂conn
  · exact Hypermap.onePointSum_eulerPlanar _ _ _ _
      hR₁conn hR₂conn hR₁ hR₂
  · exact firstPointSum_yPoints_node_separate R₁ R₂ hxy₁ hxy₂
  · exact firstPointSum_yPredecessors_faceReachable R₁ R₂ hxy₁ hxy₂

theorem twoPointSum_plain
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    (twoPointSum R₁ R₂ hxy₁ hxy₂).Plain := by
  apply Hypermap.nodeSplice_plain
  exact Hypermap.onePointSum_plain _ _ _ _
    R₁.toHypermap_plain R₂.toHypermap_plain

/-- The right copy of the marker edge is the duplicate removed after the two
endpoint rotations have been merged. -/
noncomputable def duplicateMarker
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    (twoPointSum R₁ R₂ hxy₁ hxy₂).Dart :=
  Sum.inr (markerForward hxy₂)

noncomputable def duplicateOpposite
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    ((twoPointSum R₁ R₂ hxy₁ hxy₂).walkupF
      (duplicateMarker R₁ R₂ hxy₁ hxy₂)).Dart :=
  let K := twoPointSum R₁ R₂ hxy₁ hxy₂
  let z := duplicateMarker R₁ R₂ hxy₁ hxy₂
  ⟨K.edge z, Hypermap.Plain.edge_ne (G := K)
    (twoPointSum_plain R₁ R₂ hxy₁ hxy₂) z⟩

/-- Delete the redundant right marker pair from the planar two-point sum. -/
noncomputable def collapsedHypermap
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) : Hypermap.{u} :=
  let K := twoPointSum R₁ R₂ hxy₁ hxy₂
  let z := duplicateMarker R₁ R₂ hxy₁ hxy₂
  (K.walkupF z).walkupE (duplicateOpposite R₁ R₂ hxy₁ hxy₂)

theorem collapsedHypermap_eulerPlanar
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hR₁conn : R₁.toHypermap.Connected)
    (hR₂conn : R₂.toHypermap.Connected)
    (hR₁ : R₁.toHypermap.EulerPlanar)
    (hR₂ : R₂.toHypermap.EulerPlanar) :
    (collapsedHypermap R₁ R₂ hxy₁ hxy₂).EulerPlanar := by
  apply Unavoidability.walkupE_eulerPlanar_of_eulerPlanar
  exact Unavoidability.walkupF_eulerPlanar_of_eulerPlanar _ _
    (twoPointSum_eulerPlanar R₁ R₂ hxy₁ hxy₂
      hR₁conn hR₂conn hR₁ hR₂)

@[simp]
theorem duplicateOpposite_val
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    (duplicateOpposite R₁ R₂ hxy₁ hxy₂).1 =
      Sum.inr (markerBackward hxy₂) := by
  rfl

/-- Both endpoint splices preserve the graph vertex represented by a dart. -/
theorem twoPointSum_node_sumTail
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (d : (twoPointSum R₁ R₂ hxy₁ hxy₂).Dart) :
    RotationSystemGluing.sumTail
        ((twoPointSum R₁ R₂ hxy₁ hxy₂).node d) =
      RotationSystemGluing.sumTail d := by
  let K := firstPointSum R₁ R₂ hxy₁ hxy₂
  let a := leftYPoint R₁ R₂ hxy₁ hxy₂
  let b := rightYPoint R₁ R₂ hxy₁ hxy₂
  apply permSplice_preserves K.node RotationSystemGluing.sumTail
  · intro e
    exact RotationSystemGluing.splicedNode_tail
      R₁ R₂ x (markerForward hxy₁) (markerForward hxy₂)
      rfl rfl e
  · change
      (R₁.toHypermap.face (markerForward hxy₁)).tail =
        (R₂.toHypermap.face (markerForward hxy₂)).tail
    rw [leftYPoint_tail R₁ hxy₁, rightYPoint_tail R₂ hxy₂]

/-- Removing the duplicate marker pair preserves the tail vertex code. -/
theorem collapsedHypermap_node_sumTail
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (d : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart) :
    RotationSystemGluing.sumTail
        (((collapsedHypermap R₁ R₂ hxy₁ hxy₂).node d).1.1) =
      RotationSystemGluing.sumTail d.1.1 := by
  let K := twoPointSum R₁ R₂ hxy₁ hxy₂
  let z := duplicateMarker R₁ R₂ hxy₁ hxy₂
  let L := K.walkupF z
  let u := duplicateOpposite R₁ R₂ hxy₁ hxy₂
  have hK : forall e : K.Dart,
      RotationSystemGluing.sumTail (K.node e) =
        RotationSystemGluing.sumTail e :=
    twoPointSum_node_sumTail R₁ R₂ hxy₁ hxy₂
  have hL : forall e : L.Dart,
      RotationSystemGluing.sumTail ((L.node e).1) =
        RotationSystemGluing.sumTail e.1 := by
    intro e
    change
      RotationSystemGluing.sumTail
          (((PermSkip.skip K.node z e : L.Dart) : K.Dart)) =
        RotationSystemGluing.sumTail e.1
    exact PermSkip.skip_preserves K.node
      RotationSystemGluing.sumTail hK e
  change
    RotationSystemGluing.sumTail
        (PermSkip.skip L.node u d).1.1 =
      RotationSystemGluing.sumTail d.1.1
  exact PermSkip.skip_preserves L.node
    (fun e : L.Dart => RotationSystemGluing.sumTail e.1) hL d


end RotationSystemEdgeGluing
end FourColor
end Schematic.Math.GraphTheory
