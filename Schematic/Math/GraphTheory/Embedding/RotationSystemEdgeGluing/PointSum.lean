import Schematic.Math.GraphTheory.Embedding.RotationSystemDeletion
import Schematic.Math.GraphTheory.Embedding.RotationSystemGluing

/-!
Two-vertex gluing for graph rotation systems.

This is the Lean counterpart of Coq
`embedding.v::smerge_plane_embedding_disconnected'` followed by
`smerge_plane_embedding_face`, as used by
`wagner.v::edge_plane_embedding`.  We first keep both copies of a common
marker edge, merge the two endpoint rotations while retaining the marked
face, and then delete one duplicate marker pair before transporting to the
simple graph union.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemEdgeGluing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
variable {x y : V}

abbrev markerForward (hxy : G₁.Adj x y) : OrientedEdge G₁ :=
  EdgeDeletion.forwardDart hxy

abbrev markerBackward (hxy : G₁.Adj x y) : OrientedEdge G₁ :=
  EdgeDeletion.backwardDart hxy

/-- The first endpoint merge, using the two forward marker darts. -/
noncomputable def firstPointSum
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) : Hypermap.{u} :=
  Hypermap.onePointSum R₁.toHypermap R₂.toHypermap
    (markerForward hxy₁) (markerForward hxy₂)

/-- The marker-face successor in the left summand has tail `y` and is the
left pivot for the second endpoint merge. -/
noncomputable def leftYPoint
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    (firstPointSum R₁ R₂ hxy₁ hxy₂).Dart :=
  Sum.inl (R₁.toHypermap.face (markerForward hxy₁))

/-- Right marker-face successor used at the second endpoint. -/
noncomputable def rightYPoint
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    (firstPointSum R₁ R₂ hxy₁ hxy₂).Dart :=
  Sum.inr (R₂.toHypermap.face (markerForward hxy₂))

@[simp]
theorem leftYPoint_tail
    (R₁ : RotationSystem G₁) (hxy₁ : G₁.Adj x y) :
    (R₁.toHypermap.face (markerForward hxy₁)).tail = y := by
  simp [markerForward]

@[simp]
theorem rightYPoint_tail
    (R₂ : RotationSystem G₂) (hxy₂ : G₂.Adj x y) :
    (R₂.toHypermap.face (markerForward hxy₂)).tail = y := by
  simp [markerForward]

/-- Merge the `y`-rotations at the two points retained on the marker face. -/
noncomputable def twoPointSum
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) : Hypermap.{u} :=
  Hypermap.nodeSplice (firstPointSum R₁ R₂ hxy₁ hxy₂)
    (leftYPoint R₁ R₂ hxy₁ hxy₂)
    (rightYPoint R₁ R₂ hxy₁ hxy₂)

omit [Fintype V] [DecidableEq V]
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
private theorem permSum_node_not_reachable_inr_inl
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (a : OrientedEdge G₂) (b : OrientedEdge G₁) :
    ¬ PermReachable (permSum R₁.node R₂.node) (Sum.inr a) (Sum.inl b) := by
  intro h
  have hcode := permSumOrbitCode_of_reachable R₁.node R₂.node h
  simp [permSumOrbitCode] at hcode

omit [Fintype V] [DecidableEq V]
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
private theorem permSum_node_not_reachable_inr_of_tail_ne
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (a b : OrientedEdge G₂) (hab : a.tail ≠ b.tail) :
    ¬ PermReachable (permSum R₁.node R₂.node) (Sum.inr a) (Sum.inr b) := by
  intro h
  have hcode := permSumOrbitCode_of_reachable R₁.node R₂.node h
  have horbit : PermOrbit.of R₂.node a = PermOrbit.of R₂.node b :=
    Sum.inr.inj hcode
  have hreach : PermReachable R₂.node a b := Quotient.exact horbit
  exact hab (R₂.node_reachable_tail hreach).symm

/-- The two `y` node cycles are still distinct after only the `x` merge. -/
theorem firstPointSum_yPoints_node_separate
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    ¬ PermReachable (firstPointSum R₁ R₂ hxy₁ hxy₂).node
      (leftYPoint R₁ R₂ hxy₁ hxy₂)
      (rightYPoint R₁ R₂ hxy₁ hxy₂) := by
  let H₁ := R₁.toHypermap
  let H₂ := R₂.toHypermap
  let B := Hypermap.disjointSum H₁ H₂
  let p : B.Dart := Sum.inl (markerForward hxy₁)
  let q : B.Dart := Sum.inr (markerForward hxy₂)
  let a : B.Dart := Sum.inl (H₁.face (markerForward hxy₁))
  let b : B.Dart := Sum.inr (H₂.face (markerForward hxy₂))
  have hsep : ¬ PermReachable B.node p q :=
    Hypermap.disjointSum_node_pivots_separate H₁ H₂
      (markerForward hxy₁) (markerForward hxy₂)
  have hqa : ¬ PermReachable B.node q a := by
    exact permSum_node_not_reachable_inr_inl R₁ R₂ _ _
  have hqb : ¬ PermReachable B.node q b := by
    apply permSum_node_not_reachable_inr_of_tail_ne R₁ R₂
    simpa [q, b, H₂, markerForward] using hxy₂.ne
  intro hab
  change PermReachable (permSplice B.node p q) a b at hab
  have hcode :=
    permSpliceOrbitCode_of_reachable B.node p q hsep hab
  have hval := congrArg Subtype.val hcode
  simp only [permSpliceOrbitCode, hqa, hqb, dite_false] at hval
  change PermOrbit.of B.node a = PermOrbit.of B.node b at hval
  have hold : PermReachable B.node a b := Quotient.exact hval
  exact
    (Hypermap.disjointSum_node_pivots_separate H₁ H₂
      (H₁.face (markerForward hxy₁))
      (H₂.face (markerForward hxy₂))) hold

/-- The face retained by the first merge contains both marker-face
successors at `y`. -/
theorem firstPointSum_yPoints_faceReachable
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    PermReachable (firstPointSum R₁ R₂ hxy₁ hxy₂).face
      (leftYPoint R₁ R₂ hxy₁ hxy₂)
      (rightYPoint R₁ R₂ hxy₁ hxy₂) := by
  let H₁ := R₁.toHypermap
  let H₂ := R₂.toHypermap
  let B := Hypermap.disjointSum H₁ H₂
  let p : B.Dart := Sum.inl (markerForward hxy₁)
  let q : B.Dart := Sum.inr (markerForward hxy₂)
  let fp : B.Dart := B.face.symm p
  let fq : B.Dart := B.face.symm q
  have hsep : ¬ PermReachable B.face fp fq := by
    simpa [fp, fq, p, q, B, H₁, H₂] using
      Hypermap.disjointSum_face_pivots_separate H₁ H₂
        (H₁.face.symm (markerForward hxy₁))
        (H₂.face.symm (markerForward hxy₂))
  have hleftOld :
      PermReachable B.face
        (Sum.inl (H₁.face (markerForward hxy₁))) fp := by
    apply permSum_reachable_inl H₁.face H₂.face
    have hback :
        PermReachable H₁.face (H₁.face (markerForward hxy₁))
          (markerForward hxy₁) := by
      simpa using
        PermReachable.backward H₁.face (H₁.face (markerForward hxy₁))
    exact PermReachable.trans H₁.face hback
      (PermReachable.backward H₁.face (markerForward hxy₁))
  have hrightOld :
      PermReachable B.face fq
        (Sum.inr (H₂.face (markerForward hxy₂))) := by
    apply PermReachable.symm B.face
    apply permSum_reachable_inr H₁.face H₂.face
    have hback :
        PermReachable H₂.face (H₂.face (markerForward hxy₂))
          (markerForward hxy₂) := by
      simpa using
        PermReachable.backward H₂.face (H₂.face (markerForward hxy₂))
    exact PermReachable.trans H₂.face hback
      (PermReachable.backward H₂.face (markerForward hxy₂))
  change
    PermReachable
      (Hypermap.onePointSum H₁ H₂
        (markerForward hxy₁) (markerForward hxy₂)).face
      (Sum.inl (H₁.face (markerForward hxy₁)))
      (Sum.inr (H₂.face (markerForward hxy₂)))
  rw [Hypermap.onePointSum_face_eq_splice]
  exact PermReachable.trans _
    (permSplice_reachable_of_old_reachable B.face fp fq hsep hleftOld)
    (PermReachable.trans _
      (permSplice_left_reachable_right B.face fp fq hsep)
      (permSplice_reachable_of_old_reachable B.face fp fq hsep hrightOld))

theorem firstPointSum_yPredecessors_faceReachable
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    let K := firstPointSum R₁ R₂ hxy₁ hxy₂
    let a := leftYPoint R₁ R₂ hxy₁ hxy₂
    let b := rightYPoint R₁ R₂ hxy₁ hxy₂
    PermReachable K.face (K.face.symm a) (K.face.symm b) := by
  dsimp only
  let K := firstPointSum R₁ R₂ hxy₁ hxy₂
  let a := leftYPoint R₁ R₂ hxy₁ hxy₂
  let b := rightYPoint R₁ R₂ hxy₁ hxy₂
  exact PermReachable.trans K.face
    (by simpa using PermReachable.forward K.face (K.face.symm a))
    (PermReachable.trans K.face
      (firstPointSum_yPoints_faceReachable R₁ R₂ hxy₁ hxy₂)
      (PermReachable.backward K.face b))


end RotationSystemEdgeGluing
end FourColor
end Schematic.Math.GraphTheory
