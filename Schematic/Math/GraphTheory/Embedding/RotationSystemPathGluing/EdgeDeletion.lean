import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing.FacialCycles
import Schematic.Math.GraphTheory.Embedding.RotationSystemDeletion

/-!
Facial-path gluing support for graph rotation systems.

The cycle-sum construction removes one selected face from each summand.  The
other face orbits are already classified in `RotationSystemCycleGluing`; this
file packages the consequence needed for gluing disk societies along a common
boundary path: a facial cycle in the left summand remains facial provided none
of its forward darts belongs to the selected gluing face.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

/-- In the non-cross branch of `walkupE`, the new edge orbit through an
affected surviving dart consists exactly of the two old edge orbits touched
by the deletion.  Applied to `G.permFace`, this is the statement that deleting
one side of an ordinary edge merges exactly its two incident faces. -/
theorem Hypermap.walkupE_nonCross_edgePermReachable_iff_edgeDomain
    (G : Hypermap.{u}) {z : G.Dart}
    (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {x : (G.walkupE z).Dart}
    (hxdom : G.EdgeDomain z x.1)
    (y : (G.walkupE z).Dart) :
    PermReachable (G.walkupE z).edge x y ↔ G.EdgeDomain z y.1 := by
  classical
  let F := G.walkupENonCrossEdgeOrbitLift hz hncross
  have horbit (w : (G.walkupE z).Dart) :
      PermOrbit.of (G.walkupE z).edge w =
        F (PermOrbit.of G.edge w.1) := by
    change
      PermOrbit.of (G.walkupE z).edge w =
        G.walkupENonCrossEdgeOrbitLift hz hncross
          (PermOrbit.of G.edge w.1)
    rw [G.walkupENonCrossEdgeOrbitLift_of,
      G.walkupENonSelfEdgeRepresentative_of_ne hz w.2]
    congr 1
  have hxAffected :
      F (PermOrbit.of G.edge x.1) = F (PermOrbit.of G.edge z) :=
    G.walkupENonCrossEdgeOrbitLift_eq_of_edgeDomain hz hncross hxdom
  constructor
  · intro hxy
    by_contra hydom
    apply
      G.walkupENonCrossEdgeOrbitLift_ne_z_of_not_edgeDomain
        hz hncross hydom
    calc
      F (PermOrbit.of G.edge y.1) =
          PermOrbit.of (G.walkupE z).edge y := (horbit y).symm
      _ = PermOrbit.of (G.walkupE z).edge x :=
        PermOrbit.of_eq_of (G.walkupE z).edge
          (PermReachable.symm (G.walkupE z).edge hxy)
      _ = F (PermOrbit.of G.edge x.1) := horbit x
      _ = F (PermOrbit.of G.edge z) := hxAffected
  · intro hydom
    have hyAffected :
        F (PermOrbit.of G.edge y.1) = F (PermOrbit.of G.edge z) :=
      G.walkupENonCrossEdgeOrbitLift_eq_of_edgeDomain hz hncross hydom
    exact Quotient.exact (show
      PermOrbit.of (G.walkupE z).edge x =
        PermOrbit.of (G.walkupE z).edge y from
      calc
        PermOrbit.of (G.walkupE z).edge x =
            F (PermOrbit.of G.edge x.1) := horbit x
        _ = F (PermOrbit.of G.edge z) := hxAffected
        _ = F (PermOrbit.of G.edge y.1) := hyAffected.symm
        _ = PermOrbit.of (G.walkupE z).edge y := (horbit y).symm)

namespace EdgeDeletion

/-- The dart beginning a facial cycle is not self-linked in the face-cyclic
hypermap.  The three possible self-links are excluded respectively by the
edge's distinct endpoints, plainness of graph darts, and the opposite
orientation at the same facial-cycle vertex. -/
theorem permFace_forwardDart_not_link_self_of_facialCycle_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b r : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (d : G.Walk r r) (hd : d.IsCycle)
    (hfac : RotationSystemGluing.IsFacialCycle R d hd)
    (hfirst : cycleFirstDart d hd = forwardDart hab) :
    ¬ (R.toHypermap.permFace).Link
      (forwardDart hab) (forwardDart hab) := by
  intro hlink
  change
    forwardDart hab = R.toHypermap.face (forwardDart hab) ∨
      forwardDart hab = R.toHypermap.edge (forwardDart hab) ∨
        forwardDart hab = R.toHypermap.node (forwardDart hab) at hlink
  rcases hlink with hface | hedge | hnode
  · have htail := congrArg OrientedEdge.tail hface
    have habEq : a = b := by
      simpa [forwardDart, RotationSystem.toHypermap_face_tail] using htail
    exact hab.ne habEq
  · exact Hypermap.Plain.edge_ne (G := R.toHypermap)
      R.toHypermap_plain (forwardDart hab) hedge.symm
  · have hzForward : CycleForwardDart d (forwardDart hab) := by
      rw [← hfirst]
      exact cycleForwardDart_first d hd
    have hzBackward :
        CycleBackwardDart d (R.node (forwardDart hab)) :=
      hfac.node_forward_backward hzForward
    change forwardDart hab = R.node (forwardDart hab) at hnode
    rw [← hnode] at hzBackward
    exact cycleForwardDart_not_backward hd hzForward hzBackward

/-- Two disjoint facial cycles beginning with the two orientations of an edge
show that the edge has two distinct incident faces. -/
theorem permFace_forwardDart_not_cross_of_two_facialCycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b r₁ r₂ : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (d₁ : G.Walk r₁ r₁) (hd₁ : d₁.IsCycle)
    (d₂ : G.Walk r₂ r₂) (hd₂ : d₂.IsCycle)
    (hfac₁ : RotationSystemGluing.IsFacialCycle R d₁ hd₁)
    (hfirst₁ : cycleFirstDart d₁ hd₁ = forwardDart hab)
    (hfirst₂ :
      cycleFirstDart d₂ hd₂ = (forwardDart hab).symm)
    (hdisjoint :
      ∀ e : OrientedEdge G,
        CycleForwardDart d₁ e → ¬ CycleForwardDart d₂ e) :
    ¬ (R.toHypermap.permFace).CrossEdge (forwardDart hab) := by
  intro hcross
  have hsecondForward :
      CycleForwardDart d₂ ((forwardDart hab).symm) := by
    rw [← hfirst₂]
    exact cycleForwardDart_first d₂ hd₂
  have hfirstAlso :
      CycleForwardDart d₁ ((forwardDart hab).symm) := by
    apply (hfac₁ ((forwardDart hab).symm)).mpr
    rw [hfirst₁]
    simpa [Hypermap.permFace, RotationSystem.toHypermap] using hcross
  exact hdisjoint _ hfirstAlso hsecondForward

/-- Face-orbit description for deleting an ordinary graph edge.  If the two
incident faces are distinct, the restricted face through an affected dart is
exactly their union, with the two deleted edge darts removed. -/
theorem restrictedHypermap_facePermReachable_iff_edgeDomain
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hz :
      ¬ (R.toHypermap.permFace).Link
        (forwardDart hab) (forwardDart hab))
    (hncross :
      ¬ (R.toHypermap.permFace).CrossEdge (forwardDart hab))
    {x : (restrictedHypermap R hab).Dart}
    (hxdom :
      (R.toHypermap.permFace).EdgeDomain
        (forwardDart hab) x.1.1)
    (y : (restrictedHypermap R hab).Dart) :
    PermReachable (restrictedHypermap R hab).face x y ↔
      (R.toHypermap.permFace).EdgeDomain
        (forwardDart hab) y.1.1 := by
  let K := R.toHypermap.permFace
  let z : K.Dart := forwardDart hab
  change
    PermReachable
        (((R.toHypermap).walkupF (forwardDart hab)).walkupE
          (walkupFOppositeDart R hab)).face x y ↔
      K.EdgeDomain z y.1.1
  rw [(R.toHypermap.walkupF (forwardDart hab)).walkupE_facePermReachable_iff]
  change
    PermReachable (K.walkupE z).edge x.1 y.1 ↔
      K.EdgeDomain z y.1.1
  exact K.walkupE_nonCross_edgePermReachable_iff_edgeDomain
    hz hncross hxdom y.1

/-- Graph-rotation form of
`restrictedHypermap_facePermReachable_iff_edgeDomain`. -/
theorem restrictedRotationSystem_facePermReachable_iff_edgeDomain
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hz :
      ¬ (R.toHypermap.permFace).Link
        (forwardDart hab) (forwardDart hab))
    (hncross :
      ¬ (R.toHypermap.permFace).CrossEdge (forwardDart hab))
    {e : OrientedEdge (deletedGraph G a b)}
    (hedom :
      (R.toHypermap.permFace).EdgeDomain
        (forwardDart hab) (sourceDart e))
    (f : OrientedEdge (deletedGraph G a b)) :
    PermReachable
        ((restrictedRotationSystem R hab).toHypermap).face e f ↔
      (R.toHypermap.permFace).EdgeDomain
        (forwardDart hab) (sourceDart f) := by
  let φ := restrictedHypermapIso R hab
  let x := φ.toEquiv.symm e
  let y := φ.toEquiv.symm f
  have hxSource : x.1.1 = sourceDart e := by
    exact restrictedDartEquiv_symm_source R hab e
  have hySource : y.1.1 = sourceDart f := by
    exact restrictedDartEquiv_symm_source R hab f
  have hxdom :
      (R.toHypermap.permFace).EdgeDomain
        (forwardDart hab) x.1.1 := by
    simpa [hxSource] using hedom
  have hdelete :=
    restrictedHypermap_facePermReachable_iff_edgeDomain
      R hab hz hncross hxdom y
  have hiso := φ.faceReachable_iff (x := x) (y := y)
  have hxe : φ.toEquiv x = e := φ.toEquiv.apply_symm_apply e
  have hyf : φ.toEquiv y = f := φ.toEquiv.apply_symm_apply f
  rw [hxe, hyf] at hiso
  exact hiso.symm.trans (by simpa [hySource] using hdelete)

/-- A cycle in the edge-deleted graph is facial when its directed darts are
exactly the surviving darts of the two old faces incident with the deleted
edge. -/
theorem restrictedRotationSystem_isFacialCycle_of_forward_iff_edgeDomain
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b r : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hz :
      ¬ (R.toHypermap.permFace).Link
        (forwardDart hab) (forwardDart hab))
    (hncross :
      ¬ (R.toHypermap.permFace).CrossEdge (forwardDart hab))
    (d : (deletedGraph G a b).Walk r r) (hd : d.IsCycle)
    (hforward :
      ∀ f : OrientedEdge (deletedGraph G a b),
        CycleForwardDart d f ↔
          (R.toHypermap.permFace).EdgeDomain
            (forwardDart hab) (sourceDart f)) :
    RotationSystemGluing.IsFacialCycle
      (restrictedRotationSystem R hab) d hd := by
  have hfirstdom :
      (R.toHypermap.permFace).EdgeDomain
        (forwardDart hab) (sourceDart (cycleFirstDart d hd)) :=
    (hforward _).mp (cycleForwardDart_first d hd)
  intro f
  exact (hforward f).trans
    (restrictedRotationSystem_facePermReachable_iff_edgeDomain
      R hab hz hncross hfirstdom f).symm

/-- Chord-deletion form of facial merging.  The two old facial cycles are the
two sides of the chord; the new cycle consists exactly of their surviving
forward darts. -/
theorem restrictedRotationSystem_isFacialCycle_of_two_faces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b r₁ r₂ r : V}
    (R : RotationSystem G) (hab : G.Adj a b)
    (hz :
      ¬ (R.toHypermap.permFace).Link
        (forwardDart hab) (forwardDart hab))
    (hncross :
      ¬ (R.toHypermap.permFace).CrossEdge (forwardDart hab))
    (d₁ : G.Walk r₁ r₁) (hd₁ : d₁.IsCycle)
    (d₂ : G.Walk r₂ r₂) (hd₂ : d₂.IsCycle)
    (hfac₁ : RotationSystemGluing.IsFacialCycle R d₁ hd₁)
    (hfac₂ : RotationSystemGluing.IsFacialCycle R d₂ hd₂)
    (hfirst₁ : cycleFirstDart d₁ hd₁ = forwardDart hab)
    (hfirst₂ :
      cycleFirstDart d₂ hd₂ = (forwardDart hab).symm)
    (d : (deletedGraph G a b).Walk r r) (hd : d.IsCycle)
    (hforward :
      ∀ f : OrientedEdge (deletedGraph G a b),
        CycleForwardDart d f ↔
          CycleForwardDart d₁ (sourceDart f) ∨
            CycleForwardDart d₂ (sourceDart f)) :
    RotationSystemGluing.IsFacialCycle
      (restrictedRotationSystem R hab) d hd := by
  apply restrictedRotationSystem_isFacialCycle_of_forward_iff_edgeDomain
    R hab hz hncross d hd
  intro f
  rw [hforward f]
  constructor
  · rintro (hf | hf)
    · left
      have hreach := (hfac₁ (sourceDart f)).mp hf
      rw [hfirst₁] at hreach
      exact PermReachable.symm R.toHypermap.face hreach
    · right
      have hreach := (hfac₂ (sourceDart f)).mp hf
      rw [hfirst₂] at hreach
      simpa [Hypermap.permFace] using
        (PermReachable.symm R.toHypermap.face hreach)
  · rintro (hf | hf)
    · left
      apply (hfac₁ (sourceDart f)).mpr
      rw [hfirst₁]
      exact PermReachable.symm R.toHypermap.face hf
    · right
      apply (hfac₂ (sourceDart f)).mpr
      rw [hfirst₂]
      exact PermReachable.symm R.toHypermap.face (by
        simpa [Hypermap.permFace] using hf)

end EdgeDeletion

end FourColor
end Schematic.Math.GraphTheory
