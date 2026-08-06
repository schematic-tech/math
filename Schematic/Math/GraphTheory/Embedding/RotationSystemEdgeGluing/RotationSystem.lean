import Schematic.Math.GraphTheory.Embedding.RotationSystemEdgeGluing.NodeReachability

/-! The glued rotation system and its Euler planarity. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemEdgeGluing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
variable {x y : V}

theorem collapsedNode_conj
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (d : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart) :
    collapsedDartEquiv R₁ R₂ hxy₁ hxy₂ hcommon
        ((collapsedHypermap R₁ R₂ hxy₁ hxy₂).node d) =
      collapsedNode R₁ R₂ hxy₁ hxy₂ hcommon
        (collapsedDartEquiv R₁ R₂ hxy₁ hxy₂ hcommon d) := by
  simp [collapsedNode]

/-- Rotation system on the simple union after collapsing the duplicate marker
edge. -/
noncomputable def edgeSumRotationSystem
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hattach : forall ⦃v : V⦄,
      v ∈ G₁.support -> v ∈ G₂.support -> v = x ∨ v = y) :
    RotationSystem (G₁ ⊔ G₂) where
  node := collapsedNode R₁ R₂ hxy₁ hxy₂ hcommon
  node_tail := by
    intro e
    let H := collapsedHypermap R₁ R₂ hxy₁ hxy₂
    let E := collapsedDartEquiv R₁ R₂ hxy₁ hxy₂ hcommon
    let d := E.symm e
    change (E (H.node d)).tail = e.tail
    calc
      (E (H.node d)).tail =
          RotationSystemGluing.sumTail (H.node d).1.1 :=
        collapsedDartMap_tail R₁ R₂ hxy₁ hxy₂ _
      _ = RotationSystemGluing.sumTail d.1.1 :=
        collapsedHypermap_node_sumTail R₁ R₂ hxy₁ hxy₂ d
      _ = (E d).tail :=
        (collapsedDartMap_tail R₁ R₂ hxy₁ hxy₂ d).symm
      _ = e.tail := by rw [E.apply_symm_apply]
  node_orbit_of_same_tail := by
    intro e f hef
    let H := collapsedHypermap R₁ R₂ hxy₁ hxy₂
    let E := collapsedDartEquiv R₁ R₂ hxy₁ hxy₂ hcommon
    let d := E.symm e
    let g := E.symm f
    have hdgTail :
        RotationSystemGluing.sumTail d.1.1 =
          RotationSystemGluing.sumTail g.1.1 := by
      calc
        RotationSystemGluing.sumTail d.1.1 = (E d).tail :=
          (collapsedDartMap_tail R₁ R₂ hxy₁ hxy₂ d).symm
        _ = e.tail := by rw [E.apply_symm_apply]
        _ = f.tail := hef
        _ = (E g).tail := by rw [E.apply_symm_apply]
        _ = RotationSystemGluing.sumTail g.1.1 :=
          collapsedDartMap_tail R₁ R₂ hxy₁ hxy₂ g
    have hdg : PermReachable H.node d g :=
      collapsedHypermap_node_reachable_of_same_tail R₁ R₂
        hxy₁ hxy₂ hattach d g hdgTail
    simpa [d, g] using
      (permReachable_conj E H.node
        (collapsedNode R₁ R₂ hxy₁ hxy₂ hcommon)
        (collapsedNode_conj R₁ R₂ hxy₁ hxy₂ hcommon) hdg)

noncomputable def edgeSumRotationSystem_toHypermapIso
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hattach : forall ⦃v : V⦄,
      v ∈ G₁.support -> v ∈ G₂.support -> v = x ∨ v = y) :
    Hypermap.Iso (collapsedHypermap R₁ R₂ hxy₁ hxy₂)
      ((edgeSumRotationSystem R₁ R₂ hxy₁ hxy₂
        hcommon hattach).toHypermap) :=
  Hypermap.Iso.ofEdgeNode
    (collapsedDartEquiv R₁ R₂ hxy₁ hxy₂ hcommon)
    (collapsedDartMap_edge R₁ R₂ hxy₁ hxy₂)
    (collapsedNode_conj R₁ R₂ hxy₁ hxy₂ hcommon)

/-- Coq `edge_plane_embedding`: two connected planar rotations sharing only
the marker edge glue to a planar rotation of their simple union. -/
theorem edgeSumRotationSystem_dual_eulerPlanar
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hattach : forall ⦃v : V⦄,
      v ∈ G₁.support -> v ∈ G₂.support -> v = x ∨ v = y)
    (hR₁conn : R₁.toHypermap.Connected)
    (hR₂conn : R₂.toHypermap.Connected)
    (hR₁ : R₁.toHypermap.dual.EulerPlanar)
    (hR₂ : R₂.toHypermap.dual.EulerPlanar) :
    ((edgeSumRotationSystem R₁ R₂ hxy₁ hxy₂
      hcommon hattach).toHypermap).dual.EulerPlanar := by
  have hR₁' : R₁.toHypermap.EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R₁.toHypermap)).mp hR₁
  have hR₂' : R₂.toHypermap.EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R₂.toHypermap)).mp hR₂
  have hcollapsed :
      (collapsedHypermap R₁ R₂ hxy₁ hxy₂).EulerPlanar :=
    collapsedHypermap_eulerPlanar R₁ R₂ hxy₁ hxy₂
      hR₁conn hR₂conn hR₁' hR₂'
  have hsum :
      ((edgeSumRotationSystem R₁ R₂ hxy₁ hxy₂
        hcommon hattach).toHypermap).EulerPlanar :=
    (edgeSumRotationSystem_toHypermapIso R₁ R₂ hxy₁ hxy₂
      hcommon hattach).eulerPlanar_iff.mp hcollapsed
  exact (Hypermap.dual_eulerPlanar_iff
    (G := (edgeSumRotationSystem R₁ R₂ hxy₁ hxy₂
      hcommon hattach).toHypermap)).mpr hsum


end RotationSystemEdgeGluing
end FourColor
end Schematic.Math.GraphTheory
