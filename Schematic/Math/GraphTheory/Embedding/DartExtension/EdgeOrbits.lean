import Schematic.Math.GraphTheory.Embedding.DartExtension.EdgePermutationOrbits
import Schematic.Math.GraphTheory.Embedding.DartExtension.Constructions

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

/-- Classify `ecpU` edge orbits: the fresh edge orbit maps to `none`, old edge
orbits map to their original edge orbit. -/
def extensionUEdgeOrbitCode :
    (extensionU G x0).Dart → Option G.EdgeOrbit
  | ExtDart.new => none
  | ExtDart.newEdge => none
  | ExtDart.old y => some (PermOrbit.of G.edge y)

private theorem extensionUEdgeOrbitCode_eq_generic :
    extensionUEdgeOrbitCode G x0 = ExtDart.Perm.edgeOrbitCode G.edge := by
  funext x
  cases x <;> rfl

theorem extensionUEdgeOrbitCode_of_link
    {x y : (extensionU G x0).Dart}
    (hxy : PermLink (extensionU G x0).edge x y) :
    extensionUEdgeOrbitCode G x0 x =
      extensionUEdgeOrbitCode G x0 y := by
  rw [extensionUEdgeOrbitCode_eq_generic (G := G) x0]
  simpa [extensionU] using ExtDart.Perm.edgeOrbitCode_of_link G.edge hxy

theorem extensionUEdgeOrbitCode_of_reachable
    {x y : (extensionU G x0).Dart}
    (hxy : PermReachable (extensionU G x0).edge x y) :
    extensionUEdgeOrbitCode G x0 x =
      extensionUEdgeOrbitCode G x0 y := by
  rw [extensionUEdgeOrbitCode_eq_generic (G := G) x0]
  simpa [extensionU] using
    ExtDart.Perm.edgeOrbitCode_of_reachable G.edge hxy

theorem extensionU_old_edgeReachable_of_edge_link
    {x y : G.Dart}
    (hxy : PermLink G.edge x y) :
    PermReachable (extensionU G x0).edge
      (ExtDart.old x) (ExtDart.old y) := by
  simpa [extensionU] using ExtDart.Perm.old_reachable_of_link G.edge hxy

theorem extensionU_old_edgeReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    PermReachable (extensionU G x0).edge
      (ExtDart.old x) (ExtDart.old y) := by
  simpa [extensionU] using ExtDart.Perm.old_reachable G.edge hxy

theorem extensionU_old_edgeReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionU G x0).edge
      (ExtDart.old x) (ExtDart.old y) ↔
      PermReachable G.edge x y := by
  simpa [extensionU] using
    (ExtDart.Perm.old_reachable_iff G.edge (x := x) (y := y))

theorem extensionU_old_generatedReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    (extensionU G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  (extensionU G x0).edgePermReachable_reachable
    (extensionU_old_edgeReachable_of_edgeReachable (G := G) x0 hxy)

/-- The `ecpU` constructor adds exactly one new edge orbit. -/
noncomputable def extensionUEdgeOrbitEquiv :
    (extensionU G x0).EdgeOrbit ≃ Option G.EdgeOrbit := by
  change PermOrbit (ExtDart.Perm.edge G.edge) ≃ Option (PermOrbit G.edge)
  exact ExtDart.Perm.edgeOrbitEquiv G.edge

theorem extensionU_edgeOrbitCount :
    (extensionU G x0).edgeOrbitCount = G.edgeOrbitCount + 1 := by
  unfold Hypermap.edgeOrbitCount
  change Nat.card (PermOrbit (ExtDart.Perm.edge G.edge)) =
    Nat.card (PermOrbit G.edge) + 1
  exact ExtDart.Perm.edgeOrbitCard G.edge

/-- Classify `ecpN` edge orbits: the fresh edge orbit maps to `none`, old edge
orbits map to their original edge orbit. -/
def extensionNEdgeOrbitCode :
    (extensionN G x0).Dart → Option G.EdgeOrbit
  | ExtDart.new => none
  | ExtDart.newEdge => none
  | ExtDart.old y => some (PermOrbit.of G.edge y)

private theorem extensionNEdgeOrbitCode_eq_generic :
    extensionNEdgeOrbitCode G x0 = ExtDart.Perm.edgeOrbitCode G.edge := by
  funext x
  cases x <;> rfl

theorem extensionNEdgeOrbitCode_of_link
    {x y : (extensionN G x0).Dart}
    (hxy : PermLink (extensionN G x0).edge x y) :
    extensionNEdgeOrbitCode G x0 x =
      extensionNEdgeOrbitCode G x0 y := by
  rw [extensionNEdgeOrbitCode_eq_generic (G := G) x0]
  simpa [extensionN] using ExtDart.Perm.edgeOrbitCode_of_link G.edge hxy

theorem extensionNEdgeOrbitCode_of_reachable
    {x y : (extensionN G x0).Dart}
    (hxy : PermReachable (extensionN G x0).edge x y) :
    extensionNEdgeOrbitCode G x0 x =
      extensionNEdgeOrbitCode G x0 y := by
  rw [extensionNEdgeOrbitCode_eq_generic (G := G) x0]
  simpa [extensionN] using
    ExtDart.Perm.edgeOrbitCode_of_reachable G.edge hxy

theorem extensionN_old_edgeReachable_of_edge_link
    {x y : G.Dart}
    (hxy : PermLink G.edge x y) :
    PermReachable (extensionN G x0).edge
      (ExtDart.old x) (ExtDart.old y) := by
  simpa [extensionN] using ExtDart.Perm.old_reachable_of_link G.edge hxy

theorem extensionN_old_edgeReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    PermReachable (extensionN G x0).edge
      (ExtDart.old x) (ExtDart.old y) := by
  simpa [extensionN] using ExtDart.Perm.old_reachable G.edge hxy

theorem extensionN_old_edgeReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionN G x0).edge
      (ExtDart.old x) (ExtDart.old y) ↔
      PermReachable G.edge x y := by
  simpa [extensionN] using
    (ExtDart.Perm.old_reachable_iff G.edge (x := x) (y := y))

/-- The old-dart embedding for the `ecpN` constructor, matching Coq's `icpN`. -/
def extensionNOld (x : G.Dart) : (extensionN G x0).Dart :=
  ExtDart.old x

theorem extensionNOld_edgeReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionN G x0).edge
      (extensionNOld G x0 x) (extensionNOld G x0 y) ↔
      PermReachable G.edge x y :=
  extensionN_old_edgeReachable_iff (G := G) x0

theorem extensionN_old_generatedReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    (extensionN G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  (extensionN G x0).edgePermReachable_reachable
    (extensionN_old_edgeReachable_of_edgeReachable (G := G) x0 hxy)

/-- The `ecpN` constructor adds exactly one new edge orbit. -/
noncomputable def extensionNEdgeOrbitEquiv :
    (extensionN G x0).EdgeOrbit ≃ Option G.EdgeOrbit := by
  change PermOrbit (ExtDart.Perm.edge G.edge) ≃ Option (PermOrbit G.edge)
  exact ExtDart.Perm.edgeOrbitEquiv G.edge

theorem extensionN_edgeOrbitCount :
    (extensionN G x0).edgeOrbitCount = G.edgeOrbitCount + 1 := by
  unfold Hypermap.edgeOrbitCount
  change Nat.card (PermOrbit (ExtDart.Perm.edge G.edge)) =
    Nat.card (PermOrbit G.edge) + 1
  exact ExtDart.Perm.edgeOrbitCard G.edge

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
