import Schematic.Math.GraphTheory.Embedding.DartExtension.U.NodeOrbits

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

/-- Projection from `ecpU` darts back to original generated components. -/
def extensionUComponentProj : (extensionU G x0).Dart → G.Dart
  | ExtDart.new => G.node x0
  | ExtDart.newEdge => G.node x0
  | ExtDart.old y => y

theorem extensionUComponentProj_of_link
    {x y : (extensionU G x0).Dart}
    (hxy : (extensionU G x0).Link x y) :
    G.Reachable
      (extensionUComponentProj G x0 x)
      (extensionUComponentProj G x0 y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new =>
        exact G.reachable_refl (G.node x0)
    | newEdge =>
        exact G.reachable_refl (G.node x0)
    | old y =>
        exact G.reachable_edge y
  · subst y
    cases x with
    | new =>
        exact G.reachable_refl (G.node x0)
    | newEdge =>
        exact G.reachable_node (G.node x0)
    | old y =>
        by_cases hy : y = G.node x0
        · subst y
          have hnode :
            (extensionU G x0).node (ExtDart.old (G.node x0)) =
              ExtDart.new := by
            change ExtensionU.node G x0 (ExtDart.old (G.node x0)) =
              ExtDart.new
            simp [ExtensionU.node, ExtensionU.nodeToFun]
          simpa [extensionUComponentProj, hnode] using
            G.reachable_refl (G.node x0)
        · have hnode :
            (extensionU G x0).node (ExtDart.old y) =
              ExtDart.old (G.node y) := by
            change ExtensionU.node G x0 (ExtDart.old y) =
              ExtDart.old (G.node y)
            simp [ExtensionU.node, ExtensionU.nodeToFun, hy]
          simpa [extensionUComponentProj, hnode] using G.reachable_node y
  · subst y
    cases x with
    | new =>
        exact G.reachable_refl (G.node x0)
    | newEdge =>
        exact G.reachable_refl (G.node x0)
    | old y =>
        by_cases hy : G.face y = G.node x0
        · have hface :
            (extensionU G x0).face (ExtDart.old y) = ExtDart.newEdge := by
            change ExtensionU.face G x0 (ExtDart.old y) = ExtDart.newEdge
            simp [ExtensionU.face, ExtensionU.faceToFun, hy]
          simpa [extensionUComponentProj, hface, hy] using
            G.reachable_face y
        · have hface :
            (extensionU G x0).face (ExtDart.old y) =
              ExtDart.old (G.face y) := by
            change ExtensionU.face G x0 (ExtDart.old y) =
              ExtDart.old (G.face y)
            simp [ExtensionU.face, ExtensionU.faceToFun, hy]
          simpa [extensionUComponentProj, hface] using G.reachable_face y

theorem extensionUComponentProj_of_reachable
    {x y : (extensionU G x0).Dart}
    (hxy : (extensionU G x0).Reachable x y) :
    G.Reachable
      (extensionUComponentProj G x0 x)
      (extensionUComponentProj G x0 y) :=
  Relation.ReflTransGen.lift' (extensionUComponentProj G x0)
    (fun _ _ h => extensionUComponentProj_of_link (G := G) x0 h) hxy

theorem extensionU_reachable_old_componentProj
    (x : (extensionU G x0).Dart) :
    (extensionU G x0).Reachable x
      (ExtDart.old (extensionUComponentProj G x0 x)) := by
  cases x with
  | new =>
      have h1 :
          (extensionU G x0).Reachable ExtDart.new ExtDart.newEdge :=
        (extensionU G x0).reachable_node ExtDart.new
      have h2 :
          (extensionU G x0).Reachable
            ExtDart.newEdge (ExtDart.old (G.node x0)) :=
        (extensionU G x0).reachable_face ExtDart.newEdge
      simpa [extensionUComponentProj] using h1.trans h2
  | newEdge =>
      simpa [extensionUComponentProj] using
        ((extensionU G x0).reachable_face ExtDart.newEdge)
  | old y =>
      exact (extensionU G x0).reachable_refl (ExtDart.old y)

/-- The `ecpU` constructor preserves generated dart components. -/
noncomputable def extensionUComponentEquiv :
    (extensionU G x0).Component ≃ G.Component where
  toFun :=
    Quotient.lift
      (fun x => G.componentOf (extensionUComponentProj G x0 x))
      (by
        intro x y hxy
        exact G.componentOf_eq_componentOf
          (extensionUComponentProj_of_reachable (G := G) x0 hxy))
  invFun :=
    Quotient.lift
      (fun x => (extensionU G x0).componentOf (ExtDart.old x))
      (by
        intro x y hxy
        exact (extensionU G x0).componentOf_eq_componentOf
          (extensionU_old_reachable_of_reachable (G := G) x0 hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply (extensionU G x0).componentOf_eq_componentOf
            simpa [extensionUComponentProj] using
              (extensionU G x0).nodePermReachable_reachable
                (extensionU_nodeReachable_old_node_x0_new (G := G) x0)
        | newEdge =>
            apply (extensionU G x0).componentOf_eq_componentOf
            have h1 :
                (extensionU G x0).Reachable
                  (ExtDart.old (G.node x0)) ExtDart.new :=
              (extensionU G x0).nodePermReachable_reachable
                (extensionU_nodeReachable_old_node_x0_new (G := G) x0)
            have h2 :
                (extensionU G x0).Reachable ExtDart.new ExtDart.newEdge :=
              (extensionU G x0).reachable_node ExtDart.new
            exact h1.trans h2
        | old y =>
            rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        rfl

theorem extensionU_componentCount :
    (extensionU G x0).componentCount = G.componentCount := by
  unfold Hypermap.componentCount
  exact Nat.card_congr (extensionUComponentEquiv (G := G) x0)

theorem extensionU_eulerLeft :
    (extensionU G x0).eulerLeft = G.eulerLeft + 2 := by
  unfold Hypermap.eulerLeft
  rw [extensionU_componentCount (G := G) x0,
    extensionU_card (G := G) x0]
  omega

theorem extensionU_genus :
    (extensionU G x0).genus = G.genus := by
  unfold Hypermap.genus
  rw [extensionU_eulerLeft (G := G) x0,
    extensionU_eulerRight (G := G) x0,
    Nat.add_sub_add_right]

theorem extensionU_eulerPlanar_iff :
    (extensionU G x0).EulerPlanar ↔ G.EulerPlanar := by
  simp [Hypermap.EulerPlanar, extensionU_genus (G := G) x0]

theorem extensionU_bridgeless
    (hG : G.Bridgeless) :
    (extensionU G x0).Bridgeless := by
  intro x hx
  cases x with
  | new =>
      exact extensionU_not_faceReachable_new_edge (G := G) x0 hx
  | newEdge =>
      exact extensionU_not_faceReachable_newEdge_edge (G := G) x0 hx
  | old y =>
      have hproj :=
        extensionUFaceProj_of_faceReachable (G := G) x0 hx
      change PermReachable G.face y (G.edge y) at hproj
      exact hG y hproj

theorem extensionU_planarBridgelessPlainConnected
    (hG : G.PlanarBridgelessPlainConnected) :
    (extensionU G x0).PlanarBridgelessPlainConnected where
  base := {
    base := {
      planar := (extensionU_eulerPlanar_iff (G := G) x0).2
        hG.base.base.planar
      bridgeless := extensionU_bridgeless (G := G) x0
        hG.base.base.bridgeless }
    plain := extensionU_plain (G := G) x0 hG.base.plain }
  connected := extensionU_connected (G := G) x0 hG.connected

theorem extensionU_long_new :
    (extensionU G x0).LongRingHead ExtDart.new := by
  unfold Hypermap.LongRingHead
  change ExtensionU.face G x0 (ExtDart.Perm.edge G.edge ExtDart.new) ≠
    ExtensionU.node G x0 ExtDart.new
  simp [ExtDart.Perm.edge, ExtensionU.face, ExtensionU.faceToFun,
    ExtensionU.node, ExtensionU.nodeToFun]

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
