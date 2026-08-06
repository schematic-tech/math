import Schematic.Math.GraphTheory.Embedding.DartExtension.EdgeOrbits
import Schematic.Math.GraphTheory.Embedding.DartExtension.U.FaceOrbits

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem extensionU_old_nodeReachable_forward
    (x : G.Dart) :
    PermReachable (extensionU G x0).node
      (ExtDart.old x) (ExtDart.old (G.node x)) := by
  by_cases hx : x = G.node x0
  · have h1 :
        PermReachable (extensionU G x0).node
          (ExtDart.old x) ExtDart.new := by
      have hstep :=
        PermReachable.forward (extensionU G x0).node (ExtDart.old x)
      have hnode :
          (extensionU G x0).node (ExtDart.old x) = ExtDart.new := by
        change ExtensionU.node G x0 (ExtDart.old x) = ExtDart.new
        simp [ExtensionU.node, ExtensionU.nodeToFun, hx]
      simpa [hnode] using hstep
    have h2 :
        PermReachable (extensionU G x0).node
          ExtDart.new ExtDart.newEdge := by
      simpa [extensionU, ExtensionU.node, ExtensionU.nodeToFun] using
        (PermReachable.forward (extensionU G x0).node ExtDart.new)
    have h3 :
        PermReachable (extensionU G x0).node
          ExtDart.newEdge (ExtDart.old (G.node (G.node x0))) := by
      simpa [extensionU, ExtensionU.node, ExtensionU.nodeToFun] using
        (PermReachable.forward (extensionU G x0).node ExtDart.newEdge)
    simpa [hx] using
      PermReachable.trans (extensionU G x0).node h1
        (PermReachable.trans (extensionU G x0).node h2 h3)
  · have hstep :=
      PermReachable.forward (extensionU G x0).node (ExtDart.old x)
    have hnode :
        (extensionU G x0).node (ExtDart.old x) =
          ExtDart.old (G.node x) := by
      change ExtensionU.node G x0 (ExtDart.old x) =
        ExtDart.old (G.node x)
      simp [ExtensionU.node, ExtensionU.nodeToFun, hx]
    simpa [hnode] using hstep

theorem extensionU_old_nodeReachable_of_node_link
    {x y : G.Dart}
    (hxy : PermLink G.node x y) :
    PermReachable (extensionU G x0).node
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      exact extensionU_old_nodeReachable_forward (G := G) x0 x
  | backward =>
      have hforward :
          PermReachable (extensionU G x0).node
            (ExtDart.old (G.node.symm x)) (ExtDart.old x) := by
        have h :=
          extensionU_old_nodeReachable_forward (G := G) x0
            (G.node.symm x)
        simpa using h
      exact PermReachable.symm (extensionU G x0).node hforward

theorem extensionU_old_nodeReachable_of_nodeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    PermReachable (extensionU G x0).node
      (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h => extensionU_old_nodeReachable_of_node_link (G := G) x0 h) hxy

theorem extensionU_old_generatedReachable_of_nodeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    (extensionU G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  (extensionU G x0).nodePermReachable_reachable
    (extensionU_old_nodeReachable_of_nodeReachable (G := G) x0 hxy)

/-- Projection from `ecpU` node darts back to the original node orbit. -/
def extensionUNodeOrbitProj : (extensionU G x0).Dart → G.Dart
  | ExtDart.new => G.node x0
  | ExtDart.newEdge => G.node (G.node x0)
  | ExtDart.old y => y

theorem extensionUNodeOrbitProj_node
    (x : (extensionU G x0).Dart) :
    PermReachable G.node
      (extensionUNodeOrbitProj G x0 x)
      (extensionUNodeOrbitProj G x0 ((extensionU G x0).node x)) := by
  cases x with
  | new =>
      exact PermReachable.forward G.node (G.node x0)
  | newEdge =>
      exact PermReachable.refl G.node (G.node (G.node x0))
  | old y =>
      by_cases hy : y = G.node x0
      · subst y
        have hnode :
          (extensionU G x0).node (ExtDart.old (G.node x0)) =
            ExtDart.new := by
          change ExtensionU.node G x0 (ExtDart.old (G.node x0)) =
            ExtDart.new
          simp [ExtensionU.node, ExtensionU.nodeToFun]
        simpa [extensionUNodeOrbitProj, hnode] using
          (PermReachable.refl G.node (G.node x0))
      · have hnode :
          (extensionU G x0).node (ExtDart.old y) =
            ExtDart.old (G.node y) := by
          change ExtensionU.node G x0 (ExtDart.old y) =
            ExtDart.old (G.node y)
          simp [ExtensionU.node, ExtensionU.nodeToFun, hy]
        simpa [extensionUNodeOrbitProj, hnode] using
          (PermReachable.forward G.node y)

theorem extensionUNodeOrbitProj_of_node_link
    {x y : (extensionU G x0).Dart}
    (hxy : PermLink (extensionU G x0).node x y) :
    PermReachable G.node
      (extensionUNodeOrbitProj G x0 x)
      (extensionUNodeOrbitProj G x0 y) := by
  cases hxy with
  | forward =>
      exact extensionUNodeOrbitProj_node (G := G) x0 x
  | backward =>
      have hforward :=
        extensionUNodeOrbitProj_node (G := G) x0
          ((extensionU G x0).node.symm x)
      exact PermReachable.symm G.node (by
        simpa using hforward)

theorem extensionUNodeOrbitProj_of_nodeReachable
    {x y : (extensionU G x0).Dart}
    (hxy : PermReachable (extensionU G x0).node x y) :
    PermReachable G.node
      (extensionUNodeOrbitProj G x0 x)
      (extensionUNodeOrbitProj G x0 y) :=
  Relation.ReflTransGen.lift' (extensionUNodeOrbitProj G x0)
    (fun _ _ h => extensionUNodeOrbitProj_of_node_link (G := G) x0 h) hxy

theorem extensionU_nodeReachable_old_node_x0_new :
    PermReachable (extensionU G x0).node
      (ExtDart.old (G.node x0)) ExtDart.new := by
  have hstep :=
    PermReachable.forward (extensionU G x0).node
      (ExtDart.old (G.node x0))
  have hnode :
      (extensionU G x0).node (ExtDart.old (G.node x0)) =
        ExtDart.new := by
    change ExtensionU.node G x0 (ExtDart.old (G.node x0)) =
      ExtDart.new
    simp [ExtensionU.node, ExtensionU.nodeToFun]
  simpa [hnode] using hstep

theorem extensionU_nodeReachable_new_old_node_x0 :
    PermReachable (extensionU G x0).node
      ExtDart.new (ExtDart.old (G.node x0)) :=
  PermReachable.symm (extensionU G x0).node
    (extensionU_nodeReachable_old_node_x0_new (G := G) x0)

theorem extensionU_nodeReachable_newEdge_old_node_node_x0 :
    PermReachable (extensionU G x0).node
      ExtDart.newEdge (ExtDart.old (G.node (G.node x0))) := by
  simpa [extensionU, ExtensionU.node, ExtensionU.nodeToFun] using
    (PermReachable.forward (extensionU G x0).node ExtDart.newEdge)

theorem extensionU_nodeReachable_old_of_nodeReachable_proj
    {x : G.Dart} {y : (extensionU G x0).Dart}
    (hxy :
      PermReachable G.node x (extensionUNodeOrbitProj G x0 y)) :
    PermReachable (extensionU G x0).node (ExtDart.old x) y := by
  cases y with
  | new =>
      have hold :
          PermReachable (extensionU G x0).node
            (ExtDart.old x) (ExtDart.old (G.node x0)) := by
        simpa [extensionUNodeOrbitProj] using
          extensionU_old_nodeReachable_of_nodeReachable (G := G) x0 hxy
      exact PermReachable.trans (extensionU G x0).node hold
        (extensionU_nodeReachable_old_node_x0_new (G := G) x0)
  | newEdge =>
      have hold :
          PermReachable (extensionU G x0).node
            (ExtDart.old x) (ExtDart.old (G.node (G.node x0))) := by
        simpa [extensionUNodeOrbitProj] using
          extensionU_old_nodeReachable_of_nodeReachable (G := G) x0 hxy
      exact PermReachable.trans (extensionU G x0).node hold
        (PermReachable.symm (extensionU G x0).node
          (extensionU_nodeReachable_newEdge_old_node_node_x0 (G := G) x0))
  | old z =>
      simpa [extensionUNodeOrbitProj] using
        extensionU_old_nodeReachable_of_nodeReachable (G := G) x0 hxy

theorem extensionU_nodeReachable_old_iff_proj
    {x : G.Dart} {y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).node (ExtDart.old x) y ↔
      PermReachable G.node x (extensionUNodeOrbitProj G x0 y) := by
  constructor
  · intro hxy
    simpa [extensionUNodeOrbitProj] using
      extensionUNodeOrbitProj_of_nodeReachable (G := G) x0 hxy
  · exact extensionU_nodeReachable_old_of_nodeReachable_proj (G := G) x0

theorem extensionU_old_nodeReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionU G x0).node
      (ExtDart.old x) (ExtDart.old y) ↔
      PermReachable G.node x y := by
  simpa [extensionUNodeOrbitProj] using
    (extensionU_nodeReachable_old_iff_proj
      (G := G) x0 (x := x) (y := ExtDart.old y))

theorem extensionU_nodeReachable_of_nodeReachable_proj
    {x y : (extensionU G x0).Dart}
    (hxy :
      PermReachable G.node
        (extensionUNodeOrbitProj G x0 x)
        (extensionUNodeOrbitProj G x0 y)) :
    PermReachable (extensionU G x0).node x y := by
  cases x with
  | new =>
      exact PermReachable.trans (extensionU G x0).node
        (extensionU_nodeReachable_new_old_node_x0 (G := G) x0)
        (extensionU_nodeReachable_old_of_nodeReachable_proj
          (G := G) x0 (x := G.node x0) (y := y) (by
            simpa [extensionUNodeOrbitProj] using hxy))
  | newEdge =>
      exact PermReachable.trans (extensionU G x0).node
        (extensionU_nodeReachable_newEdge_old_node_node_x0 (G := G) x0)
        (extensionU_nodeReachable_old_of_nodeReachable_proj
          (G := G) x0 (x := G.node (G.node x0)) (y := y) (by
            simpa [extensionUNodeOrbitProj] using hxy))
  | old z =>
      exact extensionU_nodeReachable_old_of_nodeReachable_proj
        (G := G) x0 (x := z) (y := y) (by
          simpa [extensionUNodeOrbitProj] using hxy)

theorem extensionU_nodeReachable_iff_proj
    {x y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).node x y ↔
      PermReachable G.node
        (extensionUNodeOrbitProj G x0 x)
        (extensionUNodeOrbitProj G x0 y) := by
  constructor
  · exact extensionUNodeOrbitProj_of_nodeReachable (G := G) x0
  · exact extensionU_nodeReachable_of_nodeReachable_proj (G := G) x0

theorem extensionU_nodeReachable_new_iff_proj
    {y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).node ExtDart.new y ↔
      PermReachable G.node
        (G.node x0) (extensionUNodeOrbitProj G x0 y) := by
  simpa [extensionUNodeOrbitProj] using
    (extensionU_nodeReachable_iff_proj (G := G) x0
      (x := ExtDart.new) (y := y))

theorem extensionU_nodeReachable_newEdge_iff_proj
    {y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).node ExtDart.newEdge y ↔
      PermReachable G.node
        (G.node (G.node x0)) (extensionUNodeOrbitProj G x0 y) := by
  simpa [extensionUNodeOrbitProj] using
    (extensionU_nodeReachable_iff_proj (G := G) x0
      (x := ExtDart.newEdge) (y := y))

/-- The `ecpU` constructor preserves the number of node orbits. -/
noncomputable def extensionUNodeOrbitEquiv :
    (extensionU G x0).NodeOrbit ≃ G.NodeOrbit where
  toFun :=
    Quotient.lift
      (fun x => PermOrbit.of G.node (extensionUNodeOrbitProj G x0 x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of G.node
          (extensionUNodeOrbitProj_of_nodeReachable (G := G) x0 hxy))
  invFun :=
    Quotient.lift
      (fun x => PermOrbit.of (extensionU G x0).node (ExtDart.old x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of (extensionU G x0).node
          (extensionU_old_nodeReachable_of_nodeReachable (G := G) x0 hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            simpa [extensionUNodeOrbitProj] using
              extensionU_nodeReachable_old_node_x0_new (G := G) x0
        | newEdge =>
            apply PermOrbit.of_eq_of
            simpa [extensionUNodeOrbitProj, extensionU, ExtensionU.node,
              ExtensionU.nodeToFun] using
              (PermReachable.symm (extensionU G x0).node
                (PermReachable.forward (extensionU G x0).node ExtDart.newEdge))
        | old y =>
            rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        rfl

theorem extensionU_nodeOrbitCount :
    (extensionU G x0).nodeOrbitCount = G.nodeOrbitCount := by
  unfold Hypermap.nodeOrbitCount
  exact Nat.card_congr (extensionUNodeOrbitEquiv (G := G) x0)

theorem extensionU_eulerRight :
    (extensionU G x0).eulerRight = G.eulerRight + 2 := by
  unfold Hypermap.eulerRight
  rw [extensionU_edgeOrbitCount (G := G) x0,
    extensionU_nodeOrbitCount (G := G) x0,
    extensionU_faceOrbitCount (G := G) x0]
  omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
