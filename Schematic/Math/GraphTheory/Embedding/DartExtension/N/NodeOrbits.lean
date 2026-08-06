import Schematic.Math.GraphTheory.Embedding.DartExtension.N.FaceOrbits

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem node_node_eq_self_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    G.node (G.node x0) = x0 := by
  have h : G.face (G.edge x0) = G.node x0 := not_not.mp hnot
  calc
    G.node (G.node x0) = G.node (G.face (G.edge x0)) := by rw [h]
    _ = x0 := G.node_face_edge x0

theorem long_node_ne_self
    (hlong : G.LongRingHead x0) :
    G.node x0 ≠ x0 := by
  intro hnode
  have hsymm : G.node.symm x0 = x0 := by
    calc
      G.node.symm x0 = G.node.symm (G.node x0) := by rw [hnode]
      _ = x0 := by simp
  have hface : G.face (G.edge x0) = G.node x0 := by
    rw [face_edge_eq_node_symm (G := G) x0, hsymm, hnode]
  exact hlong hface

theorem long_face_edge_ne_self
    (hlong : G.LongRingHead x0) :
    G.face (G.edge x0) ≠ x0 := by
  intro hface
  have hnode : G.node x0 = x0 := by
    calc
      G.node x0 = G.node (G.face (G.edge x0)) := by rw [hface]
      _ = x0 := G.node_face_edge x0
  exact long_node_ne_self (G := G) x0 hlong hnode

theorem long_node_symm_symm_ne_self
    (hlong : G.LongRingHead x0) :
    G.node.symm (G.node.symm x0) ≠ x0 := by
  intro h
  have hnode2 : G.node (G.node x0) = x0 := by
    calc
      G.node (G.node x0) =
          G.node (G.node (G.node.symm (G.node.symm x0))) := by rw [h]
      _ = x0 := by simp
  have hsymm : G.node.symm x0 = G.node x0 := by
    apply G.node.injective
    simp [hnode2]
  have hface : G.face (G.edge x0) = G.node x0 := by
    rw [face_edge_eq_node_symm (G := G) x0, hsymm]
  exact hlong hface

theorem extensionN_nodeReachable_old_x0_newEdge :
    PermReachable (extensionN G x0).node
      (ExtDart.old x0) ExtDart.newEdge := by
  have hraw :=
    PermReachable.forward (extensionN G x0).node (ExtDart.old x0)
  have hnode :
      (extensionN G x0).node (ExtDart.old x0) = ExtDart.newEdge := by
    change ExtensionN.node G x0 (ExtDart.old x0) = ExtDart.newEdge
    simp [ExtensionN.node, ExtensionN.nodeToFun]
  simpa [hnode] using hraw

theorem extensionN_nodeReachable_newEdge_old_face_edge :
    PermReachable (extensionN G x0).node
      ExtDart.newEdge (ExtDart.old (G.face (G.edge x0))) := by
  have hraw :=
    PermReachable.forward (extensionN G x0).node ExtDart.newEdge
  have hnode :
      (extensionN G x0).node ExtDart.newEdge =
        ExtDart.old (G.face (G.edge x0)) := by
    rfl
  simpa [hnode] using hraw

theorem extensionN_nodeReachable_old_x0_old_face_edge :
    PermReachable (extensionN G x0).node
      (ExtDart.old x0) (ExtDart.old (G.face (G.edge x0))) := by
  exact PermReachable.trans (extensionN G x0).node
    (extensionN_nodeReachable_old_x0_newEdge (G := G) x0)
    (extensionN_nodeReachable_newEdge_old_face_edge (G := G) x0)

theorem extensionN_nodeReachable_new_old_node_of_long
    (hlong : G.LongRingHead x0) :
    PermReachable (extensionN G x0).node
      ExtDart.new (ExtDart.old (G.node x0)) := by
  have hraw :=
    PermReachable.forward (extensionN G x0).node ExtDart.new
  have hnode :
      (extensionN G x0).node ExtDart.new =
        ExtDart.old (G.node x0) := by
    change ExtensionN.node G x0 ExtDart.new = ExtDart.old (G.node x0)
    simp [ExtensionN.node, ExtensionN.nodeToFun, hlong]
  simpa [hnode] using hraw

theorem extensionN_nodeReachable_old_face_edge_old_x0_of_long
    (hlong : G.LongRingHead x0) :
    PermReachable (extensionN G x0).node
      (ExtDart.old (G.face (G.edge x0))) (ExtDart.old x0) := by
  have hraw :=
    PermReachable.forward (extensionN G x0).node
      (ExtDart.old (G.face (G.edge x0)))
  have hnotSelf :
      G.face (G.edge x0) ≠ x0 :=
    long_face_edge_ne_self (G := G) x0 hlong
  have hnodeA :
      G.node (G.face (G.edge x0)) = x0 :=
    G.node_face_edge x0
  have hnotTwo :
      G.node (G.node (G.face (G.edge x0))) ≠ x0 := by
    rw [hnodeA]
    exact long_node_ne_self (G := G) x0 hlong
  have hnodeNe : G.node x0 ≠ x0 :=
    long_node_ne_self (G := G) x0 hlong
  have hnode :
      (extensionN G x0).node (ExtDart.old (G.face (G.edge x0))) =
        ExtDart.old x0 := by
    change ExtensionN.node G x0 (ExtDart.old (G.face (G.edge x0))) =
      ExtDart.old x0
    simp [ExtensionN.node, ExtensionN.nodeToFun, hnotSelf, hnodeNe, hnodeA]
  simpa [hnode] using hraw

theorem extensionN_nodeReachable_old_nodeSymmSymm_new_of_long
    (hlong : G.LongRingHead x0) :
    PermReachable (extensionN G x0).node
      (ExtDart.old (G.node.symm (G.node.symm x0))) ExtDart.new := by
  have hraw :=
    PermReachable.forward (extensionN G x0).node
      (ExtDart.old (G.node.symm (G.node.symm x0)))
  have hnotSelf :
      G.node.symm (G.node.symm x0) ≠ x0 :=
    long_node_symm_symm_ne_self (G := G) x0 hlong
  have hnode :
      (extensionN G x0).node
          (ExtDart.old (G.node.symm (G.node.symm x0))) =
        ExtDart.new := by
    change ExtensionN.node G x0
      (ExtDart.old (G.node.symm (G.node.symm x0))) = ExtDart.new
    simp [ExtensionN.node, ExtensionN.nodeToFun, hnotSelf]
  simpa [hnode] using hraw

theorem extensionN_nodeReachable_old_nodeSymmSymm_old_node_of_long
    (hlong : G.LongRingHead x0) :
    PermReachable (extensionN G x0).node
      (ExtDart.old (G.node.symm (G.node.symm x0)))
      (ExtDart.old (G.node x0)) := by
  exact PermReachable.trans (extensionN G x0).node
    (extensionN_nodeReachable_old_nodeSymmSymm_new_of_long
      (G := G) x0 hlong)
    (extensionN_nodeReachable_new_old_node_of_long (G := G) x0 hlong)

theorem extensionN_old_nodeReachable_forward_of_regular
    {x : G.Dart}
    (hx : x ≠ x0)
    (hxx : G.node (G.node x) ≠ x0) :
    PermReachable (extensionN G x0).node
      (ExtDart.old x) (ExtDart.old (G.node x)) := by
  have hraw :=
    PermReachable.forward (extensionN G x0).node (ExtDart.old x)
  have hnode :
      (extensionN G x0).node (ExtDart.old x) =
        ExtDart.old (G.node x) := by
    change ExtensionN.node G x0 (ExtDart.old x) =
      ExtDart.old (G.node x)
    simp [ExtensionN.node, ExtensionN.nodeToFun, hx, hxx]
  simpa [hnode] using hraw

theorem extensionN_nodeReachable_old_node_old_x0_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    PermReachable (extensionN G x0).node
      (ExtDart.old (G.node x0)) (ExtDart.old x0) := by
  by_cases hfixed : G.node x0 = x0
  · simpa [hfixed] using
      (PermReachable.refl (extensionN G x0).node (ExtDart.old x0))
  · have hnode2 :
        G.node (G.node x0) = x0 :=
      node_node_eq_self_of_not_long (G := G) x0 hnot
    have hraw :=
      PermReachable.forward (extensionN G x0).node
        (ExtDart.old (G.node x0))
    have hnode :
        (extensionN G x0).node (ExtDart.old (G.node x0)) =
          ExtDart.old x0 := by
      change ExtensionN.node G x0 (ExtDart.old (G.node x0)) =
        ExtDart.old x0
      simp [ExtensionN.node, ExtensionN.nodeToFun, hfixed, hnode2]
    simpa [hnode] using hraw

/-- Classify `ecpN` node orbits.  In the long-ring case the small cycle
`x0 -> newEdge -> face(edge x0)` is the added orbit; in the short-ring case the
fixed fresh dart `new` is the added orbit. -/
def extensionNNodeOrbitCode :
    (extensionN G x0).Dart → Option G.NodeOrbit
  | ExtDart.new =>
      if G.LongRingHead x0 then some (PermOrbit.of G.node (G.node x0))
      else none
  | ExtDart.newEdge =>
      if G.LongRingHead x0 then none
      else some (PermOrbit.of G.node (G.face (G.edge x0)))
  | ExtDart.old y =>
      if G.LongRingHead x0 then
        if y = x0 then none
        else if y = G.face (G.edge x0) then none
        else some (PermOrbit.of G.node y)
      else some (PermOrbit.of G.node y)

theorem nodeReachable_two (x : G.Dart) :
    PermReachable G.node x (G.node (G.node x)) :=
  PermReachable.trans G.node
    (PermReachable.forward G.node x)
    (PermReachable.forward G.node (G.node x))

theorem nodeReachable_three (x : G.Dart) :
    PermReachable G.node x (G.node (G.node (G.node x))) :=
  PermReachable.trans G.node
    (nodeReachable_two (G := G) x)
    (PermReachable.forward G.node (G.node (G.node x)))

theorem extensionNNodeOrbitCode_node
    (x : (extensionN G x0).Dart) :
    extensionNNodeOrbitCode G x0 x =
      extensionNNodeOrbitCode G x0 ((extensionN G x0).node x) := by
  cases x with
  | new =>
      by_cases hlong : G.LongRingHead x0
      · have hnode :
            (extensionN G x0).node ExtDart.new =
              ExtDart.old (G.node x0) := by
          change ExtensionN.node G x0 ExtDart.new =
            ExtDart.old (G.node x0)
          simp [ExtensionN.node, ExtensionN.nodeToFun, hlong]
        have hnx : G.node x0 ≠ x0 :=
          long_node_ne_self (G := G) x0 hlong
        have hna : G.node x0 ≠ G.face (G.edge x0) := hlong.symm
        simp [extensionNNodeOrbitCode, hlong, hnode, hnx, hna]
      · have hnode :
            (extensionN G x0).node ExtDart.new = ExtDart.new := by
          change ExtensionN.node G x0 ExtDart.new = ExtDart.new
          simp [ExtensionN.node, ExtensionN.nodeToFun, hlong]
        simp [extensionNNodeOrbitCode, hlong, hnode]
  | newEdge =>
      by_cases hlong : G.LongRingHead x0
      · have hnode :
            (extensionN G x0).node ExtDart.newEdge =
              ExtDart.old (G.face (G.edge x0)) := by
          rfl
        have ha : G.face (G.edge x0) ≠ x0 :=
          long_face_edge_ne_self (G := G) x0 hlong
        simp [extensionNNodeOrbitCode, hlong, hnode, ha]
      · have hnode :
            (extensionN G x0).node ExtDart.newEdge =
              ExtDart.old (G.face (G.edge x0)) := by
          rfl
        simp [extensionNNodeOrbitCode, hlong, hnode]
  | old y =>
      by_cases hlong : G.LongRingHead x0
      · by_cases hyx : y = x0
        · subst y
          have hnode :
              (extensionN G x0).node (ExtDart.old x0) = ExtDart.newEdge := by
            change ExtensionN.node G x0 (ExtDart.old x0) = ExtDart.newEdge
            simp [ExtensionN.node, ExtensionN.nodeToFun]
          simp [extensionNNodeOrbitCode, hlong, hnode]
        · by_cases hya : y = G.face (G.edge x0)
          · subst y
            have hnodeA : G.node (G.face (G.edge x0)) = x0 :=
              G.node_face_edge x0
            have hnodeNe : G.node x0 ≠ x0 :=
              long_node_ne_self (G := G) x0 hlong
            have hnode :
                (extensionN G x0).node
                    (ExtDart.old (G.face (G.edge x0))) =
                  ExtDart.old x0 := by
              change ExtensionN.node G x0
                (ExtDart.old (G.face (G.edge x0))) = ExtDart.old x0
              simp [ExtensionN.node, ExtensionN.nodeToFun,
                long_face_edge_ne_self (G := G) x0 hlong, hnodeNe, hnodeA]
            simp [extensionNNodeOrbitCode, hlong, hnode]
          · by_cases hyy : G.node (G.node y) = x0
            · have hnode :
                  (extensionN G x0).node (ExtDart.old y) = ExtDart.new := by
                change ExtensionN.node G x0 (ExtDart.old y) = ExtDart.new
                simp [ExtensionN.node, ExtensionN.nodeToFun, hyx, hyy]
              have horbit :
                  PermOrbit.of G.node y =
                    PermOrbit.of G.node (G.node x0) := by
                apply PermOrbit.of_eq_of
                exact PermReachable.trans G.node
                  (nodeReachable_two (G := G) y)
                  (by simpa [hyy] using
                    (PermReachable.forward G.node x0))
              simp [extensionNNodeOrbitCode, hlong, hnode, hyx, hya, horbit]
            · have hnode :
                  (extensionN G x0).node (ExtDart.old y) =
                    ExtDart.old (G.node y) := by
                change ExtensionN.node G x0 (ExtDart.old y) =
                  ExtDart.old (G.node y)
                simp [ExtensionN.node, ExtensionN.nodeToFun, hyx, hyy]
              have hnode_ne_x : G.node y ≠ x0 := by
                intro h
                apply hya
                calc
                  y = G.node.symm (G.node y) := by simp
                  _ = G.node.symm x0 := by rw [h]
                  _ = G.face (G.edge x0) :=
                    (face_edge_eq_node_symm (G := G) x0).symm
              have hnode_ne_a : G.node y ≠ G.face (G.edge x0) := by
                intro h
                apply hyy
                calc
                  G.node (G.node y) = G.node (G.face (G.edge x0)) := by
                    rw [h]
                  _ = x0 := G.node_face_edge x0
              have horbit :
                  PermOrbit.of G.node y =
                    PermOrbit.of G.node (G.node y) :=
                (PermOrbit.of_apply G.node y).symm
              simp [extensionNNodeOrbitCode, hlong, hnode, hyx, hya,
                hnode_ne_x, hnode_ne_a, horbit]
      · by_cases hyx : y = x0
        · subst y
          have hnode :
              (extensionN G x0).node (ExtDart.old x0) = ExtDart.newEdge := by
            change ExtensionN.node G x0 (ExtDart.old x0) = ExtDart.newEdge
            simp [ExtensionN.node, ExtensionN.nodeToFun]
          have hface : G.face (G.edge x0) = G.node x0 := not_not.mp hlong
          have horbit :
              PermOrbit.of G.node x0 =
                PermOrbit.of G.node (G.face (G.edge x0)) := by
            rw [hface]
            exact (PermOrbit.of_apply G.node x0).symm
          simp [extensionNNodeOrbitCode, hlong, hnode, horbit]
        · by_cases hyy : G.node (G.node y) = x0
          · have hnode2 :
                G.node (G.node x0) = x0 :=
              node_node_eq_self_of_not_long (G := G) x0 hlong
            have hyx0 : y = x0 := by
              apply G.node.injective
              apply G.node.injective
              rw [hyy, hnode2]
            exact (hyx hyx0).elim
          · have hnode :
                (extensionN G x0).node (ExtDart.old y) =
                  ExtDart.old (G.node y) := by
              change ExtensionN.node G x0 (ExtDart.old y) =
                ExtDart.old (G.node y)
              simp [ExtensionN.node, ExtensionN.nodeToFun, hyx, hyy]
            have horbit :
                PermOrbit.of G.node y =
                  PermOrbit.of G.node (G.node y) :=
              (PermOrbit.of_apply G.node y).symm
            simp [extensionNNodeOrbitCode, hlong, hnode, horbit]

theorem extensionNNodeOrbitCode_of_link
    {x y : (extensionN G x0).Dart}
    (hxy : PermLink (extensionN G x0).node x y) :
    extensionNNodeOrbitCode G x0 x =
      extensionNNodeOrbitCode G x0 y := by
  cases hxy with
  | forward =>
      exact extensionNNodeOrbitCode_node (G := G) x0 x
  | backward =>
      have hforward :=
        extensionNNodeOrbitCode_node (G := G) x0
          ((extensionN G x0).node.symm x)
      simpa using hforward.symm

theorem extensionNNodeOrbitCode_of_reachable
    {x y : (extensionN G x0).Dart}
    (hxy : PermReachable (extensionN G x0).node x y) :
    extensionNNodeOrbitCode G x0 x =
      extensionNNodeOrbitCode G x0 y :=
  hxy.apply_eq (extensionNNodeOrbitCode G x0)
    (fun {_ _} h => extensionNNodeOrbitCode_of_link (G := G) x0 h)

theorem extensionN_old_nodeReachable_forward_of_not_long
    (hnot : ¬ G.LongRingHead x0)
    (x : G.Dart) :
    PermReachable (extensionN G x0).node
      (ExtDart.old x) (ExtDart.old (G.node x)) := by
  by_cases hx : x = x0
  · subst x
    have hface : G.face (G.edge x0) = G.node x0 := not_not.mp hnot
    simpa [hface] using
      (extensionN_nodeReachable_old_x0_old_face_edge (G := G) x0)
  · have hnode2 :
        G.node (G.node x0) = x0 :=
      node_node_eq_self_of_not_long (G := G) x0 hnot
    have hxx : G.node (G.node x) ≠ x0 := by
      intro h
      apply hx
      apply G.node.injective
      apply G.node.injective
      rw [h, hnode2]
    exact extensionN_old_nodeReachable_forward_of_regular
      (G := G) x0 hx hxx

theorem extensionN_old_nodeReachable_of_node_link_of_not_long
    (hnot : ¬ G.LongRingHead x0)
    {x y : G.Dart}
    (hxy : PermLink G.node x y) :
    PermReachable (extensionN G x0).node
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      exact extensionN_old_nodeReachable_forward_of_not_long
        (G := G) x0 hnot x
  | backward =>
      have hforward :
          PermReachable (extensionN G x0).node
            (ExtDart.old (G.node.symm x)) (ExtDart.old x) := by
        have h :=
          extensionN_old_nodeReachable_forward_of_not_long
            (G := G) x0 hnot (G.node.symm x)
        simpa using h
      exact PermReachable.symm (extensionN G x0).node hforward

theorem extensionN_old_nodeReachable_of_nodeReachable_of_not_long
    (hnot : ¬ G.LongRingHead x0)
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    PermReachable (extensionN G x0).node
      (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h =>
      extensionN_old_nodeReachable_of_node_link_of_not_long
        (G := G) x0 hnot h) hxy

theorem extensionN_old_generatedReachable_of_nodeReachable_of_not_long
    (hnot : ¬ G.LongRingHead x0)
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    (extensionN G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  (extensionN G x0).nodePermReachable_reachable
    (extensionN_old_nodeReachable_of_nodeReachable_of_not_long
      (G := G) x0 hnot hxy)

/-- In the short-ring `ecpN` case, `new` is the added node orbit and the old
node orbits are preserved. -/
noncomputable def extensionNNodeOrbitEquivOfNotLong
    (hnot : ¬ G.LongRingHead x0) :
    (extensionN G x0).NodeOrbit ≃ Option G.NodeOrbit where
  toFun :=
    Quotient.lift
      (extensionNNodeOrbitCode G x0)
      (by
        intro x y hxy
        exact extensionNNodeOrbitCode_of_reachable (G := G) x0 hxy)
  invFun
    | none => PermOrbit.of (extensionN G x0).node ExtDart.new
    | some q =>
        PermOrbit.of (extensionN G x0).node
          (ExtDart.old (Quotient.out q))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            simp [extensionNNodeOrbitCode, hnot, PermOrbit.of]
        | newEdge =>
            simp [extensionNNodeOrbitCode, hnot]
            change
              PermOrbit.of (extensionN G x0).node
                  (ExtDart.old
                    (Quotient.out
                      (PermOrbit.of G.node (G.face (G.edge x0))))) =
                PermOrbit.of (extensionN G x0).node ExtDart.newEdge
            apply PermOrbit.of_eq_of
            have hout :
                PermReachable G.node
                  (Quotient.out
                    (PermOrbit.of G.node (G.face (G.edge x0))))
                  (G.face (G.edge x0)) :=
              Quotient.exact
                (Quotient.out_eq
                  (PermOrbit.of G.node (G.face (G.edge x0))))
            exact PermReachable.trans (extensionN G x0).node
              (extensionN_old_nodeReachable_of_nodeReachable_of_not_long
                (G := G) x0 hnot hout)
              (PermReachable.symm (extensionN G x0).node
                (extensionN_nodeReachable_newEdge_old_face_edge
                  (G := G) x0))
        | old y =>
            simp [extensionNNodeOrbitCode, hnot]
            change
              PermOrbit.of (extensionN G x0).node
                  (ExtDart.old (Quotient.out (PermOrbit.of G.node y))) =
                PermOrbit.of (extensionN G x0).node (ExtDart.old y)
            apply PermOrbit.of_eq_of
            have hout :
                PermReachable G.node
                  (Quotient.out (PermOrbit.of G.node y)) y :=
              Quotient.exact (Quotient.out_eq (PermOrbit.of G.node y))
            exact extensionN_old_nodeReachable_of_nodeReachable_of_not_long
              (G := G) x0 hnot hout
  right_inv := by
    intro q
    cases q with
    | none =>
        simp [extensionNNodeOrbitCode, hnot, PermOrbit.of]
    | some q =>
        simp [extensionNNodeOrbitCode, hnot, PermOrbit.of]

theorem extensionN_nodeOrbitCount_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    (extensionN G x0).nodeOrbitCount = G.nodeOrbitCount + 1 := by
  unfold Hypermap.nodeOrbitCount
  rw [Nat.card_congr
    (extensionNNodeOrbitEquivOfNotLong (G := G) x0 hnot)]
  haveI : Finite G.Dart := Finite.of_fintype G.Dart
  haveI : Finite G.NodeOrbit := Quotient.finite (permOrbitSetoid G.node)
  exact Finite.card_option

theorem extensionN_eulerRight_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    (extensionN G x0).eulerRight = G.eulerRight + 2 :=
  extensionN_eulerRight_of_nodeOrbitCount (G := G) x0
    (extensionN_nodeOrbitCount_of_not_long (G := G) x0 hnot)

theorem extensionN_genus_of_not_long_of_componentCount
    (hnot : ¬ G.LongRingHead x0)
    (hcomp :
      (extensionN G x0).componentCount = G.componentCount) :
    (extensionN G x0).genus = G.genus :=
  extensionN_genus_of_counts (G := G) x0 hcomp
    (extensionN_nodeOrbitCount_of_not_long (G := G) x0 hnot)

theorem extensionN_eulerPlanar_iff_of_not_long_of_componentCount
    (hnot : ¬ G.LongRingHead x0)
    (hcomp :
      (extensionN G x0).componentCount = G.componentCount) :
    (extensionN G x0).EulerPlanar ↔ G.EulerPlanar :=
  extensionN_eulerPlanar_iff_of_counts (G := G) x0 hcomp
    (extensionN_nodeOrbitCount_of_not_long (G := G) x0 hnot)

/-- In the long-ring `ecpN` case, the old source node orbit is represented by
the remaining old darts together with `new`; the two old darts cut out into the
fresh 3-cycle are redirected to `new`. -/
def extensionNLongNodeOrbitLift
    (_hlong : G.LongRingHead x0) :
    G.Dart → (extensionN G x0).NodeOrbit :=
  fun x =>
    if x = x0 then
      PermOrbit.of (extensionN G x0).node ExtDart.new
    else if x = G.face (G.edge x0) then
      PermOrbit.of (extensionN G x0).node ExtDart.new
    else
      PermOrbit.of (extensionN G x0).node (ExtDart.old x)

theorem extensionNLongNodeOrbitLift_node
    (hlong : G.LongRingHead x0)
    (x : G.Dart) :
    extensionNLongNodeOrbitLift G x0 hlong x =
      extensionNLongNodeOrbitLift G x0 hlong (G.node x) := by
  by_cases hx : x = x0
  · subst x
    have hnx : G.node x0 ≠ x0 :=
      long_node_ne_self (G := G) x0 hlong
    have hna : G.node x0 ≠ G.face (G.edge x0) :=
      hlong.symm
    simp [extensionNLongNodeOrbitLift, hnx, hna]
    apply PermOrbit.of_eq_of
    exact extensionN_nodeReachable_new_old_node_of_long (G := G) x0 hlong
  · by_cases hxa : x = G.face (G.edge x0)
    · subst x
      have hnodeA : G.node (G.face (G.edge x0)) = x0 :=
        G.node_face_edge x0
      simp [extensionNLongNodeOrbitLift, hnodeA]
    · by_cases hnx : G.node x = x0
      · have hx_a : x = G.face (G.edge x0) := by
          calc
            x = G.node.symm (G.node x) := by simp
            _ = G.node.symm x0 := by rw [hnx]
            _ = G.face (G.edge x0) :=
              (face_edge_eq_node_symm (G := G) x0).symm
        exact (hxa hx_a).elim
      · by_cases hna : G.node x = G.face (G.edge x0)
        · have hx_pred :
              x = G.node.symm (G.node.symm x0) := by
            calc
              x = G.node.symm (G.node x) := by simp
              _ = G.node.symm (G.face (G.edge x0)) := by rw [hna]
              _ = G.node.symm (G.node.symm x0) := by
                rw [face_edge_eq_node_symm (G := G) x0]
          simp [extensionNLongNodeOrbitLift, hx, hxa, hna]
          subst x
          apply PermOrbit.of_eq_of
          exact extensionN_nodeReachable_old_nodeSymmSymm_new_of_long
            (G := G) x0 hlong
        · have hxx : G.node (G.node x) ≠ x0 := by
            intro hxx
            apply hna
            calc
              G.node x = G.node.symm x0 := by
                apply G.node.injective
                simp [hxx]
              _ = G.face (G.edge x0) :=
                (face_edge_eq_node_symm (G := G) x0).symm
          simp [extensionNLongNodeOrbitLift, hx, hxa, hnx, hna]
          apply PermOrbit.of_eq_of
          exact extensionN_old_nodeReachable_forward_of_regular
            (G := G) x0 hx hxx

theorem extensionNLongNodeOrbitLift_of_node_link
    (hlong : G.LongRingHead x0)
    {x y : G.Dart}
    (hxy : PermLink G.node x y) :
    extensionNLongNodeOrbitLift G x0 hlong x =
      extensionNLongNodeOrbitLift G x0 hlong y := by
  cases hxy with
  | forward =>
      exact extensionNLongNodeOrbitLift_node (G := G) x0 hlong x
  | backward =>
      have hforward :=
        extensionNLongNodeOrbitLift_node (G := G) x0 hlong
          (G.node.symm x)
      simpa using hforward.symm

theorem extensionNLongNodeOrbitLift_of_nodeReachable
    (hlong : G.LongRingHead x0)
    {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    extensionNLongNodeOrbitLift G x0 hlong x =
      extensionNLongNodeOrbitLift G x0 hlong y :=
  hxy.apply_eq (extensionNLongNodeOrbitLift G x0 hlong)
    (fun {_ _} h =>
      extensionNLongNodeOrbitLift_of_node_link (G := G) x0 hlong h)

/-- In the long-ring `ecpN` case, the fresh 3-cycle is the added node orbit
and the remaining node orbits are the old source node orbits. -/
noncomputable def extensionNNodeOrbitEquivOfLong
    (hlong : G.LongRingHead x0) :
    (extensionN G x0).NodeOrbit ≃ Option G.NodeOrbit where
  toFun :=
    Quotient.lift
      (extensionNNodeOrbitCode G x0)
      (by
        intro x y hxy
        exact extensionNNodeOrbitCode_of_reachable (G := G) x0 hxy)
  invFun
    | none => PermOrbit.of (extensionN G x0).node (ExtDart.old x0)
    | some q =>
        Quotient.lift
          (extensionNLongNodeOrbitLift G x0 hlong)
          (by
            intro x y hxy
            exact extensionNLongNodeOrbitLift_of_nodeReachable
              (G := G) x0 hlong hxy)
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            simp [extensionNNodeOrbitCode, hlong]
            have hnx : G.node x0 ≠ x0 :=
              long_node_ne_self (G := G) x0 hlong
            have hna : G.node x0 ≠ G.face (G.edge x0) :=
              hlong.symm
            change
              extensionNLongNodeOrbitLift G x0 hlong (G.node x0) =
                PermOrbit.of (extensionN G x0).node ExtDart.new
            simp [extensionNLongNodeOrbitLift, hnx, hna]
            apply PermOrbit.of_eq_of
            exact PermReachable.symm (extensionN G x0).node
              (extensionN_nodeReachable_new_old_node_of_long
                (G := G) x0 hlong)
        | newEdge =>
            simp [extensionNNodeOrbitCode, hlong]
            change
              PermOrbit.of (extensionN G x0).node (ExtDart.old x0) =
                PermOrbit.of (extensionN G x0).node ExtDart.newEdge
            apply PermOrbit.of_eq_of
            exact extensionN_nodeReachable_old_x0_newEdge (G := G) x0
        | old y =>
            by_cases hyx : y = x0
            · subst y
              simp [extensionNNodeOrbitCode, hlong]
              change
                PermOrbit.of (extensionN G x0).node (ExtDart.old x0) =
                  PermOrbit.of (extensionN G x0).node (ExtDart.old x0)
              rfl
            · by_cases hya : y = G.face (G.edge x0)
              · subst y
                have ha : G.face (G.edge x0) ≠ x0 :=
                  long_face_edge_ne_self (G := G) x0 hlong
                simp [extensionNNodeOrbitCode, hlong, ha]
                change
                  PermOrbit.of (extensionN G x0).node (ExtDart.old x0) =
                    PermOrbit.of (extensionN G x0).node
                      (ExtDart.old (G.face (G.edge x0)))
                apply PermOrbit.of_eq_of
                exact extensionN_nodeReachable_old_x0_old_face_edge
                  (G := G) x0
              · simp [extensionNNodeOrbitCode, hlong, hyx, hya]
                change
                  extensionNLongNodeOrbitLift G x0 hlong y =
                    PermOrbit.of (extensionN G x0).node (ExtDart.old y)
                simp [extensionNLongNodeOrbitLift, hyx, hya]
  right_inv := by
    intro q
    cases q with
    | none =>
        change extensionNNodeOrbitCode G x0 (ExtDart.old x0) = none
        simp [extensionNNodeOrbitCode, hlong]
    | some q =>
        induction q using Quotient.inductionOn with
        | h x =>
            by_cases hx : x = x0
            · subst x
              have horbit :
                  PermOrbit.of G.node (G.node x0) =
                    PermOrbit.of G.node x0 :=
                PermOrbit.of_apply G.node x0
              simp [extensionNLongNodeOrbitLift]
              change
                extensionNNodeOrbitCode G x0 ExtDart.new =
                  some (PermOrbit.of G.node x0)
              simp [extensionNNodeOrbitCode, hlong, horbit]
            · by_cases hxa : x = G.face (G.edge x0)
              · subst x
                have ha : G.face (G.edge x0) ≠ x0 :=
                  long_face_edge_ne_self (G := G) x0 hlong
                have horbit :
                    PermOrbit.of G.node (G.node x0) =
                      PermOrbit.of G.node (G.face (G.edge x0)) := by
                  apply PermOrbit.of_eq_of
                  exact PermReachable.trans G.node
                    (by
                      simpa using
                        (PermReachable.backward G.node (G.node x0)))
                    (by
                      simpa [face_edge_eq_node_symm (G := G) x0] using
                        (PermReachable.backward G.node x0))
                simp [extensionNLongNodeOrbitLift, ha]
                change
                  extensionNNodeOrbitCode G x0 ExtDart.new =
                    some (PermOrbit.of G.node (G.face (G.edge x0)))
                simp [extensionNNodeOrbitCode, hlong, horbit]
              · simp [extensionNLongNodeOrbitLift, hx, hxa]
                change
                  extensionNNodeOrbitCode G x0 (ExtDart.old x) =
                    some (PermOrbit.of G.node x)
                simp [extensionNNodeOrbitCode, hlong, hx, hxa]

theorem extensionN_nodeOrbitCount_of_long
    (hlong : G.LongRingHead x0) :
    (extensionN G x0).nodeOrbitCount = G.nodeOrbitCount + 1 := by
  unfold Hypermap.nodeOrbitCount
  rw [Nat.card_congr
    (extensionNNodeOrbitEquivOfLong (G := G) x0 hlong)]
  haveI : Finite G.Dart := Finite.of_fintype G.Dart
  haveI : Finite G.NodeOrbit := Quotient.finite (permOrbitSetoid G.node)
  exact Finite.card_option

theorem extensionN_nodeOrbitCount :
    (extensionN G x0).nodeOrbitCount = G.nodeOrbitCount + 1 := by
  by_cases hlong : G.LongRingHead x0
  · exact extensionN_nodeOrbitCount_of_long (G := G) x0 hlong
  · exact extensionN_nodeOrbitCount_of_not_long (G := G) x0 hlong

theorem extensionN_eulerRight :
    (extensionN G x0).eulerRight = G.eulerRight + 2 :=
  extensionN_eulerRight_of_nodeOrbitCount (G := G) x0
    (extensionN_nodeOrbitCount (G := G) x0)

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
