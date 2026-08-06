import Schematic.Math.GraphTheory.Embedding.DartExtension.N.NodeOrbits

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem extensionN_old_reachable_node_forward
    (x : G.Dart) :
    (extensionN G x0).Reachable
      (ExtDart.old x) (ExtDart.old (G.node x)) := by
  by_cases hx : x = x0
  · subst x
    by_cases hlong : G.LongRingHead x0
    · have h1 : (extensionN G x0).Reachable
          (ExtDart.old x0) ExtDart.newEdge :=
        (extensionN G x0).nodePermReachable_reachable
          (extensionN_nodeReachable_old_x0_newEdge (G := G) x0)
      have h2 : (extensionN G x0).Reachable ExtDart.newEdge ExtDart.new :=
        (extensionN G x0).reachable_edge ExtDart.newEdge
      have h3 : (extensionN G x0).Reachable
          ExtDart.new (ExtDart.old (G.node x0)) :=
        (extensionN G x0).nodePermReachable_reachable
          (extensionN_nodeReachable_new_old_node_of_long
            (G := G) x0 hlong)
      exact h1.trans (h2.trans h3)
    · have hface : G.face (G.edge x0) = G.node x0 := not_not.mp hlong
      simpa [hface] using
        ((extensionN G x0).nodePermReachable_reachable
          (extensionN_nodeReachable_old_x0_old_face_edge (G := G) x0))
  · by_cases hxx : G.node (G.node x) = x0
    · have hold_new :
          (extensionN G x0).Reachable (ExtDart.old x) ExtDart.new := by
        apply (extensionN G x0).nodePermReachable_reachable
        have hraw :=
          PermReachable.forward (extensionN G x0).node (ExtDart.old x)
        have hnode :
            (extensionN G x0).node (ExtDart.old x) = ExtDart.new := by
          change ExtensionN.node G x0 (ExtDart.old x) = ExtDart.new
          simp [ExtensionN.node, ExtensionN.nodeToFun, hx, hxx]
        simpa [hnode] using hraw
      have htarget : G.face (G.edge x0) = G.node x := by
        rw [face_edge_eq_node_symm (G := G) x0]
        apply G.node.injective
        simp [hxx]
      have hnew_target :
          (extensionN G x0).Reachable
            ExtDart.new (ExtDart.old (G.node x)) := by
        have h1 : (extensionN G x0).Reachable ExtDart.new ExtDart.newEdge :=
          (extensionN G x0).reachable_edge ExtDart.new
        have h2 : (extensionN G x0).Reachable
            ExtDart.newEdge (ExtDart.old (G.face (G.edge x0))) :=
          (extensionN G x0).nodePermReachable_reachable
            (extensionN_nodeReachable_newEdge_old_face_edge
              (G := G) x0)
        simpa [htarget] using h1.trans h2
      exact hold_new.trans hnew_target
    · exact (extensionN G x0).nodePermReachable_reachable
        (extensionN_old_nodeReachable_forward_of_regular
          (G := G) x0 hx hxx)

theorem extensionN_old_reachable_of_link
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (extensionN G x0).Reachable (ExtDart.old x) (ExtDart.old y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    exact extensionN_old_generatedReachable_of_edgeReachable (G := G) x0
      (PermReachable.forward G.edge x)
  · subst y
    exact extensionN_old_reachable_node_forward (G := G) x0 x
  · subst y
    exact extensionN_old_generatedReachable_of_faceReachable (G := G) x0
      (PermReachable.forward G.face x)

theorem extensionN_old_reachable_of_reachable
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (extensionN G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h => extensionN_old_reachable_of_link (G := G) x0 h) hxy

/-- Projection from `ecpN` darts back to original generated components. -/
def extensionNComponentProj : (extensionN G x0).Dart → G.Dart
  | ExtDart.new => x0
  | ExtDart.newEdge => x0
  | ExtDart.old y => y

theorem extensionNComponentProj_of_link
    {x y : (extensionN G x0).Dart}
    (hxy : (extensionN G x0).Link x y) :
    G.Reachable
      (extensionNComponentProj G x0 x)
      (extensionNComponentProj G x0 y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new =>
        exact G.reachable_refl x0
    | newEdge =>
        exact G.reachable_refl x0
    | old y =>
        exact G.reachable_edge y
  · subst y
    cases x with
    | new =>
        by_cases hlong : G.LongRingHead x0
        · have hnode :
              (extensionN G x0).node ExtDart.new =
                ExtDart.old (G.node x0) := by
            change ExtensionN.node G x0 ExtDart.new =
              ExtDart.old (G.node x0)
            simp [ExtensionN.node, ExtensionN.nodeToFun, hlong]
          simpa [extensionNComponentProj, hnode] using
            G.reachable_node x0
        · have hnode :
              (extensionN G x0).node ExtDart.new = ExtDart.new := by
            change ExtensionN.node G x0 ExtDart.new = ExtDart.new
            simp [ExtensionN.node, ExtensionN.nodeToFun, hlong]
          simpa [extensionNComponentProj, hnode] using
            G.reachable_refl x0
    | newEdge =>
        have hx0_face :
            G.Reachable x0 (G.face (G.edge x0)) := by
          simpa [face_edge_eq_node_symm (G := G) x0] using
            G.reachable_node_symm (G.node.symm x0)
        simpa [extensionNComponentProj] using hx0_face
    | old y =>
        by_cases hy : y = x0
        · subst y
          have hnode :
              (extensionN G x0).node (ExtDart.old x0) =
                ExtDart.newEdge := by
            change ExtensionN.node G x0 (ExtDart.old x0) = ExtDart.newEdge
            simp [ExtensionN.node, ExtensionN.nodeToFun]
          simpa [extensionNComponentProj, hnode] using
            G.reachable_refl x0
        · by_cases hyy : G.node (G.node y) = x0
          · have hnode :
                (extensionN G x0).node (ExtDart.old y) = ExtDart.new := by
              change ExtensionN.node G x0 (ExtDart.old y) = ExtDart.new
              simp [ExtensionN.node, ExtensionN.nodeToFun, hy, hyy]
            have hreach : G.Reachable y x0 :=
              (G.reachable_node y).trans
                (by simpa [hyy] using G.reachable_node (G.node y))
            simpa [extensionNComponentProj, hnode] using hreach
          · have hnode :
                (extensionN G x0).node (ExtDart.old y) =
                  ExtDart.old (G.node y) := by
              change ExtensionN.node G x0 (ExtDart.old y) =
                ExtDart.old (G.node y)
              simp [ExtensionN.node, ExtensionN.nodeToFun, hy, hyy]
            simpa [extensionNComponentProj, hnode] using
              G.reachable_node y
  · subst y
    cases x with
    | new =>
        simpa [extensionNComponentProj] using G.reachable_refl x0
    | newEdge =>
        by_cases hlong : G.LongRingHead x0
        · have hface :
              (extensionN G x0).face ExtDart.newEdge =
                ExtDart.old
                  (G.face (G.edge (G.face (G.edge x0)))) := by
            change ExtensionN.face G x0 ExtDart.newEdge =
              ExtDart.old (G.face (G.edge (G.face (G.edge x0))))
            simp [ExtensionN.face_newEdge, hlong]
          have htoFaceEdge :
              G.Reachable x0 (G.face (G.edge x0)) := by
            simpa [face_edge_eq_node_symm (G := G) x0] using
              G.reachable_node_symm (G.node.symm x0)
          have htoTarget :
              G.Reachable x0
                (G.face (G.edge (G.face (G.edge x0)))) :=
            htoFaceEdge.trans
              ((G.reachable_edge (G.face (G.edge x0))).trans
                (G.reachable_face (G.edge (G.face (G.edge x0)))))
          simpa [extensionNComponentProj, hface] using htoTarget
        · have hface :
              (extensionN G x0).face ExtDart.newEdge = ExtDart.new := by
            change ExtensionN.face G x0 ExtDart.newEdge = ExtDart.new
            simp [ExtensionN.face_newEdge, hlong]
          simpa [extensionNComponentProj, hface] using
            G.reachable_refl x0
    | old y =>
        by_cases hy1 : y = G.edge (G.face (G.edge x0))
        · have hface :
              (extensionN G x0).face (ExtDart.old y) = ExtDart.newEdge := by
            change ExtensionN.face G x0 (ExtDart.old y) = ExtDart.newEdge
            simp [ExtensionN.face_old, hy1]
          have hy_face :
              G.Reachable y (G.face (G.edge x0)) := by
            simpa [hy1] using
              G.reachable_edge_symm (G.face (G.edge x0))
          have hface_x0 :
              G.Reachable (G.face (G.edge x0)) x0 := by
            simpa using G.reachable_node (G.face (G.edge x0))
          simpa [extensionNComponentProj, hface] using
            hy_face.trans hface_x0
        · by_cases hy2 : y = G.edge (G.node x0)
          · have hface :
                (extensionN G x0).face (ExtDart.old y) = ExtDart.new := by
              change ExtensionN.face G x0 (ExtDart.old y) = ExtDart.new
              have hnot :
                  G.node x0 ≠ G.face (G.edge x0) := by
                intro h
                apply hy1
                calc
                  y = G.edge (G.node x0) := hy2
                  _ = G.edge (G.face (G.edge x0)) := by rw [h]
              simp [ExtensionN.face_old, hy2, hnot]
            have hreach : G.Reachable y x0 := by
              simpa [hy2] using G.reachable_face (G.edge (G.node x0))
            simpa [extensionNComponentProj, hface] using hreach
          · have hface :
                (extensionN G x0).face (ExtDart.old y) =
                  ExtDart.old (G.face y) := by
              change ExtensionN.face G x0 (ExtDart.old y) =
                ExtDart.old (G.face y)
              simp [ExtensionN.face_old, hy1, hy2]
            simpa [extensionNComponentProj, hface] using
              G.reachable_face y

theorem extensionNComponentProj_of_reachable
    {x y : (extensionN G x0).Dart}
    (hxy : (extensionN G x0).Reachable x y) :
    G.Reachable
      (extensionNComponentProj G x0 x)
      (extensionNComponentProj G x0 y) :=
  Relation.ReflTransGen.lift' (extensionNComponentProj G x0)
    (fun _ _ h => extensionNComponentProj_of_link (G := G) x0 h) hxy

theorem extensionN_reachable_old_componentProj
    (x : (extensionN G x0).Dart) :
    (extensionN G x0).Reachable x
      (ExtDart.old (extensionNComponentProj G x0 x)) := by
  cases x with
  | new =>
      simpa [extensionNComponentProj, extensionN, ExtensionN.face_new] using
        (extensionN G x0).reachable_face ExtDart.new
  | newEdge =>
      exact (extensionN G x0).reachable_symm
        ((extensionN G x0).nodePermReachable_reachable
          (extensionN_nodeReachable_old_x0_newEdge (G := G) x0))
  | old y =>
      exact (extensionN G x0).reachable_refl (ExtDart.old y)

theorem extensionN_connected
    (hG : G.Connected) :
    (extensionN G x0).Connected := by
  refine ⟨⟨ExtDart.new⟩, ?_⟩
  intro x y
  have hx :=
    extensionN_reachable_old_componentProj (G := G) x0 x
  have hy :=
    extensionN_reachable_old_componentProj (G := G) x0 y
  have hproj :
      (extensionN G x0).Reachable
        (ExtDart.old (extensionNComponentProj G x0 x))
        (ExtDart.old (extensionNComponentProj G x0 y)) :=
    extensionN_old_reachable_of_reachable (G := G) x0
      (Connected.reachable (G := G) hG
        (extensionNComponentProj G x0 x)
        (extensionNComponentProj G x0 y))
  exact hx.trans (hproj.trans ((extensionN G x0).reachable_symm hy))

/-- The `ecpN` constructor preserves generated dart components. -/
noncomputable def extensionNComponentEquiv :
    (extensionN G x0).Component ≃ G.Component where
  toFun :=
    Quotient.lift
      (fun x => G.componentOf (extensionNComponentProj G x0 x))
      (by
        intro x y hxy
        exact G.componentOf_eq_componentOf
          (extensionNComponentProj_of_reachable (G := G) x0 hxy))
  invFun :=
    Quotient.lift
      (fun x => (extensionN G x0).componentOf (ExtDart.old x))
      (by
        intro x y hxy
        exact (extensionN G x0).componentOf_eq_componentOf
          (extensionN_old_reachable_of_reachable (G := G) x0 hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply (extensionN G x0).componentOf_eq_componentOf
            have hnew_old :
                (extensionN G x0).Reachable ExtDart.new
                  (ExtDart.old x0) := by
              simpa [extensionN, ExtensionN.face_new] using
                (extensionN G x0).reachable_face ExtDart.new
            exact (extensionN G x0).reachable_symm hnew_old
        | newEdge =>
            apply (extensionN G x0).componentOf_eq_componentOf
            exact (extensionN G x0).nodePermReachable_reachable
              (extensionN_nodeReachable_old_x0_newEdge (G := G) x0)
        | old y =>
            rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        rfl

theorem extensionN_componentCount :
    (extensionN G x0).componentCount = G.componentCount := by
  unfold Hypermap.componentCount
  exact Nat.card_congr (extensionNComponentEquiv (G := G) x0)

theorem extensionN_eulerLeft :
    (extensionN G x0).eulerLeft = G.eulerLeft + 2 :=
  extensionN_eulerLeft_of_componentCount (G := G) x0
    (extensionN_componentCount (G := G) x0)

theorem extensionN_genus :
    (extensionN G x0).genus = G.genus :=
  extensionN_genus_of_counts (G := G) x0
    (extensionN_componentCount (G := G) x0)
    (extensionN_nodeOrbitCount (G := G) x0)

theorem extensionN_eulerPlanar_iff :
    (extensionN G x0).EulerPlanar ↔ G.EulerPlanar :=
  extensionN_eulerPlanar_iff_of_counts (G := G) x0
    (extensionN_componentCount (G := G) x0)
    (extensionN_nodeOrbitCount (G := G) x0)

theorem extensionN_genus_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    (extensionN G x0).genus = G.genus :=
  extensionN_genus_of_counts (G := G) x0
    (extensionN_componentCount (G := G) x0)
    (extensionN_nodeOrbitCount_of_not_long (G := G) x0 hnot)

theorem extensionN_eulerPlanar_iff_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    (extensionN G x0).EulerPlanar ↔ G.EulerPlanar :=
  extensionN_eulerPlanar_iff_of_counts (G := G) x0
    (extensionN_componentCount (G := G) x0)
    (extensionN_nodeOrbitCount_of_not_long (G := G) x0 hnot)

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
