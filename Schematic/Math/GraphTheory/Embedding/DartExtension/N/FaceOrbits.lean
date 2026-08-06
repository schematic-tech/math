import Schematic.Math.GraphTheory.Embedding.DartExtension.EdgeOrbits

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem extensionN_face_edge_face_edge_eq_of_not_long
    (hnot : ¬ G.LongRingHead x0) :
    G.face (G.edge (G.face (G.edge x0))) = x0 := by
  have h : G.face (G.edge x0) = G.node x0 := not_not.mp hnot
  calc
    G.face (G.edge (G.face (G.edge x0))) =
        G.face (G.edge (G.node x0)) := by rw [h]
    _ = x0 := G.face_edge_node x0

/-- Projection used to compare `ecpN` face orbits with original face orbits. -/
def extensionNFaceProj : (extensionN G x0).Dart → G.Dart
  | ExtDart.new => x0
  | ExtDart.newEdge => G.face (G.edge (G.face (G.edge x0)))
  | ExtDart.old y => y

@[simp]
theorem extensionNFaceProj_old (x : G.Dart) :
    extensionNFaceProj G x0 (extensionNOld G x0 x) = x :=
  rfl

theorem extensionNFaceProj_face
    (x : (extensionN G x0).Dart) :
    PermReachable G.face
      (extensionNFaceProj G x0 x)
      (extensionNFaceProj G x0 ((extensionN G x0).face x)) := by
  cases x with
  | new =>
      simpa [extensionNFaceProj, extensionN, ExtensionN.face_new] using
        (PermReachable.refl G.face x0)
  | newEdge =>
      by_cases hlong : G.LongRingHead x0
      · have hface :
            (extensionN G x0).face ExtDart.newEdge =
              ExtDart.old (G.face (G.edge (G.face (G.edge x0)))) := by
          change ExtensionN.face G x0 ExtDart.newEdge =
            ExtDart.old (G.face (G.edge (G.face (G.edge x0))))
          simp [ExtensionN.face_newEdge, hlong]
        simpa [extensionNFaceProj, hface] using
          (PermReachable.refl G.face
            (G.face (G.edge (G.face (G.edge x0)))))
      · have hface :
            (extensionN G x0).face ExtDart.newEdge = ExtDart.new := by
          change ExtensionN.face G x0 ExtDart.newEdge = ExtDart.new
          simp [ExtensionN.face_newEdge, hlong]
        have hcollapse :=
          extensionN_face_edge_face_edge_eq_of_not_long (G := G) x0 hlong
        simpa [extensionNFaceProj, hface, hcollapse] using
          (PermReachable.refl G.face x0)
  | old y =>
      by_cases hy1 : y = G.edge (G.face (G.edge x0))
      · subst y
        have hface :
            (extensionN G x0).face
              (ExtDart.old (G.edge (G.face (G.edge x0)))) =
              ExtDart.newEdge := by
          change ExtensionN.face G x0
            (ExtDart.old (G.edge (G.face (G.edge x0)))) = ExtDart.newEdge
          simp [ExtensionN.face_old]
        change PermReachable G.face (G.edge (G.face (G.edge x0)))
          (extensionNFaceProj G x0
            ((extensionN G x0).face
              (ExtDart.old (G.edge (G.face (G.edge x0))))))
        simpa [extensionNFaceProj, hface] using
          (PermReachable.forward G.face (G.edge (G.face (G.edge x0))))
      · by_cases hy2 : y = G.edge (G.node x0)
        · have hface :
              (extensionN G x0).face (ExtDart.old y) = ExtDart.new := by
            change ExtensionN.face G x0 (ExtDart.old y) = ExtDart.new
            have hnotFace : G.node x0 ≠ G.face (G.edge x0) := by
              intro h
              exact hy1 (by rw [hy2, h])
            simp [ExtensionN.face_old, hy2, hnotFace]
          have htarget : G.face y = x0 := by
            rw [hy2]
            exact G.face_edge_node x0
          simpa [extensionNFaceProj, hface, htarget] using
            (PermReachable.forward G.face y)
        · have hface :
              (extensionN G x0).face (ExtDart.old y) =
                ExtDart.old (G.face y) := by
            change ExtensionN.face G x0 (ExtDart.old y) =
              ExtDart.old (G.face y)
            simp [ExtensionN.face_old, hy1, hy2]
          simpa [extensionNFaceProj, hface] using
            (PermReachable.forward G.face y)

theorem extensionNFaceProj_of_face_link
    {x y : (extensionN G x0).Dart}
    (hxy : PermLink (extensionN G x0).face x y) :
    PermReachable G.face
      (extensionNFaceProj G x0 x) (extensionNFaceProj G x0 y) := by
  cases hxy with
  | forward =>
      exact extensionNFaceProj_face (G := G) x0 x
  | backward =>
      have hforward :=
        extensionNFaceProj_face (G := G) x0
          ((extensionN G x0).face.symm x)
      exact PermReachable.symm G.face (by
        simpa using hforward)

theorem extensionNFaceProj_of_faceReachable
    {x y : (extensionN G x0).Dart}
    (hxy : PermReachable (extensionN G x0).face x y) :
    PermReachable G.face
      (extensionNFaceProj G x0 x) (extensionNFaceProj G x0 y) :=
  Relation.ReflTransGen.lift' (extensionNFaceProj G x0)
    (fun _ _ h => extensionNFaceProj_of_face_link (G := G) x0 h) hxy

theorem extensionN_faceReachable_newEdge_to_old_proj :
    PermReachable (extensionN G x0).face
      ExtDart.newEdge
      (ExtDart.old (G.face (G.edge (G.face (G.edge x0))))) := by
  by_cases hlong : G.LongRingHead x0
  · have hraw :=
      PermReachable.forward (extensionN G x0).face ExtDart.newEdge
    have hface :
        (extensionN G x0).face ExtDart.newEdge =
          ExtDart.old (G.face (G.edge (G.face (G.edge x0)))) := by
      change ExtensionN.face G x0 ExtDart.newEdge =
        ExtDart.old (G.face (G.edge (G.face (G.edge x0))))
      simp [ExtensionN.face_newEdge, hlong]
    simpa [hface] using hraw
  · have h1 :
        PermReachable (extensionN G x0).face ExtDart.newEdge ExtDart.new := by
      have hraw :=
        PermReachable.forward (extensionN G x0).face ExtDart.newEdge
      have hface :
          (extensionN G x0).face ExtDart.newEdge = ExtDart.new := by
        change ExtensionN.face G x0 ExtDart.newEdge = ExtDart.new
        simp [ExtensionN.face_newEdge, hlong]
      simpa [hface] using hraw
    have h2 :
        PermReachable (extensionN G x0).face ExtDart.new
          (ExtDart.old x0) := by
      simpa [extensionN, ExtensionN.face_new] using
        (PermReachable.forward (extensionN G x0).face ExtDart.new)
    have hcollapse :=
      extensionN_face_edge_face_edge_eq_of_not_long (G := G) x0 hlong
    simpa [hcollapse] using
      PermReachable.trans (extensionN G x0).face h1 h2

theorem extensionN_old_edge_face_edge_faceReachable_newEdge :
    PermReachable (extensionN G x0).face
      (ExtDart.old (G.edge (G.face (G.edge x0)))) ExtDart.newEdge := by
  have hstep :=
    PermReachable.forward (extensionN G x0).face
      (ExtDart.old (G.edge (G.face (G.edge x0))))
  have hface :
      (extensionN G x0).face
        (ExtDart.old (G.edge (G.face (G.edge x0)))) = ExtDart.newEdge := by
    change ExtensionN.face G x0
      (ExtDart.old (G.edge (G.face (G.edge x0)))) = ExtDart.newEdge
    simp [ExtensionN.face_old]
  simpa [hface] using hstep

theorem extensionN_old_faceReachable_forward
    (x : G.Dart) :
    PermReachable (extensionN G x0).face
      (ExtDart.old x) (ExtDart.old (G.face x)) := by
  by_cases hx1 : x = G.edge (G.face (G.edge x0))
  · have h1 :
        PermReachable (extensionN G x0).face
          (ExtDart.old x) ExtDart.newEdge := by
      have hraw :=
        PermReachable.forward (extensionN G x0).face (ExtDart.old x)
      have hface :
          (extensionN G x0).face (ExtDart.old x) = ExtDart.newEdge := by
        change ExtensionN.face G x0 (ExtDart.old x) = ExtDart.newEdge
        simp [ExtensionN.face_old, hx1]
      simpa [hface] using hraw
    have h2 := extensionN_faceReachable_newEdge_to_old_proj (G := G) x0
    have htarget :
        G.face x = G.face (G.edge (G.face (G.edge x0))) := by
      rw [hx1]
    simpa [htarget] using
      PermReachable.trans (extensionN G x0).face h1 h2
  · by_cases hx2 : x = G.edge (G.node x0)
    · have h1 :
          PermReachable (extensionN G x0).face
            (ExtDart.old x) ExtDart.new := by
        have hraw :=
          PermReachable.forward (extensionN G x0).face (ExtDart.old x)
        have hface :
            (extensionN G x0).face (ExtDart.old x) = ExtDart.new := by
          change ExtensionN.face G x0 (ExtDart.old x) = ExtDart.new
          have hnotFace : G.node x0 ≠ G.face (G.edge x0) := by
            intro h
            exact hx1 (by rw [hx2, h])
          simp [ExtensionN.face_old, hx2, hnotFace]
        simpa [hface] using hraw
      have h2 :
          PermReachable (extensionN G x0).face
            ExtDart.new (ExtDart.old x0) := by
        simpa [extensionN, ExtensionN.face_new] using
          (PermReachable.forward (extensionN G x0).face ExtDart.new)
      have htarget : G.face x = x0 := by
        rw [hx2]
        exact G.face_edge_node x0
      simpa [htarget] using
        PermReachable.trans (extensionN G x0).face h1 h2
    · have hraw :=
        PermReachable.forward (extensionN G x0).face (ExtDart.old x)
      have hface :
          (extensionN G x0).face (ExtDart.old x) =
            ExtDart.old (G.face x) := by
        change ExtensionN.face G x0 (ExtDart.old x) =
          ExtDart.old (G.face x)
        simp [ExtensionN.face_old, hx1, hx2]
      simpa [hface] using hraw

theorem extensionN_old_faceReachable_of_face_link
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    PermReachable (extensionN G x0).face
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      exact extensionN_old_faceReachable_forward (G := G) x0 x
  | backward =>
      have hforward :
          PermReachable (extensionN G x0).face
            (ExtDart.old (G.face.symm x)) (ExtDart.old x) := by
        have h :=
          extensionN_old_faceReachable_forward (G := G) x0
            (G.face.symm x)
        simpa using h
      exact PermReachable.symm (extensionN G x0).face hforward

theorem extensionN_old_faceReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionN G x0).face
      (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h => extensionN_old_faceReachable_of_face_link (G := G) x0 h) hxy

theorem extensionN_old_faceReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionN G x0).face
      (ExtDart.old x) (ExtDart.old y) ↔
      PermReachable G.face x y := by
  constructor
  · intro hxy
    simpa [extensionNFaceProj] using
      (extensionNFaceProj_of_faceReachable (G := G) x0 hxy)
  · exact extensionN_old_faceReachable_of_faceReachable (G := G) x0

theorem extensionNOld_faceReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionN G x0).face
      (extensionNOld G x0 x) (extensionNOld G x0 y) ↔
      PermReachable G.face x y :=
  extensionN_old_faceReachable_iff (G := G) x0

theorem extensionN_faceReachable_new_old_x0 :
    PermReachable (extensionN G x0).face ExtDart.new
      (ExtDart.old x0) := by
  simpa [extensionN, ExtensionN.face_new] using
    (PermReachable.forward (extensionN G x0).face ExtDart.new)

theorem extensionN_faceReachable_old_of_faceReachable_proj
    {x : G.Dart} {y : (extensionN G x0).Dart}
    (hxy :
      PermReachable G.face x (extensionNFaceProj G x0 y)) :
    PermReachable (extensionN G x0).face (ExtDart.old x) y := by
  cases y with
  | new =>
      have hold :
          PermReachable (extensionN G x0).face
            (ExtDart.old x) (ExtDart.old x0) := by
        simpa [extensionNFaceProj] using
          extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxy
      exact PermReachable.trans (extensionN G x0).face hold
        (PermReachable.symm (extensionN G x0).face
          (extensionN_faceReachable_new_old_x0 (G := G) x0))
  | newEdge =>
      have hold :
          PermReachable (extensionN G x0).face
            (ExtDart.old x)
            (ExtDart.old (G.face (G.edge (G.face (G.edge x0))))) := by
        simpa [extensionNFaceProj] using
          extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxy
      exact PermReachable.trans (extensionN G x0).face hold
        (PermReachable.symm (extensionN G x0).face
          (extensionN_faceReachable_newEdge_to_old_proj (G := G) x0))
  | old z =>
      simpa [extensionNFaceProj] using
        extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxy

theorem extensionN_faceReachable_old_iff_proj
    {x : G.Dart} {y : (extensionN G x0).Dart} :
    PermReachable (extensionN G x0).face (ExtDart.old x) y ↔
      PermReachable G.face x (extensionNFaceProj G x0 y) := by
  constructor
  · intro hxy
    simpa [extensionNFaceProj] using
      extensionNFaceProj_of_faceReachable (G := G) x0 hxy
  · exact extensionN_faceReachable_old_of_faceReachable_proj (G := G) x0

theorem extensionN_faceReachable_of_faceReachable_proj
    {x y : (extensionN G x0).Dart}
    (hxy :
      PermReachable G.face
        (extensionNFaceProj G x0 x)
        (extensionNFaceProj G x0 y)) :
    PermReachable (extensionN G x0).face x y := by
  cases x with
  | new =>
      exact PermReachable.trans (extensionN G x0).face
        (extensionN_faceReachable_new_old_x0 (G := G) x0)
        (extensionN_faceReachable_old_of_faceReachable_proj
          (G := G) x0 (x := x0) (y := y) (by
            simpa [extensionNFaceProj] using hxy))
  | newEdge =>
      exact PermReachable.trans (extensionN G x0).face
        (extensionN_faceReachable_newEdge_to_old_proj (G := G) x0)
        (extensionN_faceReachable_old_of_faceReachable_proj
          (G := G) x0
          (x := G.face (G.edge (G.face (G.edge x0)))) (y := y) (by
            simpa [extensionNFaceProj] using hxy))
  | old z =>
      exact extensionN_faceReachable_old_of_faceReachable_proj
        (G := G) x0 (x := z) (y := y) (by
          simpa [extensionNFaceProj] using hxy)

theorem extensionN_faceReachable_iff_proj
    {x y : (extensionN G x0).Dart} :
    PermReachable (extensionN G x0).face x y ↔
      PermReachable G.face
        (extensionNFaceProj G x0 x)
        (extensionNFaceProj G x0 y) := by
  constructor
  · exact extensionNFaceProj_of_faceReachable (G := G) x0
  · exact extensionN_faceReachable_of_faceReachable_proj (G := G) x0

theorem extensionN_faceReachable_new_iff_proj
    {y : (extensionN G x0).Dart} :
    PermReachable (extensionN G x0).face ExtDart.new y ↔
      PermReachable G.face x0 (extensionNFaceProj G x0 y) := by
  simpa [extensionNFaceProj] using
    (extensionN_faceReachable_iff_proj (G := G) x0
      (x := ExtDart.new) (y := y))

theorem extensionN_faceReachable_newEdge_iff_proj
    {y : (extensionN G x0).Dart} :
    PermReachable (extensionN G x0).face ExtDart.newEdge y ↔
      PermReachable G.face
        (G.face (G.edge (G.face (G.edge x0))))
        (extensionNFaceProj G x0 y) := by
  simpa [extensionNFaceProj] using
    (extensionN_faceReachable_iff_proj (G := G) x0
      (x := ExtDart.newEdge) (y := y))

theorem extensionN_ringAdj_old_iff
    {x y : G.Dart} :
    (extensionN G x0).RingAdj (ExtDart.old x) (ExtDart.old y) ↔
      G.RingAdj x y ∨
        (PermReachable G.face (G.edge (G.face (G.edge x0))) x ∧
          PermReachable G.face x0 y) ∨
        (PermReachable G.face (G.edge (G.face (G.edge x0))) y ∧
          PermReachable G.face x0 x) := by
  constructor
  · rintro ⟨z, hxz, hzy⟩
    cases z with
    | new =>
        have hx_x0 : PermReachable G.face x x0 := by
          simpa [extensionNFaceProj] using
            extensionNFaceProj_of_faceReachable (G := G) x0 hxz
        have hp_y :
            PermReachable G.face
              (G.face (G.edge (G.face (G.edge x0)))) y := by
          have hproj :=
            extensionNFaceProj_of_faceReachable (G := G) x0 hzy
          simpa [extensionNFaceProj, extensionN, ExtDart.Perm.edge] using hproj
        have hq_y :
            PermReachable G.face (G.edge (G.face (G.edge x0))) y :=
          PermReachable.trans G.face
            (PermReachable.forward G.face (G.edge (G.face (G.edge x0))))
            hp_y
        exact Or.inr (Or.inr
          ⟨hq_y, PermReachable.symm G.face hx_x0⟩)
    | newEdge =>
        have hx_p :
            PermReachable G.face x
              (G.face (G.edge (G.face (G.edge x0)))) := by
          simpa [extensionNFaceProj] using
            extensionNFaceProj_of_faceReachable (G := G) x0 hxz
        have hq_x :
            PermReachable G.face (G.edge (G.face (G.edge x0))) x :=
          PermReachable.trans G.face
            (PermReachable.forward G.face (G.edge (G.face (G.edge x0))))
            (PermReachable.symm G.face hx_p)
        have hx0_y : PermReachable G.face x0 y := by
          have hproj :=
            extensionNFaceProj_of_faceReachable (G := G) x0 hzy
          simpa [extensionNFaceProj, extensionN, ExtDart.Perm.edge] using hproj
        exact Or.inr (Or.inl ⟨hq_x, hx0_y⟩)
    | old z =>
        refine Or.inl ⟨z, ?_, ?_⟩
        · simpa [extensionNFaceProj] using
            extensionNFaceProj_of_faceReachable (G := G) x0 hxz
        · have hproj :=
            extensionNFaceProj_of_faceReachable (G := G) x0 hzy
          simpa [extensionNFaceProj, extensionN, ExtDart.Perm.edge] using hproj
  · intro hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨z, hxz, hzy⟩
      refine ⟨ExtDart.old z,
        extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxz, ?_⟩
      simpa [extensionN, ExtDart.Perm.edge] using
        extensionN_old_faceReachable_of_faceReachable (G := G) x0 hzy
    · rcases hxy with hxy | hyx
      · rcases hxy with ⟨hqx, hx0y⟩
        refine ⟨ExtDart.newEdge, ?_, ?_⟩
        · have hxq :
              PermReachable G.face x (G.edge (G.face (G.edge x0))) :=
            PermReachable.symm G.face hqx
          exact PermReachable.trans (extensionN G x0).face
            (extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxq)
            (extensionN_old_edge_face_edge_faceReachable_newEdge (G := G) x0)
        · have hnew_y :
              PermReachable (extensionN G x0).face
                ExtDart.new (ExtDart.old y) :=
            PermReachable.trans (extensionN G x0).face
              (extensionN_faceReachable_new_old_x0 (G := G) x0)
              (extensionN_old_faceReachable_of_faceReachable
                (G := G) x0 hx0y)
          simpa [extensionN, ExtDart.Perm.edge] using hnew_y
      · rcases hyx with ⟨hqy, hx0x⟩
        refine ⟨ExtDart.new, ?_, ?_⟩
        · have hxx0 : PermReachable G.face x x0 :=
            PermReachable.symm G.face hx0x
          exact PermReachable.trans (extensionN G x0).face
            (extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxx0)
            (PermReachable.symm (extensionN G x0).face
              (extensionN_faceReachable_new_old_x0 (G := G) x0))
        · have hp_y :
              PermReachable G.face
                (G.face (G.edge (G.face (G.edge x0)))) y :=
            PermReachable.trans G.face
              (PermReachable.symm G.face
                (PermReachable.forward G.face
                  (G.edge (G.face (G.edge x0)))))
              hqy
          have hnewEdge_y :
              PermReachable (extensionN G x0).face
                ExtDart.newEdge (ExtDart.old y) :=
            PermReachable.trans (extensionN G x0).face
              (extensionN_faceReachable_newEdge_to_old_proj (G := G) x0)
              (extensionN_old_faceReachable_of_faceReachable
                (G := G) x0 hp_y)
          simpa [extensionN, ExtDart.Perm.edge] using hnewEdge_y

theorem extensionN_ringAdj_old_of_ringAdj
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionN G x0).RingAdj (ExtDart.old x) (ExtDart.old y) :=
  (extensionN_ringAdj_old_iff (G := G) x0).2 (Or.inl hxy)

theorem extensionNOld_ringAdj_iff
    {x y : G.Dart} :
    (extensionN G x0).RingAdj
        (extensionNOld G x0 x) (extensionNOld G x0 y) ↔
      G.RingAdj x y ∨
        (PermReachable G.face (G.edge (G.face (G.edge x0))) x ∧
          PermReachable G.face x0 y) ∨
        (PermReachable G.face (G.edge (G.face (G.edge x0))) y ∧
          PermReachable G.face x0 x) :=
  extensionN_ringAdj_old_iff (G := G) x0

theorem extensionNOld_ringAdj_of_ringAdj
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionN G x0).RingAdj
      (extensionNOld G x0 x) (extensionNOld G x0 y) :=
  extensionN_ringAdj_old_of_ringAdj (G := G) x0 hxy

theorem extensionN_exists_old_faceReachable
    (x : (extensionN G x0).Dart) :
    ∃ y : G.Dart,
      PermReachable (extensionN G x0).face x (ExtDart.old y) := by
  cases x with
  | new =>
      exact ⟨x0, extensionN_faceReachable_new_old_x0 (G := G) x0⟩
  | newEdge =>
      exact ⟨G.face (G.edge (G.face (G.edge x0))),
        extensionN_faceReachable_newEdge_to_old_proj (G := G) x0⟩
  | old y =>
      exact ⟨y, PermReachable.refl (extensionN G x0).face (ExtDart.old y)⟩

theorem extensionN_old_generatedReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    (extensionN G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  (extensionN G x0).facePermReachable_reachable
    (extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxy)

/-- The `ecpN` constructor preserves face orbits. -/
noncomputable def extensionNFaceOrbitEquiv :
    (extensionN G x0).FaceOrbit ≃ G.FaceOrbit where
  toFun :=
    Quotient.lift
      (fun x => PermOrbit.of G.face (extensionNFaceProj G x0 x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of G.face
          (extensionNFaceProj_of_faceReachable (G := G) x0 hxy))
  invFun :=
    Quotient.lift
      (fun x => PermOrbit.of (extensionN G x0).face (ExtDart.old x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of (extensionN G x0).face
          (extensionN_old_faceReachable_of_faceReachable (G := G) x0 hxy))
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            exact PermReachable.symm (extensionN G x0).face (by
              simpa [extensionN, ExtensionN.face_new, extensionNFaceProj] using
                (PermReachable.forward (extensionN G x0).face ExtDart.new))
        | newEdge =>
            apply PermOrbit.of_eq_of
            exact PermReachable.symm (extensionN G x0).face (by
              simpa [extensionNFaceProj] using
                (extensionN_faceReachable_newEdge_to_old_proj (G := G) x0))
        | old y =>
            rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        rfl

theorem extensionN_faceOrbitCount :
    (extensionN G x0).faceOrbitCount = G.faceOrbitCount := by
  unfold Hypermap.faceOrbitCount
  exact Nat.card_congr (extensionNFaceOrbitEquiv (G := G) x0)

theorem extensionN_eulerRight_of_nodeOrbitCount
    (hnode :
      (extensionN G x0).nodeOrbitCount = G.nodeOrbitCount + 1) :
    (extensionN G x0).eulerRight = G.eulerRight + 2 := by
  unfold Hypermap.eulerRight
  rw [extensionN_edgeOrbitCount (G := G) x0,
    hnode, extensionN_faceOrbitCount (G := G) x0]
  omega

theorem extensionN_eulerLeft_of_componentCount
    (hcomp :
      (extensionN G x0).componentCount = G.componentCount) :
    (extensionN G x0).eulerLeft = G.eulerLeft + 2 := by
  unfold Hypermap.eulerLeft
  rw [hcomp, extensionN_card (G := G) x0]
  omega

theorem extensionN_genus_of_counts
    (hcomp :
      (extensionN G x0).componentCount = G.componentCount)
    (hnode :
      (extensionN G x0).nodeOrbitCount = G.nodeOrbitCount + 1) :
    (extensionN G x0).genus = G.genus := by
  unfold Hypermap.genus
  rw [extensionN_eulerLeft_of_componentCount (G := G) x0 hcomp,
    extensionN_eulerRight_of_nodeOrbitCount (G := G) x0 hnode,
    Nat.add_sub_add_right]

theorem extensionN_eulerPlanar_iff_of_counts
    (hcomp :
      (extensionN G x0).componentCount = G.componentCount)
    (hnode :
      (extensionN G x0).nodeOrbitCount = G.nodeOrbitCount + 1) :
    (extensionN G x0).EulerPlanar ↔ G.EulerPlanar := by
  simp [Hypermap.EulerPlanar,
    extensionN_genus_of_counts (G := G) x0 hcomp hnode]

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
