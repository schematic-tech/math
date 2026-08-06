import Schematic.Math.GraphTheory.Embedding.DartExtension.Constructions

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem extensionU_old_reachable_of_link
    {x y : G.Dart}
    (hxy : G.Link x y) :
    (extensionU G x0).Reachable (ExtDart.old x) (ExtDart.old y) := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    simpa [extensionU, ExtDart.Perm.edge] using
      (extensionU G x0).reachable_edge (ExtDart.old x)
  · subst y
    by_cases hx : x = G.node x0
    · have h1 :
          (extensionU G x0).Reachable
            (ExtDart.old x) ExtDart.new := by
        exact Relation.ReflTransGen.single
          (Or.inr (Or.inl (by
            change ExtDart.new =
              ExtensionU.node G x0 (ExtDart.old x)
            simp [ExtensionU.node, ExtensionU.nodeToFun, hx])))
      have h2 :
          (extensionU G x0).Reachable
            ExtDart.new ExtDart.newEdge := by
        simpa [extensionU, ExtDart.Perm.edge] using
          (extensionU G x0).reachable_edge ExtDart.new
      have h3 :
          (extensionU G x0).Reachable
            ExtDart.newEdge (ExtDart.old (G.node (G.node x0))) := by
        exact Relation.ReflTransGen.single
          (Or.inr (Or.inl (by
            change ExtDart.old (G.node (G.node x0)) =
              ExtensionU.node G x0 ExtDart.newEdge
            rfl)))
      simpa [hx] using h1.trans (h2.trans h3)
    · simpa [extensionU, ExtensionU.node, ExtensionU.nodeToFun, hx] using
        (Relation.ReflTransGen.single
          (Or.inr (Or.inl (by
            change ExtDart.old (G.node x) =
              ExtensionU.node G x0 (ExtDart.old x)
            simp [ExtensionU.node, ExtensionU.nodeToFun, hx]))) :
          (extensionU G x0).Reachable
            (ExtDart.old x) (ExtDart.old (G.node x)))
  · subst y
    by_cases hx : G.face x = G.node x0
    · have h1 :
          (extensionU G x0).Reachable
            (ExtDart.old x) ExtDart.newEdge := by
        exact Relation.ReflTransGen.single
          (Or.inr (Or.inr (by
            change ExtDart.newEdge =
              ExtensionU.face G x0 (ExtDart.old x)
            simp [ExtensionU.face, ExtensionU.faceToFun, hx])))
      have h2 :
          (extensionU G x0).Reachable
            ExtDart.newEdge (ExtDart.old (G.node x0)) := by
        exact Relation.ReflTransGen.single
          (Or.inr (Or.inr (by
            change ExtDart.old (G.node x0) =
              ExtensionU.face G x0 ExtDart.newEdge
            rfl)))
      simpa [hx] using h1.trans h2
    · simpa [extensionU, ExtensionU.face, ExtensionU.faceToFun, hx] using
        (Relation.ReflTransGen.single
          (Or.inr (Or.inr (by
            change ExtDart.old (G.face x) =
              ExtensionU.face G x0 (ExtDart.old x)
            simp [ExtensionU.face, ExtensionU.faceToFun, hx]))) :
          (extensionU G x0).Reachable
            (ExtDart.old x) (ExtDart.old (G.face x)))

theorem extensionU_old_reachable_of_reachable
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (extensionU G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h => extensionU_old_reachable_of_link (G := G) x0 h) hxy

theorem extensionU_reachable_to_old_base
    (hG : G.Connected)
    (x : (extensionU G x0).Dart) :
    (extensionU G x0).Reachable x (ExtDart.old x0) := by
  cases x with
  | new =>
      have h1 :
          (extensionU G x0).Reachable
            ExtDart.new ExtDart.newEdge := by
        simpa [extensionU, ExtDart.Perm.edge] using
          (extensionU G x0).reachable_edge ExtDart.new
      have h2 :
          (extensionU G x0).Reachable
            ExtDart.newEdge (ExtDart.old (G.node x0)) := by
        simpa [extensionU, ExtensionU.face, ExtensionU.faceToFun] using
          (extensionU G x0).reachable_face ExtDart.newEdge
      have h3 :
          (extensionU G x0).Reachable
            (ExtDart.old (G.node x0)) (ExtDart.old x0) :=
        extensionU_old_reachable_of_reachable (G := G) x0
          (Connected.reachable (G := G) hG (G.node x0) x0)
      exact h1.trans (h2.trans h3)
  | newEdge =>
      have h1 :
          (extensionU G x0).Reachable
            ExtDart.newEdge (ExtDart.old (G.node x0)) := by
        simpa [extensionU, ExtensionU.face, ExtensionU.faceToFun] using
          (extensionU G x0).reachable_face ExtDart.newEdge
      have h2 :
          (extensionU G x0).Reachable
            (ExtDart.old (G.node x0)) (ExtDart.old x0) :=
        extensionU_old_reachable_of_reachable (G := G) x0
          (Connected.reachable (G := G) hG (G.node x0) x0)
      exact h1.trans h2
  | old y =>
      exact extensionU_old_reachable_of_reachable (G := G) x0
        (Connected.reachable (G := G) hG y x0)

theorem extensionU_connected
    (hG : G.Connected) :
    (extensionU G x0).Connected := by
  constructor
  · exact ⟨ExtDart.new⟩
  · intro x y
    exact (extensionU_reachable_to_old_base (G := G) x0 hG x).trans
      ((extensionU G x0).reachable_symm
        (extensionU_reachable_to_old_base (G := G) x0 hG y))

@[simp]
theorem extensionU_face_new :
    (extensionU G x0).face ExtDart.new = ExtDart.new :=
  rfl

@[simp]
theorem extensionU_face_symm_new :
    (extensionU G x0).face.symm ExtDart.new = ExtDart.new :=
  rfl

theorem extensionU_face_link_from_new
    {y : (extensionU G x0).Dart}
    (h : PermLink (extensionU G x0).face ExtDart.new y) :
    y = ExtDart.new := by
  cases h with
  | forward => rfl
  | backward => rfl

theorem extensionU_faceReachable_from_new
    {y : (extensionU G x0).Dart}
    (h : PermReachable (extensionU G x0).face ExtDart.new y) :
    y = ExtDart.new := by
  induction h with
  | refl => rfl
  | tail hxb hbc ih =>
      subst ih
      exact extensionU_face_link_from_new (G := G) x0 hbc

theorem extensionU_faceReachable_new_iff
    {y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).face ExtDart.new y ↔
      y = ExtDart.new := by
  constructor
  · exact extensionU_faceReachable_from_new (G := G) x0
  · intro hy
    subst hy
    exact PermReachable.refl (extensionU G x0).face ExtDart.new

theorem extensionU_faceReachable_to_new
    {y : (extensionU G x0).Dart}
    (h : PermReachable (extensionU G x0).face y ExtDart.new) :
    y = ExtDart.new := by
  have hsymm :
      PermReachable (extensionU G x0).face ExtDart.new y :=
    PermReachable.symm (extensionU G x0).face h
  exact extensionU_faceReachable_from_new (G := G) x0 hsymm

theorem extensionU_faceReachable_to_new_iff
    {y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).face y ExtDart.new ↔
      y = ExtDart.new := by
  constructor
  · exact extensionU_faceReachable_to_new (G := G) x0
  · intro hy
    subst hy
    exact PermReachable.refl (extensionU G x0).face ExtDart.new

theorem extensionU_not_faceReachable_new_edge :
    ¬ PermReachable (extensionU G x0).face
      ExtDart.new ((extensionU G x0).edge ExtDart.new) := by
  intro h
  have hEq := extensionU_faceReachable_from_new (G := G) x0 h
  cases hEq

theorem extensionU_not_faceReachable_newEdge_edge :
    ¬ PermReachable (extensionU G x0).face
      ExtDart.newEdge ((extensionU G x0).edge ExtDart.newEdge) := by
  intro h
  have hEq := extensionU_faceReachable_to_new (G := G) x0 (by
    simpa [extensionU, ExtDart.Perm.edge] using h)
  cases hEq

/-- Projection used to compare `ecpU` face orbits with original face orbits. -/
def extensionUFaceProj : (extensionU G x0).Dart → G.Dart
  | ExtDart.new => x0
  | ExtDart.newEdge => G.face.symm (G.node x0)
  | ExtDart.old y => y

theorem extensionUFaceProj_face
    (x : (extensionU G x0).Dart) :
    PermReachable G.face
      (extensionUFaceProj G x0 x)
      (extensionUFaceProj G x0 ((extensionU G x0).face x)) := by
  cases x with
  | new =>
      exact PermReachable.refl G.face x0
  | newEdge =>
      change PermReachable G.face
        (G.face.symm (G.node x0)) (G.node x0)
      simpa using
        (PermReachable.forward G.face (G.face.symm (G.node x0)))
  | old y =>
      by_cases hy : G.face y = G.node x0
      · change PermReachable G.face y
          (extensionUFaceProj G x0
            (ExtensionU.face G x0 (ExtDart.old y)))
        rw [ExtensionU.face_old]
        simp [extensionUFaceProj, hy]
        exact PermReachable.trans G.face
          (PermReachable.forward G.face y)
          (by
            have hback :
                PermReachable G.face (G.node x0)
                  (G.face.symm (G.node x0)) :=
              PermReachable.backward G.face (G.node x0)
            simpa [hy] using hback)
      · change PermReachable G.face y
          (extensionUFaceProj G x0
            (ExtensionU.face G x0 (ExtDart.old y)))
        rw [ExtensionU.face_old]
        simp [extensionUFaceProj, hy]
        exact PermReachable.forward G.face y

theorem extensionUFaceProj_of_face_link
    {x y : (extensionU G x0).Dart}
    (hxy : PermLink (extensionU G x0).face x y) :
    PermReachable G.face
      (extensionUFaceProj G x0 x) (extensionUFaceProj G x0 y) := by
  cases hxy with
  | forward =>
      exact extensionUFaceProj_face (G := G) x0 x
  | backward =>
      have hforward :=
        extensionUFaceProj_face (G := G) x0
          ((extensionU G x0).face.symm x)
      exact PermReachable.symm G.face (by
        simpa using hforward)

theorem extensionUFaceProj_of_faceReachable
    {x y : (extensionU G x0).Dart}
    (hxy : PermReachable (extensionU G x0).face x y) :
    PermReachable G.face
      (extensionUFaceProj G x0 x) (extensionUFaceProj G x0 y) :=
  Relation.ReflTransGen.lift' (extensionUFaceProj G x0)
    (fun _ _ h => extensionUFaceProj_of_face_link (G := G) x0 h) hxy

theorem extensionU_old_faceReachable_forward
    (x : G.Dart) :
    PermReachable (extensionU G x0).face
      (ExtDart.old x) (ExtDart.old (G.face x)) := by
  by_cases hx : G.face x = G.node x0
  · have h1 :
        PermReachable (extensionU G x0).face
          (ExtDart.old x) ExtDart.newEdge := by
      have hstep :=
        PermReachable.forward (extensionU G x0).face (ExtDart.old x)
      have hface :
          (extensionU G x0).face (ExtDart.old x) = ExtDart.newEdge := by
        change ExtensionU.face G x0 (ExtDart.old x) = ExtDart.newEdge
        simp [ExtensionU.face, ExtensionU.faceToFun, hx]
      simpa [hface] using hstep
    have h2 :
        PermReachable (extensionU G x0).face
          ExtDart.newEdge (ExtDart.old (G.node x0)) := by
      have hstep :=
        PermReachable.forward (extensionU G x0).face ExtDart.newEdge
      have hface :
          (extensionU G x0).face ExtDart.newEdge =
            ExtDart.old (G.node x0) := by
        rfl
      simpa [hface] using hstep
    simpa [hx] using PermReachable.trans (extensionU G x0).face h1 h2
  · have hstep :=
      PermReachable.forward (extensionU G x0).face (ExtDart.old x)
    have hface :
        (extensionU G x0).face (ExtDart.old x) =
          ExtDart.old (G.face x) := by
      change ExtensionU.face G x0 (ExtDart.old x) =
        ExtDart.old (G.face x)
      simp [ExtensionU.face, ExtensionU.faceToFun, hx]
    simpa [hface] using hstep

theorem extensionU_old_faceReachable_of_face_link
    {x y : G.Dart}
    (hxy : PermLink G.face x y) :
    PermReachable (extensionU G x0).face
      (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      exact extensionU_old_faceReachable_forward (G := G) x0 x
  | backward =>
      have hforward :
          PermReachable (extensionU G x0).face
            (ExtDart.old (G.face.symm x)) (ExtDart.old x) :=
        by
          have h :=
            extensionU_old_faceReachable_forward (G := G) x0
              (G.face.symm x)
          simpa using h
      exact PermReachable.symm (extensionU G x0).face hforward

theorem extensionU_old_faceReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionU G x0).face
      (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h => extensionU_old_faceReachable_of_face_link (G := G) x0 h) hxy

theorem extensionU_old_faceReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionU G x0).face
      (ExtDart.old x) (ExtDart.old y) ↔
      PermReachable G.face x y := by
  constructor
  · intro hxy
    have hproj :=
      extensionUFaceProj_of_faceReachable (G := G) x0 hxy
    exact hproj
  · exact extensionU_old_faceReachable_of_faceReachable (G := G) x0

theorem extensionU_old_generatedReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    (extensionU G x0).Reachable (ExtDart.old x) (ExtDart.old y) :=
  (extensionU G x0).facePermReachable_reachable
    (extensionU_old_faceReachable_of_faceReachable (G := G) x0 hxy)

theorem extensionU_old_faceSymm_node_faceReachable_newEdge :
    PermReachable (extensionU G x0).face
      (ExtDart.old (G.face.symm (G.node x0))) ExtDart.newEdge := by
  have hstep :=
    PermReachable.forward (extensionU G x0).face
      (ExtDart.old (G.face.symm (G.node x0)))
  have hface :
      (extensionU G x0).face
        (ExtDart.old (G.face.symm (G.node x0))) = ExtDart.newEdge := by
    change ExtensionU.face G x0
      (ExtDart.old (G.face.symm (G.node x0))) = ExtDart.newEdge
    simp [ExtensionU.face, ExtensionU.faceToFun]
  simpa [hface] using hstep

theorem extensionU_faceReachable_newEdge_old_faceSymm_node :
    PermReachable (extensionU G x0).face ExtDart.newEdge
      (ExtDart.old (G.face.symm (G.node x0))) :=
  PermReachable.symm (extensionU G x0).face
    (extensionU_old_faceSymm_node_faceReachable_newEdge (G := G) x0)

theorem extensionU_faceReachable_old_of_faceReachable_proj
    {x : G.Dart} {y : (extensionU G x0).Dart}
    (hy : y ≠ ExtDart.new)
    (hxy :
      PermReachable G.face x (extensionUFaceProj G x0 y)) :
    PermReachable (extensionU G x0).face (ExtDart.old x) y := by
  cases y with
  | new =>
      exact False.elim (hy rfl)
  | newEdge =>
      have hold :
          PermReachable (extensionU G x0).face
            (ExtDart.old x)
            (ExtDart.old (G.face.symm (G.node x0))) := by
        simpa [extensionUFaceProj] using
          extensionU_old_faceReachable_of_faceReachable (G := G) x0 hxy
      exact PermReachable.trans (extensionU G x0).face hold
        (extensionU_old_faceSymm_node_faceReachable_newEdge (G := G) x0)
  | old z =>
      simpa [extensionUFaceProj] using
        extensionU_old_faceReachable_of_faceReachable (G := G) x0 hxy

theorem extensionU_faceReachable_old_iff_proj
    {x : G.Dart} {y : (extensionU G x0).Dart}
    (hy : y ≠ ExtDart.new) :
    PermReachable (extensionU G x0).face (ExtDart.old x) y ↔
      PermReachable G.face x (extensionUFaceProj G x0 y) := by
  constructor
  · intro hxy
    simpa [extensionUFaceProj] using
      extensionUFaceProj_of_faceReachable (G := G) x0 hxy
  · exact extensionU_faceReachable_old_of_faceReachable_proj
      (G := G) x0 hy

theorem extensionU_faceReachable_of_faceReachable_proj
    {x y : (extensionU G x0).Dart}
    (hx : x ≠ ExtDart.new)
    (hy : y ≠ ExtDart.new)
    (hxy :
      PermReachable G.face
        (extensionUFaceProj G x0 x)
        (extensionUFaceProj G x0 y)) :
    PermReachable (extensionU G x0).face x y := by
  cases x with
  | new =>
      exact False.elim (hx rfl)
  | newEdge =>
      exact PermReachable.trans (extensionU G x0).face
        (extensionU_faceReachable_newEdge_old_faceSymm_node (G := G) x0)
        (extensionU_faceReachable_old_of_faceReachable_proj
          (G := G) x0 (x := G.face.symm (G.node x0)) (y := y)
          hy (by
            simpa [extensionUFaceProj] using hxy))
  | old z =>
      exact extensionU_faceReachable_old_of_faceReachable_proj
        (G := G) x0 (x := z) (y := y) hy (by
          simpa [extensionUFaceProj] using hxy)

theorem extensionU_faceReachable_iff_proj_of_ne_new
    {x y : (extensionU G x0).Dart}
    (hx : x ≠ ExtDart.new)
    (hy : y ≠ ExtDart.new) :
    PermReachable (extensionU G x0).face x y ↔
      PermReachable G.face
        (extensionUFaceProj G x0 x)
        (extensionUFaceProj G x0 y) := by
  constructor
  · exact extensionUFaceProj_of_faceReachable (G := G) x0
  · exact extensionU_faceReachable_of_faceReachable_proj
      (G := G) x0 hx hy

theorem extensionU_faceReachable_newEdge_iff_proj
    {y : (extensionU G x0).Dart}
    (hy : y ≠ ExtDart.new) :
    PermReachable (extensionU G x0).face ExtDart.newEdge y ↔
      PermReachable G.face
        (G.face.symm (G.node x0))
        (extensionUFaceProj G x0 y) := by
  simpa [extensionUFaceProj] using
    (extensionU_faceReachable_iff_proj_of_ne_new (G := G) x0
      (x := ExtDart.newEdge) (y := y) (by intro h; cases h) hy)

theorem extensionU_faceReachable_newEdge_iff_old_node
    {y : (extensionU G x0).Dart} :
    PermReachable (extensionU G x0).face ExtDart.newEdge y ↔
      PermReachable (extensionU G x0).face
        (ExtDart.old (G.node x0)) y := by
  have hstep :
      PermReachable (extensionU G x0).face
        ExtDart.newEdge (ExtDart.old (G.node x0)) := by
    simpa [extensionU, ExtensionU.face, ExtensionU.faceToFun] using
      (PermReachable.forward (extensionU G x0).face ExtDart.newEdge)
  constructor
  · intro hy
    exact PermReachable.trans (extensionU G x0).face
      (PermReachable.symm (extensionU G x0).face hstep) hy
  · intro hy
    exact PermReachable.trans (extensionU G x0).face hstep hy

theorem extensionU_ringAdj_new_iff
    {y : (extensionU G x0).Dart} :
    (extensionU G x0).RingAdj ExtDart.new y ↔
      PermReachable (extensionU G x0).face ExtDart.newEdge y := by
  constructor
  · rintro ⟨z, hnz, hzy⟩
    have hz := extensionU_faceReachable_from_new (G := G) x0 hnz
    subst z
    simpa [extensionU, ExtDart.Perm.edge] using hzy
  · intro hy
    refine ⟨ExtDart.new,
      PermReachable.refl (extensionU G x0).face ExtDart.new, ?_⟩
    simpa [extensionU, ExtDart.Perm.edge] using hy

theorem extensionU_ringAdj_new_iff_proj
    {y : (extensionU G x0).Dart} :
    (extensionU G x0).RingAdj ExtDart.new y ↔
      y ≠ ExtDart.new ∧
        PermReachable G.face
          (G.face.symm (G.node x0))
          (extensionUFaceProj G x0 y) := by
  constructor
  · intro hxy
    have hface :=
      (extensionU_ringAdj_new_iff (G := G) x0 (y := y)).1 hxy
    have hy : y ≠ ExtDart.new := by
      intro hy
      subst y
      have hEq := extensionU_faceReachable_to_new (G := G) x0 hface
      cases hEq
    exact ⟨hy,
      (extensionU_faceReachable_newEdge_iff_proj (G := G) x0
        (y := y) hy).1 hface⟩
  · rintro ⟨hy, hproj⟩
    exact (extensionU_ringAdj_new_iff (G := G) x0 (y := y)).2
      ((extensionU_faceReachable_newEdge_iff_proj (G := G) x0
        (y := y) hy).2 hproj)

theorem extensionU_ringAdj_new_iff_old_node
    {y : (extensionU G x0).Dart} :
    (extensionU G x0).RingAdj ExtDart.new y ↔
      PermReachable (extensionU G x0).face
        (ExtDart.old (G.node x0)) y := by
  rw [extensionU_ringAdj_new_iff (G := G) x0,
    extensionU_faceReachable_newEdge_iff_old_node (G := G) x0]

theorem extensionU_ringAdj_old_iff
    {x y : G.Dart} :
    (extensionU G x0).RingAdj (ExtDart.old x) (ExtDart.old y) ↔
      G.RingAdj x y := by
  constructor
  · rintro ⟨z, hxz, hzy⟩
    cases z with
    | new =>
        have hEq := extensionU_faceReachable_to_new (G := G) x0 hxz
        cases hEq
    | newEdge =>
        have hfromNew :
            PermReachable (extensionU G x0).face
              ExtDart.new (ExtDart.old y) := by
          simpa [extensionU, ExtDart.Perm.edge] using hzy
        have hEq := extensionU_faceReachable_from_new (G := G) x0 hfromNew
        cases hEq
    | old z =>
        refine ⟨z, ?_, ?_⟩
        · simpa [extensionUFaceProj] using
            extensionUFaceProj_of_faceReachable (G := G) x0 hxz
        · have hproj :=
            extensionUFaceProj_of_faceReachable (G := G) x0 hzy
          simpa [extensionUFaceProj, extensionU, ExtDart.Perm.edge] using hproj
  · rintro ⟨z, hxz, hzy⟩
    refine ⟨ExtDart.old z,
      extensionU_old_faceReachable_of_faceReachable (G := G) x0 hxz, ?_⟩
    simpa [extensionU, ExtDart.Perm.edge] using
      extensionU_old_faceReachable_of_faceReachable (G := G) x0 hzy

theorem extensionU_ringAdj_old_of_ringAdj
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionU G x0).RingAdj (ExtDart.old x) (ExtDart.old y) :=
  (extensionU_ringAdj_old_iff (G := G) x0).2 hxy

theorem extensionU_exists_old_faceReachable_of_ne_new
    (x : (extensionU G x0).Dart)
    (hx : x ≠ ExtDart.new) :
    ∃ y : G.Dart,
      PermReachable (extensionU G x0).face x (ExtDart.old y) := by
  cases x with
  | new =>
      exact False.elim (hx rfl)
  | newEdge =>
      exact ⟨G.face.symm (G.node x0),
        extensionU_faceReachable_newEdge_old_faceSymm_node (G := G) x0⟩
  | old y =>
      exact ⟨y,
        PermReachable.refl (extensionU G x0).face (ExtDart.old y)⟩

theorem extensionU_exists_old_faceReachable_iff_ne_new
    (x : (extensionU G x0).Dart) :
    (∃ y : G.Dart,
      PermReachable (extensionU G x0).face x (ExtDart.old y)) ↔
      x ≠ ExtDart.new := by
  constructor
  · rintro ⟨y, hxy⟩ hx
    subst x
    have hEq := extensionU_faceReachable_from_new (G := G) x0 hxy
    cases hEq
  · exact extensionU_exists_old_faceReachable_of_ne_new (G := G) x0 x

theorem extensionU_exists_old_faceReachable_or_new
    (x : (extensionU G x0).Dart) :
    (∃ y : G.Dart,
      PermReachable (extensionU G x0).face x (ExtDart.old y)) ∨
      PermReachable (extensionU G x0).face ExtDart.new x := by
  by_cases hx : x = ExtDart.new
  · subst x
    exact Or.inr
      (PermReachable.refl (extensionU G x0).face ExtDart.new)
  · exact Or.inl
      (extensionU_exists_old_faceReachable_of_ne_new (G := G) x0 x hx)

/-- The `ecpU` constructor adds exactly one new face orbit.  The singleton
new-dart face maps to `none`; all other faces project to old face orbits. -/
noncomputable def extensionUFaceOrbitEquiv :
    (extensionU G x0).FaceOrbit ≃ Option G.FaceOrbit where
  toFun :=
    Quotient.lift
      (fun x =>
        if x = ExtDart.new then none
        else some (PermOrbit.of G.face (extensionUFaceProj G x0 x)))
      (by
        intro x y hxy
        by_cases hx : x = ExtDart.new
        · subst x
          have hy := extensionU_faceReachable_from_new (G := G) x0 hxy
          subst y
          simp
        · have hy : y ≠ ExtDart.new := by
            intro hy
            subst y
            exact hx (extensionU_faceReachable_to_new (G := G) x0 hxy)
          have hproj :=
            extensionUFaceProj_of_faceReachable (G := G) x0 hxy
          simp [hx, hy, PermOrbit.of_eq_of G.face hproj])
  invFun
    | none => PermOrbit.of (extensionU G x0).face ExtDart.new
    | some q =>
        Quotient.lift
          (fun x =>
            PermOrbit.of (extensionU G x0).face (ExtDart.old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (extensionU G x0).face
              (extensionU_old_faceReachable_of_faceReachable
                (G := G) x0 hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            rfl
        | newEdge =>
            apply PermOrbit.of_eq_of
            simpa [extensionUFaceProj] using
              (extensionU_old_faceSymm_node_faceReachable_newEdge
                (G := G) x0)
        | old y =>
            rfl
  right_inv := by
    intro q
    cases q with
    | none =>
        rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x =>
            rfl

theorem extensionU_faceOrbitCount :
    (extensionU G x0).faceOrbitCount = G.faceOrbitCount + 1 := by
  unfold Hypermap.faceOrbitCount
  rw [Nat.card_congr (extensionUFaceOrbitEquiv (G := G) x0)]
  haveI : Finite G.Dart := Finite.of_fintype G.Dart
  haveI : Finite G.FaceOrbit := Quotient.finite (permOrbitSetoid G.face)
  exact Finite.card_option

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
