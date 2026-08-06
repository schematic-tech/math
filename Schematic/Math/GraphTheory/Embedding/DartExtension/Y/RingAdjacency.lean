import Schematic.Math.GraphTheory.Embedding.DartExtension.Y.Construction

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem extensionU_faceReachable_extensionY_newEdgeProj_old_x0 :
    PermReachable (extensionU G x0).face
      (extensionNFaceProj (extensionU G x0) ExtDart.new ExtDart.newEdge)
      (ExtDart.old x0) := by
  let a : (extensionU G x0).Dart := ExtDart.old (G.edge (G.node x0))
  have hstep :
      PermReachable (extensionU G x0).face a
        (extensionNFaceProj (extensionU G x0) ExtDart.new ExtDart.newEdge) := by
    have h := PermReachable.forward (extensionU G x0).face a
    simpa [a, extensionNFaceProj, extensionU, ExtDart.Perm.edge,
      ExtensionU.face, ExtensionU.faceToFun] using h
  have hold :
      PermReachable (extensionU G x0).face a (ExtDart.old x0) := by
    have h :=
      extensionU_old_faceReachable_forward (G := G) x0
        (G.edge (G.node x0))
    simpa [a, G.face_edge_node x0] using h
  exact PermReachable.trans (extensionU G x0).face
    (PermReachable.symm (extensionU G x0).face hstep) hold

theorem extensionY_faceReachable_newEdge_old_iff
    {y : G.Dart} :
    PermReachable (extensionY G x0).face
      ExtDart.newEdge (extensionYOld G x0 y) ↔
      PermReachable G.face x0 y := by
  constructor
  · intro hy
    unfold extensionY extensionYOld at hy
    have hproj :=
      (extensionN_faceReachable_newEdge_iff_proj
        (G := extensionU G x0) ExtDart.new
        (y := ExtDart.old (ExtDart.old y))).1 hy
    have hq :=
      extensionU_faceReachable_extensionY_newEdgeProj_old_x0
        (G := G) x0
    have hold :
        PermReachable (extensionU G x0).face
          (ExtDart.old x0) (ExtDart.old y) :=
      PermReachable.trans (extensionU G x0).face
        (PermReachable.symm (extensionU G x0).face hq)
        (by simpa [extensionNFaceProj] using hproj)
    exact (extensionU_old_faceReachable_iff (G := G) x0
      (x := x0) (y := y)).1 hold
  · intro hy
    unfold extensionY extensionYOld
    have hq :=
      extensionU_faceReachable_extensionY_newEdgeProj_old_x0
        (G := G) x0
    have hold :
        PermReachable (extensionU G x0).face
          (ExtDart.old x0) (ExtDart.old y) :=
      (extensionU_old_faceReachable_iff (G := G) x0
        (x := x0) (y := y)).2 hy
    exact
      (extensionN_faceReachable_newEdge_iff_proj
        (G := extensionU G x0) ExtDart.new
        (y := ExtDart.old (ExtDart.old y))).2
        (by
          simpa [extensionNFaceProj] using
            PermReachable.trans (extensionU G x0).face hq hold)

theorem extensionY_faceReachable_old_newEdge_old_iff
    {y : G.Dart} :
    PermReachable (extensionY G x0).face
      (ExtDart.old ExtDart.newEdge) (extensionYOld G x0 y) ↔
      PermReachable G.face (G.node x0) y := by
  unfold extensionY extensionYOld
  exact Iff.trans
    (extensionN_old_faceReachable_iff
      (G := extensionU G x0) ExtDart.new
      (x := ExtDart.newEdge) (y := ExtDart.old y))
    (Iff.trans
      (extensionU_faceReachable_newEdge_iff_old_node (G := G) x0)
      (extensionU_old_faceReachable_iff (G := G) x0
        (x := G.node x0) (y := y)))

theorem extensionY_ringAdj_new_old_iff
    {y : G.Dart} :
    (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) ↔
      PermReachable G.face x0 y ∨
        PermReachable G.face (G.node x0) y := by
  constructor
  · rintro ⟨z, hnz, hzy⟩
    have hzproj :=
      (extensionY_faceReachable_new_iff_proj_eq_new
        (G := G) x0 (u := z)).1 hnz
    cases z with
    | new =>
        exact Or.inl
          ((extensionY_faceReachable_newEdge_old_iff
            (G := G) x0 (y := y)).1 (by
              simpa [extensionY, ExtDart.Perm.edge] using hzy))
    | newEdge =>
        have hq :=
          extensionU_faceReachable_extensionY_newEdgeProj_old_x0
            (G := G) x0
        rw [hzproj] at hq
        have hbad := extensionU_faceReachable_from_new (G := G) x0 hq
        cases hbad
    | old z =>
        cases z with
        | new =>
            exact Or.inr
              ((extensionY_faceReachable_old_newEdge_old_iff
                (G := G) x0 (y := y)).1 (by
                  simpa [extensionY, ExtDart.Perm.edge] using hzy))
        | newEdge =>
            simp [extensionNFaceProj] at hzproj
        | old a =>
            simp [extensionNFaceProj] at hzproj
  · intro hy
    rcases hy with hy | hy
    · refine ⟨ExtDart.new,
        PermReachable.refl (extensionY G x0).face ExtDart.new, ?_⟩
      simpa [extensionY, ExtDart.Perm.edge] using
        (extensionY_faceReachable_newEdge_old_iff
          (G := G) x0 (y := y)).2 hy
    · refine ⟨ExtDart.old ExtDart.new,
        ?_, ?_⟩
      · unfold extensionY
        exact extensionN_faceReachable_new_old_x0
          (G := extensionU G x0) ExtDart.new
      · simpa [extensionY, ExtDart.Perm.edge] using
          (extensionY_faceReachable_old_newEdge_old_iff
            (G := G) x0 (y := y)).2 hy

theorem extensionY_ringAdj_new_old_iff_faceBand
    {y : G.Dart} :
    (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) ↔
      G.FaceBand [x0, G.node x0] y := by
  rw [extensionY_ringAdj_new_old_iff (G := G) x0]
  rw [FaceBand.pair]

theorem extensionY_ringAdj_new_old_iff_faceBand_coq
    {y : G.Dart} :
    (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) ↔
      G.FaceBand [G.node x0, x0] y := by
  rw [extensionY_ringAdj_new_old_iff (G := G) x0]
  rw [FaceBand.pair]
  constructor
  · rintro (hx | hn)
    · exact Or.inr hx
    · exact Or.inl hn
  · rintro (hn | hx)
    · exact Or.inr hn
    · exact Or.inl hx

theorem extensionY_ringAdj_new_old_of_faceReachable_x0
    {y : G.Dart}
    (hy : PermReachable G.face x0 y) :
    (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) :=
  (extensionY_ringAdj_new_old_iff (G := G) x0 (y := y)).2 (Or.inl hy)

theorem extensionY_ringAdj_new_old_of_faceReachable_node
    {y : G.Dart}
    (hy : PermReachable G.face (G.node x0) y) :
    (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) :=
  (extensionY_ringAdj_new_old_iff (G := G) x0 (y := y)).2 (Or.inr hy)

theorem extensionY_ringAdj_new_old_of_faceReachable_x0_or_node
    {y : G.Dart}
    (hy : PermReachable G.face x0 y ∨
      PermReachable G.face (G.node x0) y) :
    (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) :=
  (extensionY_ringAdj_new_old_iff (G := G) x0 (y := y)).2 hy

theorem extensionY_ringAdj_new_of_faceReachable_old
    {u : (extensionY G x0).Dart} {y : G.Dart}
    (hy : PermReachable G.face x0 y ∨
      PermReachable G.face (G.node x0) y)
    (hyu : PermReachable (extensionY G x0).face
      (extensionYOld G x0 y) u) :
    (extensionY G x0).RingAdj ExtDart.new u :=
  Hypermap.RingAdj.of_faceReachable_right (G := extensionY G x0)
    (extensionY_ringAdj_new_old_of_faceReachable_x0_or_node
      (G := G) x0 hy)
    hyu

theorem extensionY_ringAdj_new_of_faceBand_old
    {u : (extensionY G x0).Dart} {y : G.Dart}
    (hy : G.FaceBand [x0, G.node x0] y)
    (hyu : PermReachable (extensionY G x0).face
      (extensionYOld G x0 y) u) :
    (extensionY G x0).RingAdj ExtDart.new u :=
  extensionY_ringAdj_new_of_faceReachable_old (G := G) x0
    ((FaceBand.pair (G := G)).1 hy) hyu

theorem extensionY_exists_old_faceReachable_or_new
    (u : (extensionY G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionY G x0).face u (extensionYOld G x0 x)) ∨
      PermReachable (extensionY G x0).face ExtDart.new u := by
  unfold extensionY extensionYOld
  obtain ⟨w, huw⟩ :=
    extensionN_exists_old_faceReachable
      (G := extensionU G x0) ExtDart.new u
  rcases extensionU_exists_old_faceReachable_or_new
      (G := G) x0 w with hOld | hNew
  · rcases hOld with ⟨x, hwx⟩
    exact Or.inl ⟨x,
      PermReachable.trans (extensionN (extensionU G x0) ExtDart.new).face
        huw
        (extensionN_old_faceReachable_of_faceReachable
          (G := extensionU G x0) ExtDart.new hwx)⟩
  · have hnew_old_inner :
        PermReachable (extensionN (extensionU G x0) ExtDart.new).face
          ExtDart.new (ExtDart.old ExtDart.new) :=
      extensionN_faceReachable_new_old_x0
        (G := extensionU G x0) ExtDart.new
    have hinner_w :
        PermReachable (extensionN (extensionU G x0) ExtDart.new).face
          (ExtDart.old ExtDart.new) (ExtDart.old w) :=
      extensionN_old_faceReachable_of_faceReachable
        (G := extensionU G x0) ExtDart.new hNew
    exact Or.inr
      (PermReachable.trans (extensionN (extensionU G x0) ExtDart.new).face
        (PermReachable.trans (extensionN (extensionU G x0) ExtDart.new).face
          hnew_old_inner hinner_w)
        (PermReachable.symm
          (extensionN (extensionU G x0) ExtDart.new).face huw))

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
