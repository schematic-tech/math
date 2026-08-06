import Schematic.Math.GraphTheory.Embedding.DartExtension.H.Construction

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

theorem extensionH_faceReachable_new_iff_proj
    {u : (extensionH G x0).Dart} :
    PermReachable (extensionH G x0).face ExtDart.new u ↔
      PermReachable (extensionY G x0).face ExtDart.new
        (extensionNFaceProj (extensionY G x0) ExtDart.new u) := by
  unfold extensionH
  exact extensionN_faceReachable_new_iff_proj
    (G := extensionY G x0) ExtDart.new

theorem extensionH_faceReachable_newEdge_iff_proj
    {u : (extensionH G x0).Dart} :
    PermReachable (extensionH G x0).face ExtDart.newEdge u ↔
      PermReachable (extensionY G x0).face
        (extensionNFaceProj (extensionY G x0) ExtDart.new ExtDart.newEdge)
        (extensionNFaceProj (extensionY G x0) ExtDart.new u) := by
  unfold extensionH
  exact extensionN_faceReachable_newEdge_iff_proj
    (G := extensionY G x0) ExtDart.new

/-- The third original face band appearing in Coq's `adj_ecpH`, expressed
before simplifying the nested `ecpY` projection. -/
def extensionHNewEdgeBand (y : G.Dart) : Prop :=
  PermReachable (extensionY G x0).face
    (extensionNFaceProj (extensionY G x0) ExtDart.new ExtDart.newEdge)
    (extensionYOld G x0 y)

theorem extensionH_newEdgeProj_eq_old_face_edge
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0) :
    extensionNFaceProj (extensionY G x0) ExtDart.new ExtDart.newEdge =
      extensionYOld G x0 (G.face (G.edge x0)) := by
  unfold extensionNFaceProj extensionYOld
  change (extensionY G x0).face
      ((extensionY G x0).edge
        ((extensionY G x0).face ((extensionY G x0).edge ExtDart.new))) =
    ExtDart.old (ExtDart.old (G.face (G.edge x0)))
  have h1 : (extensionY G x0).edge ExtDart.new = ExtDart.newEdge := rfl
  have h2 : (extensionY G x0).face ExtDart.newEdge =
      ExtDart.old (ExtDart.old x0) := by
    exact extensionY_face_newEdge_of_proper (G := G) x0 hproper
  have h3 : (extensionY G x0).edge (ExtDart.old (ExtDart.old x0)) =
      ExtDart.old (ExtDart.old (G.edge x0)) := rfl
  have h4 :
      (extensionY G x0).face (ExtDart.old (ExtDart.old (G.edge x0))) =
        ExtDart.old (ExtDart.old (G.face (G.edge x0))) :=
    extensionY_face_old_edge_of_proper_long (G := G) x0 hproper hlong
  rw [h1, h2]
  change (extensionY G x0).face
      ((extensionY G x0).edge (ExtDart.old (ExtDart.old x0))) =
    ExtDart.old (ExtDart.old (G.face (G.edge x0)))
  rw [h3]
  exact h4

theorem extensionH_long_new_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0) :
    (extensionH G x0).LongRingHead ExtDart.new := by
  unfold Hypermap.LongRingHead
  have hyLong :
      (extensionY G x0).LongRingHead ExtDart.new :=
    extensionY_long_new_of_proper (G := G) x0 hproper
  have hproj :=
    extensionH_newEdgeProj_eq_old_face_edge
      (G := G) x0 hproper hlong
  rw [show (extensionH G x0).edge ExtDart.new = ExtDart.newEdge by rfl]
  unfold extensionH extensionN
  change Hypermap.ExtensionN.face (extensionY G x0) ExtDart.new
      ExtDart.newEdge ≠
    Hypermap.ExtensionN.node (extensionY G x0) ExtDart.new ExtDart.new
  rw [Hypermap.ExtensionN.face_newEdge, Hypermap.ExtensionN.node_new]
  rw [if_pos hyLong, if_pos hyLong]
  change ExtDart.old
      (extensionNFaceProj (extensionY G x0) ExtDart.new ExtDart.newEdge) ≠
    ExtDart.old ((extensionY G x0).node ExtDart.new)
  rw [hproj, extensionY_node_new]
  intro h
  have hEq := ExtDart.old_injective h
  cases hEq

theorem extensionHNewEdgeBand_iff_face_edge
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0)
    {y : G.Dart} :
    extensionHNewEdgeBand G x0 y ↔
      PermReachable G.face (G.face (G.edge x0)) y := by
  unfold extensionHNewEdgeBand
  rw [extensionH_newEdgeProj_eq_old_face_edge
    (G := G) x0 hproper hlong]
  exact extensionYOld_faceReachable_iff (G := G) x0
    (x := G.face (G.edge x0)) (y := y)

theorem extensionH_faceReachable_newEdge_old_iff_face_edge_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0)
    {y : G.Dart} :
    PermReachable (extensionH G x0).face
      ExtDart.newEdge (extensionHOld G x0 y) ↔
      PermReachable G.face (G.face (G.edge x0)) y := by
  rw [extensionH_faceReachable_newEdge_iff_proj (G := G) x0
    (u := extensionHOld G x0 y)]
  rw [extensionH_newEdgeProj_eq_old_face_edge
    (G := G) x0 hproper hlong]
  exact extensionYOld_faceReachable_iff (G := G) x0
    (x := G.face (G.edge x0)) (y := y)

theorem extensionHNewEdgeBand.of_faceReachable
    {x y : G.Dart}
    (hx : extensionHNewEdgeBand G x0 x)
    (hxy : PermReachable G.face x y) :
    extensionHNewEdgeBand G x0 y := by
  exact PermReachable.trans (extensionY G x0).face hx
    (extensionYOld_faceReachable_of_faceReachable (G := G) x0 hxy)

theorem extensionH_not_faceReachable_new_old
    (y : G.Dart) :
    ¬ PermReachable (extensionH G x0).face
      ExtDart.new (extensionHOld G x0 y) := by
  intro h
  have hproj :=
    (extensionH_faceReachable_new_iff_proj (G := G) x0
      (u := extensionHOld G x0 y)).1 h
  exact extensionY_not_faceReachable_new_old (G := G) x0 y
    (by simpa [extensionHOld, extensionNFaceProj] using hproj)

theorem extensionH_not_faceReachable_new_edge_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0) :
    ¬ PermReachable (extensionH G x0).face
      ExtDart.new ((extensionH G x0).edge ExtDart.new) := by
  intro h
  have hproj :=
    (extensionH_faceReachable_new_iff_proj
      (G := G) x0 (u := (extensionH G x0).edge ExtDart.new)).1 h
  change PermReachable (extensionY G x0).face ExtDart.new
    (extensionNFaceProj (extensionY G x0) ExtDart.new
      ExtDart.newEdge) at hproj
  rw [extensionH_newEdgeProj_eq_old_face_edge
    (G := G) x0 hproper hlong] at hproj
  exact extensionY_not_faceReachable_new_old (G := G) x0
    (G.face (G.edge x0)) hproj

/-- Coq `bridgeless_ecpH` needs only a proper perimeter.  The fresh face of
`extensionH` consists of the three nested `new` darts, whereas the other end
of the fresh edge is the outer `newEdge`; hence they cannot be face-reachable.
This sharper statement removes the unnecessary long-perimeter assumption from
the earlier projection-based proof. -/
theorem extensionH_not_faceReachable_new_edge_of_proper
    (hproper : G.ProperRingHead x0) :
    ¬ PermReachable (extensionH G x0).face
      ExtDart.new ((extensionH G x0).edge ExtDart.new) := by
  intro hreach
  have hfresh :=
    (extensionH_faceReachable_new_iff_three_of_proper
      (G := G) x0 hproper).1 hreach
  rcases hfresh with h | h | h <;> cases h

/-- Coq `bridgeless_ecpH`, with its exact properness hypothesis. -/
theorem extensionH_bridgeless_of_proper
    (hproper : G.ProperRingHead x0)
    (hG : G.Bridgeless) :
    (extensionH G x0).Bridgeless := by
  intro x hx
  cases x with
  | new =>
      exact extensionH_not_faceReachable_new_edge_of_proper
        (G := G) x0 hproper hx
  | newEdge =>
      have hsymm :
          PermReachable (extensionH G x0).face ExtDart.new
            ((extensionH G x0).edge ExtDart.new) := by
        simpa [extensionH, ExtDart.Perm.edge] using
          PermReachable.symm (extensionH G x0).face hx
      exact extensionH_not_faceReachable_new_edge_of_proper
        (G := G) x0 hproper hsymm
  | old y =>
      have hY :
          PermReachable (extensionY G x0).face
            y ((extensionY G x0).edge y) := by
        exact (extensionN_old_faceReachable_iff
          (G := extensionY G x0) ExtDart.new
          (x := y) (y := (extensionY G x0).edge y)).1 (by
            simpa [extensionH, ExtDart.Perm.edge] using hx)
      exact extensionY_bridgeless_of_proper (G := G) x0
        hproper hG y hY

theorem extensionH_planarBridgelessPlainConnected_of_proper
    (hproper : G.ProperRingHead x0)
    (hG : G.PlanarBridgelessPlainConnected) :
    (extensionH G x0).PlanarBridgelessPlainConnected where
  base := {
    base := {
      planar := (extensionH_eulerPlanar_iff (G := G) x0).2
        hG.base.base.planar
      bridgeless := extensionH_bridgeless_of_proper (G := G) x0
        hproper hG.base.base.bridgeless }
    plain := extensionH_plain (G := G) x0 hG.base.plain }
  connected := extensionH_connected (G := G) x0 hG.connected

theorem extensionH_ringAdj_new_old_of_newEdgeProj
    {y : G.Dart}
    (hy : extensionHNewEdgeBand G x0 y) :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) := by
  refine ⟨ExtDart.new,
    PermReachable.refl (extensionH G x0).face ExtDart.new, ?_⟩
  exact (extensionH_faceReachable_newEdge_iff_proj
    (G := G) x0 (u := extensionHOld G x0 y)).2
    (by simpa [extensionHOld, extensionNFaceProj] using hy)

theorem extensionH_ringAdj_new_old_iff_decomp
    {y : G.Dart} :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) ↔
      extensionHNewEdgeBand G x0 y ∨
      (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y) := by
  constructor
  · rintro ⟨z, hnz, hzy⟩
    cases z with
    | new =>
        exact Or.inl
          ((extensionH_faceReachable_newEdge_iff_proj
            (G := G) x0 (u := extensionHOld G x0 y)).1
            (by simpa [extensionH, ExtDart.Perm.edge] using hzy))
    | newEdge =>
        have hbad :
            PermReachable (extensionH G x0).face
              ExtDart.new (extensionHOld G x0 y) := by
          simpa [extensionH, ExtDart.Perm.edge] using hzy
        exact False.elim
          (extensionH_not_faceReachable_new_old (G := G) x0 y hbad)
    | old zY =>
        have hnzY :
            PermReachable (extensionY G x0).face ExtDart.new zY := by
          have hproj :=
            (extensionH_faceReachable_new_iff_proj
              (G := G) x0 (u := ExtDart.old zY)).1 hnz
          simpa [extensionNFaceProj] using hproj
        have hzyY :
            PermReachable (extensionY G x0).face
              ((extensionY G x0).edge zY) (extensionYOld G x0 y) := by
          have hproj :=
            (extensionN_old_faceReachable_iff
              (G := extensionY G x0) ExtDart.new
              (x := (extensionY G x0).edge zY)
              (y := extensionYOld G x0 y)).1
              (by simpa [extensionH, ExtDart.Perm.edge,
                extensionHOld] using hzy)
          exact hproj
        exact Or.inr ⟨zY, hnzY, hzyY⟩
  · intro hy
    rcases hy with hy | hy
    · exact extensionH_ringAdj_new_old_of_newEdgeProj
        (G := G) x0 hy
    · rcases hy with ⟨zY, hnzY, hzyY⟩
      refine ⟨ExtDart.old zY, ?_, ?_⟩
      · exact (extensionH_faceReachable_new_iff_proj
          (G := G) x0 (u := ExtDart.old zY)).2
          (by simpa [extensionNFaceProj] using hnzY)
      · simpa [extensionH, ExtDart.Perm.edge, extensionHOld] using
          extensionN_old_faceReachable_of_faceReachable
            (G := extensionY G x0) ExtDart.new hzyY

theorem extensionH_ringAdj_new_old_of_faceReachable_x0
    {y : G.Dart}
    (hy : PermReachable G.face x0 y) :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) := by
  unfold extensionH extensionHOld
  refine ⟨ExtDart.old ExtDart.new,
    extensionN_faceReachable_new_old_x0
      (G := extensionY G x0) ExtDart.new, ?_⟩
  have hY :
      PermReachable (extensionY G x0).face
        ExtDart.newEdge (extensionYOld G x0 y) :=
    (extensionY_faceReachable_newEdge_old_iff (G := G) x0
      (y := y)).2 hy
  simpa [extensionY, ExtDart.Perm.edge] using
    extensionN_old_faceReachable_of_faceReachable
      (G := extensionY G x0) ExtDart.new hY

theorem extensionH_ringAdj_new_old_of_faceReachable_node
    {y : G.Dart}
    (hy : PermReachable G.face (G.node x0) y) :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) := by
  unfold extensionH extensionHOld
  refine ⟨ExtDart.old (ExtDart.old ExtDart.new), ?_, ?_⟩
  · have hnew_old :
        PermReachable (extensionN (extensionY G x0) ExtDart.new).face
          ExtDart.new (ExtDart.old ExtDart.new) :=
      extensionN_faceReachable_new_old_x0
        (G := extensionY G x0) ExtDart.new
    have hY_new_old :
        PermReachable (extensionY G x0).face
          ExtDart.new (ExtDart.old ExtDart.new) := by
      unfold extensionY
      exact extensionN_faceReachable_new_old_x0
        (G := extensionU G x0) ExtDart.new
    exact PermReachable.trans
      (extensionN (extensionY G x0) ExtDart.new).face hnew_old
      (extensionN_old_faceReachable_of_faceReachable
        (G := extensionY G x0) ExtDart.new hY_new_old)
  · have hY :
        PermReachable (extensionY G x0).face
          (ExtDart.old ExtDart.newEdge) (extensionYOld G x0 y) :=
      (extensionY_faceReachable_old_newEdge_old_iff (G := G) x0
        (y := y)).2 hy
    simpa [extensionY, ExtDart.Perm.edge] using
      extensionN_old_faceReachable_of_faceReachable
        (G := extensionY G x0) ExtDart.new hY

theorem extensionH_ringAdj_new_old_of_extensionY_ringAdj_new_old
    {y : G.Dart}
    (hy : (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y)) :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) := by
  rcases (extensionY_ringAdj_new_old_iff (G := G) x0 (y := y)).1 hy
    with hy0 | hyn
  · exact extensionH_ringAdj_new_old_of_faceReachable_x0
      (G := G) x0 hy0
  · exact extensionH_ringAdj_new_old_of_faceReachable_node
      (G := G) x0 hyn

theorem extensionH_ringAdj_new_old_of_extensionY_decomp_right
    {y : G.Dart}
    (hy : (extensionY G x0).RingAdj ExtDart.new (extensionYOld G x0 y)) :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) :=
  (extensionH_ringAdj_new_old_iff_decomp (G := G) x0 (y := y)).2
    (Or.inr hy)

theorem extensionH_ringAdj_new_old_of_faceReachable_x0_or_node
    {y : G.Dart}
    (hy : PermReachable G.face x0 y ∨
      PermReachable G.face (G.node x0) y) :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) :=
  extensionH_ringAdj_new_old_of_extensionY_decomp_right (G := G) x0
    ((extensionY_ringAdj_new_old_iff (G := G) x0 (y := y)).2 hy)

theorem extensionH_ringAdj_new_old_iff_bands
    {y : G.Dart} :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) ↔
      extensionHNewEdgeBand G x0 y ∨
        PermReachable G.face x0 y ∨
          PermReachable G.face (G.node x0) y := by
  constructor
  · intro hy
    rcases (extensionH_ringAdj_new_old_iff_decomp
        (G := G) x0 (y := y)).1 hy with hband | hY
    · exact Or.inl hband
    · exact Or.inr
        ((extensionY_ringAdj_new_old_iff (G := G) x0 (y := y)).1 hY)
  · intro hy
    rcases hy with hband | hY
    · exact (extensionH_ringAdj_new_old_iff_decomp
        (G := G) x0 (y := y)).2 (Or.inl hband)
    · exact extensionH_ringAdj_new_old_of_faceReachable_x0_or_node
        (G := G) x0 hY

theorem extensionH_ringAdj_new_old_iff_faceBand
    {y : G.Dart} :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) ↔
      extensionHNewEdgeBand G x0 y ∨ G.FaceBand [x0, G.node x0] y := by
  rw [extensionH_ringAdj_new_old_iff_bands (G := G) x0]
  rw [FaceBand.pair]

theorem extensionH_ringAdj_new_old_iff_faceBand_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0)
    {y : G.Dart} :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) ↔
      G.FaceBand [G.face (G.edge x0), x0, G.node x0] y := by
  rw [extensionH_ringAdj_new_old_iff_bands (G := G) x0]
  rw [extensionHNewEdgeBand_iff_face_edge
    (G := G) x0 hproper hlong]
  rw [FaceBand.cons, FaceBand.pair]

theorem extensionH_ringAdj_new_old_iff_faceBand_coq_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0)
    {y : G.Dart} :
    (extensionH G x0).RingAdj ExtDart.new (extensionHOld G x0 y) ↔
      G.FaceBand [G.node x0, x0, G.face (G.edge x0)] y := by
  rw [extensionH_ringAdj_new_old_iff_bands (G := G) x0]
  rw [extensionHNewEdgeBand_iff_face_edge
    (G := G) x0 hproper hlong]
  rw [FaceBand.triple]
  constructor
  · rintro (hf | hx | hn)
    · exact Or.inr (Or.inr hf)
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hn
  · rintro (hn | hx | hf)
    · exact Or.inr (Or.inr hn)
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hf

theorem extensionH_ringAdj_new_of_faceReachable_old
    {u : (extensionH G x0).Dart} {y : G.Dart}
    (hy : extensionHNewEdgeBand G x0 y ∨
      PermReachable G.face x0 y ∨
        PermReachable G.face (G.node x0) y)
    (hyu : PermReachable (extensionH G x0).face
      (extensionHOld G x0 y) u) :
    (extensionH G x0).RingAdj ExtDart.new u :=
  Hypermap.RingAdj.of_faceReachable_right (G := extensionH G x0)
    ((extensionH_ringAdj_new_old_iff_bands
      (G := G) x0 (y := y)).2 hy)
    hyu

theorem extensionH_ringAdj_new_of_faceBand_old
    {u : (extensionH G x0).Dart} {y : G.Dart}
    (hy : extensionHNewEdgeBand G x0 y ∨
      G.FaceBand [x0, G.node x0] y)
    (hyu : PermReachable (extensionH G x0).face
      (extensionHOld G x0 y) u) :
    (extensionH G x0).RingAdj ExtDart.new u := by
  refine extensionH_ringAdj_new_of_faceReachable_old (G := G) x0 ?_ hyu
  rcases hy with hnew | hband
  · exact Or.inl hnew
  · exact Or.inr ((FaceBand.pair (G := G)).1 hband)

theorem extensionH_ringAdj_new_of_faceBand_old_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0)
    {u : (extensionH G x0).Dart} {y : G.Dart}
    (hy : G.FaceBand [G.face (G.edge x0), x0, G.node x0] y)
    (hyu : PermReachable (extensionH G x0).face
      (extensionHOld G x0 y) u) :
    (extensionH G x0).RingAdj ExtDart.new u :=
  Hypermap.RingAdj.of_faceReachable_right (G := extensionH G x0)
    ((extensionH_ringAdj_new_old_iff_faceBand_of_proper_long
      (G := G) x0 hproper hlong (y := y)).2 hy)
    hyu

theorem extensionH_exists_old_faceReachable_or_new
    (u : (extensionH G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionH G x0).face u (extensionHOld G x0 x)) ∨
      PermReachable (extensionH G x0).face ExtDart.new u := by
  unfold extensionH extensionHOld
  obtain ⟨w, huw⟩ :=
    extensionN_exists_old_faceReachable
      (G := extensionY G x0) ExtDart.new u
  rcases extensionY_exists_old_faceReachable_or_new
      (G := G) x0 w with hOld | hNew
  · rcases hOld with ⟨x, hwx⟩
    exact Or.inl ⟨x,
      PermReachable.trans (extensionN (extensionY G x0) ExtDart.new).face
        huw
        (extensionN_old_faceReachable_of_faceReachable
          (G := extensionY G x0) ExtDart.new hwx)⟩
  · have hnew_old_inner :
        PermReachable (extensionN (extensionY G x0) ExtDart.new).face
          ExtDart.new (ExtDart.old ExtDart.new) :=
      extensionN_faceReachable_new_old_x0
        (G := extensionY G x0) ExtDart.new
    have hinner_w :
        PermReachable (extensionN (extensionY G x0) ExtDart.new).face
          (ExtDart.old ExtDart.new) (ExtDart.old w) :=
      extensionN_old_faceReachable_of_faceReachable
        (G := extensionY G x0) ExtDart.new hNew
    exact Or.inr
      (PermReachable.trans (extensionN (extensionY G x0) ExtDart.new).face
        (PermReachable.trans (extensionN (extensionY G x0) ExtDart.new).face
          hnew_old_inner hinner_w)
        (PermReachable.symm
          (extensionN (extensionY G x0) ExtDart.new).face huw))

theorem extensionH_exists_old_faceReachable_or_freshFace_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionH G x0).face u (extensionHOld G x0 x)) ∨
      extensionHFreshFace G x0 u := by
  rcases extensionH_exists_old_faceReachable_or_new
      (G := G) x0 u with hOld | hNew
  · exact Or.inl hOld
  · exact Or.inr
      ((extensionH_faceReachable_new_iff_freshFace_of_proper
        (G := G) x0 hproper (u := u)).1 hNew)

theorem extensionH_fband_old_or_freshFace_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionH G x0).face u (extensionHOld G x0 x)) ∨
      extensionHFreshFace G x0 u :=
  extensionH_exists_old_faceReachable_or_freshFace_of_proper
    (G := G) x0 hproper u

theorem extensionH_exists_old_faceReachable_from_or_freshFace_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionH G x0).face (extensionHOld G x0 x) u) ∨
      extensionHFreshFace G x0 u := by
  rcases extensionH_fband_old_or_freshFace_of_proper
      (G := G) x0 hproper u with hOld | hFresh
  · rcases hOld with ⟨x, hux⟩
    exact Or.inl ⟨x, PermReachable.symm (extensionH G x0).face hux⟩
  · exact Or.inr hFresh

theorem extensionH_exists_old_faceReachable_iff_not_freshFace_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionH G x0).face u (extensionHOld G x0 x)) ↔
      ¬ extensionHFreshFace G x0 u := by
  constructor
  · rintro ⟨x, hux⟩ hu
    exact extensionHFreshFace.not_faceReachable_old
      (G := G) x0 hproper hu hux
  · intro hnot
    rcases extensionH_fband_old_or_freshFace_of_proper
        (G := G) x0 hproper u with hOld | hFresh
    · exact hOld
    · exact False.elim (hnot hFresh)

theorem extensionH_freshFace_iff_not_exists_old_faceReachable_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    extensionHFreshFace G x0 u ↔
      ¬ ∃ x : G.Dart,
        PermReachable (extensionH G x0).face u (extensionHOld G x0 x) := by
  rw [extensionH_exists_old_faceReachable_iff_not_freshFace_of_proper
    (G := G) x0 hproper u]
  exact ⟨fun h hn => hn h, not_not.mp⟩

theorem extensionH_exists_old_faceReachable_from_iff_not_freshFace_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    (∃ x : G.Dart,
      PermReachable (extensionH G x0).face (extensionHOld G x0 x) u) ↔
      ¬ extensionHFreshFace G x0 u := by
  constructor
  · rintro ⟨x, hxu⟩ hu
    exact extensionHFreshFace.not_old_faceReachable
      (G := G) x0 hproper hu hxu
  · intro hnot
    rcases extensionH_exists_old_faceReachable_from_or_freshFace_of_proper
        (G := G) x0 hproper u with hOld | hFresh
    · exact hOld
    · exact False.elim (hnot hFresh)

theorem extensionH_freshFace_iff_not_exists_old_faceReachable_from_of_proper
    (hproper : G.ProperRingHead x0)
    (u : (extensionH G x0).Dart) :
    extensionHFreshFace G x0 u ↔
      ¬ ∃ x : G.Dart,
        PermReachable (extensionH G x0).face (extensionHOld G x0 x) u := by
  rw [extensionH_exists_old_faceReachable_from_iff_not_freshFace_of_proper
    (G := G) x0 hproper u]
  exact ⟨fun h hn => hn h, not_not.mp⟩

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
