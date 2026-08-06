import Schematic.Math.GraphTheory.Embedding.DartExtension.U.Components
import Schematic.Math.GraphTheory.Embedding.DartExtension.DartOrbitEmbedding
import Schematic.Math.GraphTheory.Embedding.DartExtension.N.Components

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

/-- Coq's `ecpY`: first perform `ecpU` at `x0`, then `ecpN` at the fresh
point of the extended map. -/
def extensionY : Hypermap :=
  extensionN (extensionU G x0) ExtDart.new

/-- Embedding of original darts into the composite `ecpY` map. -/
def extensionYOld (x : G.Dart) : (extensionY G x0).Dart :=
  ExtDart.old (ExtDart.old x)

/-- The composite old-dart embedding into `ecpY`. -/
def extensionYOrbitEmbedding : DartOrbitEmbedding G (extensionY G x0) :=
  (extensionUOrbitEmbedding G x0).trans
    (extensionNOrbitEmbedding (extensionU G x0) ExtDart.new)

theorem extensionY_node_new :
    (extensionY G x0).node ExtDart.new = ExtDart.old ExtDart.newEdge := by
  unfold extensionY extensionN
  change ExtensionN.node (extensionU G x0) ExtDart.new ExtDart.new =
    ExtDart.old ExtDart.newEdge
  change (if (extensionU G x0).LongRingHead ExtDart.new then
      ExtDart.old ((extensionU G x0).node ExtDart.new) else ExtDart.new) =
    ExtDart.old ExtDart.newEdge
  rw [if_pos (extensionU_long_new (G := G) x0)]
  change ExtDart.old (ExtensionU.node G x0 ExtDart.new) =
    ExtDart.old ExtDart.newEdge
  rfl

theorem extensionU_face_edge_face_edge_new_of_proper
    (hproper : G.ProperRingHead x0) :
    (extensionU G x0).face
      ((extensionU G x0).edge
        ((extensionU G x0).face ((extensionU G x0).edge ExtDart.new))) =
      ExtDart.old x0 := by
  have h1 : (extensionU G x0).edge ExtDart.new = ExtDart.newEdge := rfl
  have h2 : (extensionU G x0).face ExtDart.newEdge =
      ExtDart.old (G.node x0) := rfl
  have h3 : (extensionU G x0).edge (ExtDart.old (G.node x0)) =
      ExtDart.old (G.edge (G.node x0)) := rfl
  have h4 :
      (extensionU G x0).face (ExtDart.old (G.edge (G.node x0))) =
        ExtDart.old x0 := by
    change ExtensionU.face G x0 (ExtDart.old (G.edge (G.node x0))) =
      ExtDart.old x0
    have hface : G.face (G.edge (G.node x0)) = x0 := G.face_edge_node x0
    have hne : ¬ x0 = G.node x0 := hproper
    simp [ExtensionU.face, ExtensionU.faceToFun, hface, hne]
  rw [h1, h2, h3, h4]

theorem extensionY_face_newEdge_of_proper
    (hproper : G.ProperRingHead x0) :
    (extensionY G x0).face ExtDart.newEdge = extensionYOld G x0 x0 := by
  unfold extensionY extensionN extensionYOld
  change ExtensionN.face (extensionU G x0) ExtDart.new ExtDart.newEdge =
    ExtDart.old (ExtDart.old x0)
  rw [ExtensionN.face_newEdge]
  rw [if_pos (extensionU_long_new (G := G) x0)]
  rw [extensionU_face_edge_face_edge_new_of_proper (G := G) x0 hproper]
  rfl

theorem extensionY_newEdgeProj_eq_old_x0_of_proper
    (hproper : G.ProperRingHead x0) :
    extensionNFaceProj (extensionU G x0) ExtDart.new ExtDart.newEdge =
      ExtDart.old x0 := by
  exact extensionU_face_edge_face_edge_new_of_proper (G := G) x0 hproper

theorem extensionY_long_new_of_proper
    (hproper : G.ProperRingHead x0) :
    (extensionY G x0).LongRingHead ExtDart.new := by
  unfold Hypermap.LongRingHead
  rw [show (extensionY G x0).edge ExtDart.new = ExtDart.newEdge by rfl]
  rw [extensionY_node_new (G := G) x0]
  rw [extensionY_face_newEdge_of_proper (G := G) x0 hproper]
  intro h
  cases h

theorem extensionY_face_old_edge_of_proper_long
    (hproper : G.ProperRingHead x0)
    (hlong : G.LongRingHead x0) :
    (extensionY G x0).face (extensionYOld G x0 (G.edge x0)) =
      extensionYOld G x0 (G.face (G.edge x0)) := by
  unfold extensionY extensionN extensionYOld
  change ExtensionN.face (extensionU G x0) ExtDart.new
      (ExtDart.old (ExtDart.old (G.edge x0))) =
    ExtDart.old (ExtDart.old (G.face (G.edge x0)))
  rw [ExtensionN.face_old]
  change (if ExtDart.old (G.edge x0) =
        ExtDart.old (G.edge (G.node x0)) then ExtDart.newEdge
      else if ExtDart.old (G.edge x0) = ExtDart.new then ExtDart.new
      else ExtDart.old ((extensionU G x0).face
        (ExtDart.old (G.edge x0)))) =
    ExtDart.old (ExtDart.old (G.face (G.edge x0)))
  have hnot1 :
      ¬ ExtDart.old (G.edge x0) = ExtDart.old (G.edge (G.node x0)) := by
    intro h
    exact hproper (G.edge.injective (ExtDart.old_injective h))
  have hnot2 : ¬ ExtDart.old (G.edge x0) = ExtDart.new := by
    intro h
    cases h
  have hlong' : G.face (G.edge x0) ≠ G.node x0 := hlong
  have hUface :
      (extensionU G x0).face (ExtDart.old (G.edge x0)) =
        ExtDart.old (G.face (G.edge x0)) := by
    change ExtensionU.face G x0 (ExtDart.old (G.edge x0)) =
      ExtDart.old (G.face (G.edge x0))
    simp [ExtensionU.face, ExtensionU.faceToFun, hlong']
  simp [hnot1, hnot2, hUface]
  rfl

theorem extensionYOld_faceReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionY G x0).face
      (extensionYOld G x0 x) (extensionYOld G x0 y) ↔
      PermReachable G.face x y := by
  change PermReachable (extensionY G x0).face
    ((extensionYOrbitEmbedding G x0).toFun x)
    ((extensionYOrbitEmbedding G x0).toFun y) ↔ PermReachable G.face x y
  exact (extensionYOrbitEmbedding G x0).faceReachable_iff

theorem extensionYOld_faceReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionY G x0).face
      (extensionYOld G x0 x) (extensionYOld G x0 y) :=
  (extensionYOld_faceReachable_iff (G := G) x0).2 hxy

theorem extensionYOld_edgeReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionY G x0).edge
      (extensionYOld G x0 x) (extensionYOld G x0 y) ↔
      PermReachable G.edge x y := by
  change PermReachable (extensionY G x0).edge
    ((extensionYOrbitEmbedding G x0).toFun x)
    ((extensionYOrbitEmbedding G x0).toFun y) ↔ PermReachable G.edge x y
  exact (extensionYOrbitEmbedding G x0).edgeReachable_iff

theorem extensionYOld_edgeReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    PermReachable (extensionY G x0).edge
      (extensionYOld G x0 x) (extensionYOld G x0 y) :=
  (extensionYOld_edgeReachable_iff (G := G) x0).2 hxy

theorem extensionYOld_generatedReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    (extensionY G x0).Reachable
      (extensionYOld G x0 x) (extensionYOld G x0 y) := by
  change (extensionY G x0).Reachable
    ((extensionYOrbitEmbedding G x0).toFun x)
    ((extensionYOrbitEmbedding G x0).toFun y)
  exact (extensionYOrbitEmbedding G x0).generatedReachable_of_faceReachable hxy

theorem extensionYOld_generatedReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    (extensionY G x0).Reachable
      (extensionYOld G x0 x) (extensionYOld G x0 y) := by
  change (extensionY G x0).Reachable
    ((extensionYOrbitEmbedding G x0).toFun x)
    ((extensionYOrbitEmbedding G x0).toFun y)
  exact (extensionYOrbitEmbedding G x0).generatedReachable_of_edgeReachable hxy

theorem extensionY_plain
    (hG : G.Plain) :
    (extensionY G x0).Plain := by
  unfold extensionY
  exact extensionN_plain (G := extensionU G x0) ExtDart.new
    (extensionU_plain (G := G) x0 hG)

theorem extensionY_connected
    (hG : G.Connected) :
    (extensionY G x0).Connected := by
  unfold extensionY
  exact extensionN_connected (G := extensionU G x0) ExtDart.new
    (extensionU_connected (G := G) x0 hG)

theorem extensionY_genus :
    (extensionY G x0).genus = G.genus := by
  unfold extensionY
  rw [extensionN_genus (G := extensionU G x0) ExtDart.new,
    extensionU_genus (G := G) x0]

theorem extensionY_eulerPlanar_iff :
    (extensionY G x0).EulerPlanar ↔ G.EulerPlanar := by
  unfold extensionY
  exact Iff.trans
    (extensionN_eulerPlanar_iff (G := extensionU G x0) ExtDart.new)
    (extensionU_eulerPlanar_iff (G := G) x0)

theorem extensionYOld_ringAdj_iff
    {x y : G.Dart} :
    (extensionY G x0).RingAdj
      (extensionYOld G x0 x) (extensionYOld G x0 y) ↔
      G.RingAdj x y := by
  unfold extensionY extensionYOld
  constructor
  · intro hxy
    have hN :=
      (extensionN_ringAdj_old_iff
        (G := extensionU G x0) ExtDart.new
        (x := ExtDart.old x) (y := ExtDart.old y)).1 hxy
    rcases hN with hU | hExtra
    · exact (extensionU_ringAdj_old_iff (G := G) x0).1 hU
    · rcases hExtra with hExtra | hExtra
      · have hbad := extensionU_faceReachable_from_new (G := G) x0
          hExtra.2
        cases hbad
      · have hbad := extensionU_faceReachable_from_new (G := G) x0
          hExtra.2
        cases hbad
  · intro hxy
    exact
      (extensionN_ringAdj_old_iff
        (G := extensionU G x0) ExtDart.new
        (x := ExtDart.old x) (y := ExtDart.old y)).2
        (Or.inl ((extensionU_ringAdj_old_iff (G := G) x0).2 hxy))

theorem extensionYOld_ringAdj_of_ringAdj
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionY G x0).RingAdj
      (extensionYOld G x0 x) (extensionYOld G x0 y) := by
  exact (extensionYOld_ringAdj_iff (G := G) x0).2 hxy

theorem extensionY_not_faceReachable_new_old
    (y : G.Dart) :
    ¬ PermReachable (extensionY G x0).face
      ExtDart.new (extensionYOld G x0 y) := by
  intro h
  unfold extensionY extensionYOld at h
  have hproj :=
    (extensionN_faceReachable_iff_proj
      (G := extensionU G x0) ExtDart.new
      (x := ExtDart.new) (y := ExtDart.old (ExtDart.old y))).1 h
  have hU :
      PermReachable (extensionU G x0).face
        ExtDart.new (ExtDart.old y) := by
    simpa [extensionNFaceProj] using hproj
  have hEq := extensionU_faceReachable_from_new (G := G) x0 hU
  cases hEq

theorem extensionY_faceReachable_new_iff_proj_eq_new
    {u : (extensionY G x0).Dart} :
    PermReachable (extensionY G x0).face ExtDart.new u ↔
      extensionNFaceProj (extensionU G x0) ExtDart.new u = ExtDart.new := by
  unfold extensionY
  constructor
  · intro hu
    have hproj :=
      (extensionN_faceReachable_new_iff_proj
        (G := extensionU G x0) ExtDart.new (y := u)).1 hu
    exact extensionU_faceReachable_from_new (G := G) x0
      (by simpa [extensionNFaceProj] using hproj)
  · intro hu
    exact
      (extensionN_faceReachable_new_iff_proj
        (G := extensionU G x0) ExtDart.new (y := u)).2
        (by
          rw [hu]
          exact PermReachable.refl (extensionU G x0).face ExtDart.new)

theorem extensionY_not_faceReachable_new_edge_of_proper
    (hproper : G.ProperRingHead x0) :
    ¬ PermReachable (extensionY G x0).face
      ExtDart.new ((extensionY G x0).edge ExtDart.new) := by
  intro h
  have hproj :=
    (extensionY_faceReachable_new_iff_proj_eq_new
      (G := G) x0 (u := (extensionY G x0).edge ExtDart.new)).1 h
  change extensionNFaceProj (extensionU G x0) ExtDart.new
    ExtDart.newEdge = ExtDart.new at hproj
  rw [extensionY_newEdgeProj_eq_old_x0_of_proper
    (G := G) x0 hproper] at hproj
  cases hproj

theorem extensionY_bridgeless_of_proper
    (hproper : G.ProperRingHead x0)
    (hG : G.Bridgeless) :
    (extensionY G x0).Bridgeless := by
  intro x hx
  cases x with
  | new =>
      exact extensionY_not_faceReachable_new_edge_of_proper
        (G := G) x0 hproper hx
  | newEdge =>
      have hsymm :
          PermReachable (extensionY G x0).face ExtDart.new
            ((extensionY G x0).edge ExtDart.new) := by
        simpa [extensionY, ExtDart.Perm.edge] using
          PermReachable.symm (extensionY G x0).face hx
      exact extensionY_not_faceReachable_new_edge_of_proper
        (G := G) x0 hproper hsymm
  | old u =>
      cases u with
      | new =>
          have hU :
              PermReachable (extensionU G x0).face
                ExtDart.new ExtDart.newEdge := by
            exact (extensionN_old_faceReachable_iff
              (G := extensionU G x0) ExtDart.new
              (x := ExtDart.new) (y := ExtDart.newEdge)).1 (by
                simpa [extensionY, ExtDart.Perm.edge] using hx)
          have hEq := extensionU_faceReachable_from_new (G := G) x0 hU
          cases hEq
      | newEdge =>
          have hU :
              PermReachable (extensionU G x0).face
                ExtDart.newEdge ExtDart.new := by
            exact (extensionN_old_faceReachable_iff
              (G := extensionU G x0) ExtDart.new
              (x := ExtDart.newEdge) (y := ExtDart.new)).1 (by
                simpa [extensionY, ExtDart.Perm.edge] using hx)
          have hEq := extensionU_faceReachable_to_new (G := G) x0 hU
          cases hEq
      | old y =>
          have hU :
              PermReachable (extensionU G x0).face
                (ExtDart.old y) (ExtDart.old (G.edge y)) := by
            exact (extensionN_old_faceReachable_iff
              (G := extensionU G x0) ExtDart.new
              (x := ExtDart.old y) (y := ExtDart.old (G.edge y))).1 (by
                simpa [extensionY, ExtDart.Perm.edge] using hx)
          have hbase := (extensionU_old_faceReachable_iff
            (G := G) x0 (x := y) (y := G.edge y)).1 hU
          exact hG y hbase

theorem extensionY_planarBridgelessPlainConnected_of_proper
    (hproper : G.ProperRingHead x0)
    (hG : G.PlanarBridgelessPlainConnected) :
    (extensionY G x0).PlanarBridgelessPlainConnected where
  base := {
    base := {
      planar := (extensionY_eulerPlanar_iff (G := G) x0).2
        hG.base.base.planar
      bridgeless := extensionY_bridgeless_of_proper (G := G) x0
        hproper hG.base.base.bridgeless }
    plain := extensionY_plain (G := G) x0 hG.base.plain }
  connected := extensionY_connected (G := G) x0 hG.connected

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
