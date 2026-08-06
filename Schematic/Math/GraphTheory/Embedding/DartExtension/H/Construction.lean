import Schematic.Math.GraphTheory.Embedding.DartExtension.Y.RingAdjacency

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

/-- Coq's `ecpH`: perform one more `ecpN` step at the fresh point of `ecpY`. -/
def extensionH : Hypermap :=
  extensionN (extensionY G x0) ExtDart.new

/-- Embedding of original darts into the composite `ecpH` map. -/
def extensionHOld (x : G.Dart) : (extensionH G x0).Dart :=
  ExtDart.old (extensionYOld G x0 x)

/-- The composite old-dart embedding into `ecpH`. -/
def extensionHOrbitEmbedding : DartOrbitEmbedding G (extensionH G x0) :=
  (extensionYOrbitEmbedding G x0).trans
    (extensionNOrbitEmbedding (extensionY G x0) ExtDart.new)

theorem extensionH_face_new :
    (extensionH G x0).face ExtDart.new = ExtDart.old ExtDart.new :=
  rfl

theorem extensionH_face_face_new :
    (extensionH G x0).face ((extensionH G x0).face ExtDart.new) =
      ExtDart.old (ExtDart.old ExtDart.new) := by
  unfold extensionH extensionN
  change ExtensionN.face (extensionY G x0) ExtDart.new
      (ExtDart.old ExtDart.new) = ExtDart.old (ExtDart.old ExtDart.new)
  rw [ExtensionN.face_old]
  change (if ExtDart.new = (extensionY G x0).edge
        ((extensionY G x0).face ((extensionY G x0).edge ExtDart.new)) then
      ExtDart.newEdge
    else if ExtDart.new =
        (extensionY G x0).edge ((extensionY G x0).node ExtDart.new) then
      ExtDart.new
    else ExtDart.old ((extensionY G x0).face ExtDart.new)) =
    ExtDart.old (ExtDart.old ExtDart.new)
  have hnot1 :
      ¬ ExtDart.new = (extensionY G x0).edge
        ((extensionY G x0).face ((extensionY G x0).edge ExtDart.new)) := by
    intro h
    cases h.symm
  have hnot2 :
      ¬ ExtDart.new =
        (extensionY G x0).edge ((extensionY G x0).node ExtDart.new) := by
    rw [extensionY_node_new (G := G) x0]
    intro h
    cases h.symm
  have hface : (extensionY G x0).face ExtDart.new =
      ExtDart.old ExtDart.new := by
    rfl
  simp [hnot1, hnot2, hface]
  rfl

theorem extensionH_face_old_new :
    (extensionH G x0).face (ExtDart.old ExtDart.new) =
      ExtDart.old (ExtDart.old ExtDart.new) := by
  have h := extensionH_face_face_new (G := G) x0
  simpa [extensionH_face_new (G := G) x0] using h

theorem extensionH_face_face_face_new_of_proper
    (hproper : G.ProperRingHead x0) :
    (extensionH G x0).face
        ((extensionH G x0).face ((extensionH G x0).face ExtDart.new)) =
      ExtDart.new := by
  rw [extensionH_face_face_new (G := G) x0]
  unfold extensionH extensionN
  change ExtensionN.face (extensionY G x0) ExtDart.new
      (ExtDart.old (ExtDart.old ExtDart.new)) = ExtDart.new
  rw [ExtensionN.face_old]
  have htarget :
      (extensionY G x0).edge ((extensionY G x0).node ExtDart.new) =
        ExtDart.old ExtDart.new := by
    rw [extensionY_node_new (G := G) x0]
    rfl
  have hproj :
      (extensionY G x0).edge
        ((extensionY G x0).face ((extensionY G x0).edge ExtDart.new)) =
      ExtDart.old (ExtDart.old (G.edge x0)) := by
    rw [show (extensionY G x0).edge ExtDart.new = ExtDart.newEdge by rfl]
    rw [extensionY_face_newEdge_of_proper (G := G) x0 hproper]
    rfl
  change (if ExtDart.old ExtDart.new = (extensionY G x0).edge
        ((extensionY G x0).face ((extensionY G x0).edge ExtDart.new)) then
      ExtDart.newEdge
    else if ExtDart.old ExtDart.new =
        (extensionY G x0).edge ((extensionY G x0).node ExtDart.new) then
      ExtDart.new
    else ExtDart.old ((extensionY G x0).face (ExtDart.old ExtDart.new))) =
    ExtDart.new
  have hnot1 :
      ¬ ExtDart.old ExtDart.new = (extensionY G x0).edge
        ((extensionY G x0).face ((extensionY G x0).edge ExtDart.new)) := by
    intro h
    rw [hproj] at h
    have hEq := ExtDart.old_injective h
    cases hEq
  rw [if_neg hnot1]
  rw [← htarget]
  rw [if_pos rfl]

theorem extensionH_face_old_old_new_of_proper
    (hproper : G.ProperRingHead x0) :
    (extensionH G x0).face (ExtDart.old (ExtDart.old ExtDart.new)) =
      ExtDart.new := by
  have h := extensionH_face_face_face_new_of_proper (G := G) x0 hproper
  simpa [extensionH_face_face_new (G := G) x0] using h

def extensionHFreshFace (u : (extensionH G x0).Dart) : Prop :=
  u = ExtDart.new ∨
    u = ExtDart.old ExtDart.new ∨
      u = ExtDart.old (ExtDart.old ExtDart.new)

theorem extensionHFreshFace.face
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart}
    (hu : extensionHFreshFace G x0 u) :
    extensionHFreshFace G x0 ((extensionH G x0).face u) := by
  rcases hu with rfl | rfl | rfl
  · exact Or.inr (Or.inl (extensionH_face_new (G := G) x0))
  · exact Or.inr (Or.inr (extensionH_face_old_new (G := G) x0))
  · exact Or.inl (extensionH_face_old_old_new_of_proper
      (G := G) x0 hproper)

theorem extensionHFreshFace.face_symm
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart}
    (hu : extensionHFreshFace G x0 u) :
    extensionHFreshFace G x0 ((extensionH G x0).face.symm u) := by
  rcases hu with rfl | rfl | rfl
  · right
    right
    calc
      (extensionH G x0).face.symm ExtDart.new =
          (extensionH G x0).face.symm
            ((extensionH G x0).face
              (ExtDart.old (ExtDart.old ExtDart.new))) := by
            rw [extensionH_face_old_old_new_of_proper
              (G := G) x0 hproper]
      _ = ExtDart.old (ExtDart.old ExtDart.new) := by
            simp
            rfl
  · left
    calc
      (extensionH G x0).face.symm (ExtDart.old ExtDart.new) =
          (extensionH G x0).face.symm ((extensionH G x0).face ExtDart.new) := by
            rw [extensionH_face_new (G := G) x0]
            rfl
      _ = ExtDart.new := by simp
  · right
    left
    calc
      (extensionH G x0).face.symm
          (ExtDart.old (ExtDart.old ExtDart.new)) =
          (extensionH G x0).face.symm
            ((extensionH G x0).face (ExtDart.old ExtDart.new)) := by
            rw [extensionH_face_old_new (G := G) x0]
            rfl
      _ = ExtDart.old ExtDart.new := by
            simp
            rfl

theorem extensionHFreshFace.of_face_link
    (hproper : G.ProperRingHead x0)
    {u v : (extensionH G x0).Dart}
    (hu : extensionHFreshFace G x0 u)
    (huv : PermLink (extensionH G x0).face u v) :
    extensionHFreshFace G x0 v := by
  cases huv with
  | forward =>
      exact extensionHFreshFace.face (G := G) x0 hproper hu
  | backward =>
      exact extensionHFreshFace.face_symm (G := G) x0 hproper hu

theorem extensionHFreshFace.of_faceReachable
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart}
    (hu : PermReachable (extensionH G x0).face ExtDart.new u) :
    extensionHFreshFace G x0 u := by
  induction hu with
  | refl =>
      exact Or.inl rfl
  | tail _ huv ih =>
      exact extensionHFreshFace.of_face_link (G := G) x0 hproper ih huv

theorem extensionHFreshFace.of_faceReachable_from
    (hproper : G.ProperRingHead x0)
    {u v : (extensionH G x0).Dart}
    (hu : extensionHFreshFace G x0 u)
    (huv : PermReachable (extensionH G x0).face u v) :
    extensionHFreshFace G x0 v := by
  induction huv with
  | refl =>
      exact hu
  | tail _ hvw ih =>
      exact extensionHFreshFace.of_face_link (G := G) x0 hproper ih hvw

theorem extensionHOld_not_freshFace
    (x : G.Dart) :
    ¬ extensionHFreshFace G x0 (extensionHOld G x0 x) := by
  rintro (h | h | h)
  · cases h
  · cases h
  · cases h

theorem extensionHFreshFace.not_faceReachable_old
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart} {x : G.Dart}
    (hu : extensionHFreshFace G x0 u) :
    ¬ PermReachable (extensionH G x0).face u (extensionHOld G x0 x) := by
  intro hux
  exact extensionHOld_not_freshFace (G := G) x0 x
    (extensionHFreshFace.of_faceReachable_from
      (G := G) x0 hproper hu hux)

theorem extensionHFreshFace.not_old_faceReachable
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart} {x : G.Dart}
    (hu : extensionHFreshFace G x0 u) :
    ¬ PermReachable (extensionH G x0).face (extensionHOld G x0 x) u := by
  intro hxu
  exact extensionHFreshFace.not_faceReachable_old
    (G := G) x0 hproper hu (PermReachable.symm (extensionH G x0).face hxu)

theorem extensionH_faceReachable_new_iff_freshFace_of_proper
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart} :
    PermReachable (extensionH G x0).face ExtDart.new u ↔
      extensionHFreshFace G x0 u := by
  constructor
  · exact extensionHFreshFace.of_faceReachable (G := G) x0 hproper
  · intro hu
    rcases hu with rfl | rfl | rfl
    · exact PermReachable.refl (extensionH G x0).face ExtDart.new
    · have hstep := PermReachable.forward (extensionH G x0).face ExtDart.new
      simpa [extensionH_face_new (G := G) x0] using hstep
    · have h1 :
          PermReachable (extensionH G x0).face
            ExtDart.new (ExtDart.old ExtDart.new) := by
          have hstep := PermReachable.forward (extensionH G x0).face ExtDart.new
          simpa [extensionH_face_new (G := G) x0] using hstep
      have h2 :
          PermReachable (extensionH G x0).face
            (ExtDart.old ExtDart.new)
            (ExtDart.old (ExtDart.old ExtDart.new)) := by
          have hstep := PermReachable.forward (extensionH G x0).face
            (ExtDart.old ExtDart.new)
          simpa [extensionH_face_old_new (G := G) x0] using hstep
      exact PermReachable.trans (extensionH G x0).face h1 h2

theorem extensionH_faceReachable_new_iff_three_of_proper
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart} :
    PermReachable (extensionH G x0).face ExtDart.new u ↔
      u = ExtDart.new ∨
        u = ExtDart.old ExtDart.new ∨
          u = ExtDart.old (ExtDart.old ExtDart.new) :=
  extensionH_faceReachable_new_iff_freshFace_of_proper
    (G := G) x0 hproper

theorem extensionH_freshFace_iff_faceBand_new_of_proper
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart} :
    extensionHFreshFace G x0 u ↔
      (extensionH G x0).FaceBand [ExtDart.new] u := by
  rw [FaceBand.singleton]
  exact (extensionH_faceReachable_new_iff_freshFace_of_proper
    (G := G) x0 hproper (u := u)).symm

theorem extensionH_faceBand_new_iff_three_of_proper
    (hproper : G.ProperRingHead x0)
    {u : (extensionH G x0).Dart} :
    (extensionH G x0).FaceBand [ExtDart.new] u ↔
      u = ExtDart.new ∨
        u = ExtDart.old ExtDart.new ∨
          u = ExtDart.old (ExtDart.old ExtDart.new) := by
  rw [← extensionH_freshFace_iff_faceBand_new_of_proper
    (G := G) x0 hproper]
  rfl

theorem extensionHOld_faceReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionH G x0).face
      (extensionHOld G x0 x) (extensionHOld G x0 y) ↔
      PermReachable G.face x y := by
  change PermReachable (extensionH G x0).face
    ((extensionHOrbitEmbedding G x0).toFun x)
    ((extensionHOrbitEmbedding G x0).toFun y) ↔ PermReachable G.face x y
  exact (extensionHOrbitEmbedding G x0).faceReachable_iff

theorem extensionHOld_faceReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionH G x0).face
      (extensionHOld G x0 x) (extensionHOld G x0 y) :=
  (extensionHOld_faceReachable_iff (G := G) x0).2 hxy

theorem extensionHOld_edgeReachable_iff
    {x y : G.Dart} :
    PermReachable (extensionH G x0).edge
      (extensionHOld G x0 x) (extensionHOld G x0 y) ↔
      PermReachable G.edge x y := by
  change PermReachable (extensionH G x0).edge
    ((extensionHOrbitEmbedding G x0).toFun x)
    ((extensionHOrbitEmbedding G x0).toFun y) ↔ PermReachable G.edge x y
  exact (extensionHOrbitEmbedding G x0).edgeReachable_iff

theorem extensionHOld_edgeReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    PermReachable (extensionH G x0).edge
      (extensionHOld G x0 x) (extensionHOld G x0 y) :=
  (extensionHOld_edgeReachable_iff (G := G) x0).2 hxy

theorem extensionHOld_generatedReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    (extensionH G x0).Reachable
      (extensionHOld G x0 x) (extensionHOld G x0 y) := by
  change (extensionH G x0).Reachable
    ((extensionHOrbitEmbedding G x0).toFun x)
    ((extensionHOrbitEmbedding G x0).toFun y)
  exact (extensionHOrbitEmbedding G x0).generatedReachable_of_faceReachable hxy

theorem extensionHOld_generatedReachable_of_edgeReachable
    {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    (extensionH G x0).Reachable
      (extensionHOld G x0 x) (extensionHOld G x0 y) := by
  change (extensionH G x0).Reachable
    ((extensionHOrbitEmbedding G x0).toFun x)
    ((extensionHOrbitEmbedding G x0).toFun y)
  exact (extensionHOrbitEmbedding G x0).generatedReachable_of_edgeReachable hxy

theorem extensionH_plain
    (hG : G.Plain) :
    (extensionH G x0).Plain := by
  unfold extensionH
  exact extensionN_plain (G := extensionY G x0) ExtDart.new
    (extensionY_plain (G := G) x0 hG)

theorem extensionH_connected
    (hG : G.Connected) :
    (extensionH G x0).Connected := by
  unfold extensionH
  exact extensionN_connected (G := extensionY G x0) ExtDart.new
    (extensionY_connected (G := G) x0 hG)

theorem extensionH_genus :
    (extensionH G x0).genus = G.genus := by
  unfold extensionH
  rw [extensionN_genus (G := extensionY G x0) ExtDart.new,
    extensionY_genus (G := G) x0]

theorem extensionH_eulerPlanar_iff :
    (extensionH G x0).EulerPlanar ↔ G.EulerPlanar := by
  unfold extensionH
  exact Iff.trans
    (extensionN_eulerPlanar_iff (G := extensionY G x0) ExtDart.new)
    (extensionY_eulerPlanar_iff (G := G) x0)

theorem extensionHOld_ringAdj_iff
    {x y : G.Dart} :
    (extensionH G x0).RingAdj
      (extensionHOld G x0 x) (extensionHOld G x0 y) ↔
      G.RingAdj x y := by
  unfold extensionH extensionHOld
  constructor
  · intro hxy
    have hN :=
      (extensionN_ringAdj_old_iff
        (G := extensionY G x0) ExtDart.new
        (x := extensionYOld G x0 x) (y := extensionYOld G x0 y)).1 hxy
    rcases hN with hY | hExtra
    · exact (extensionYOld_ringAdj_iff (G := G) x0).1 hY
    · rcases hExtra with hExtra | hExtra
      · exact False.elim
          (extensionY_not_faceReachable_new_old (G := G) x0 y hExtra.2)
      · exact False.elim
          (extensionY_not_faceReachable_new_old (G := G) x0 x hExtra.2)
  · intro hxy
    exact
      (extensionN_ringAdj_old_iff
        (G := extensionY G x0) ExtDart.new
        (x := extensionYOld G x0 x) (y := extensionYOld G x0 y)).2
        (Or.inl ((extensionYOld_ringAdj_iff (G := G) x0).2 hxy))

theorem extensionHOld_ringAdj_of_ringAdj
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionH G x0).RingAdj
      (extensionHOld G x0 x) (extensionHOld G x0 y) := by
  exact (extensionHOld_ringAdj_iff (G := G) x0).2 hxy

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
