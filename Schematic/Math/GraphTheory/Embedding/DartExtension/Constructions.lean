import Schematic.Math.GraphTheory.Embedding.DartExtension.ReachabilityTransport

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

def ProperRingHead : Prop :=
  x0 ≠ G.node x0

/-- The long-ring condition from `cfmap.v`, expressed at the pointed dart. -/
def LongRingHead : Prop :=
  G.face (G.edge x0) ≠ G.node x0

instance decidableLongRingHead : Decidable (G.LongRingHead x0) :=
  inferInstanceAs (Decidable (G.face (G.edge x0) ≠ G.node x0))

namespace ExtensionU

/-- Node permutation for Coq's `ecpU` constructor. -/
def nodeToFun : ExtDart G.Dart → ExtDart G.Dart
  | ExtDart.new => ExtDart.newEdge
  | ExtDart.newEdge => ExtDart.old (G.node (G.node x0))
  | ExtDart.old y =>
      if y = G.node x0 then ExtDart.new else ExtDart.old (G.node y)

/-- Inverse node permutation for Coq's `ecpU` constructor. -/
def nodeInvFun : ExtDart G.Dart → ExtDart G.Dart
  | ExtDart.new => ExtDart.old (G.node x0)
  | ExtDart.newEdge => ExtDart.new
  | ExtDart.old y =>
      if y = G.node (G.node x0) then ExtDart.newEdge
      else ExtDart.old (G.node.symm y)

theorem node_left_inv :
    Function.LeftInverse (nodeInvFun G x0) (nodeToFun G x0) := by
  intro x
  cases x with
  | new => rfl
  | newEdge =>
      simp [nodeToFun, nodeInvFun]
  | old y =>
      by_cases hy : y = G.node x0
      · simp [nodeToFun, nodeInvFun, hy]
      · have hny : G.node y ≠ G.node (G.node x0) := by
          intro h
          exact hy (G.node.injective h)
        simp [nodeToFun, nodeInvFun, hy, hny]

theorem node_right_inv :
    Function.RightInverse (nodeInvFun G x0) (nodeToFun G x0) := by
  intro x
  cases x with
  | new =>
      simp [nodeToFun, nodeInvFun]
  | newEdge => rfl
  | old y =>
      by_cases hy : y = G.node (G.node x0)
      · simp [nodeToFun, nodeInvFun, hy]
      · have hsymm : G.node.symm y ≠ G.node x0 := by
          intro h
          apply hy
          calc
            y = G.node (G.node.symm y) := by simp
            _ = G.node (G.node x0) := by rw [h]
        simp [nodeToFun, nodeInvFun, hy, hsymm]

/-- Face permutation for Coq's `ecpU` constructor. -/
def faceToFun : ExtDart G.Dart → ExtDart G.Dart
  | ExtDart.new => ExtDart.new
  | ExtDart.newEdge => ExtDart.old (G.node x0)
  | ExtDart.old y =>
      if G.face y = G.node x0 then ExtDart.newEdge
      else ExtDart.old (G.face y)

/-- Inverse face permutation for Coq's `ecpU` constructor. -/
def faceInvFun : ExtDart G.Dart → ExtDart G.Dart
  | ExtDart.new => ExtDart.new
  | ExtDart.newEdge => ExtDart.old (G.face.symm (G.node x0))
  | ExtDart.old y =>
      if y = G.node x0 then ExtDart.newEdge
      else ExtDart.old (G.face.symm y)

theorem face_left_inv :
    Function.LeftInverse (faceInvFun G x0) (faceToFun G x0) := by
  intro x
  cases x with
  | new => rfl
  | newEdge =>
      simp [faceToFun, faceInvFun]
  | old y =>
      by_cases hy : G.face y = G.node x0
      · have hsymm : G.face.symm (G.node x0) = y := by
          rw [← hy]
          simp
        simp [faceToFun, faceInvFun, hy, hsymm]
      · simp [faceToFun, faceInvFun, hy]

theorem face_right_inv :
    Function.RightInverse (faceInvFun G x0) (faceToFun G x0) := by
  intro x
  cases x with
  | new => rfl
  | newEdge =>
      simp [faceToFun, faceInvFun]
  | old y =>
      by_cases hy : y = G.node x0
      · simp [faceToFun, faceInvFun, hy]
      · have hface : G.face (G.face.symm y) ≠ G.node x0 := by
          simpa using hy
        simp [faceToFun, faceInvFun, hy]

/-- Node permutation for the `ecpU` hypermap extension. -/
def node : Equiv.Perm (ExtDart G.Dart) where
  toFun := nodeToFun G x0
  invFun := nodeInvFun G x0
  left_inv := node_left_inv G x0
  right_inv := node_right_inv G x0

/-- Face permutation for the `ecpU` hypermap extension. -/
def face : Equiv.Perm (ExtDart G.Dart) where
  toFun := faceToFun G x0
  invFun := faceInvFun G x0
  left_inv := face_left_inv G x0
  right_inv := face_right_inv G x0

@[simp]
theorem node_new :
    node G x0 ExtDart.new = ExtDart.newEdge :=
  rfl

@[simp]
theorem node_newEdge :
    node G x0 ExtDart.newEdge =
      ExtDart.old (G.node (G.node x0)) :=
  rfl

@[simp]
theorem node_old (y : G.Dart) :
    node G x0 (ExtDart.old y) =
      if y = G.node x0 then ExtDart.new else ExtDart.old (G.node y) :=
  rfl

@[simp]
theorem face_new :
    face G x0 ExtDart.new = ExtDart.new :=
  rfl

@[simp]
theorem face_newEdge :
    face G x0 ExtDart.newEdge = ExtDart.old (G.node x0) :=
  rfl

@[simp]
theorem face_old (y : G.Dart) :
    face G x0 (ExtDart.old y) =
      if G.face y = G.node x0 then ExtDart.newEdge
      else ExtDart.old (G.face y) :=
  rfl

theorem node_face_edge (x : ExtDart G.Dart) :
    node G x0 (face G x0 (ExtDart.Perm.edge G.edge x)) = x := by
  cases x with
  | new =>
      simp [ExtDart.Perm.edge, face, node, faceToFun, nodeToFun]
  | newEdge =>
      simp [ExtDart.Perm.edge, face, node, faceToFun, nodeToFun]
  | old y =>
      by_cases hy : G.face (G.edge y) = G.node x0
      · have hyeq : y = G.node (G.node x0) := by
          calc
            y = G.node (G.face (G.edge y)) :=
              (G.node_face_edge y).symm
            _ = G.node (G.node x0) := by rw [hy]
        simp [ExtDart.Perm.edge, face, node, faceToFun, nodeToFun, hyeq]
      · simp [ExtDart.Perm.edge, face, node, faceToFun, nodeToFun, hy,
          G.node_face_edge y]

end ExtensionU

namespace ExtensionN

/-- Node permutation for Coq's `ecpN` constructor. -/
def nodeToFun : ExtDart G.Dart → ExtDart G.Dart
  | ExtDart.new =>
      if G.LongRingHead x0 then ExtDart.old (G.node x0) else ExtDart.new
  | ExtDart.newEdge => ExtDart.old (G.face (G.edge x0))
  | ExtDart.old y =>
      if y = x0 then ExtDart.newEdge
      else if G.node (G.node y) = x0 then ExtDart.new
      else ExtDart.old (G.node y)

/-- Inverse node permutation for Coq's `ecpN` constructor. -/
def nodeInvFun : ExtDart G.Dart → ExtDart G.Dart
  | ExtDart.new =>
      if G.LongRingHead x0 then
        ExtDart.old (G.node.symm (G.node.symm x0))
      else ExtDart.new
  | ExtDart.newEdge => ExtDart.old x0
  | ExtDart.old y =>
      if y = G.face (G.edge x0) then ExtDart.newEdge
      else if y = G.node x0 then ExtDart.new
      else ExtDart.old (G.node.symm y)

theorem node_left_inv :
    Function.LeftInverse (nodeInvFun G x0) (nodeToFun G x0) := by
  intro x
  cases x with
  | new =>
      by_cases hlong : G.LongRingHead x0
      · have hne : G.node x0 ≠ G.face (G.edge x0) := hlong.symm
        simp [nodeToFun, nodeInvFun, hlong, hne]
      · simp [nodeToFun, nodeInvFun, hlong]
  | newEdge =>
      simp [nodeToFun, nodeInvFun]
  | old y =>
      by_cases hy : y = x0
      · subst y
        simp [nodeToFun, nodeInvFun]
      · by_cases hyy : G.node (G.node y) = x0
        · by_cases hlong : G.LongRingHead x0
          · have hyval : G.node.symm (G.node.symm x0) = y := by
              apply G.node.injective
              apply G.node.injective
              simp [hyy]
            simp [nodeToFun, nodeInvFun, hy, hyy, hlong, hyval]
          · have hfe : G.face (G.edge x0) = G.node x0 := not_not.mp hlong
            have hx0period : G.node (G.node x0) = x0 := by
              calc
                G.node (G.node x0) = G.node (G.face (G.edge x0)) := by
                  rw [hfe]
                _ = x0 := G.node_face_edge x0
            have hyx0 : y = x0 := by
              apply G.node.injective
              apply G.node.injective
              rw [hyy, hx0period]
            exact (hy hyx0).elim
        · have hneFace : G.node y ≠ G.face (G.edge x0) := by
            intro h
            apply hyy
            calc
              G.node (G.node y) = G.node (G.face (G.edge x0)) := by
                rw [h]
              _ = x0 := G.node_face_edge x0
          have hneNode : G.node y ≠ G.node x0 := by
            intro h
            exact hy (G.node.injective h)
          simp [nodeToFun, nodeInvFun, hy, hyy, hneFace, hneNode]

theorem node_right_inv :
    Function.RightInverse (nodeInvFun G x0) (nodeToFun G x0) := by
  intro x
  cases x with
  | new =>
      by_cases hlong : G.LongRingHead x0
      · have hne : G.node.symm (G.node.symm x0) ≠ x0 := by
          intro h
          have hx0period : G.node (G.node x0) = x0 := by
            calc
              G.node (G.node x0) =
                  G.node (G.node (G.node.symm (G.node.symm x0))) := by
                    rw [h]
              _ = x0 := by simp
          have hface : G.face (G.edge x0) = G.node x0 := by
            calc
              G.face (G.edge x0) = G.node.symm x0 :=
                face_edge_eq_node_symm (G := G) x0
              _ = G.node x0 := by
                apply G.node.injective
                simp [hx0period]
          exact hlong hface
        simp [nodeToFun, nodeInvFun, hlong, hne]
      · simp [nodeToFun, nodeInvFun, hlong]
  | newEdge =>
      simp [nodeToFun, nodeInvFun]
  | old y =>
      by_cases hface : y = G.face (G.edge x0)
      · subst y
        simp [nodeToFun, nodeInvFun]
      · by_cases hnode : y = G.node x0
        · subst y
          have hlong : G.LongRingHead x0 := by
            intro h
            exact hface h.symm
          simp [nodeToFun, nodeInvFun, hlong, hface]
        · have hpreNe : G.node.symm y ≠ x0 := by
            intro h
            apply hnode
            calc
              y = G.node (G.node.symm y) := by simp
              _ = G.node x0 := by rw [h]
          have hpreTwo : G.node (G.node (G.node.symm y)) ≠ x0 := by
            intro h
            apply hface
            calc
              y = G.node.symm (G.node (G.node (G.node.symm y))) := by
                simp
              _ = G.node.symm x0 := by rw [h]
              _ = G.face (G.edge x0) :=
                (face_edge_eq_node_symm (G := G) x0).symm
          have hnodey : G.node y ≠ x0 := by
            intro h
            exact hpreTwo (by simp [h])
          simp [nodeToFun, nodeInvFun, hface, hnode, hpreNe, hnodey]

/-- Node permutation for the `ecpN` hypermap extension. -/
def node : Equiv.Perm (ExtDart G.Dart) where
  toFun := nodeToFun G x0
  invFun := nodeInvFun G x0
  left_inv := node_left_inv G x0
  right_inv := node_right_inv G x0

@[simp]
theorem node_new :
    node G x0 ExtDart.new =
      if G.LongRingHead x0 then ExtDart.old (G.node x0)
      else ExtDart.new :=
  rfl

@[simp]
theorem node_newEdge :
    node G x0 ExtDart.newEdge =
      ExtDart.old (G.face (G.edge x0)) :=
  rfl

@[simp]
theorem node_old (y : G.Dart) :
    node G x0 (ExtDart.old y) =
      if y = x0 then ExtDart.newEdge
      else if G.node (G.node y) = x0 then ExtDart.new
      else ExtDart.old (G.node y) :=
  rfl

/-- Face permutation for the `ecpN` hypermap extension, derived from `edge`
and `node` so that the hypermap cancellation law is definitional. -/
def face : Equiv.Perm (ExtDart G.Dart) :=
  (ExtDart.Perm.edge G.edge).symm.trans (node G x0).symm

theorem node_face_edge (x : ExtDart G.Dart) :
    node G x0 (face G x0 (ExtDart.Perm.edge G.edge x)) = x := by
  simp [face, Equiv.trans_apply]

@[simp]
theorem face_new :
    face G x0 ExtDart.new = ExtDart.old x0 := by
  rfl

@[simp]
theorem face_newEdge :
    face G x0 ExtDart.newEdge =
      if G.LongRingHead x0 then
        ExtDart.old (G.face (G.edge (G.face (G.edge x0))))
      else ExtDart.new := by
  by_cases hlong : G.LongRingHead x0
  · have hface :
        G.face (G.edge (G.face (G.edge x0))) =
          G.node.symm (G.node.symm x0) := by
      rw [face_edge_eq_node_symm (G := G) (G.face (G.edge x0)),
        face_edge_eq_node_symm (G := G) x0]
    simp [face, node, nodeInvFun, ExtDart.Perm.edge, hlong, hface]
  · simp [face, node, nodeInvFun, ExtDart.Perm.edge, hlong]

@[simp]
theorem face_old (y : G.Dart) :
    face G x0 (ExtDart.old y) =
      if y = G.edge (G.face (G.edge x0)) then ExtDart.newEdge
      else if y = G.edge (G.node x0) then ExtDart.new
      else ExtDart.old (G.face y) := by
  change nodeInvFun G x0 (ExtDart.old (G.edge.symm y)) =
    if y = G.edge (G.face (G.edge x0)) then ExtDart.newEdge
    else if y = G.edge (G.node x0) then ExtDart.new
    else ExtDart.old (G.face y)
  by_cases hface : y = G.edge (G.face (G.edge x0))
  · subst y
    simp [nodeInvFun]
  · by_cases hnode : y = G.edge (G.node x0)
    · subst y
      have hnotFace : G.node x0 ≠ G.face (G.edge x0) := by
        intro h
        apply hface
        rw [h]
      simp [nodeInvFun, hface, hnotFace]
    · have hnotFace : G.edge.symm y ≠ G.face (G.edge x0) := by
        intro h
        apply hface
        calc
          y = G.edge (G.edge.symm y) := by simp
          _ = G.edge (G.face (G.edge x0)) := by rw [h]
      have hnotNode : G.edge.symm y ≠ G.node x0 := by
        intro h
        apply hnode
        calc
          y = G.edge (G.edge.symm y) := by simp
          _ = G.edge (G.node x0) := by rw [h]
      have hnodeFace : G.node (G.face y) = G.edge.symm y := by
        apply G.edge.injective
        calc
          G.edge (G.node (G.face y)) = y := G.edge_node_face y
          _ = G.edge (G.edge.symm y) := by simp
      have hfaceEq : G.node.symm (G.edge.symm y) = G.face y := by
        apply G.node.injective
        simp [hnodeFace]
      simp [nodeInvFun, hface, hnode, hnotFace, hnotNode, hfaceEq]

end ExtensionN

/-- Coq's `ecpU` hypermap constructor: add a new U-shaped outer face. -/
def extensionU : Hypermap where
  Dart := ExtDart G.Dart
  edge := ExtDart.Perm.edge G.edge
  node := ExtensionU.node G x0
  face := ExtensionU.face G x0
  node_face_edge := ExtensionU.node_face_edge G x0

/-- Coq's `ecpN` hypermap constructor: close the next outer ring corner. -/
def extensionN : Hypermap where
  Dart := ExtDart G.Dart
  edge := ExtDart.Perm.edge G.edge
  node := ExtensionN.node G x0
  face := ExtensionN.face G x0
  node_face_edge := ExtensionN.node_face_edge G x0

@[simp]
theorem extensionU_card :
    Fintype.card (extensionU G x0).Dart = Fintype.card G.Dart + 2 :=
  ExtDart.card

@[simp]
theorem extensionN_card :
    Fintype.card (extensionN G x0).Dart = Fintype.card G.Dart + 2 :=
  ExtDart.card

theorem extensionU_plain
    (hG : G.Plain) :
    (extensionU G x0).Plain := by
  exact ExtDart.Perm.edge_plain G.edge hG

theorem extensionN_plain
    (hG : G.Plain) :
    (extensionN G x0).Plain := by
  exact ExtDart.Perm.edge_plain G.edge hG

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
