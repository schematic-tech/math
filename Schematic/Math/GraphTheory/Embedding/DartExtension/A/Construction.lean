import Schematic.Math.GraphTheory.Embedding.DartExtension.H.RingAdjacency

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

/-!
### The `ecpA` merge constructor

Coq's `ecpA` keeps the dart type fixed and merges the two neighboring ring
nodes around `x0`.  The edge permutation is changed only when the two relevant
faces were already connected, while the node permutation always bypasses the
two ring darts that are removed by the merge.
-/

/-- Edge permutation for Coq's `ecpA` constructor. -/
noncomputable def extensionAEdge : Equiv.Perm G.Dart := by
  classical
  exact
    if PermReachable G.face (G.edge x0) (G.node x0) then
      G.edge.trans
        (Equiv.swap (G.edge x0) (G.edge (G.node (G.node x0))))
    else
      G.edge

/-- Node permutation for Coq's `ecpA` constructor. -/
def extensionANode : Equiv.Perm G.Dart :=
  G.node.trans (Equiv.swap x0 (G.node (G.node x0)))

/-- Face permutation for Coq's `ecpA` constructor, determined by cancellation. -/
noncomputable def extensionAFace : Equiv.Perm G.Dart :=
  (extensionAEdge G x0).symm.trans (extensionANode G x0).symm

@[simp]
theorem extensionAEdge_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0)) :
    extensionAEdge G x0 = G.edge := by
  classical
  simp [extensionAEdge, hnot]

@[simp]
theorem extensionAEdge_of_faceReachable
    (h : PermReachable G.face (G.edge x0) (G.node x0)) :
    extensionAEdge G x0 =
      G.edge.trans
        (Equiv.swap (G.edge x0) (G.edge (G.node (G.node x0)))) := by
  classical
  simp [extensionAEdge, h]

@[simp]
theorem extensionANode_apply (x : G.Dart) :
    extensionANode G x0 x =
      Equiv.swap x0 (G.node (G.node x0)) (G.node x) :=
  rfl

theorem extensionANode_apply_coq (x : G.Dart) :
    extensionANode G x0 x =
      if x = G.node x0 then x0
      else if G.node x = x0 then G.node (G.node x0)
      else G.node x := by
  unfold extensionANode
  by_cases hx : x = G.node x0
  · subst x
    simp [Equiv.trans_apply]
  · by_cases hn : G.node x = x0
    · simp [Equiv.trans_apply, hx, hn]
    · have hnn : G.node x ≠ G.node (G.node x0) := by
        intro h
        apply hx
        exact G.node.injective h
      simp only [Equiv.trans_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hn hnn]
      simp [hx, hn]

@[simp]
theorem extensionANode_node_x0 :
    extensionANode G x0 (G.node x0) = x0 := by
  rw [extensionANode_apply_coq]
  simp

theorem extensionANode_x0_of_proper
    (hproper : G.ProperRingHead x0) :
    extensionANode G x0 x0 = G.node x0 := by
  rw [extensionANode_apply_coq]
  have hne : G.node x0 ≠ x0 := fun h => hproper h.symm
  simp [hne]

theorem extensionANode_face_edge_x0_of_long
    (hlong : G.LongRingHead x0) :
    extensionANode G x0 (G.face (G.edge x0)) =
      G.node (G.node x0) := by
  rw [extensionANode_apply_coq]
  change G.face (G.edge x0) ≠ G.node x0 at hlong
  have hn : G.node (G.face (G.edge x0)) = x0 := by simp
  simp [hlong, hn]

theorem extensionANode_of_regular
    {x : G.Dart}
    (hxnode : x ≠ G.node x0)
    (hxface : x ≠ G.face (G.edge x0)) :
    extensionANode G x0 x = G.node x := by
  rw [extensionANode_apply_coq]
  have hn : G.node x ≠ x0 := by
    intro h
    apply hxface
    apply G.node.injective
    simp [h]
  simp [hxnode, hn]

theorem extensionAEdge_apply_coq
    [Decidable (PermReachable G.face (G.edge x0) (G.node x0))]
    (x : G.Dart) :
    extensionAEdge G x0 x =
      if PermReachable G.face (G.edge x0) (G.node x0) then
        if x = x0 then G.edge (G.node (G.node x0))
        else if x = G.node (G.node x0) then G.edge x0
        else G.edge x
      else G.edge x := by
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · unfold extensionAEdge
    simp only [h, ↓reduceIte, Equiv.trans_apply]
    by_cases hx : x = x0
    · subst x
      simp
    · by_cases hnn : x = G.node (G.node x0)
      · subst x
        simp [hx]
      · have he0 : G.edge x ≠ G.edge x0 := by
          intro he
          apply hx
          exact G.edge.injective he
        have henn : G.edge x ≠ G.edge (G.node (G.node x0)) := by
          intro he
          apply hnn
          exact G.edge.injective he
        rw [Equiv.swap_apply_of_ne_of_ne he0 henn]
        simp [hx, hnn]
  · unfold extensionAEdge
    simp [h]

@[simp]
theorem extensionAFace_edge_cancel (x : G.Dart) :
    extensionAFace G x0 (extensionAEdge G x0 x) =
      (extensionANode G x0).symm x := by
  simp [extensionAFace, Equiv.trans_apply]

private theorem edge_symm_ne_of_ne_edge
    {x y : G.Dart}
    (hxy : x ≠ G.edge y) :
    G.edge.symm x ≠ y := by
  intro h
  apply hxy
  calc
    x = G.edge (G.edge.symm x) := by simp
    _ = G.edge y := by rw [h]

theorem extensionAFace_of_faceReachable
    (h : PermReachable G.face (G.edge x0) (G.node x0)) :
    extensionAFace G x0 = G.face := by
  ext x
  by_cases hx : x = G.edge x0
  · subst x
    unfold extensionAFace extensionAEdge extensionANode
    simp [h, Equiv.trans_apply, Hypermap.face_edge_eq_node_symm]
  · by_cases hnn : x = G.edge (G.node (G.node x0))
    · subst x
      unfold extensionAFace extensionAEdge extensionANode
      simp [h, Equiv.trans_apply, Hypermap.face_edge_eq_node_symm]
    · have hy0 := edge_symm_ne_of_ne_edge (G := G) hx
      have hynn := edge_symm_ne_of_ne_edge (G := G) hnn
      unfold extensionAFace extensionAEdge extensionANode
      simp only [h, ↓reduceIte, Equiv.trans_apply, Equiv.symm_trans_apply]
      rw [Equiv.symm_swap (G.edge x0) (G.edge (G.node (G.node x0)))]
      rw [Equiv.swap_apply_of_ne_of_ne hx hnn]
      rw [Equiv.symm_swap x0 (G.node (G.node x0))]
      rw [Equiv.swap_apply_of_ne_of_ne hy0 hynn]
      simpa using
        (Hypermap.face_edge_eq_node_symm (G := G) (G.edge.symm x)).symm

theorem extensionAFace_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    (x : G.Dart) :
    extensionAFace G x0 x =
      if x = G.edge x0 then G.node x0
      else if G.face x = G.node x0 then G.face (G.edge x0)
      else G.face x := by
  by_cases hx : x = G.edge x0
  · subst x
    unfold extensionAFace extensionAEdge extensionANode
    simp [hnot, Equiv.trans_apply, Equiv.symm_trans_apply]
  · by_cases hf : G.face x = G.node x0
    · have hynn : G.edge.symm x = G.node (G.node x0) := by
        calc
          G.edge.symm x = G.node (G.face x) := by
            simpa using (G.node_face_edge (G.edge.symm x)).symm
          _ = G.node (G.node x0) := by rw [hf]
      unfold extensionAFace extensionAEdge extensionANode
      simp only [hnot, ↓reduceIte, Equiv.trans_apply, Equiv.symm_trans_apply]
      rw [Equiv.symm_swap x0 (G.node (G.node x0))]
      rw [hynn]
      rw [Equiv.swap_apply_right]
      simp [hx, hf, Hypermap.face_edge_eq_node_symm]
    · have hy0 := edge_symm_ne_of_ne_edge (G := G) hx
      have hynn : G.edge.symm x ≠ G.node (G.node x0) := by
        intro hy
        apply hf
        calc
          G.face x = G.node.symm (G.edge.symm x) := by
            simpa using
              (Hypermap.face_edge_eq_node_symm (G := G) (G.edge.symm x))
          _ = G.node.symm (G.node (G.node x0)) := by rw [hy]
          _ = G.node x0 := by simp
      unfold extensionAFace extensionAEdge extensionANode
      simp only [hnot, ↓reduceIte, Equiv.trans_apply, Equiv.symm_trans_apply]
      rw [Equiv.symm_swap x0 (G.node (G.node x0))]
      rw [Equiv.swap_apply_of_ne_of_ne hy0 hynn]
      simp [hx, hf]
      simpa using
        (Hypermap.face_edge_eq_node_symm (G := G) (G.edge.symm x)).symm

theorem extensionAFace_apply
    [Decidable (PermReachable G.face (G.edge x0) (G.node x0))]
    (x : G.Dart) :
    extensionAFace G x0 x =
      if PermReachable G.face (G.edge x0) (G.node x0) then
        G.face x
      else if x = G.edge x0 then
        G.node x0
      else if G.face x = G.node x0 then
        G.face (G.edge x0)
      else
        G.face x := by
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · rw [if_pos h]
    rw [extensionAFace_of_faceReachable (G := G) x0 h]
  · rw [if_neg h]
    exact extensionAFace_of_not_faceReachable (G := G) x0 h x

/-- Coq's `ecpA` hypermap constructor. -/
noncomputable def extensionA : Hypermap where
  Dart := G.Dart
  edge := extensionAEdge G x0
  node := extensionANode G x0
  face := extensionAFace G x0
  node_face_edge := by
    intro x
    simp [extensionAFace, Equiv.trans_apply]

theorem extensionA_face_of_faceReachable
    (h : PermReachable G.face (G.edge x0) (G.node x0)) :
    (extensionA G x0).face = G.face :=
  extensionAFace_of_faceReachable (G := G) x0 h

@[simp]
theorem extensionA_node_node_x0 :
    (extensionA G x0).node (G.node x0) = x0 :=
  extensionANode_node_x0 (G := G) (x0 := x0)

theorem extensionA_node_x0_of_proper
    (hproper : G.ProperRingHead x0) :
    (extensionA G x0).node x0 = G.node x0 :=
  extensionANode_x0_of_proper (G := G) x0 hproper

theorem extensionA_node_face_edge_x0_of_long
    (hlong : G.LongRingHead x0) :
    (extensionA G x0).node (G.face (G.edge x0)) =
      G.node (G.node x0) :=
  extensionANode_face_edge_x0_of_long (G := G) x0 hlong

theorem extensionA_node_of_regular
    {x : G.Dart}
    (hxnode : x ≠ G.node x0)
    (hxface : x ≠ G.face (G.edge x0)) :
    (extensionA G x0).node x = G.node x :=
  extensionANode_of_regular (G := G) x0 hxnode hxface

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
