import Schematic.Math.GraphTheory.Embedding.DartExtension.A.Construction

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap) (x0 : G.Dart)

/-- Away from the two darts bypassed by `ecpA`, its inverse node step is the
source inverse node step. -/
theorem extensionA_node_symm_apply_of_ne
    {x : G.Dart}
    (hx0 : x ≠ x0) (hxnn : x ≠ G.node (G.node x0)) :
    (extensionA G x0).node.symm x = G.node.symm x := by
  change (extensionANode G x0).symm x = G.node.symm x
  unfold extensionANode
  simp only [Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [Equiv.swap_apply_of_ne_of_ne hx0 hxnn]

@[simp]
theorem extensionA_node_symm_node_node :
    (extensionA G x0).node.symm (G.node (G.node x0)) =
      G.node.symm x0 := by
  change (extensionANode G x0).symm (G.node (G.node x0)) =
    G.node.symm x0
  unfold extensionANode
  simp [Equiv.symm_trans_apply]

theorem extensionA_nodeReachable_x0_node_x0_of_proper
    (hproper : G.ProperRingHead x0) :
    PermReachable (extensionA G x0).node x0 (G.node x0) := by
  have hnode := extensionA_node_x0_of_proper (G := G) x0 hproper
  simpa [hnode] using PermReachable.forward (extensionA G x0).node x0

theorem extensionA_nodeReachable_node_x0_x0 :
    PermReachable (extensionA G x0).node (G.node x0) x0 := by
  have hnode := extensionA_node_node_x0 (G := G) (x0 := x0)
  simpa [hnode] using
    PermReachable.forward (extensionA G x0).node (G.node x0)

theorem extensionA_nodeReachable_face_edge_x0_node_node_x0_of_long
    (hlong : G.LongRingHead x0) :
    PermReachable (extensionA G x0).node
      (G.face (G.edge x0)) (G.node (G.node x0)) := by
  have hnode := extensionA_node_face_edge_x0_of_long (G := G) x0 hlong
  simpa [hnode] using
    PermReachable.forward (extensionA G x0).node (G.face (G.edge x0))

theorem extensionA_node_step_oldReachable (x : G.Dart) :
    PermReachable G.node x ((extensionA G x0).node x) := by
  change PermReachable G.node x (extensionANode G x0 x)
  rw [extensionANode_apply_coq]
  by_cases hx : x = G.node x0
  · subst x
    simp
    simpa using PermReachable.backward G.node (G.node x0)
  · simp only [hx, ↓reduceIte]
    by_cases hn : G.node x = x0
    · simp only [hn, ↓reduceIte]
      exact PermReachable.trans G.node
        (by simpa [hn] using PermReachable.forward G.node x)
        (PermReachable.trans G.node
          (PermReachable.forward G.node x0)
          (PermReachable.forward G.node (G.node x0)))
    · simp only [hn, ↓reduceIte]
      exact PermReachable.forward G.node x

theorem extensionA_nodeReachable_implies_nodeReachable
    {x y : G.Dart}
    (hxy : PermReachable (extensionA G x0).node x y) :
    PermReachable G.node x y := by
  induction hxy with
  | refl => exact PermReachable.refl G.node x
  | @tail b c hxb hbc ih =>
      cases hbc with
      | forward =>
          exact PermReachable.trans G.node ih
            (extensionA_node_step_oldReachable (G := G) x0 b)
      | backward =>
          have hstep := extensionA_node_step_oldReachable
            (G := G) x0 ((extensionA G x0).node.symm b)
          exact PermReachable.trans G.node ih
            (by simpa using PermReachable.symm G.node hstep)

theorem extensionA_nodeReachable_of_iterate_regular
    {x y : G.Dart} {n : ℕ}
    (hiter : (G.node : G.Dart → G.Dart)^[n] x = y)
    (hxnode : ∀ k : ℕ, k < n →
      (G.node : G.Dart → G.Dart)^[k] x ≠ G.node x0)
    (hxface : ∀ k : ℕ, k < n →
      (G.node : G.Dart → G.Dart)^[k] x ≠ G.face (G.edge x0)) :
    PermReachable (extensionA G x0).node x y := by
  induction n generalizing x with
  | zero =>
      rw [← hiter]
      exact PermReachable.refl (extensionA G x0).node x
  | succ n ih =>
      have hx0 : x ≠ G.node x0 := by
        simpa using hxnode 0 (Nat.succ_pos n)
      have hxf : x ≠ G.face (G.edge x0) := by
        simpa using hxface 0 (Nat.succ_pos n)
      have hstep : PermReachable (extensionA G x0).node x (G.node x) := by
        have hnode := extensionA_node_of_regular (G := G) (x0 := x0) hx0 hxf
        simpa [hnode] using PermReachable.forward (extensionA G x0).node x
      have hiter_tail : (G.node : G.Dart → G.Dart)^[n] (G.node x) = y := by
        simpa [Function.iterate_succ_apply] using hiter
      have hxnode_tail : ∀ k : ℕ, k < n →
          (G.node : G.Dart → G.Dart)^[k] (G.node x) ≠ G.node x0 := by
        intro k hk
        have hk' : k.succ < n.succ := Nat.succ_lt_succ hk
        simpa [Function.iterate_succ_apply] using hxnode k.succ hk'
      have hxface_tail : ∀ k : ℕ, k < n →
          (G.node : G.Dart → G.Dart)^[k] (G.node x) ≠
            G.face (G.edge x0) := by
        intro k hk
        have hk' : k.succ < n.succ := Nat.succ_lt_succ hk
        simpa [Function.iterate_succ_apply] using hxface k.succ hk'
      exact PermReachable.trans (extensionA G x0).node hstep
        (ih hiter_tail hxnode_tail hxface_tail)

theorem extensionA_face_edge_x0_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0)) :
    (extensionA G x0).face (G.edge x0) = G.node x0 := by
  change extensionAFace G x0 (G.edge x0) = G.node x0
  rw [extensionAFace_of_not_faceReachable (G := G) x0 hnot]
  simp

theorem extensionA_face_of_not_faceReachable_of_face_node
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x : G.Dart}
    (hx : G.face x = G.node x0) :
    (extensionA G x0).face x = G.face (G.edge x0) := by
  change extensionAFace G x0 x = G.face (G.edge x0)
  rw [extensionAFace_of_not_faceReachable (G := G) x0 hnot]
  by_cases hx0 : x = G.edge x0
  · subst x
    simpa using hx.symm
  · simp [hx0, hx]

theorem extensionA_face_of_not_faceReachable_of_regular
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x : G.Dart}
    (hx0 : x ≠ G.edge x0)
    (hx : G.face x ≠ G.node x0) :
    (extensionA G x0).face x = G.face x := by
  change extensionAFace G x0 x = G.face x
  rw [extensionAFace_of_not_faceReachable (G := G) x0 hnot]
  simp [hx0, hx]

theorem extensionA_faceReachable_of_faceReachable_of_faceReachable_edge_node
    (h : PermReachable G.face (G.edge x0) (G.node x0))
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionA G x0).face x y := by
  rw [extensionA_face_of_faceReachable (G := G) x0 h]
  exact hxy

theorem extensionA_edge_faceReachable_edge_of_faceReachable_edge_node
    (h : PermReachable G.face (G.edge x0) (G.node x0))
    (x : G.Dart) :
    PermReachable (extensionA G x0).face
      ((extensionA G x0).edge x) (G.edge x) := by
  change PermReachable (extensionAFace G x0)
    (extensionAEdge G x0 x) (G.edge x)
  rw [extensionAFace_of_faceReachable (G := G) x0 h,
    extensionAEdge_of_faceReachable (G := G) x0 h]
  have hstep :
      PermReachable G.face
        (G.edge (G.node (G.node x0))) (G.node x0) := by
    simpa using
      (PermReachable.forward G.face (G.edge (G.node (G.node x0))))
  by_cases hx : x = x0
  · subst x
    simpa [Equiv.trans_apply] using
      PermReachable.trans G.face hstep (PermReachable.symm G.face h)
  · by_cases hnn : x = G.node (G.node x0)
    · subst x
      simpa [Equiv.trans_apply, hx] using
        PermReachable.trans G.face h (PermReachable.symm G.face hstep)
    · have he0 : G.edge x ≠ G.edge x0 := by
        intro he
        exact hx (G.edge.injective he)
      have henn : G.edge x ≠ G.edge (G.node (G.node x0)) := by
        intro he
        exact hnn (G.edge.injective he)
      rw [Equiv.trans_apply,
        Equiv.swap_apply_of_ne_of_ne he0 henn]
      exact PermReachable.refl G.face (G.edge x)

theorem extensionA_ringAdj_of_ringAdj_of_faceReachable_edge_node
    (h : PermReachable G.face (G.edge x0) (G.node x0))
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionA G x0).RingAdj x y := by
  rcases hxy with ⟨z, hxz, hzy⟩
  refine ⟨z,
    extensionA_faceReachable_of_faceReachable_of_faceReachable_edge_node
      (G := G) x0 h hxz,
    ?_⟩
  exact PermReachable.trans (extensionA G x0).face
    (extensionA_edge_faceReachable_edge_of_faceReachable_edge_node
      (G := G) x0 h z)
    (extensionA_faceReachable_of_faceReachable_of_faceReachable_edge_node
      (G := G) x0 h hzy)

theorem extensionA_faceReachable_edge_x0_node_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0)) :
    PermReachable (extensionA G x0).face (G.edge x0) (G.node x0) := by
  have hface :=
    extensionA_face_edge_x0_of_not_faceReachable (G := G) x0 hnot
  simpa [hface] using
    (PermReachable.forward (extensionA G x0).face (G.edge x0))

theorem extensionA_faceReachable_of_not_faceReachable_of_face_node
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x : G.Dart}
    (hx : G.face x = G.node x0) :
    PermReachable (extensionA G x0).face x (G.face (G.edge x0)) := by
  have hface :=
    extensionA_face_of_not_faceReachable_of_face_node
      (G := G) x0 hnot hx
  simpa [hface] using
    (PermReachable.forward (extensionA G x0).face x)

theorem extensionA_faceReachable_of_not_faceReachable_of_regular
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x : G.Dart}
    (hx0 : x ≠ G.edge x0)
    (hx : G.face x ≠ G.node x0) :
    PermReachable (extensionA G x0).face x (G.face x) := by
  have hface :=
    extensionA_face_of_not_faceReachable_of_regular
      (G := G) x0 hnot hx0 hx
  simpa [hface] using
    (PermReachable.forward (extensionA G x0).face x)

/-- A forward face iterate lifts to `ecpA` as long as all traversed darts use
the unchanged `ecpA` face equation.  This is the path-level replacement for
the regular branch of Coq's `map_path baseF_ecpA`. -/
theorem extensionA_faceReachable_of_not_faceReachable_of_iterate_regular
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x y : G.Dart} {n : ℕ}
    (hiter : (G.face : G.Dart → G.Dart)^[n] x = y)
    (hxedge : ∀ k : ℕ, k < n →
      (G.face : G.Dart → G.Dart)^[k] x ≠ G.edge x0)
    (hxnode : ∀ k : ℕ, k < n →
      G.face ((G.face : G.Dart → G.Dart)^[k] x) ≠ G.node x0) :
    PermReachable (extensionA G x0).face x y := by
  induction n generalizing x with
  | zero =>
      rw [← hiter]
      exact PermReachable.refl (extensionA G x0).face x
  | succ n ih =>
      have hx0 : x ≠ G.edge x0 := by
        simpa using hxedge 0 (Nat.succ_pos n)
      have hxf : G.face x ≠ G.node x0 := by
        simpa using hxnode 0 (Nat.succ_pos n)
      have hstep : PermReachable (extensionA G x0).face x (G.face x) :=
        extensionA_faceReachable_of_not_faceReachable_of_regular
          (G := G) x0 hnot hx0 hxf
      have hiter_tail : (G.face : G.Dart → G.Dart)^[n] (G.face x) = y := by
        simpa [Function.iterate_succ_apply] using hiter
      have hxedge_tail : ∀ k : ℕ, k < n →
          (G.face : G.Dart → G.Dart)^[k] (G.face x) ≠ G.edge x0 := by
        intro k hk
        have hk' : k.succ < n.succ := Nat.succ_lt_succ hk
        simpa [Function.iterate_succ_apply] using hxedge k.succ hk'
      have hxnode_tail : ∀ k : ℕ, k < n →
          G.face ((G.face : G.Dart → G.Dart)^[k] (G.face x)) ≠
            G.node x0 := by
        intro k hk
        have hk' : k.succ < n.succ := Nat.succ_lt_succ hk
        simpa [Function.iterate_succ_apply] using hxnode k.succ hk'
      exact PermReachable.trans (extensionA G x0).face hstep
        (ih hiter_tail hxedge_tail hxnode_tail)

theorem extensionA_face_predecessor_node (x0 : G.Dart) :
    G.face (G.edge (G.node (G.node x0))) = G.node x0 := by
  simp [Hypermap.face_edge_eq_node_symm]

theorem extensionA_face_symm_node_eq_predecessor (x0 : G.Dart) :
    G.face.symm (G.node x0) = G.edge (G.node (G.node x0)) := by
  apply G.face.injective
  simp [Hypermap.face_edge_eq_node_symm]

theorem extensionA_faceReachable_node_predecessor_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0)) :
    PermReachable (extensionA G x0).face
      (G.node x0) (G.edge (G.node (G.node x0))) := by
  classical
  let p := G.edge (G.node (G.node x0))
  have hp : G.face p = G.node x0 := by
    dsimp [p]
    exact extensionA_face_predecessor_node (G := G) x0
  have hback : PermReachable G.face (G.node x0) p := by
    simpa [p, extensionA_face_symm_node_eq_predecessor (G := G) x0] using
      (PermReachable.backward G.face (G.node x0))
  rcases permReachable_exists_first_iterate G.face hback with ⟨n, hn, hmin⟩
  refine extensionA_faceReachable_of_not_faceReachable_of_iterate_regular
    (G := G) x0 hnot hn ?_ ?_
  · intro k hk heq
    apply hnot
    have hnk : PermReachable G.face (G.node x0) (G.edge x0) :=
      permReachable_of_iterate_eq G.face heq
    exact PermReachable.symm G.face hnk
  · intro k hk hface
    have hkp : (G.face : G.Dart → G.Dart)^[k] (G.node x0) = p := by
      apply G.face.injective
      simpa [hp] using hface
    exact hmin k hk hkp

theorem extensionA_faceReachable_edge_x0_face_edge_x0_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0)) :
    PermReachable (extensionA G x0).face
      (G.edge x0) (G.face (G.edge x0)) := by
  let p := G.edge (G.node (G.node x0))
  have hedge_node :
      PermReachable (extensionA G x0).face (G.edge x0) (G.node x0) :=
    extensionA_faceReachable_edge_x0_node_of_not_faceReachable
      (G := G) x0 hnot
  have hnode_p :
      PermReachable (extensionA G x0).face (G.node x0) p :=
    extensionA_faceReachable_node_predecessor_of_not_faceReachable
      (G := G) x0 hnot
  have hpface : G.face p = G.node x0 := by
    dsimp [p]
    exact extensionA_face_predecessor_node (G := G) x0
  have hp_next :
      PermReachable (extensionA G x0).face p (G.face (G.edge x0)) :=
    extensionA_faceReachable_of_not_faceReachable_of_face_node
      (G := G) x0 hnot hpface
  exact PermReachable.trans (extensionA G x0).face hedge_node
    (PermReachable.trans (extensionA G x0).face hnode_p hp_next)

theorem extensionA_faceReachable_face_edge_x0_node_x0_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0)) :
    PermReachable (extensionA G x0).face
      (G.face (G.edge x0)) (G.node x0) := by
  have h_edge_face :
      PermReachable (extensionA G x0).face
        (G.edge x0) (G.face (G.edge x0)) :=
    extensionA_faceReachable_edge_x0_face_edge_x0_of_not_faceReachable
      (G := G) x0 hnot
  have h_edge_node :
      PermReachable (extensionA G x0).face (G.edge x0) (G.node x0) :=
    extensionA_faceReachable_edge_x0_node_of_not_faceReachable
      (G := G) x0 hnot
  exact PermReachable.trans (extensionA G x0).face
    (PermReachable.symm (extensionA G x0).face h_edge_face) h_edge_node

theorem extensionA_faceReachable_step_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    (x : G.Dart) :
    PermReachable (extensionA G x0).face x (G.face x) := by
  by_cases hx0 : x = G.edge x0
  · subst x
    exact extensionA_faceReachable_edge_x0_face_edge_x0_of_not_faceReachable
      (G := G) x0 hnot
  · by_cases hxnode : G.face x = G.node x0
    · have hxfedge :
          PermReachable (extensionA G x0).face x (G.face (G.edge x0)) :=
        extensionA_faceReachable_of_not_faceReachable_of_face_node
          (G := G) x0 hnot hxnode
      have hfe_node :
          PermReachable (extensionA G x0).face
            (G.face (G.edge x0)) (G.node x0) :=
        extensionA_faceReachable_face_edge_x0_node_x0_of_not_faceReachable
          (G := G) x0 hnot
      simpa [hxnode] using
        PermReachable.trans (extensionA G x0).face hxfedge hfe_node
    · exact extensionA_faceReachable_of_not_faceReachable_of_regular
        (G := G) x0 hnot hx0 hxnode

theorem extensionA_faceReachable_of_faceReachable_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionA G x0).face x y := by
  induction hxy with
  | refl => exact PermReachable.refl (extensionA G x0).face x
  | @tail b c hxb hbc ih =>
      cases hbc with
      | forward =>
          exact PermReachable.trans (extensionA G x0).face ih
            (extensionA_faceReachable_step_of_not_faceReachable
              (G := G) x0 hnot b)
      | backward =>
          have hstep :
              PermReachable (extensionA G x0).face (G.face.symm b) b := by
            simpa using extensionA_faceReachable_step_of_not_faceReachable
              (G := G) x0 hnot (G.face.symm b)
          exact PermReachable.trans (extensionA G x0).face ih
            (PermReachable.symm (extensionA G x0).face hstep)

theorem extensionA_faceReachable_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    PermReachable (extensionA G x0).face x y := by
  classical
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · exact extensionA_faceReachable_of_faceReachable_of_faceReachable_edge_node
      (G := G) x0 h hxy
  · exact extensionA_faceReachable_of_faceReachable_of_not_faceReachable
      (G := G) x0 h hxy

theorem extensionA_edge_faceReachable_edge_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    (x : G.Dart) :
    PermReachable (extensionA G x0).face
      ((extensionA G x0).edge x) (G.edge x) := by
  change PermReachable (extensionAFace G x0) (extensionAEdge G x0 x)
    (G.edge x)
  rw [extensionAEdge_of_not_faceReachable (G := G) x0 hnot]
  exact PermReachable.refl (extensionAFace G x0) (G.edge x)

theorem extensionA_edge_faceReachable_edge (x : G.Dart) :
    PermReachable (extensionA G x0).face
      ((extensionA G x0).edge x) (G.edge x) := by
  classical
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · exact extensionA_edge_faceReachable_edge_of_faceReachable_edge_node
      (G := G) x0 h x
  · exact extensionA_edge_faceReachable_edge_of_not_faceReachable
      (G := G) x0 h x

theorem extensionA_ringAdj_of_ringAdj_of_not_faceReachable
    (hnot : ¬ PermReachable G.face (G.edge x0) (G.node x0))
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionA G x0).RingAdj x y := by
  rcases hxy with ⟨z, hxz, hzy⟩
  refine ⟨z,
    extensionA_faceReachable_of_faceReachable_of_not_faceReachable
      (G := G) x0 hnot hxz,
    ?_⟩
  exact PermReachable.trans (extensionA G x0).face
    (extensionA_edge_faceReachable_edge_of_not_faceReachable
      (G := G) x0 hnot z)
    (extensionA_faceReachable_of_faceReachable_of_not_faceReachable
      (G := G) x0 hnot hzy)

theorem extensionA_ringAdj_of_ringAdj
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    (extensionA G x0).RingAdj x y := by
  classical
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · exact extensionA_ringAdj_of_ringAdj_of_faceReachable_edge_node
      (G := G) x0 h hxy
  · exact extensionA_ringAdj_of_ringAdj_of_not_faceReachable
      (G := G) x0 h hxy

theorem extensionA_faceReachable_face_edge_x0_node_x0
    (x0 : G.Dart) :
    PermReachable (extensionA G x0).face
      (G.face (G.edge x0)) (G.node x0) := by
  classical
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · rw [extensionA_face_of_faceReachable (G := G) x0 h]
    exact PermReachable.trans G.face
      (PermReachable.symm G.face (PermReachable.forward G.face (G.edge x0))) h
  · exact extensionA_faceReachable_face_edge_x0_node_x0_of_not_faceReachable
      (G := G) x0 h

theorem extensionA_faceReachable_node_x0_face_edge_x0
    (x0 : G.Dart) :
    PermReachable (extensionA G x0).face
      (G.node x0) (G.face (G.edge x0)) :=
  PermReachable.symm (extensionA G x0).face
    (extensionA_faceReachable_face_edge_x0_node_x0 (G := G) x0)

theorem extensionA_faceReachable_source_to_faceBand_pair
    {x : G.Dart}
    (hx : G.FaceBand [G.face (G.edge x0), G.node x0] x) :
    PermReachable (extensionA G x0).face (G.node x0) x := by
  rw [FaceBand.pair] at hx
  rcases hx with hx | hx
  · exact PermReachable.trans (extensionA G x0).face
      (extensionA_faceReachable_node_x0_face_edge_x0 (G := G) x0)
      (extensionA_faceReachable_of_faceReachable (G := G) x0 hx)
  · exact extensionA_faceReachable_of_faceReachable (G := G) x0 hx

theorem extensionA_faceReachable_of_faceBand_pair
    {x y : G.Dart}
    (hx : G.FaceBand [G.face (G.edge x0), G.node x0] x)
    (hy : G.FaceBand [G.face (G.edge x0), G.node x0] y) :
    PermReachable (extensionA G x0).face x y := by
  exact PermReachable.trans (extensionA G x0).face
    (PermReachable.symm (extensionA G x0).face
      (extensionA_faceReachable_source_to_faceBand_pair (G := G) x0 hx))
    (extensionA_faceReachable_source_to_faceBand_pair (G := G) x0 hy)

theorem extensionA_faceBand_pair_of_edge_x0 :
    G.FaceBand [G.face (G.edge x0), G.node x0] (G.edge x0) := by
  rw [FaceBand.pair]
  exact Or.inl
    (PermReachable.symm G.face (PermReachable.forward G.face (G.edge x0)))

theorem extensionA_faceBand_pair_of_face_edge_x0 :
    G.FaceBand [G.face (G.edge x0), G.node x0]
      (G.face (G.edge x0)) := by
  rw [FaceBand.pair]
  exact Or.inl (PermReachable.refl G.face (G.face (G.edge x0)))

theorem extensionA_faceBand_pair_of_node_x0 :
    G.FaceBand [G.face (G.edge x0), G.node x0] (G.node x0) := by
  rw [FaceBand.pair]
  exact Or.inr (PermReachable.refl G.face (G.node x0))

theorem extensionA_faceBand_pair_of_face_node
    {x : G.Dart} (hx : G.face x = G.node x0) :
    G.FaceBand [G.face (G.edge x0), G.node x0] x := by
  rw [FaceBand.pair]
  exact Or.inr (by
    have h : PermReachable G.face x (G.node x0) := by
      simpa [hx] using PermReachable.forward G.face x
    exact PermReachable.symm G.face h)

theorem extensionA_face_step_old_or_faceBand_pair
    (x : G.Dart) :
    PermReachable G.face x ((extensionA G x0).face x) ∨
      (G.FaceBand [G.face (G.edge x0), G.node x0] x ∧
        G.FaceBand [G.face (G.edge x0), G.node x0]
          ((extensionA G x0).face x)) := by
  classical
  by_cases h : PermReachable G.face (G.edge x0) (G.node x0)
  · rw [extensionA_face_of_faceReachable (G := G) x0 h]
    exact Or.inl (PermReachable.forward G.face x)
  · change PermReachable G.face x (extensionAFace G x0 x) ∨
      (G.FaceBand [G.face (G.edge x0), G.node x0] x ∧
        G.FaceBand [G.face (G.edge x0), G.node x0] (extensionAFace G x0 x))
    rw [extensionAFace_of_not_faceReachable (G := G) x0 h]
    by_cases hx0 : x = G.edge x0
    · subst x
      simp only [↓reduceIte]
      exact Or.inr ⟨extensionA_faceBand_pair_of_edge_x0 (G := G) (x0 := x0),
        extensionA_faceBand_pair_of_node_x0 (G := G) (x0 := x0)⟩
    · simp only [hx0, ↓reduceIte]
      by_cases hxnode : G.face x = G.node x0
      · simp only [hxnode, ↓reduceIte]
        exact Or.inr
          ⟨extensionA_faceBand_pair_of_face_node (G := G) (x0 := x0) hxnode,
            extensionA_faceBand_pair_of_face_edge_x0 (G := G) (x0 := x0)⟩
      · simp only [hxnode, ↓reduceIte]
        exact Or.inl (PermReachable.forward G.face x)

theorem extensionA_faceBand_pair_of_faceReachable_left
    {x y : G.Dart}
    (hy : G.FaceBand [G.face (G.edge x0), G.node x0] y)
    (hxy : PermReachable G.face x y) :
    G.FaceBand [G.face (G.edge x0), G.node x0] x :=
  FaceBand.of_faceReachable (G := G) hy (PermReachable.symm G.face hxy)

theorem extensionA_faceBand_pair_of_faceReachable_right
    {x y : G.Dart}
    (hx : G.FaceBand [G.face (G.edge x0), G.node x0] x)
    (hxy : PermReachable G.face x y) :
    G.FaceBand [G.face (G.edge x0), G.node x0] y :=
  FaceBand.of_faceReachable (G := G) hx hxy

private def extensionAFaceState (x y : G.Dart) : Prop :=
  PermReachable G.face x y ∨
    (G.FaceBand [G.face (G.edge x0), G.node x0] x ∧
      G.FaceBand [G.face (G.edge x0), G.node x0] y)

private theorem extensionAFaceState_trans
    {x y z : G.Dart}
    (hxy : extensionAFaceState G x0 x y)
    (hyz : extensionAFaceState G x0 y z) :
    extensionAFaceState G x0 x z := by
  unfold extensionAFaceState at hxy hyz ⊢
  rcases hxy with hxy | ⟨hx, hy⟩
  · rcases hyz with hyz | ⟨hy, hz⟩
    · exact Or.inl (PermReachable.trans G.face hxy hyz)
    · exact Or.inr ⟨
        extensionA_faceBand_pair_of_faceReachable_left
          (G := G) (x0 := x0) hy hxy,
        hz⟩
  · rcases hyz with hyz | ⟨_, hz⟩
    · exact Or.inr ⟨hx,
        extensionA_faceBand_pair_of_faceReachable_right
          (G := G) (x0 := x0) hy hyz⟩
    · exact Or.inr ⟨hx, hz⟩

theorem extensionA_faceReachable_implies_old_or_faceBand_pair
    {x y : G.Dart}
    (hxy : PermReachable (extensionA G x0).face x y) :
    PermReachable G.face x y ∨
      (G.FaceBand [G.face (G.edge x0), G.node x0] x ∧
        G.FaceBand [G.face (G.edge x0), G.node x0] y) := by
  change extensionAFaceState G x0 x y
  induction hxy with
  | refl => exact Or.inl (PermReachable.refl G.face x)
  | @tail b c hxb hbc ih =>
      apply extensionAFaceState_trans (G := G) (x0 := x0) ih
      cases hbc with
      | forward =>
          exact extensionA_face_step_old_or_faceBand_pair (G := G) x0 b
      | backward =>
          have hstep := extensionA_face_step_old_or_faceBand_pair
            (G := G) x0 ((extensionA G x0).face.symm b)
          unfold extensionAFaceState
          rcases hstep with stepOld | stepBand
          · exact Or.inl (by
              simpa using PermReachable.symm G.face stepOld)
          · exact Or.inr (by
              simpa using And.intro stepBand.2 stepBand.1)

theorem extensionA_faceReachable_iff_old_or_faceBand_pair
    {x y : G.Dart} :
    PermReachable (extensionA G x0).face x y ↔
      PermReachable G.face x y ∨
        (G.FaceBand [G.face (G.edge x0), G.node x0] x ∧
          G.FaceBand [G.face (G.edge x0), G.node x0] y) := by
  constructor
  · exact extensionA_faceReachable_implies_old_or_faceBand_pair (G := G) x0
  · rintro (hxy | ⟨hx, hy⟩)
    · exact extensionA_faceReachable_of_faceReachable (G := G) x0 hxy
    · exact extensionA_faceReachable_of_faceBand_pair (G := G) x0 hx hy

/-- The identity embedding into `ecpA`, matching Coq's `icpA`. -/
noncomputable def extensionAOld (x : G.Dart) : (extensionA G x0).Dart :=
  x

@[simp]
theorem extensionAOld_apply (x : G.Dart) :
    extensionAOld G x0 x = x :=
  rfl

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
