import Schematic.Math.GraphTheory.Embedding.EulerCharacteristic
import Schematic.Math.GraphTheory.Embedding.PermutationSplice

/-!
One-point sums of finite hypermaps.

The dart and edge sets are disjoint sums.  A selected node cycle from each
summand is joined by swapping their successors.  The induced face permutation
is the corresponding splice of one face cycle from each summand, so connected
Euler-planar hypermaps glue to a connected Euler-planar hypermap.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

/-- Disjoint sum of two hypermaps. -/
def disjointSum (G H : Hypermap.{u}) : Hypermap.{u} where
  Dart := Sum G.Dart H.Dart
  edge := permSum G.edge H.edge
  node := permSum G.node H.node
  face := permSum G.face H.face
  node_face_edge := by
    intro x
    cases x with
    | inl x => simp [permSum]
    | inr y => simp [permSum]

@[simp]
theorem disjointSum_edge_inl
    (G H : Hypermap.{u}) (x : G.Dart) :
    (disjointSum G H).edge (Sum.inl x) = Sum.inl (G.edge x) :=
  rfl

@[simp]
theorem disjointSum_edge_inr
    (G H : Hypermap.{u}) (y : H.Dart) :
    (disjointSum G H).edge (Sum.inr y) = Sum.inr (H.edge y) :=
  rfl

@[simp]
theorem disjointSum_node_inl
    (G H : Hypermap.{u}) (x : G.Dart) :
    (disjointSum G H).node (Sum.inl x) = Sum.inl (G.node x) :=
  rfl

@[simp]
theorem disjointSum_node_inr
    (G H : Hypermap.{u}) (y : H.Dart) :
    (disjointSum G H).node (Sum.inr y) = Sum.inr (H.node y) :=
  rfl

@[simp]
theorem disjointSum_face_inl
    (G H : Hypermap.{u}) (x : G.Dart) :
    (disjointSum G H).face (Sum.inl x) = Sum.inl (G.face x) :=
  rfl

@[simp]
theorem disjointSum_face_inr
    (G H : Hypermap.{u}) (y : H.Dart) :
    (disjointSum G H).face (Sum.inr y) = Sum.inr (H.face y) :=
  rfl

theorem face_apply_eq_node_symm_edge_symm
    (G : Hypermap.{u}) (x : G.Dart) :
    G.face x = G.node.symm (G.edge.symm x) := by
  apply G.node.injective
  simpa using G.node_face_edge (G.edge.symm x)

/-- Join the node cycles containing `p` and `q` in the disjoint hypermap sum. -/
def onePointSum
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    Hypermap.{u} where
  Dart := Sum G.Dart H.Dart
  edge := (disjointSum G H).edge
  node :=
    permSplice (disjointSum G H).node (Sum.inl p) (Sum.inr q)
  face :=
    (disjointSum G H).edge.symm.trans
      (permSplice (disjointSum G H).node
        (Sum.inl p) (Sum.inr q)).symm
  node_face_edge := by
    intro x
    let E := (disjointSum G H).edge
    let N := permSplice (disjointSum G H).node (Sum.inl p) (Sum.inr q)
    change N (N.symm (E.symm (E x))) = x
    rw [E.symm_apply_apply, N.apply_symm_apply]

@[simp]
theorem onePointSum_edge
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (x : (onePointSum G H p q).Dart) :
    (onePointSum G H p q).edge x = (disjointSum G H).edge x :=
  rfl

@[simp]
theorem onePointSum_node
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (x : (onePointSum G H p q).Dart) :
    (onePointSum G H p q).node x =
      permSplice (disjointSum G H).node (Sum.inl p) (Sum.inr q) x :=
  rfl

theorem disjointSum_node_pivots_separate
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    ¬ PermReachable (disjointSum G H).node (Sum.inl p) (Sum.inr q) := by
  intro h
  have hcode :=
    permSumOrbitCode_of_reachable G.node H.node h
  simp [permSumOrbitCode] at hcode

theorem disjointSum_face_pivots_separate
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    ¬ PermReachable (disjointSum G H).face (Sum.inl p) (Sum.inr q) := by
  intro h
  have hcode :=
    permSumOrbitCode_of_reachable G.face H.face h
  simp [permSumOrbitCode] at hcode

/-- The node splice induces a face splice at the old face predecessors of the
same two darts. -/
theorem onePointSum_face_eq_splice
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    (onePointSum G H p q).face =
      permSplice (disjointSum G H).face
        ((disjointSum G H).face.symm (Sum.inl p))
        ((disjointSum G H).face.symm (Sum.inr q)) := by
  let B := disjointSum G H
  let p' : B.Dart := Sum.inl p
  let q' : B.Dart := Sum.inr q
  apply Equiv.ext
  intro x
  change
    B.node.symm
        (Equiv.swap (B.node p') (B.node q') (B.edge.symm x)) =
      Equiv.swap
        (B.face (B.face.symm p'))
        (B.face (B.face.symm q'))
        (B.face x)
  have hfp : B.face (B.face.symm p') = p' :=
    B.face.apply_symm_apply p'
  have hfq : B.face (B.face.symm q') = q' :=
    B.face.apply_symm_apply q'
  rw [hfp, hfq]
  rw [B.face_apply_eq_node_symm_edge_symm]
  simpa using
    B.node.symm.injective.map_swap
      (B.node p') (B.node q') (B.edge.symm x)

theorem onePointSum_nodeOrbitCount
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    (onePointSum G H p q).nodeOrbitCount + 1 =
      G.nodeOrbitCount + H.nodeOrbitCount := by
  change
    Nat.card
        (PermOrbit
          (permSplice (disjointSum G H).node
            (Sum.inl p) (Sum.inr q))) + 1 =
      Nat.card (PermOrbit G.node) + Nat.card (PermOrbit H.node)
  rw [permSplice_orbitCount _ _ _
    (disjointSum_node_pivots_separate G H p q)]
  exact permSum_orbitCount G.node H.node

theorem onePointSum_faceOrbitCount
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    (onePointSum G H p q).faceOrbitCount + 1 =
      G.faceOrbitCount + H.faceOrbitCount := by
  change
    Nat.card (PermOrbit (onePointSum G H p q).face) + 1 =
      Nat.card (PermOrbit G.face) + Nat.card (PermOrbit H.face)
  rw [onePointSum_face_eq_splice]
  let B := disjointSum G H
  have hsep :
      ¬ PermReachable B.face
        (B.face.symm (Sum.inl p)) (B.face.symm (Sum.inr q)) := by
    simpa [B] using
      disjointSum_face_pivots_separate G H
        (G.face.symm p) (H.face.symm q)
  calc
    Nat.card
          (PermOrbit
            (permSplice B.face
              (B.face.symm (Sum.inl p))
              (B.face.symm (Sum.inr q)))) + 1 =
        Nat.card (PermOrbit B.face) :=
      permSplice_orbitCount B.face
        (B.face.symm (Sum.inl p))
        (B.face.symm (Sum.inr q)) hsep
    _ = Nat.card (PermOrbit G.face) + Nat.card (PermOrbit H.face) :=
      permSum_orbitCount G.face H.face

theorem onePointSum_edgeOrbitCount
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    (onePointSum G H p q).edgeOrbitCount =
      G.edgeOrbitCount + H.edgeOrbitCount := by
  exact permSum_orbitCount G.edge H.edge

theorem onePointSum_dart_card
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart) :
    Fintype.card (onePointSum G H p q).Dart =
      Fintype.card G.Dart + Fintype.card H.Dart := by
  exact Fintype.card_sum

theorem disjointSum_plain
    (G H : Hypermap.{u})
    (hG : G.Plain) (hH : H.Plain) :
    (disjointSum G H).Plain := by
  intro x
  cases x with
  | inl x =>
      exact ⟨congrArg Sum.inl (hG x).1,
        fun h => (hG x).2 (Sum.inl.inj h)⟩
  | inr x =>
      exact ⟨congrArg Sum.inr (hH x).1,
        fun h => (hH x).2 (Sum.inr.inj h)⟩

theorem onePointSum_plain
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (hG : G.Plain) (hH : H.Plain) :
    (onePointSum G H p q).Plain :=
  disjointSum_plain G H hG hH

private theorem onePointSum_reachable_inl_of_reachable
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (onePointSum G H p q).Reachable (Sum.inl x) (Sum.inl y) := by
  let B := disjointSum G H
  let K := onePointSum G H p q
  have hsep : ¬ PermReachable B.node (Sum.inl p) (Sum.inr q) :=
    disjointSum_node_pivots_separate G H p q
  have hfaceSep :
      ¬ PermReachable B.face
        (B.face.symm (Sum.inl p)) (B.face.symm (Sum.inr q)) := by
    simpa using
      disjointSum_face_pivots_separate G H
        (G.face.symm p) (H.face.symm q)
  induction hxy with
  | refl =>
      exact K.reachable_refl (Sum.inl x)
  | @tail b c _ hbc ih =>
      exact K.reachable_trans ih (by
        rcases hbc with hbc | hbc | hbc
        · subst c
          exact K.reachable_edge (Sum.inl b)
        · subst c
          apply K.nodePermReachable_reachable
          change
            PermReachable
              (permSplice B.node (Sum.inl p) (Sum.inr q))
              (Sum.inl b) (Sum.inl (G.node b))
          exact permSplice_reachable_of_old_reachable
            B.node (Sum.inl p) (Sum.inr q) hsep
            (permSum_reachable_inl G.node H.node
              (PermReachable.forward G.node b))
        · subst c
          apply K.facePermReachable_reachable
          rw [onePointSum_face_eq_splice]
          exact permSplice_reachable_of_old_reachable
            B.face (B.face.symm (Sum.inl p))
              (B.face.symm (Sum.inr q)) hfaceSep
            (permSum_reachable_inl G.face H.face
              (PermReachable.forward G.face b)))

private theorem onePointSum_reachable_inr_of_reachable
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    {x y : H.Dart}
    (hxy : H.Reachable x y) :
    (onePointSum G H p q).Reachable (Sum.inr x) (Sum.inr y) := by
  let B := disjointSum G H
  let K := onePointSum G H p q
  have hsep : ¬ PermReachable B.node (Sum.inl p) (Sum.inr q) :=
    disjointSum_node_pivots_separate G H p q
  have hfaceSep :
      ¬ PermReachable B.face
        (B.face.symm (Sum.inl p)) (B.face.symm (Sum.inr q)) := by
    simpa using
      disjointSum_face_pivots_separate G H
        (G.face.symm p) (H.face.symm q)
  induction hxy with
  | refl =>
      exact K.reachable_refl (Sum.inr x)
  | @tail b c _ hbc ih =>
      exact K.reachable_trans ih (by
        rcases hbc with hbc | hbc | hbc
        · subst c
          exact K.reachable_edge (Sum.inr b)
        · subst c
          apply K.nodePermReachable_reachable
          change
            PermReachable
              (permSplice B.node (Sum.inl p) (Sum.inr q))
              (Sum.inr b) (Sum.inr (H.node b))
          exact permSplice_reachable_of_old_reachable
            B.node (Sum.inl p) (Sum.inr q) hsep
            (permSum_reachable_inr G.node H.node
              (PermReachable.forward H.node b))
        · subst c
          apply K.facePermReachable_reachable
          rw [onePointSum_face_eq_splice]
          exact permSplice_reachable_of_old_reachable
            B.face (B.face.symm (Sum.inl p))
              (B.face.symm (Sum.inr q)) hfaceSep
            (permSum_reachable_inr G.face H.face
              (PermReachable.forward H.face b)))

theorem onePointSum_connected
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (hG : G.Connected) (hH : H.Connected) :
    (onePointSum G H p q).Connected := by
  let K := onePointSum G H p q
  have hpq :
      K.Reachable (Sum.inl p) (Sum.inr q) := by
    apply K.nodePermReachable_reachable
    exact permSplice_left_reachable_right
      (disjointSum G H).node (Sum.inl p) (Sum.inr q)
      (disjointSum_node_pivots_separate G H p q)
  refine ⟨⟨Sum.inl p⟩, ?_⟩
  intro x y
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact onePointSum_reachable_inl_of_reachable
            G H p q (hG.reachable G x y)
      | inr y =>
          exact K.reachable_trans
            (onePointSum_reachable_inl_of_reachable
              G H p q (hG.reachable G x p))
            (K.reachable_trans hpq
              (onePointSum_reachable_inr_of_reachable
                G H p q (hH.reachable H q y)))
  | inr x =>
      cases y with
      | inl y =>
          exact K.reachable_symm
            (K.reachable_trans
              (onePointSum_reachable_inl_of_reachable
                G H p q (hG.reachable G y p))
              (K.reachable_trans hpq
                (onePointSum_reachable_inr_of_reachable
                  G H p q (hH.reachable H q x))))
      | inr y =>
          exact onePointSum_reachable_inr_of_reachable
            G H p q (hH.reachable H x y)

theorem onePointSum_componentCount
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (hG : G.Connected) (hH : H.Connected) :
    (onePointSum G H p q).componentCount = 1 :=
  (onePointSum_connected G H p q hG hH).componentCount_eq_one

theorem onePointSum_eulerPlanar
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (hGconn : G.Connected) (hHconn : H.Connected)
    (hG : G.EulerPlanar) (hH : H.EulerPlanar) :
    (onePointSum G H p q).EulerPlanar := by
  have hGeq : G.eulerLeft = G.eulerRight :=
    euler_eq_of_evenGenus_planar (evenGenus G) hG
  have hHeq : H.eulerLeft = H.eulerRight :=
    euler_eq_of_evenGenus_planar (evenGenus H) hH
  have hGcomp := hGconn.componentCount_eq_one
  have hHcomp := hHconn.componentCount_eq_one
  have hKcomp := onePointSum_componentCount G H p q hGconn hHconn
  have hnode := onePointSum_nodeOrbitCount G H p q
  have hface := onePointSum_faceOrbitCount G H p q
  have hedge := onePointSum_edgeOrbitCount G H p q
  have hdart := onePointSum_dart_card G H p q
  apply eulerPlanar_of_eulerLeft_le_eulerRight
  unfold eulerLeft eulerRight componentCount edgeOrbitCount nodeOrbitCount faceOrbitCount at hGeq hHeq ⊢
  unfold componentCount at hGcomp hHcomp hKcomp
  unfold nodeOrbitCount at hnode
  unfold faceOrbitCount at hface
  unfold edgeOrbitCount at hedge
  omega

theorem onePointSum_dual_eulerPlanar
    (G H : Hypermap.{u}) (p : G.Dart) (q : H.Dart)
    (hGconn : G.Connected) (hHconn : H.Connected)
    (hG : G.dual.EulerPlanar) (hH : H.dual.EulerPlanar) :
    (onePointSum G H p q).dual.EulerPlanar := by
  rw [dual_eulerPlanar_iff] at hG hH ⊢
  exact onePointSum_eulerPlanar G H p q hGconn hHconn hG hH

/-- Join two node cycles of one hypermap by swapping the successors of the
selected darts.  The face permutation is forced by the hypermap equation. -/
def nodeSplice (G : Hypermap.{u}) (p q : G.Dart) : Hypermap.{u} where
  Dart := G.Dart
  edge := G.edge
  node := permSplice G.node p q
  face := G.edge.symm.trans (permSplice G.node p q).symm
  node_face_edge := by
    intro x
    let N := permSplice G.node p q
    change N (N.symm (G.edge.symm (G.edge x))) = x
    rw [G.edge.symm_apply_apply, N.apply_symm_apply]

@[simp]
theorem nodeSplice_edge
    (G : Hypermap.{u}) (p q x : G.Dart) :
    (nodeSplice G p q).edge x = G.edge x :=
  rfl

@[simp]
theorem nodeSplice_node
    (G : Hypermap.{u}) (p q x : G.Dart) :
    (nodeSplice G p q).node x = permSplice G.node p q x :=
  rfl

/-- A node splice is dually a face splice at the old face predecessors of the
two selected darts. -/
theorem nodeSplice_face_eq_splice
    (G : Hypermap.{u}) (p q : G.Dart) :
    (nodeSplice G p q).face =
      permSplice G.face (G.face.symm p) (G.face.symm q) := by
  apply Equiv.ext
  intro x
  change
    G.node.symm
        (Equiv.swap (G.node p) (G.node q) (G.edge.symm x)) =
      Equiv.swap
        (G.face (G.face.symm p))
        (G.face (G.face.symm q))
        (G.face x)
  rw [G.face.apply_symm_apply, G.face.apply_symm_apply]
  rw [G.face_apply_eq_node_symm_edge_symm]
  simpa using
    G.node.symm.injective.map_swap
      (G.node p) (G.node q) (G.edge.symm x)

theorem nodeSplice_nodeOrbitCount
    (G : Hypermap.{u}) (p q : G.Dart)
    (hsep : ¬ PermReachable G.node p q) :
    (nodeSplice G p q).nodeOrbitCount + 1 = G.nodeOrbitCount := by
  exact permSplice_orbitCount G.node p q hsep

theorem nodeSplice_faceOrbitCount
    (G : Hypermap.{u}) (p q : G.Dart)
    (hsep : ¬ PermReachable G.node p q)
    (hface :
      PermReachable G.face (G.face.symm p) (G.face.symm q)) :
    G.faceOrbitCount + 1 = (nodeSplice G p q).faceOrbitCount := by
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hsep (PermReachable.refl G.node p)
  have hpred : G.face.symm p ≠ G.face.symm q := by
    exact fun h => hpq (G.face.symm.injective h)
  unfold faceOrbitCount
  change
    Nat.card (PermOrbit G.face) + 1 =
      Nat.card (PermOrbit (nodeSplice G p q).face)
  rw [nodeSplice_face_eq_splice]
  exact permSplice_orbitCount_of_reachable G.face
    (G.face.symm p) (G.face.symm q) hface hpred

theorem nodeSplice_edgeOrbitCount
    (G : Hypermap.{u}) (p q : G.Dart) :
    (nodeSplice G p q).edgeOrbitCount = G.edgeOrbitCount :=
  rfl

theorem nodeSplice_dart_card
    (G : Hypermap.{u}) (p q : G.Dart) :
    Fintype.card (nodeSplice G p q).Dart = Fintype.card G.Dart :=
  rfl

theorem nodeSplice_plain
    (G : Hypermap.{u}) (p q : G.Dart)
    (hG : G.Plain) :
    (nodeSplice G p q).Plain :=
  hG

private theorem nodeSplice_reachable_of_reachable
    (G : Hypermap.{u}) (p q : G.Dart)
    (hsep : ¬ PermReachable G.node p q)
    {x y : G.Dart}
    (hxy : G.Reachable x y) :
    (nodeSplice G p q).Reachable x y := by
  let K := nodeSplice G p q
  induction hxy with
  | refl => exact K.reachable_refl x
  | @tail b c _ hbc ih =>
      exact K.reachable_trans ih (by
        rcases hbc with hbc | hbc | hbc
        · subst c
          exact K.reachable_edge b
        · subst c
          apply K.nodePermReachable_reachable
          change PermReachable (permSplice G.node p q) b (G.node b)
          exact permSplice_reachable_of_old_reachable G.node p q hsep
            (PermReachable.forward G.node b)
        · subst c
          have hedge : K.Reachable b (G.edge.symm b) := by
            have h := K.reachable_edge_symm (G.edge.symm b)
            change K.Reachable (G.edge (G.edge.symm b)) (G.edge.symm b) at h
            rw [G.edge.apply_symm_apply] at h
            exact h
          have hnodePerm :
              PermReachable K.node (G.edge.symm b)
                (G.node.symm (G.edge.symm b)) := by
            change
              PermReachable (permSplice G.node p q) (G.edge.symm b)
                (G.node.symm (G.edge.symm b))
            exact permSplice_reachable_of_old_reachable G.node p q hsep
              (PermReachable.backward G.node (G.edge.symm b))
          have hnode := K.nodePermReachable_reachable hnodePerm
          simpa [G.face_apply_eq_node_symm_edge_symm] using
            K.reachable_trans hedge hnode)

theorem nodeSplice_connected
    (G : Hypermap.{u}) (p q : G.Dart)
    (hG : G.Connected)
    (hsep : ¬ PermReachable G.node p q) :
    (nodeSplice G p q).Connected := by
  exact ⟨hG.nonempty, fun x y =>
    nodeSplice_reachable_of_reachable G p q hsep (hG.reachable G x y)⟩

/-- Identifying two distinct node cycles whose splice positions lie on one
face preserves connected Euler planarity: one node orbit is lost and one face
orbit is gained. -/
theorem nodeSplice_eulerPlanar
    (G : Hypermap.{u}) (p q : G.Dart)
    (hGconn : G.Connected)
    (hG : G.EulerPlanar)
    (hnode : ¬ PermReachable G.node p q)
    (hface :
      PermReachable G.face (G.face.symm p) (G.face.symm q)) :
    (nodeSplice G p q).EulerPlanar := by
  have hGeq : G.eulerLeft = G.eulerRight :=
    euler_eq_of_evenGenus_planar (evenGenus G) hG
  have hGcomp := hGconn.componentCount_eq_one
  have hKcomp := (nodeSplice_connected G p q hGconn hnode).componentCount_eq_one
  have hnodeCount := nodeSplice_nodeOrbitCount G p q hnode
  have hfaceCount := nodeSplice_faceOrbitCount G p q hnode hface
  have hedgeCount := nodeSplice_edgeOrbitCount G p q
  have hdart := nodeSplice_dart_card G p q
  apply eulerPlanar_of_eulerLeft_le_eulerRight
  unfold eulerLeft eulerRight componentCount edgeOrbitCount nodeOrbitCount faceOrbitCount at hGeq ⊢
  unfold componentCount at hGcomp hKcomp
  unfold nodeOrbitCount at hnodeCount
  unfold faceOrbitCount at hfaceCount
  unfold edgeOrbitCount at hedgeCount
  omega

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
