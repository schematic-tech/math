import Schematic.Math.GraphTheory.Embedding.Walkup.CrossEdgeOrbits

/-! Orbit projections and the node and face Walkup transforms. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

theorem walkupE_nodePermReachable_project
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : PermReachable (G.walkupE z).node x y) :
    PermReachable G.node x.1 y.1 := by
  simpa [walkupE_node, walkupSkipNode] using
    (PermSkip.skip_permReachable_project G.node hxy)

theorem walkupE_facePermReachable_project
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : PermReachable (G.walkupE z).face x y) :
    PermReachable G.face x.1 y.1 := by
  simpa [walkupE_face, walkupSkipFace] using
    (PermSkip.skip_permReachable_project G.face hxy)

theorem walkupE_nodePermReachable_iff
    {z : G.Dart} {x y : G.DeletedDart z} :
    PermReachable (G.walkupE z).node x y ↔
      PermReachable G.node x.1 y.1 := by
  simpa [walkupE_node, walkupSkipNode] using
    (PermSkip.skip_permReachable_iff G.node (z := z) (x := x) (y := y))

theorem walkupE_facePermReachable_iff
    {z : G.Dart} {x y : G.DeletedDart z} :
    PermReachable (G.walkupE z).face x y ↔
      PermReachable G.face x.1 y.1 := by
  simpa [walkupE_face, walkupSkipFace] using
    (PermSkip.skip_permReachable_iff G.face (z := z) (x := x) (y := y))

theorem walkupE_walkupE_nodePermReachable_iff
    {z : G.Dart} {u : (G.walkupE z).Dart}
    {x y : ((G.walkupE z).walkupE u).Dart} :
    PermReachable ((G.walkupE z).walkupE u).node x y ↔
      PermReachable G.node x.1.1 y.1.1 := by
  calc
    PermReachable ((G.walkupE z).walkupE u).node x y
        ↔ PermReachable (G.walkupE z).node x.1 y.1 :=
      (G.walkupE z).walkupE_nodePermReachable_iff
    _ ↔ PermReachable G.node x.1.1 y.1.1 :=
      G.walkupE_nodePermReachable_iff

theorem walkupE_walkupE_facePermReachable_iff
    {z : G.Dart} {u : (G.walkupE z).Dart}
    {x y : ((G.walkupE z).walkupE u).Dart} :
    PermReachable ((G.walkupE z).walkupE u).face x y ↔
      PermReachable G.face x.1.1 y.1.1 := by
  calc
    PermReachable ((G.walkupE z).walkupE u).face x y
        ↔ PermReachable (G.walkupE z).face x.1 y.1 :=
      (G.walkupE z).walkupE_facePermReachable_iff
    _ ↔ PermReachable G.face x.1.1 y.1.1 :=
      G.walkupE_facePermReachable_iff

/-- The pointwise node-projection identity used in Coq
`minimal_counter_example_is_cubic`.  After deleting `z` and then the dart
corresponding to `node z`, the composed inclusion commutes with `node` when
`z` lies in a two-node orbit. -/
theorem walkupE_walkupE_node_apply_coe_of_node_node_eq
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart) :
    (((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).node w).1.1 =
        G.node w.1.1 := by
  let u : (G.walkupE z).Dart := ⟨G.node z, hz_ne⟩
  have hw_ne_node_z : w.1.1 ≠ G.node z := by
    intro hbad
    exact w.2 (Subtype.ext hbad)
  have hnode_ne_z : G.node w.1.1 ≠ z := by
    intro hbad
    have hsame : G.node w.1.1 = G.node (G.node z) := by
      rw [hbad, hzz]
    exact hw_ne_node_z (G.node.injective hsame)
  have hnode_w_eq :
      ((G.walkupE z).node w.1 : G.DeletedDart z) =
        ⟨G.node w.1.1, hnode_ne_z⟩ := by
    apply Subtype.ext
    exact G.walkupE_node_apply_coe_of_ne w.1 hnode_ne_z
  have hnode_outer_ne :
      ((G.walkupE z).node w.1 : (G.walkupE z).Dart) ≠ u := by
    intro hbad
    have hval : G.node w.1.1 = G.node z := by
      have h := congrArg Subtype.val hbad
      rwa [hnode_w_eq] at h
    exact w.1.2 (G.node.injective hval)
  calc
    (((G.walkupE z).walkupE u).node w).1.1 =
        ((G.walkupE z).node w.1).1 := by
          have houter :=
            (G.walkupE z).walkupE_node_apply_coe_of_ne w hnode_outer_ne
          exact congrArg (fun t : (G.walkupE z).Dart => t.1) houter
    _ = G.node w.1.1 := by
      exact G.walkupE_node_apply_coe_of_ne w.1 hnode_ne_z

theorem walkupE_walkupE_node_conj_complEquiv_of_node_node_eq
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart) :
    G.walkupE_walkupE_complEquiv
        (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).node w) =
      G.nodeOnTwoNodeComplement hzz
        (G.walkupE_walkupE_complEquiv
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart) w) := by
  apply Subtype.ext
  exact G.walkupE_walkupE_node_apply_coe_of_node_node_eq hz_ne hzz w

theorem walkupE_walkupE_dart_card_add_two
    {z : G.Dart} (u : (G.walkupE z).Dart) :
    Fintype.card ((G.walkupE z).walkupE u).Dart + 2 =
      Fintype.card G.Dart := by
  have h₁ := (G.walkupE z).walkupE_dart_card_add_one u
  have h₂ := G.walkupE_dart_card_add_one z
  omega

/-- The part of the original edge permutation whose cycles may change under
`WalkupE`. -/
def WalkupSkipEdgeDomain (z x : G.Dart) : Prop :=
  G.EdgeDomain z x

theorem walkupSkipEdgeDomain_iff (z x : G.Dart) :
    G.WalkupSkipEdgeDomain z x ↔ G.EdgeDomain z x :=
  Iff.rfl

/-- Coq `WalkupN`, obtained from `WalkupE` by cyclic permutation. -/
def walkupN (z : G.Dart) : Hypermap.{u} :=
  (G.permNode.walkupE z).permFace

/-- Coq `WalkupF`, obtained from `WalkupE` by cyclic permutation. -/
def walkupF (z : G.Dart) : Hypermap.{u} :=
  (G.permFace.walkupE z).permNode

theorem walkupN_link_reachable
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : (G.walkupN z).Link x y) :
    G.Reachable x.1 y.1 := by
  change ((G.permNode.walkupE z).permFace).Link x y at hxy
  have hxyE : (G.permNode.walkupE z).Link x y :=
    ((G.permNode.walkupE z).permFace_link_iff).mp hxy
  exact G.permNode_reachable
    ((G.permNode).walkupE_link_reachable hxyE)

theorem walkupN_reachable_reachable
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : (G.walkupN z).Reachable x y) :
    G.Reachable x.1 y.1 :=
  hxy.lift' Subtype.val fun _ _ h => G.walkupN_link_reachable h

theorem walkupF_link_reachable
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : (G.walkupF z).Link x y) :
    G.Reachable x.1 y.1 := by
  change ((G.permFace.walkupE z).permNode).Link x y at hxy
  have hxyE : (G.permFace.walkupE z).Link x y :=
    ((G.permFace.walkupE z).permNode_link_iff).mp hxy
  exact G.permFace_reachable
    ((G.permFace).walkupE_link_reachable hxyE)

theorem walkupF_reachable_reachable
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : (G.walkupF z).Reachable x y) :
    G.Reachable x.1 y.1 :=
  hxy.lift' Subtype.val fun _ _ h => G.walkupF_link_reachable h

@[simp]
theorem walkupN_dart_card (z : G.Dart) :
    Fintype.card (G.walkupN z).Dart = Fintype.card G.Dart - 1 :=
  DeletedPoint.card z

@[simp]
theorem walkupF_dart_card (z : G.Dart) :
    Fintype.card (G.walkupF z).Dart = Fintype.card G.Dart - 1 :=
  DeletedPoint.card z

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
