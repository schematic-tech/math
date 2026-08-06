import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.Counting

/-!
Explicit edge and face actions for one and two `WalkupE` deletions.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

theorem walkupSkipEdgeAux_eq_of_plain
    (hG : G.Plain) (z x : G.Dart) :
    G.walkupSkipEdgeAux z x =
      if x = G.node z then G.edge z
      else if x = G.edge z then G.edge (G.node z)
      else G.edge x := by
  have hez : G.edge z ≠ z := Plain.edge_ne (G := G) hG z
  unfold walkupSkipEdgeAux
  simp only [hez, ↓reduceIte]
  by_cases hxnode : x = G.node z
  · have hfe : G.face (G.edge x) = z := by
      subst x
      simp
    simp [hxnode]
  · have hfe : G.face (G.edge x) ≠ z := by
      intro hbad
      apply hxnode
      calc
        x = G.node (G.face (G.edge x)) := (G.node_face_edge x).symm
        _ = G.node z := by rw [hbad]
    simp only [hfe, ↓reduceIte, hxnode]
    by_cases hxedge : x = G.edge z
    · subst x
      have hex : G.edge (G.edge z) = z :=
        Plain.edge_edge (G := G) hG z
      simp [hex]
    · have hex : G.edge x ≠ z := by
        intro hbad
        apply hxedge
        calc
          x = G.edge (G.edge x) :=
            (Plain.edge_edge (G := G) hG x).symm
          _ = G.edge z := by rw [hbad]
      simp [hxedge, hex]

theorem walkupE_edge_apply_coe_of_plain
    (hG : G.Plain) {z : G.Dart} (x : G.DeletedDart z) :
    ((G.walkupE z).edge x).1 =
      if x.1 = G.node z then G.edge z
      else if x.1 = G.edge z then G.edge (G.node z)
      else G.edge x.1 := by
  rw [G.walkupE_edge_apply_coe,
    G.walkupSkipEdgeAux_eq_of_plain hG z x.1]

theorem walkupE_edge_apply_coe_of_plain_of_ne
    (hG : G.Plain) {z : G.Dart} (x : G.DeletedDart z)
    (hxnode : x.1 ≠ G.node z) (hxedge : x.1 ≠ G.edge z) :
    ((G.walkupE z).edge x).1 = G.edge x.1 := by
  rw [G.walkupE_edge_apply_coe_of_plain hG x]
  simp [hxnode, hxedge]

theorem walkupE_edge_apply_coe_of_plain_of_eq_node
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z) :
    ((G.walkupE z).edge
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).1 = G.edge z := by
  rw [G.walkupE_edge_apply_coe_of_plain hG]
  simp

theorem walkupE_edge_apply_coe_of_plain_of_eq_edge
    (hG : G.Plain) {z : G.Dart} (x : G.DeletedDart z)
    (hxnode : x.1 ≠ G.node z) (hxedge : x.1 = G.edge z) :
    ((G.walkupE z).edge x).1 = G.edge (G.node z) := by
  have hEdgeNode : G.edge z ≠ G.node z := by
    intro hbad
    exact hxnode (by rw [hxedge, hbad])
  rw [G.walkupE_edge_apply_coe_of_plain hG x]
  simp [hxedge, hEdgeNode]

theorem walkupE_edge_edge_of_plain_of_edge_eq_node
    (hG : G.Plain) {z : G.Dart}
    (hedgeNode : G.edge z = G.node z)
    (x : (G.walkupE z).Dart) :
    (G.walkupE z).edge ((G.walkupE z).edge x) = x := by
  apply Subtype.ext
  by_cases hxnode : x.1 = G.node z
  · have h₁ : ((G.walkupE z).edge x).1 = G.node z := by
      rw [G.walkupE_edge_apply_coe_of_plain hG x]
      simp [hxnode, hedgeNode]
    have h₂ :
        ((G.walkupE z).edge ((G.walkupE z).edge x)).1 =
          G.node z := by
      rw [G.walkupE_edge_apply_coe_of_plain hG]
      simp [h₁, hedgeNode]
    simpa [hxnode] using h₂
  · have hxedge : x.1 ≠ G.edge z := by
      simpa [hedgeNode] using hxnode
    have h₁ : ((G.walkupE z).edge x).1 = G.edge x.1 := by
      exact G.walkupE_edge_apply_coe_of_plain_of_ne hG x hxnode hxedge
    have hstep_node : G.edge x.1 ≠ G.node z := by
      intro hbad
      have hsame : G.edge x.1 = G.edge z := by rw [hbad, hedgeNode]
      exact x.2 (G.edge.injective hsame)
    have hstep_edge : G.edge x.1 ≠ G.edge z := by
      intro hbad
      exact x.2 (G.edge.injective hbad)
    have h₂ :
        ((G.walkupE z).edge ((G.walkupE z).edge x)).1 =
          G.edge (G.edge x.1) := by
      rw [G.walkupE_edge_apply_coe_of_plain hG]
      simp [h₁, hstep_node, hstep_edge]
    simpa [Plain.edge_edge (G := G) hG x.1] using h₂

theorem walkupE_walkupE_edge_apply_coe_of_plain_of_ne
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hxedgez : x ≠ G.edge z)
    (hexz : G.edge x ≠ z) (hexnode : G.edge x ≠ G.node z)
    (hedgeNode : G.edge z ≠ G.node z)
    (hfaceEdgeNode : G.face (G.edge x) ≠ G.node z) :
    (((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (⟨⟨x, hxz⟩, by
          intro hx
          exact hxnode (congrArg Subtype.val hx)⟩ :
            ((G.walkupE z).walkupE
              (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart)).1.1 =
      G.edge x := by
  let u : (G.walkupE z).Dart := ⟨G.node z, hz_ne⟩
  let wx : ((G.walkupE z).walkupE u).Dart :=
    ⟨⟨x, hxz⟩, by
      intro hx
      exact hxnode (congrArg Subtype.val hx)⟩
  have hedge_u_val : ((G.walkupE z).edge u).1 = G.edge z := by
    exact G.walkupE_edge_apply_coe_of_plain_of_eq_node hG hz_ne
  have hedge_u_ne : (G.walkupE z).edge u ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hedge_u_val] at hval
    exact hedgeNode hval
  have hedge_wx_val : ((G.walkupE z).edge wx.1).1 = G.edge x := by
    exact G.walkupE_edge_apply_coe_of_plain_of_ne hG wx.1 hxnode hxedgez
  have hedge_wx_eq :
      (G.walkupE z).edge wx.1 =
        (⟨G.edge x, hexz⟩ : (G.walkupE z).Dart) := by
    apply Subtype.ext
    exact hedge_wx_val
  have hedge_wx_ne_u : (G.walkupE z).edge wx.1 ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hedge_wx_val] at hval
    exact hexnode hval
  have hface_ne_z : G.face (G.edge x) ≠ z := by
    intro hbad
    apply hxnode
    calc
      x = G.node (G.face (G.edge x)) := (G.node_face_edge x).symm
      _ = G.node z := by rw [hbad]
  have hface_edge_val :
      ((G.walkupE z).face
        (⟨G.edge x, hexz⟩ : (G.walkupE z).Dart)).1 =
          G.face (G.edge x) := by
    exact G.walkupE_face_apply_coe_of_ne
      (⟨G.edge x, hexz⟩ : (G.walkupE z).Dart) hface_ne_z
  have hface_outer_ne :
      (G.walkupE z).face ((G.walkupE z).edge wx.1) ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hedge_wx_eq] at hval
    rw [hface_edge_val] at hval
    exact hfaceEdgeNode hval
  change (((G.walkupE z).walkupE u).edge wx).1.1 = G.edge x
  rw [G.walkupE_walkupE_edge_apply_coe]
  unfold walkupSkipEdgeAux
  rw [if_neg hedge_u_ne]
  rw [if_neg hface_outer_ne]
  rw [if_neg hedge_wx_ne_u]
  exact hedge_wx_val

theorem walkupE_walkupE_edge_edge_of_plain_of_edge_eq_node
    (hG : G.Plain) {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hedgeNode : G.edge z = G.node z)
    (w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge w) =
      w := by
  let G' := G.walkupE z
  let u : G'.Dart := ⟨G.node z, hz_ne⟩
  have hedge_u : G'.edge u = u := by
    apply Subtype.ext
    rw [G.walkupE_edge_apply_coe_of_plain_of_eq_node hG hz_ne,
      hedgeNode]
  have hedge₂ : ∀ x : G'.Dart, G'.edge (G'.edge x) = x :=
    G.walkupE_edge_edge_of_plain_of_edge_eq_node hG hedgeNode
  change (G'.walkupE u).edge ((G'.walkupE u).edge w) = w
  rw [G'.walkupE_edge_eq_skip_edge_of_edge_eq hedge_u]
  exact PermSkip.skip_involutive_of_fixed G'.edge hedge_u hedge₂ w

theorem walkupE_walkupE_face_apply_coe_of_ne
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    {x : G.Dart}
    (hxz : x ≠ z) (hxnode : x ≠ G.node z)
    (hfacez : G.face x ≠ z) (hfacenode : G.face x ≠ G.node z) :
    (((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).face
        (⟨⟨x, hxz⟩, by
          intro hx
          exact hxnode (congrArg Subtype.val hx)⟩ :
            ((G.walkupE z).walkupE
              (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart)).1.1 =
      G.face x := by
  let u : (G.walkupE z).Dart := ⟨G.node z, hz_ne⟩
  let wx : ((G.walkupE z).walkupE u).Dart :=
    ⟨⟨x, hxz⟩, by
      intro hx
      exact hxnode (congrArg Subtype.val hx)⟩
  have hinner_val : ((G.walkupE z).face wx.1).1 = G.face x := by
    exact G.walkupE_face_apply_coe_of_ne wx.1 hfacez
  have houter_ne : (G.walkupE z).face wx.1 ≠ u := by
    intro hbad
    have hval := congrArg Subtype.val hbad
    rw [hinner_val] at hval
    exact hfacenode hval
  change (((G.walkupE z).walkupE u).face wx).1.1 = G.face x
  calc
    (((G.walkupE z).walkupE u).face wx).1.1 =
        ((G.walkupE z).face wx.1).1 := by
          have houter :=
            (G.walkupE z).walkupE_face_apply_coe_of_ne wx houter_ne
          exact congrArg Subtype.val houter
    _ = G.face x := hinner_val

theorem walkupE_walkupE_face_edge_apply_coe_of_node_node_eq
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z)
    (w : ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Dart) :
    (((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).face
        (((G.walkupE z).walkupE
          (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).edge w)).1.1 =
      G.face (G.edge w.1.1) := by
  let H :=
    (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  apply G.node.injective
  have hnode :=
    G.walkupE_walkupE_node_apply_coe_of_node_node_eq
      hz_ne hzz (H.face (H.edge w))
  calc
    G.node ((H.face (H.edge w)).1.1) =
        (H.node (H.face (H.edge w))).1.1 := hnode.symm
    _ = w.1.1 := by
      rw [H.node_face_edge]
    _ = G.node (G.face (G.edge w.1.1)) :=
      (G.node_face_edge w.1.1).symm

theorem walkupE_walkupE_bridgeless_of_node_node_eq
    (hG : G.Bridgeless)
    {z : G.Dart} (hz_ne : G.node z ≠ z)
    (hzz : G.node (G.node z) = z) :
    ((G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)).Bridgeless := by
  let H :=
    (G.walkupE z).walkupE
      (⟨G.node z, hz_ne⟩ : (G.walkupE z).Dart)
  intro w hw
  have hstep : PermReachable H.face (H.edge w) (H.face (H.edge w)) :=
    PermReachable.forward H.face (H.edge w)
  have hreachH : PermReachable H.face w (H.face (H.edge w)) :=
    PermReachable.trans H.face hw hstep
  have hreachG :
      PermReachable G.face w.1.1 (H.face (H.edge w)).1.1 :=
    G.walkupE_walkupE_facePermReachable_iff.mp hreachH
  have hproj :
      (H.face (H.edge w)).1.1 = G.face (G.edge w.1.1) :=
    G.walkupE_walkupE_face_edge_apply_coe_of_node_node_eq
      hz_ne hzz w
  have hreachFaceEdge :
      PermReachable G.face w.1.1 (G.face (G.edge w.1.1)) := by
    simpa [hproj] using hreachG
  have hreachEdge :
      PermReachable G.face w.1.1 (G.edge w.1.1) :=
    PermReachable.trans G.face hreachFaceEdge
      (by
        simpa using
          PermReachable.backward G.face (G.face (G.edge w.1.1)))
  exact hG w.1.1 hreachEdge

end Hypermap
end FourColor
end Schematic.Math.GraphTheory

