import Schematic.Math.GraphTheory.Embedding.Walkup.ComponentCounts

/-! Regular non-self edge behavior under Walkup deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

theorem edge_ne_self_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.edge z ≠ z := by
  intro he
  exact hz (Or.inl he.symm)

theorem node_ne_self_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.node z ≠ z := by
  intro hn
  exact hz (Or.inr (Or.inl hn.symm))

theorem face_ne_self_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.face z ≠ z := by
  intro hf
  exact hz (Or.inr (Or.inr hf.symm))

theorem face_edge_eq_iff_eq_node
    {z x : G.Dart} :
    G.face (G.edge x) = z ↔ x = G.node z := by
  constructor
  · intro hx
    calc
      x = G.node (G.face (G.edge x)) := (G.node_face_edge x).symm
      _ = G.node z := by rw [hx]
  · intro hx
    rw [hx]
    simp

theorem edge_eq_iff_eq_edge_symm
    {z x : G.Dart} :
    G.edge x = z ↔ x = G.edge.symm z := by
  constructor
  · intro hx
    exact G.edge.injective (by simpa using hx)
  · intro hx
    rw [hx]
    simp

theorem edge_symm_ne_self_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.edge.symm z ≠ z := by
  intro hsymm
  apply hz
  exact Or.inl (by simpa using congrArg G.edge hsymm)

theorem node_face_eq_edge_symm (x : G.Dart) :
    G.node (G.face x) = G.edge.symm x := by
  apply G.edge.injective
  simp

theorem edge_node_ne_self_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.edge (G.node z) ≠ z := by
  intro hbad
  apply G.face_ne_self_of_not_link_self hz
  calc
    G.face z = G.face (G.edge (G.node z)) := by rw [hbad]
    _ = z := by simp

theorem walkupSkipEdgeAux_node_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.walkupSkipEdgeAux z (G.node z) = G.edge z := by
  have he : G.edge z ≠ z := G.edge_ne_self_of_not_link_self hz
  simp [walkupSkipEdgeAux, he]

theorem walkupSkipEdgeAux_edge_symm_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.walkupSkipEdgeAux z (G.edge.symm z) = G.edge (G.node z) := by
  have he : G.edge z ≠ z := G.edge_ne_self_of_not_link_self hz
  have hf : G.face z ≠ z := G.face_ne_self_of_not_link_self hz
  simp [walkupSkipEdgeAux, he, hf]

theorem walkupSkipEdgeAux_of_not_link_self_of_regular
    {z x : G.Dart} (hz : ¬ G.Link z z)
    (hxnode : x ≠ G.node z) (hxpred : x ≠ G.edge.symm z) :
    G.walkupSkipEdgeAux z x = G.edge x := by
  have he : G.edge z ≠ z := G.edge_ne_self_of_not_link_self hz
  have hface : G.face (G.edge x) ≠ z := by
    intro hx
    exact hxnode ((G.face_edge_eq_iff_eq_node).mp hx)
  have hedge : G.edge x ≠ z := by
    intro hx
    exact hxpred ((G.edge_eq_iff_eq_edge_symm).mp hx)
  simp [walkupSkipEdgeAux, he, hface, hedge]

theorem walkupE_edge_apply_node_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    (G.walkupE z).edge
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart) := by
  apply Subtype.ext
  rw [G.walkupE_edge_apply_coe]
  exact G.walkupSkipEdgeAux_node_of_not_link_self hz

theorem walkupE_edge_apply_edge_symm_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    (G.walkupE z).edge
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart) := by
  apply Subtype.ext
  rw [G.walkupE_edge_apply_coe]
  exact G.walkupSkipEdgeAux_edge_symm_of_not_link_self hz

theorem walkupE_node_apply_face_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    (G.walkupE z).node
        (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart) := by
  apply Subtype.ext
  have hnode_ne : G.node (G.face z) ≠ z := by
    rw [G.node_face_eq_edge_symm]
    exact G.edge_symm_ne_self_of_not_link_self hz
  calc
    (((G.walkupE z).node
        (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)).1 : G.Dart) =
        G.node (G.face z) :=
      G.walkupE_node_apply_coe_of_ne
        (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
          G.DeletedDart z) hnode_ne
    _ = G.edge.symm z := G.node_face_eq_edge_symm z

theorem walkupE_edge_apply_of_not_link_self_of_regular
    {z : G.Dart} (hz : ¬ G.Link z z)
    (x : (G.walkupE z).Dart)
    (hxnode : x.1 ≠ G.node z) (hxpred : x.1 ≠ G.edge.symm z) :
    ((G.walkupE z).edge x).1 = G.edge x.1 := by
  rw [G.walkupE_edge_apply_coe]
  exact G.walkupSkipEdgeAux_of_not_link_self_of_regular hz hxnode hxpred

theorem walkupE_edge_eq_of_not_link_self_of_regular
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hy : y.1 = G.edge x.1)
    (hxnode : x.1 ≠ G.node z) (hxpred : x.1 ≠ G.edge.symm z) :
    (G.walkupE z).edge x = y := by
  apply Subtype.ext
  calc
    (((G.walkupE z).edge x).1 : G.Dart) = G.edge x.1 :=
      G.walkupE_edge_apply_of_not_link_self_of_regular hz x hxnode hxpred
    _ = y.1 := hy.symm

theorem walkupE_edgePermReachable_of_original_edge_regular
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hy : y.1 = G.edge x.1)
    (hxnode : x.1 ≠ G.node z) (hxpred : x.1 ≠ G.edge.symm z) :
    PermReachable (G.walkupE z).edge x y := by
  rw [← G.walkupE_edge_eq_of_not_link_self_of_regular
    hz hy hxnode hxpred]
  exact PermReachable.forward (G.walkupE z).edge x

theorem walkupE_edgePermReachable_node_to_edge_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    PermReachable (G.walkupE z).edge
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  rw [← G.walkupE_edge_apply_node_of_not_link_self hz]
  exact PermReachable.forward (G.walkupE z).edge
    (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
      (G.walkupE z).Dart)

theorem walkupE_edgePermReachable_edge_symm_to_edge_node_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    PermReachable (G.walkupE z).edge
        (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  rw [← G.walkupE_edge_apply_edge_symm_of_not_link_self hz]
  exact PermReachable.forward (G.walkupE z).edge
    (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
      (G.walkupE z).Dart)


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
