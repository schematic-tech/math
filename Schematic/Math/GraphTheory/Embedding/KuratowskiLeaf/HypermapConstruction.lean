import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.InsertedNodeOrbits
import Schematic.Math.GraphTheory.Embedding.RotationSystem

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

/-- Choose an outgoing dart at a vertex, when one exists.  For the leaf lift,
this is the splice point for the old endpoint's node cycle. -/
noncomputable def orientedEdgePivot
    {V : Type u} {G : SimpleGraph V} (x : V) :
    Option (OrientedEdge G) := by
  classical
  exact
    if h : Exists fun e : OrientedEdge G => e.tail = x then
      some h.choose
    else
      none

theorem orientedEdgePivot_spec_of_eq_some
    {V : Type u} {G : SimpleGraph V} {x : V} {e : OrientedEdge G}
    (h : orientedEdgePivot (G := G) x = some e) :
    e.tail = x := by
  classical
  unfold orientedEdgePivot at h
  by_cases h_exists : Exists fun e : OrientedEdge G => e.tail = x
  · simp [h_exists] at h
    simpa [h] using h_exists.choose_spec
  · simp [h_exists] at h

theorem orientedEdgePivot_eq_none_iff
    {V : Type u} {G : SimpleGraph V} {x : V} :
    orientedEdgePivot (G := G) x = none ↔
      ¬ Exists fun e : OrientedEdge G => e.tail = x := by
  classical
  unfold orientedEdgePivot
  by_cases h : Exists fun e : OrientedEdge G => e.tail = x
  · simp [h]
  · simp [h]

theorem no_orientedEdge_tail_of_pivot_eq_none
    {V : Type u} {G : SimpleGraph V} {x : V}
    (h : orientedEdgePivot (G := G) x = none)
    (e : OrientedEdge G) :
    e.tail ≠ x := by
  intro he
  exact (orientedEdgePivot_eq_none_iff.mp h) ⟨e, he⟩

/-- Hypermap obtained by adding a leaf edge-pair to a hypermap node order.
This is the pure hypermap object behind the graph leaf reattachment lift. -/
def leafHypermap (G : Hypermap.{u}) (pivot : Option G.Dart) :
    Hypermap.{u} where
  Dart := ExtDart G.Dart
  edge := ExtDart.Perm.edge G.edge
  node := insertedLeafNode G.node pivot
  face := (ExtDart.Perm.edge G.edge).symm.trans
    (insertedLeafNode G.node pivot).symm
  node_face_edge := by
    intro x
    simp [Equiv.trans_apply]

@[simp]
theorem leafHypermap_edge
    (G : Hypermap.{u}) (pivot : Option G.Dart)
    (x : (leafHypermap G pivot).Dart) :
    (leafHypermap G pivot).edge x = ExtDart.Perm.edge G.edge x :=
  rfl

@[simp]
theorem leafHypermap_edge_symm_old
    (G : Hypermap.{u}) (pivot : Option G.Dart) (x : G.Dart) :
    (leafHypermap G pivot).edge.symm (ExtDart.old x) =
      ExtDart.old (G.edge.symm x) :=
  rfl

@[simp]
theorem leafHypermap_node
    (G : Hypermap.{u}) (pivot : Option G.Dart)
    (x : (leafHypermap G pivot).Dart) :
    (leafHypermap G pivot).node x = insertedLeafNode G.node pivot x :=
  rfl

@[simp]
theorem leafHypermap_face
    (G : Hypermap.{u}) (pivot : Option G.Dart)
    (x : (leafHypermap G pivot).Dart) :
    (leafHypermap G pivot).face x =
      (insertedLeafNode G.node pivot).symm
        ((ExtDart.Perm.edge G.edge).symm x) :=
  rfl

end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
