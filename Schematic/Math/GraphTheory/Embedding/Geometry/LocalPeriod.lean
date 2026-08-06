import Schematic.Math.GraphTheory.Embedding.Hypermap

/-!
Local orbit identities for hypermaps.

These lemmas deliberately use pointwise period hypotheses.  They are useful
when a map is cubic only on a selected set, without manufacturing a global
`Hypermap.Cubic` assumption.
-/

namespace Schematic.Math.GraphTheory.FourColor.Hypermap

universe u

variable {G : Hypermap.{u}}

/-- A three-periodic node orbit identifies the second node successor with the
face successor of the opposite dart. -/
theorem node_node_eq_face_edge_of_period_three
    {x : G.Dart}
    (hperiod : G.node (G.node (G.node x)) = x) :
    G.node (G.node x) = G.face (G.edge x) := by
  apply G.node.injective
  rw [hperiod, G.node_face_edge]

end Schematic.Math.GraphTheory.FourColor.Hypermap
