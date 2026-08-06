import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.DeletedDartEquivalence

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

/-- Reattach a deleted leaf to a rotation system on `G - v`.  The new leaf
dart is a singleton node; the opposite dart is spliced into the old endpoint
node orbit when that orbit exists, and is singleton otherwise. -/
noncomputable def leafReattachRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v})) :
    RotationSystem G where
  node :=
    let E := orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let N := insertedLeafNode R.node
      (leafExtPivot (G := G) (v := v) (w := w) hvw)
    (E.trans N).trans E.symm
  node_tail := by
    intro e
    let E := orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let N := insertedLeafNode R.node
      (leafExtPivot (G := G) (v := v) (w := w) hvw)
    change (E.symm (N (E e))).tail = e.tail
    calc
      (E.symm (N (E e))).tail =
          leafExtTail (G := G) (v := v) (w := w) (N (E e)) :=
        orientedEdgeDeleteLeafEquiv_symm_tail
          (G := G) (v := v) (w := w) hvw hdegree (N (E e))
      _ = leafExtTail (G := G) (v := v) (w := w) (E e) :=
        insertedLeafNode_leafExtTail (G := G) (v := v) (w := w) hvw R (E e)
      _ = e.tail :=
        orientedEdgeDeleteLeafEquiv_tail
          (G := G) (v := v) (w := w) hvw hdegree e
  node_orbit_of_same_tail := by
    intro e f hef
    let E := orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let N := insertedLeafNode R.node
      (leafExtPivot (G := G) (v := v) (w := w) hvw)
    change PermReachable ((E.trans N).trans E.symm) e f
    have htail :
        leafExtTail (G := G) (v := v) (w := w) (E e) =
          leafExtTail (G := G) (v := v) (w := w) (E f) := by
      rw [orientedEdgeDeleteLeafEquiv_tail
          (G := G) (v := v) (w := w) hvw hdegree e,
        orientedEdgeDeleteLeafEquiv_tail
          (G := G) (v := v) (w := w) hvw hdegree f,
        hef]
    have hN :
        PermReachable N (E e) (E f) :=
      insertedLeafNode_leafExtReachable_of_same_tail
        (G := G) (v := v) (w := w) hvw R htail
    have hconj :
        forall x : OrientedEdge G,
          E (((E.trans N).trans E.symm) x) = N (E x) := by
      intro x
      change E (E.symm (N (E x))) = N (E x)
      exact E.apply_symm_apply (N (E x))
    exact
      (permReachable_conj_iff E ((E.trans N).trans E.symm) N hconj).mpr hN

@[simp]
theorem leafReattachRotationSystem_node_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (e : OrientedEdge G) :
    (orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree)
      ((leafReattachRotationSystem
        (G := G) (v := v) (w := w) hvw hdegree R).node e) =
    insertedLeafNode R.node
      (leafExtPivot (G := G) (v := v) (w := w) hvw)
      ((orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree) e) := by
  let E := orientedEdgeDeleteLeafEquiv
    (G := G) (v := v) (w := w) hvw hdegree
  let N := insertedLeafNode R.node
    (leafExtPivot (G := G) (v := v) (w := w) hvw)
  change E (E.symm (N (E e))) = N (E e)
  exact E.apply_symm_apply (N (E e))

theorem leafHypermap_edge_symm_eq_edge_for_orientedEdge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : ExtDart (OrientedEdge G)) :
    (ExtDart.Perm.edge (OrientedEdge.edgePerm G)).symm x =
      ExtDart.Perm.edge (OrientedEdge.edgePerm G) x := by
  cases x <;> simp [ExtDart.Perm.edge, OrientedEdge.edgePerm]

/-- The hypermap induced by the reattached rotation system is isomorphic to
the pure `leafHypermap` extension of the old hypermap. -/
noncomputable def leafReattachRotationSystem_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v})) :
    Hypermap.Iso
      ((leafReattachRotationSystem
        (G := G) (v := v) (w := w) hvw hdegree R).toHypermap)
      (leafHypermap R.toHypermap
        (leafExtPivot (G := G) (v := v) (w := w) hvw)) where
  toEquiv :=
    orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
  map_edge := by
    intro e
    exact orientedEdgeDeleteLeafEquiv_edge
      (G := G) (v := v) (w := w) hvw hdegree e
  map_node := by
    intro e
    exact leafReattachRotationSystem_node_conj
      (G := G) (v := v) (w := w) hvw hdegree R e
  map_face := by
    intro e
    let E := orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let S := leafReattachRotationSystem
      (G := G) (v := v) (w := w) hvw hdegree R
    let N := insertedLeafNode R.node
      (leafExtPivot (G := G) (v := v) (w := w) hvw)
    let τ := ExtDart.Perm.edge
      (OrientedEdge.edgePerm (G.induce {z : V | z ≠ v}))
    have hnode : forall x : OrientedEdge G, E (S.node x) = N (E x) := by
      intro x
      exact leafReattachRotationSystem_node_conj
        (G := G) (v := v) (w := w) hvw hdegree R x
    change E (S.node.symm e.symm) = N.symm (τ.symm (E e))
    calc
      E (S.node.symm e.symm) = N.symm (E e.symm) :=
        perm_conj_symm_apply E S.node N hnode e.symm
      _ = N.symm (τ (E e)) := by
        rw [orientedEdgeDeleteLeafEquiv_edge
          (G := G) (v := v) (w := w) hvw hdegree e]
      _ = N.symm (τ.symm (E e)) := by
        rw [leafHypermap_edge_symm_eq_edge_for_orientedEdge
          (G := G.induce {z : V | z ≠ v}) (E e)]

theorem leafReattachRotationSystem_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (hR : (R.toHypermap).dual.EulerPlanar) :
    ((leafReattachRotationSystem
      (G := G) (v := v) (w := w) hvw hdegree R).toHypermap).dual.EulerPlanar := by
  let S := leafReattachRotationSystem
    (G := G) (v := v) (w := w) hvw hdegree R
  have hold : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hleaf :
      (leafHypermap R.toHypermap
        (leafExtPivot (G := G) (v := v) (w := w) hvw)).EulerPlanar :=
    (leafHypermap_eulerPlanar_iff R.toHypermap
      (leafExtPivot (G := G) (v := v) (w := w) hvw)).mpr hold
  have hsource : S.toHypermap.EulerPlanar := by
    let φ := leafReattachRotationSystem_toHypermapIso
      (G := G) (v := v) (w := w) hvw hdegree R
    exact (φ.eulerPlanar_iff).mpr hleaf
  exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hsource


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
