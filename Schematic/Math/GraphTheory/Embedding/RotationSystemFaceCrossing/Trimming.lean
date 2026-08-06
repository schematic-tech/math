import Schematic.Math.GraphTheory.Embedding.RotationSystemFaceCrossing.Data

/-! Trimmed crossing contours between disjoint face arcs. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The two arc-to-arc contours after Coq's `disjoint_subpath` trimming.
Their open interiors avoid both face arcs.  The node contour remains over the
branch, whereas the alternate contour remains off the branch, so the two
trimmed contours are disjoint. -/
structure FaceOrbitCrossingTrimmed
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {D : FaceOrbitCrossingData R e}
    (A : FaceOrbitCrossingArcs D) where
  nodeRight : OrientedEdge H
  nodeLeft : OrientedEdge H
  nodeMiddle : List (OrientedEdge H)
  nodeRight_mem : nodeRight ∈ D.y :: A.right
  nodeLeft_mem : nodeLeft ∈ D.x :: A.left
  node_path :
    (R.toHypermap).CPath nodeRight (nodeMiddle ++ [nodeLeft])
  node_nodup :
    (nodeRight :: nodeMiddle ++ [nodeLeft]).Nodup
  nodeMiddle_avoids_arcs :
    ∀ z : OrientedEdge H, z ∈ nodeMiddle →
      z ∉ D.y :: A.right ∧ z ∉ D.x :: A.left
  node_tail :
    ∀ z : OrientedEdge H,
      z ∈ nodeRight :: nodeMiddle ++ [nodeLeft] →
        z.tail = D.branch
  connectorRight : OrientedEdge H
  connectorLeft : OrientedEdge H
  connectorMiddle : List (OrientedEdge H)
  connectorRight_mem : connectorRight ∈ D.y :: A.right
  connectorLeft_mem : connectorLeft ∈ D.x :: A.left
  connector_path :
    (R.toHypermap).CPath connectorRight
      (connectorMiddle ++ [connectorLeft])
  connector_nodup :
    (connectorRight :: connectorMiddle ++ [connectorLeft]).Nodup
  connectorMiddle_avoids_arcs :
    ∀ z : OrientedEdge H, z ∈ connectorMiddle →
      z ∉ D.y :: A.right ∧ z ∉ D.x :: A.left
  connector_tail_ne :
    ∀ z : OrientedEdge H,
      z ∈ connectorRight :: connectorMiddle ++ [connectorLeft] →
        z.tail ≠ D.branch

theorem FaceOrbitCrossingArcs.exists_trimmed
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {D : FaceOrbitCrossingData R e}
    (A : FaceOrbitCrossingArcs D) :
    Nonempty (FaceOrbitCrossingTrimmed A) := by
  classical
  let leftArc : Set (OrientedEdge H) :=
    {z | z ∈ D.x :: A.left}
  let rightArc : Set (OrientedEdge H) :=
    {z | z ∈ D.y :: A.right}
  have hdisjoint : Disjoint rightArc leftArc := by
    exact A.arcs_disjoint.symm
  rcases R.toHypermap_exists_short_cPath_of_same_tail_controlled
      (e := D.y) (f := D.x)
      (D.y_tail.trans D.x_tail.symm) with
    ⟨p, hp, hlast, hnodup, htail⟩
  rcases Hypermap.CPath.exists_trimmed_between_disjoint
      (G := R.toHypermap)
      (A := rightArc) (B := leftArc)
      hp hlast hnodup
      (by
        change D.y ∈ D.y :: A.right
        exact List.mem_cons_self)
      (by
        change D.x ∈ D.x :: A.left
        exact List.mem_cons_self)
      hdisjoint with
    ⟨nodeRight, nodeLeft, nodeMiddle,
      hnodeRight, hnodeLeft, hnodePath, hnodeNodup,
      hnodeAvoid, hnodeSub⟩
  rcases Hypermap.CPath.exists_trimmed_between_disjoint
      (G := R.toHypermap)
      (A := rightArc) (B := leftArc)
      D.connector_path D.connector_last D.connector_nodup
      (by simpa [rightArc] using A.connector_source_mem_right)
      (by simpa [leftArc] using A.connector_target_mem_left)
      hdisjoint with
    ⟨connectorRight, connectorLeft, connectorMiddle,
      hconnectorRight, hconnectorLeft, hconnectorPath,
      hconnectorNodup, hconnectorAvoid, hconnectorSub⟩
  exact ⟨{
    nodeRight := nodeRight
    nodeLeft := nodeLeft
    nodeMiddle := nodeMiddle
    nodeRight_mem := hnodeRight
    nodeLeft_mem := hnodeLeft
    node_path := hnodePath
    node_nodup := hnodeNodup
    nodeMiddle_avoids_arcs := by
      intro z hz
      exact hnodeAvoid z hz
    node_tail := by
      intro z hz
      exact (htail z (hnodeSub z hz)).trans D.y_tail
    connectorRight := connectorRight
    connectorLeft := connectorLeft
    connectorMiddle := connectorMiddle
    connectorRight_mem := hconnectorRight
    connectorLeft_mem := hconnectorLeft
    connector_path := hconnectorPath
    connector_nodup := hconnectorNodup
    connectorMiddle_avoids_arcs := by
      intro z hz
      exact hconnectorAvoid z hz
    connector_tail_ne := by
      intro z hz
      exact D.connector_avoids_branch z (hconnectorSub z hz)
  }⟩


end FourColor
end Schematic.Math.GraphTheory
