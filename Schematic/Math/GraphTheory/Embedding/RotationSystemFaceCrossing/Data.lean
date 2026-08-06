import Schematic.Math.GraphTheory.Embedding.RotationSystem

/-! Crossing data and face-arc decomposition for repeated face-boundary vertices. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

structure FaceOrbitCrossingData
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H) where
  branch : W
  x : OrientedEdge H
  y : OrientedEdge H
  u : OrientedEdge H
  v : OrientedEdge H
  x_tail : x.tail = branch
  y_tail : y.tail = branch
  x_ne_y : x ≠ y
  x_face :
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) x
  y_face :
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) y
  connector : List (OrientedEdge H)
  connector_path : (R.toHypermap).CPath u connector
  connector_last : (u :: connector).getLastD u = v
  connector_nodup : (u :: connector).Nodup
  connector_avoids_branch :
    ∀ d : OrientedEdge H, d ∈ u :: connector → d.tail ≠ branch
  endpoint_orientation :
    (u = (R.toHypermap).face y ∧
      v = (R.toHypermap).face x) ∨
    (u = (R.toHypermap).face.symm x ∧
      v = (R.toHypermap).face.symm y)

/-- Ordered face arcs for normalized crossing data.  Both orientation cases
put the connector source on the `y`-arc and its target on the `x`-arc. -/
structure FaceOrbitCrossingArcs
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (D : FaceOrbitCrossingData R e) where
  left : List (OrientedEdge H)
  right : List (OrientedEdge H)
  left_path :
    (R.toHypermap).FacePath D.x (left ++ [D.y])
  right_path :
    (R.toHypermap).FacePath D.y (right ++ [D.x])
  orbit_nodup :
    (D.x :: left ++ D.y :: right).Nodup
  orbit_membership :
    ∀ z : OrientedEdge H,
      z ∈ D.x :: left ++ D.y :: right ↔
        PermReachable (R.toHypermap).face D.x z
  connector_source_mem_right : D.u ∈ D.y :: right
  connector_target_mem_left : D.v ∈ D.x :: left
  arcs_disjoint :
    Disjoint
      {z : OrientedEdge H | z ∈ D.x :: left}
      {z : OrientedEdge H | z ∈ D.y :: right}

theorem FaceOrbitCrossingData.faceReachable
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (D : FaceOrbitCrossingData R e) :
    PermReachable (R.toHypermap).face D.x D.y := by
  have hx :
      PermReachable (R.toHypermap).face e D.x :=
    (Hypermap.FaceBand.faceOrbitList_iff (G := R.toHypermap)).mp D.x_face
  have hy :
      PermReachable (R.toHypermap).face e D.y :=
    (Hypermap.FaceBand.faceOrbitList_iff (G := R.toHypermap)).mp D.y_face
  exact PermReachable.trans (R.toHypermap).face
    (PermReachable.symm (R.toHypermap).face hx) hy

theorem FaceOrbitCrossingData.face_x_ne_y
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (D : FaceOrbitCrossingData R e) :
    (R.toHypermap).face D.x ≠ D.y := by
  intro h
  apply D.x.adj.ne
  calc
    D.x.tail = D.branch := D.x_tail
    _ = D.y.tail := D.y_tail.symm
    _ = ((R.toHypermap).face D.x).tail :=
      (congrArg OrientedEdge.tail h).symm
    _ = D.x.head := RotationSystem.toHypermap_face_tail R D.x

theorem FaceOrbitCrossingData.face_y_ne_x
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (D : FaceOrbitCrossingData R e) :
    (R.toHypermap).face D.y ≠ D.x := by
  intro h
  apply D.y.adj.ne
  calc
    D.y.tail = D.branch := D.y_tail
    _ = D.x.tail := D.x_tail.symm
    _ = ((R.toHypermap).face D.y).tail :=
      (congrArg OrientedEdge.tail h).symm
    _ = D.y.head := RotationSystem.toHypermap_face_tail R D.y

theorem FaceOrbitCrossingData.exists_arcs
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (D : FaceOrbitCrossingData R e) :
    Nonempty (FaceOrbitCrossingArcs D) := by
  classical
  rcases (R.toHypermap).exists_complementary_facePaths
      D.faceReachable D.x_ne_y with
    ⟨left, right, hleft, hright, hnodup, horbit⟩
  have hpartsNodup :
      ((D.x :: left) ++ (D.y :: right)).Nodup := by
    simpa [List.cons_append, List.append_assoc] using hnodup
  have hdisjoint :
      Disjoint
        {z : OrientedEdge H | z ∈ D.x :: left}
        {z : OrientedEdge H | z ∈ D.y :: right} := by
    rw [Set.disjoint_left]
    intro z hzLeft hzRight
    exact
      (List.nodup_append.mp hpartsNodup).2.2
        z hzLeft z hzRight rfl
  have hu : D.u ∈ D.y :: right := by
    rcases D.endpoint_orientation with hout | hin
    · rw [hout.1]
      exact Hypermap.FacePath.face_mem_sourceArc
        (G := R.toHypermap) hright D.face_y_ne_x
    · rw [hin.1]
      exact Hypermap.FacePath.face_symm_mem_sourceArc
        (G := R.toHypermap) hright
  have hv : D.v ∈ D.x :: left := by
    rcases D.endpoint_orientation with hout | hin
    · rw [hout.2]
      exact Hypermap.FacePath.face_mem_sourceArc
        (G := R.toHypermap) hleft D.face_x_ne_y
    · rw [hin.2]
      exact Hypermap.FacePath.face_symm_mem_sourceArc
        (G := R.toHypermap) hleft
  exact ⟨{
    left := left
    right := right
    left_path := hleft
    right_path := hright
    orbit_nodup := hnodup
    orbit_membership := horbit
    connector_source_mem_right := hu
    connector_target_mem_left := hv
    arcs_disjoint := hdisjoint
  }⟩


end FourColor
end Schematic.Math.GraphTheory
