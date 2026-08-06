import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.Construction
import Schematic.Math.GraphTheory.Embedding.RotationSystemFaceCrossing
import Schematic.Math.GraphTheory.Connectivity

/-!
Vertex simplicity of face orbits in two-connected Euler-planar rotations.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemVertexDeletion

/-- Coq's `cycleG` consequence in graph-rotation language: a facial boundary
does not visit a graph vertex twice, in either orientation.  Plane embeddings
of two-connected simple graphs satisfy this property. -/
def FaceOrbitsVertexSimple
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) : Prop :=
  ∀ {a b : OrientedEdge G},
    PermReachable (R.toHypermap).face a b →
      (a.tail = b.tail → a = b) ∧
        (a.head = b.head → a = b)

/-- Lean form of Coq `hcycle.v::two_connected_cyle`: in an Euler-planar
rotation of a two-connected simple graph, a facial boundary visits each graph
vertex at most once.  The proof follows the reference argument: deleting the
repeated vertex leaves a connector between the two opposite endpoints, and
the connector together with the two facial arcs contradicts Jordan. -/
theorem faceOrbitsVertexSimple_of_isTwoConnected_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    (h2 : IsTwoConnected G)
    (hR : (R.toHypermap).EulerPlanar) :
    FaceOrbitsVertexSimple R := by
  classical
  have hJordan : (R.toHypermap).Jordan :=
    Unavoidability.eulerPlanar_jordan R.toHypermap hR
  have htailSimple :
      ∀ {a b : OrientedEdge G},
        PermReachable (R.toHypermap).face a b →
          a.tail = b.tail → a = b := by
    intro a b habFace habTail
    by_contra hab
    let branch : V := a.tail
    have hbTail : b.tail = branch := habTail.symm
    have haHeadNe : a.head ≠ branch := by
      intro h
      apply a.adj.ne
      change branch = a.head
      exact h.symm
    have hbHeadNe : b.head ≠ branch := by
      intro h
      exact b.adj.ne (hbTail.trans h.symm)
    have hdeleted :
        (G.induce ({branch} : Set V)ᶜ).Connected := by
      apply h2.2
      simp
    rcases connected_induce_exists_walk_support_subset
        (G := G) hdeleted
        (u := b.head) (v := a.head)
        (by simpa [branch] using hbHeadNe)
        (by simpa [branch] using haHeadNe) with
      ⟨w, hw⟩
    have havoid : branch ∉ w.support := by
      intro hbranch
      have := hw branch hbranch
      simp at this
    rcases R.toHypermap_exists_short_cPath_of_walk_avoiding_vertex
        w havoid
        (e := (R.toHypermap).face b)
        (f := (R.toHypermap).face a)
        (RotationSystem.toHypermap_face_tail R b)
        (RotationSystem.toHypermap_face_tail R a) with
      ⟨connector, hconnector, hlast, hnodup, hconnectorAvoid⟩
    let D : FaceOrbitCrossingData R a := {
      branch := branch
      x := a
      y := b
      u := (R.toHypermap).face b
      v := (R.toHypermap).face a
      x_tail := rfl
      y_tail := hbTail
      x_ne_y := hab
      x_face :=
        (Hypermap.FaceBand.faceOrbitList_iff
          (G := R.toHypermap)).mpr
          (PermReachable.refl (R.toHypermap).face a)
      y_face :=
        (Hypermap.FaceBand.faceOrbitList_iff
          (G := R.toHypermap)).mpr habFace
      connector := connector
      connector_path := hconnector
      connector_last := hlast
      connector_nodup := hnodup
      connector_avoids_branch := hconnectorAvoid
      endpoint_orientation := Or.inl ⟨rfl, rfl⟩
    }
    rcases D.exists_arcs with ⟨A⟩
    exact A.false_of_jordan hJordan
  intro a b habFace
  constructor
  · exact htailSimple habFace
  · intro habHead
    apply (R.toHypermap).face.injective
    apply htailSimple
    · have hfaceA :
          PermReachable (R.toHypermap).face
            ((R.toHypermap).face a) a := by
        simpa using
          (PermReachable.backward (R.toHypermap).face
            ((R.toHypermap).face a))
      have hfaceB :
          PermReachable (R.toHypermap).face b
            ((R.toHypermap).face b) :=
        PermReachable.forward (R.toHypermap).face b
      exact
        PermReachable.trans (R.toHypermap).face hfaceA
          (PermReachable.trans (R.toHypermap).face habFace hfaceB)
    · rw [RotationSystem.toHypermap_face_tail,
        RotationSystem.toHypermap_face_tail]
      exact habHead


end RotationSystemVertexDeletion

end FourColor

end Schematic.Math.GraphTheory

