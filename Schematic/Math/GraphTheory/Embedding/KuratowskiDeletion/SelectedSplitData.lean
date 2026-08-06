import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.BoundaryWalks
import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.AddEdge


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- Local split-corner package at one visit of the selected contraction face
to the collapsed vertex.  It gives a deleted-edge lift of the leaving dart,
of the immediately preceding entering dart, and of the immediately succeeding
outside dart. -/
theorem exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_tail_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (htail :
      d.tail = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun dLeave : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab dLeave = d ∧
        (dLeave.tail = a ∨ dLeave.tail = b) ∧
          Exists fun dPrev : OrientedEdge (deletedGraph G a b) =>
            deletedGraphToCollapseEdgeDart G hab dPrev =
                (R.toHypermap).face.symm d ∧
              (dPrev.head = a ∨ dPrev.head = b) ∧
                Exists fun dNext : OrientedEdge (deletedGraph G a b) =>
                  deletedGraphToCollapseEdgeDart G hab dNext =
                      (R.toHypermap).face d ∧
                    dNext.tail ∉ ({a, b} : Set V) ∧
                      (R.toHypermap).face.symm d ∈
                          contractionFaceBoundary hab R e ∧
                        (R.toHypermap).face d ∈
                          contractionFaceBoundary hab R e := by
  rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_left_or_right
      (G := G) hab d htail with ⟨dLeave, hdLeave, hLeave_side⟩
  rcases contractionFaceBoundary_face_symm_head_none_of_tail_none
      (G := G) hab R e d hd htail with ⟨hprev_head, hprev_mem⟩
  rcases exists_deletedGraphToCollapseEdgeDart_lift_head_left_or_right
      (G := G) hab ((R.toHypermap).face.symm d) hprev_head with
    ⟨dPrev, hdPrev, hPrev_side⟩
  rcases exists_deletedGraphToCollapseEdgeDart_lift_face_of_boundary_tail_none
      (G := G) hab R e d hd htail with
    ⟨dNext, hdNext, hNext_tail, hnext_mem⟩
  exact
    ⟨dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩

/-- Symmetric local split-corner package starting from a boundary dart that
enters the collapsed vertex.  Its face successor leaves the collapsed vertex,
so the outgoing corner package applies there. -/
theorem exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_head_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (hhead :
      d.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun dEnter : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab dEnter = d ∧
        (dEnter.head = a ∨ dEnter.head = b) ∧
          Exists fun dLeave : OrientedEdge (deletedGraph G a b) =>
            deletedGraphToCollapseEdgeDart G hab dLeave =
                (R.toHypermap).face d ∧
              (dLeave.tail = a ∨ dLeave.tail = b) ∧
                Exists fun dNext : OrientedEdge (deletedGraph G a b) =>
                  deletedGraphToCollapseEdgeDart G hab dNext =
                      (R.toHypermap).face ((R.toHypermap).face d) ∧
                    dNext.tail ∉ ({a, b} : Set V) ∧
                      (R.toHypermap).face d ∈
                          contractionFaceBoundary hab R e ∧
                        (R.toHypermap).face ((R.toHypermap).face d) ∈
                          contractionFaceBoundary hab R e := by
  rcases exists_deletedGraphToCollapseEdgeDart_lift_head_left_or_right
      (G := G) hab d hhead with ⟨dEnter, hdEnter, hEnter_side⟩
  rcases contractionFaceBoundary_face_tail_none_of_head_none
      (G := G) hab R e d hd hhead with ⟨hsucc_tail, hsucc_mem⟩
  rcases exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_tail_none
      (G := G) hab R e ((R.toHypermap).face d) hsucc_mem hsucc_tail with
    ⟨dLeave, hdLeave, hLeave_side, _dPrev, _hdPrev, _hPrev_side,
      dNext, hdNext, hNext_tail, _hprev_mem, hnext_mem⟩
  exact
    ⟨dEnter, hdEnter, hEnter_side,
      dLeave, hdLeave, hLeave_side,
        dNext, hdNext, hNext_tail, hsucc_mem, hnext_mem⟩

/-- In the minimum-degree-three source branch, the collapsed vertex in
`G / ab` has an outgoing dart.  We select it by taking any surviving deleted
edge dart whose tail is `a` and then quotienting to the contraction. -/
theorem exists_contraction_dart_tail_none_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b) :
    Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target) := by
  rcases addEdgeEndpointDarts_exist_of_min_degree_three
      (G := G) hmin a b with ⟨p, _q, hp, _hq⟩
  let e : OrientedEdge (GraphContraction.collapseEdge G hab).graph :=
    deletedGraphToCollapseEdgeDart G hab p
  refine ⟨e, ?_⟩
  rw [deletedGraphToCollapseEdgeDart_tail]
  simp [hp, deletedGraphToCollapseEdgeHom_apply_left]

/-- Minimum-degree-three selected-corner package for the contraction face
boundary: choose a face through the collapsed vertex and unpack the local
deleted-edge darts around that visit. -/
theorem exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph) :
    Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
        Exists fun dLeave : OrientedEdge (deletedGraph G a b) =>
          deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
            (dLeave.tail = a ∨ dLeave.tail = b) ∧
              Exists fun dPrev : OrientedEdge (deletedGraph G a b) =>
                deletedGraphToCollapseEdgeDart G hab dPrev =
                    (R.toHypermap).face.symm e ∧
                  (dPrev.head = a ∨ dPrev.head = b) ∧
                    Exists fun dNext : OrientedEdge (deletedGraph G a b) =>
                      deletedGraphToCollapseEdgeDart G hab dNext =
                          (R.toHypermap).face e ∧
                        dNext.tail ∉ ({a, b} : Set V) ∧
                          (R.toHypermap).face.symm e ∈
                              contractionFaceBoundary hab R e ∧
                            (R.toHypermap).face e ∈
                              contractionFaceBoundary hab R e := by
  rcases exists_contraction_dart_tail_none_of_min_degree_three
      (G := G) hmin hab with ⟨e, htail⟩
  rcases exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_tail_none
      (G := G) hab R e e
      (contractionFaceBoundary_self_mem hab R e) htail with
    ⟨dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩
  exact
    ⟨e, htail, dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩

/-- Named local data at the selected collapsed-vertex visit of a contraction
face.  This is the Lean-side analogue of fixing the ring/corner at which the
contracted vertex will later be split. -/
structure SelectedBoundaryCorner
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph) where
  e : OrientedEdge (GraphContraction.collapseEdge G hab).graph
  tail_none : e.tail = (none : (GraphContraction.collapseEdge G hab).Target)
  dLeave : OrientedEdge (deletedGraph G a b)
  dLeave_map : deletedGraphToCollapseEdgeDart G hab dLeave = e
  dLeave_tail_source : dLeave.tail = a ∨ dLeave.tail = b
  dPrev : OrientedEdge (deletedGraph G a b)
  dPrev_map :
    deletedGraphToCollapseEdgeDart G hab dPrev =
      (R.toHypermap).face.symm e
  dPrev_head_source : dPrev.head = a ∨ dPrev.head = b
  dNext : OrientedEdge (deletedGraph G a b)
  dNext_map :
    deletedGraphToCollapseEdgeDart G hab dNext = (R.toHypermap).face e
  dNext_tail_outside : dNext.tail ∉ ({a, b} : Set V)
  prev_mem :
    (R.toHypermap).face.symm e ∈ contractionFaceBoundary hab R e
  next_mem :
    (R.toHypermap).face e ∈ contractionFaceBoundary hab R e

/-- Named Makarychev outside-the-boundary theta dart for a selected
contraction face. -/
structure SelectedBoundaryThetaDart
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) where
  x : {z : V | z ∉ ({a, b} : Set V)}
  y : {z : V | z ∉ ({a, b} : Set V)}
  dTheta : OrientedEdge (deletedGraph G a b)
  adj : (deleteEdgeEndsGraph G a b).Adj x y
  dTheta_tail : dTheta.tail = (x : V)
  dTheta_head : dTheta.head = (y : V)
  collapse_tail :
    (deletedGraphToCollapseEdgeDart G hab dTheta).tail =
      deleteEdgeEndsGraphToCollapseEdgeHom G hab x
  collapse_head :
    (deletedGraphToCollapseEdgeDart G hab dTheta).head =
      deleteEdgeEndsGraphToCollapseEdgeHom G hab y
  not_deleteEndsBoundary :
    Not ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x y)
  not_outsideBoundary :
    Not
      ((contractionFaceBoundaryOutsideSubgraph hab R e).Adj
        (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
        (deleteEdgeEndsGraphToCollapseEdgeHom G hab y))
  not_faceBoundary :
    deletedGraphToCollapseEdgeDart G hab dTheta ∉
      contractionFaceBoundary hab R e

/-- The compact proof-facing split datum: a selected corner at the collapsed
vertex together with a theta dart outside that same selected face boundary. -/
structure SelectedSplitDatum
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph) where
  corner : SelectedBoundaryCorner hab R
  theta : SelectedBoundaryThetaDart hab R corner.e

/-- Structure-valued form of the selected corner extractor. -/
theorem exists_selectedBoundaryCorner_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph) :
    Nonempty (SelectedBoundaryCorner hab R) := by
  rcases exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_min_degree_three
      (G := G) hmin hab R with
    ⟨e, htail, dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩
  exact
    ⟨{ e := e
       tail_none := htail
       dLeave := dLeave
       dLeave_map := hdLeave
       dLeave_tail_source := hLeave_side
       dPrev := dPrev
       dPrev_map := hdPrev
       dPrev_head_source := hPrev_side
       dNext := dNext
       dNext_map := hdNext
       dNext_tail_outside := hNext_tail
       prev_mem := hprev_mem
       next_mem := hnext_mem }⟩

/-- Structure-valued form of the outside-the-boundary theta extractor. -/
theorem exists_selectedBoundaryThetaDart_of_faceOrbitNoTheta
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Nonempty (SelectedBoundaryThetaDart hab R e) := by
  rcases
      exists_deletedGraph_theta_dart_not_boundary_and_not_faceBoundary_of_faceOrbitNoTheta
        hface hab R hplanar e htheta with
    ⟨x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
      hdTheta_collapse_tail, hdTheta_collapse_head,
      hnotBoundary, hnotOutsideBoundary, hnotFaceBoundary⟩
  exact
    ⟨{ x := x
       y := y
       dTheta := dTheta
       adj := hxy
       dTheta_tail := hdTheta_tail
       dTheta_head := hdTheta_head
       collapse_tail := hdTheta_collapse_tail
       collapse_head := hdTheta_collapse_head
       not_deleteEndsBoundary := hnotBoundary
       not_outsideBoundary := hnotOutsideBoundary
       not_faceBoundary := hnotFaceBoundary }⟩

/-- Compact structure-valued form of the selected split data. -/
theorem exists_selectedSplitDatum_of_faceOrbitNoTheta
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Nonempty (SelectedSplitDatum hab R) := by
  rcases exists_selectedBoundaryCorner_of_min_degree_three
      (G := G) hmin hab R with ⟨corner⟩
  rcases exists_selectedBoundaryThetaDart_of_faceOrbitNoTheta
      hface hab R hplanar corner.e htheta with ⟨theta⟩
  exact ⟨{ corner := corner, theta := theta }⟩

namespace SelectedSplitDatum

theorem theta_tail_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.theta.dTheta.tail ∉ ({a, b} : Set V) := by
  rw [D.theta.dTheta_tail]
  exact D.theta.x.2

theorem theta_head_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.theta.dTheta.head ∉ ({a, b} : Set V) := by
  rw [D.theta.dTheta_head]
  exact D.theta.y.2

theorem dLeave_head_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.corner.dLeave.head ∉ ({a, b} : Set V) :=
  deletedGraph_head_outside_of_tail_source D.corner.dLeave
    D.corner.dLeave_tail_source

theorem dPrev_tail_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.corner.dPrev.tail ∉ ({a, b} : Set V) :=
  deletedGraph_tail_outside_of_head_source D.corner.dPrev
    D.corner.dPrev_head_source

/-- The selected non-boundary theta dart determines a genuine crossing edge
of the selected contraction face.  One orientation `z` lies on the selected
face boundary, while the reverse orientation and the contour successor across
that edge lie outside it. -/
theorem exists_boundaryDart_symm_not_boundary
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R)
    (hconn : (R.toHypermap).Connected) :
    ∃ z : OrientedEdge (GraphContraction.collapseEdge G hab).graph,
      z ∈ contractionFaceBoundary hab R D.corner.e ∧
        R.node.symm z ∉ contractionFaceBoundary hab R D.corner.e ∧
          z.symm ∉ contractionFaceBoundary hab R D.corner.e := by
  let t :=
    deletedGraphToCollapseEdgeDart G hab D.theta.dTheta
  have htNot :
      ¬ PermReachable (R.toHypermap).face D.corner.e t := by
    simpa [mem_contractionFaceBoundary] using D.theta.not_faceBoundary
  have het : (R.toHypermap).CConnect D.corner.e t :=
    Hypermap.Connected.cConnect (G := R.toHypermap)
      hconn D.corner.e t
  rcases
      Hypermap.CConnect.exists_nodeSymm_face_crossing
        (G := R.toHypermap) het htNot with
    ⟨z, hzFace, hzNode⟩
  have hzMem :
      z ∈ contractionFaceBoundary hab R D.corner.e := by
    exact
      (mem_contractionFaceBoundary hab R D.corner.e z).mpr hzFace
  have hzNodeMem :
      R.node.symm z ∉ contractionFaceBoundary hab R D.corner.e := by
    simpa [mem_contractionFaceBoundary] using hzNode
  have hzSymm :
      z.symm ∉ contractionFaceBoundary hab R D.corner.e := by
    intro hzSymmMem
    have hzEdgeFace :
        PermReachable (R.toHypermap).face D.corner.e
          ((R.toHypermap).edge z) := by
      simpa using
        (mem_contractionFaceBoundary hab R D.corner.e z.symm).mp
          hzSymmMem
    have hzNodeFace :
        PermReachable (R.toHypermap).face D.corner.e
          (R.node.symm z) := by
      exact
        PermReachable.trans (R.toHypermap).face hzEdgeFace
          (by
            have hstep :=
              PermReachable.forward (R.toHypermap).face
                ((R.toHypermap).edge z)
            simpa [RotationSystem.toHypermap] using hstep)
    exact hzNode hzNodeFace
  exact ⟨z, hzMem, hzNodeMem, hzSymm⟩

/-- Outside endpoint reached immediately after leaving the split source at the
selected collapsed-vertex corner. -/
def dLeaveHead
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    {z : V | z ∉ ({a, b} : Set V)} :=
  ⟨D.corner.dLeave.head, D.dLeave_head_outside⟩

@[simp]
theorem dLeaveHead_coe
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    (D.dLeaveHead : V) = D.corner.dLeave.head :=
  rfl

/-- Outside endpoint immediately before entering the split source at the
selected collapsed-vertex corner. -/
def dPrevTail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    {z : V | z ∉ ({a, b} : Set V)} :=
  ⟨D.corner.dPrev.tail, D.dPrev_tail_outside⟩

@[simp]
theorem dPrevTail_coe
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    (D.dPrevTail : V) = D.corner.dPrev.tail :=
  rfl

theorem theta_image_ne_of_boundary_mem
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R)
    {e : OrientedEdge (GraphContraction.collapseEdge G hab).graph}
    (he : e ∈ contractionFaceBoundary hab R D.corner.e) :
    deletedGraphToCollapseEdgeDart G hab D.theta.dTheta ≠ e := by
  intro h
  apply D.theta.not_faceBoundary
  rw [h]
  exact he

theorem theta_image_ne_corner
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    deletedGraphToCollapseEdgeDart G hab D.theta.dTheta ≠ D.corner.e := by
  exact D.theta_image_ne_of_boundary_mem
    (contractionFaceBoundary_self_mem hab R D.corner.e)

theorem theta_image_ne_prev
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    deletedGraphToCollapseEdgeDart G hab D.theta.dTheta ≠
      (R.toHypermap).face.symm D.corner.e := by
  exact D.theta_image_ne_of_boundary_mem D.corner.prev_mem

theorem theta_image_ne_next
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    deletedGraphToCollapseEdgeDart G hab D.theta.dTheta ≠
      (R.toHypermap).face D.corner.e := by
  exact D.theta_image_ne_of_boundary_mem D.corner.next_mem

theorem theta_ne_dLeave
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.theta.dTheta ≠ D.corner.dLeave := by
  intro h
  exact D.theta_image_ne_corner
    (by rw [h, D.corner.dLeave_map])

theorem theta_ne_dPrev
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.theta.dTheta ≠ D.corner.dPrev := by
  intro h
  exact D.theta_image_ne_prev
    (by rw [h, D.corner.dPrev_map])

theorem theta_ne_dNext
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    {hab : G.Adj a b}
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    {R : RotationSystem (GraphContraction.collapseEdge G hab).graph}
    (D : SelectedSplitDatum hab R) :
    D.theta.dTheta ≠ D.corner.dNext := by
  intro h
  exact D.theta_image_ne_next
    (by rw [h, D.corner.dNext_map])

end SelectedSplitDatum

/-- Combined proof-facing data for the Makarychev/Skopenkov split step:
choose the collapsed-vertex face/corner and, for that same selected face,
choose a theta dart in `G - ab` outside the transported boundary. -/
theorem exists_selected_boundary_corner_and_theta_dart_not_boundary_of_faceOrbitNoTheta
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
        (Exists fun dLeave : OrientedEdge (deletedGraph G a b) =>
          deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
            (dLeave.tail = a ∨ dLeave.tail = b) ∧
              Exists fun dPrev : OrientedEdge (deletedGraph G a b) =>
                deletedGraphToCollapseEdgeDart G hab dPrev =
                    (R.toHypermap).face.symm e ∧
                  (dPrev.head = a ∨ dPrev.head = b) ∧
                    Exists fun dNext : OrientedEdge (deletedGraph G a b) =>
                      deletedGraphToCollapseEdgeDart G hab dNext =
                          (R.toHypermap).face e ∧
                        dNext.tail ∉ ({a, b} : Set V) ∧
                          (R.toHypermap).face.symm e ∈
                              contractionFaceBoundary hab R e ∧
                            (R.toHypermap).face e ∈
                              contractionFaceBoundary hab R e) ∧
          Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
            Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
              Exists fun dTheta : OrientedEdge (deletedGraph G a b) =>
                (deleteEdgeEndsGraph G a b).Adj x y ∧
                  dTheta.tail = (x : V) ∧
                    dTheta.head = (y : V) ∧
                      (deletedGraphToCollapseEdgeDart G hab dTheta).tail =
                          deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                        (deletedGraphToCollapseEdgeDart G hab dTheta).head =
                          deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                          Not
                            ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj
                              x y) := by
  rcases exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_min_degree_three
      (G := G) hmin hab R with
    ⟨e, htail, dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩
  rcases exists_deletedGraph_theta_dart_not_boundary_of_faceOrbitNoTheta
      hface hab R hplanar e htheta with
    ⟨x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
      hdTheta_collapse_tail, hdTheta_collapse_head, hnotBoundary⟩
  exact
    ⟨e, htail,
      ⟨dLeave, hdLeave, hLeave_side,
        dPrev, hdPrev, hPrev_side,
          dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩,
      x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
        hdTheta_collapse_tail, hdTheta_collapse_head, hnotBoundary⟩

/-- Strengthened combined split datum: the selected theta dart is outside the
pulled-back boundary and its contraction image is outside the selected
contraction face-boundary subgraph. -/
theorem exists_selected_boundary_corner_and_theta_dart_not_boundary_and_not_outsideBoundary_of_faceOrbitNoTheta
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
        (Exists fun dLeave : OrientedEdge (deletedGraph G a b) =>
          deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
            (dLeave.tail = a ∨ dLeave.tail = b) ∧
              Exists fun dPrev : OrientedEdge (deletedGraph G a b) =>
                deletedGraphToCollapseEdgeDart G hab dPrev =
                    (R.toHypermap).face.symm e ∧
                  (dPrev.head = a ∨ dPrev.head = b) ∧
                    Exists fun dNext : OrientedEdge (deletedGraph G a b) =>
                      deletedGraphToCollapseEdgeDart G hab dNext =
                          (R.toHypermap).face e ∧
                        dNext.tail ∉ ({a, b} : Set V) ∧
                          (R.toHypermap).face.symm e ∈
                              contractionFaceBoundary hab R e ∧
                            (R.toHypermap).face e ∈
                              contractionFaceBoundary hab R e) ∧
          Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
            Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
              Exists fun dTheta : OrientedEdge (deletedGraph G a b) =>
                (deleteEdgeEndsGraph G a b).Adj x y ∧
                  dTheta.tail = (x : V) ∧
                    dTheta.head = (y : V) ∧
                      (deletedGraphToCollapseEdgeDart G hab dTheta).tail =
                          deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                        (deletedGraphToCollapseEdgeDart G hab dTheta).head =
                          deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                          Not
                            ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj
                              x y) ∧
                            Not
                              ((contractionFaceBoundaryOutsideSubgraph hab R e).Adj
                                (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
                                (deleteEdgeEndsGraphToCollapseEdgeHom G hab y)) := by
  rcases exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_min_degree_three
      (G := G) hmin hab R with
    ⟨e, htail, dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩
  rcases
      exists_deletedGraph_theta_dart_not_boundary_and_not_outsideBoundary_of_faceOrbitNoTheta
        hface hab R hplanar e htheta with
    ⟨x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
      hdTheta_collapse_tail, hdTheta_collapse_head,
      hnotBoundary, hnotOutsideBoundary⟩
  exact
    ⟨e, htail,
      ⟨dLeave, hdLeave, hLeave_side,
        dPrev, hdPrev, hPrev_side,
          dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩,
      x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
        hdTheta_collapse_tail, hdTheta_collapse_head,
        hnotBoundary, hnotOutsideBoundary⟩

/-- Fully strengthened combined split datum: the selected corner and the
Makarychev theta dart are chosen for the same selected contraction face, and
the theta dart's quotient image is not on that face orbit. -/
theorem exists_selected_boundary_corner_and_theta_dart_not_boundary_and_not_faceBoundary_of_faceOrbitNoTheta
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
        (Exists fun dLeave : OrientedEdge (deletedGraph G a b) =>
          deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
            (dLeave.tail = a ∨ dLeave.tail = b) ∧
              Exists fun dPrev : OrientedEdge (deletedGraph G a b) =>
                deletedGraphToCollapseEdgeDart G hab dPrev =
                    (R.toHypermap).face.symm e ∧
                  (dPrev.head = a ∨ dPrev.head = b) ∧
                    Exists fun dNext : OrientedEdge (deletedGraph G a b) =>
                      deletedGraphToCollapseEdgeDart G hab dNext =
                          (R.toHypermap).face e ∧
                        dNext.tail ∉ ({a, b} : Set V) ∧
                          (R.toHypermap).face.symm e ∈
                              contractionFaceBoundary hab R e ∧
                            (R.toHypermap).face e ∈
                              contractionFaceBoundary hab R e) ∧
          Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
            Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
              Exists fun dTheta : OrientedEdge (deletedGraph G a b) =>
                (deleteEdgeEndsGraph G a b).Adj x y ∧
                  dTheta.tail = (x : V) ∧
                    dTheta.head = (y : V) ∧
                      (deletedGraphToCollapseEdgeDart G hab dTheta).tail =
                          deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                        (deletedGraphToCollapseEdgeDart G hab dTheta).head =
                          deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                          Not
                            ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj
                              x y) ∧
                            Not
                              ((contractionFaceBoundaryOutsideSubgraph hab R e).Adj
                                (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
                                (deleteEdgeEndsGraphToCollapseEdgeHom G hab y)) ∧
                              deletedGraphToCollapseEdgeDart G hab dTheta ∉
                                contractionFaceBoundary hab R e := by
  rcases exists_deletedGraphToCollapseEdgeDart_boundary_corner_of_min_degree_three
      (G := G) hmin hab R with
    ⟨e, htail, dLeave, hdLeave, hLeave_side,
      dPrev, hdPrev, hPrev_side,
        dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩
  rcases
      exists_deletedGraph_theta_dart_not_boundary_and_not_faceBoundary_of_faceOrbitNoTheta
        hface hab R hplanar e htheta with
    ⟨x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
      hdTheta_collapse_tail, hdTheta_collapse_head,
      hnotBoundary, hnotOutsideBoundary, hnotFaceBoundary⟩
  exact
    ⟨e, htail,
      ⟨dLeave, hdLeave, hLeave_side,
        dPrev, hdPrev, hPrev_side,
          dNext, hdNext, hNext_tail, hprev_mem, hnext_mem⟩,
      x, y, dTheta, hxy, hdTheta_tail, hdTheta_head,
        hdTheta_collapse_tail, hdTheta_collapse_head,
        hnotBoundary, hnotOutsideBoundary, hnotFaceBoundary⟩

end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
