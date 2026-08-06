import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.FaceOrbitNoTheta


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- The general face-orbit no-theta theorem specializes immediately to the
outside part of the selected contraction face boundary. -/
theorem not_containsHomeomorphicTheta_contractionFaceBoundaryOutsideSubgraph
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    Not
      (ContainsHomeomorphicTheta
        (contractionFaceBoundaryOutsideSubgraph hab R e).coe) :=
  hface R hplanar e
    (contractionFaceBoundaryOutsideSubgraph hab R e)
    (contractionFaceBoundaryOutsideSubgraph_carriedByFaceOrbit hab R e)

/-- Every outside-boundary vertex is genuinely outside the collapsed vertex. -/
theorem contractionFaceBoundaryOutsideSubgraph_vert_ne_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x : (GraphContraction.collapseEdge G hab).Target}
    (hx : x ∈ (contractionFaceBoundaryOutsideSubgraph hab R e).verts) :
    x ≠ (none : (GraphContraction.collapseEdge G hab).Target) :=
  hx.1

/-- The outside-boundary subgraph is contained in the full selected face
boundary subgraph. -/
theorem contractionFaceBoundaryOutsideSubgraph_le_boundarySubgraph
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    contractionFaceBoundaryOutsideSubgraph hab R e ≤
      contractionFaceBoundarySubgraph hab R e := by
  constructor
  · rintro x ⟨_hx, d, hd, _htail, _hhead, hdx⟩
    exact ⟨d, hd, hdx⟩
  · rintro x y ⟨d, hd, _htail, _hhead, hxy⟩
    exact ⟨d, hd, hxy⟩

/-- Left endpoint of an outside-boundary edge is not the collapsed vertex. -/
theorem contractionFaceBoundaryOutsideSubgraph_adj_left_ne_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x y : (GraphContraction.collapseEdge G hab).Target}
    (hxy : (contractionFaceBoundaryOutsideSubgraph hab R e).Adj x y) :
    x ≠ (none : (GraphContraction.collapseEdge G hab).Target) :=
  (contractionFaceBoundaryOutsideSubgraph hab R e).edge_vert hxy |>.1

/-- Right endpoint of an outside-boundary edge is not the collapsed vertex. -/
theorem contractionFaceBoundaryOutsideSubgraph_adj_right_ne_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x y : (GraphContraction.collapseEdge G hab).Target}
    (hxy : (contractionFaceBoundaryOutsideSubgraph hab R e).Adj x y) :
    y ≠ (none : (GraphContraction.collapseEdge G hab).Target) :=
  (contractionFaceBoundaryOutsideSubgraph hab R e).edge_vert hxy.symm |>.1

/-- The two-end deletion `G - a - b` maps into the contraction by the
same outside map as the explicit outside isomorphism. -/
noncomputable def deleteEdgeEndsGraphToCollapseEdgeHom
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    deleteEdgeEndsGraph G a b →g
      (GraphContraction.collapseEdge G hab).graph :=
  (deletedGraphToCollapseEdgeHom G hab).comp
    (deleteEdgeEndsGraphToDeletedGraphHom G a b)

@[simp]
theorem deleteEdgeEndsGraphToCollapseEdgeHom_apply
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (x : {z : V | z ∉ ({a, b} : Set V)}) :
    deleteEdgeEndsGraphToCollapseEdgeHom G hab x =
      (deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab x :
        (GraphContraction.collapseEdge G hab).Target) := by
  change deletedGraphToCollapseEdgeHom G hab (x : V) =
    (deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab x :
      (GraphContraction.collapseEdge G hab).Target)
  exact deletedGraphToCollapseEdgeHom_apply_outside (G := G) hab x

/-- The selected outside face-boundary subgraph transported back to the
two-end deletion `G - a - b`.  This is the graph object on which the later
cycle extraction runs before splitting the contracted vertex. -/
noncomputable def contractionFaceBoundaryDeleteEndsSubgraph
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (deleteEdgeEndsGraph G a b).Subgraph :=
  SimpleGraph.Subgraph.comap (deleteEdgeEndsGraphToCollapseEdgeHom G hab)
    (contractionFaceBoundaryOutsideSubgraph hab R e)

@[simp]
theorem contractionFaceBoundaryDeleteEndsSubgraph_verts
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (x : {z : V | z ∉ ({a, b} : Set V)}) :
    x ∈ (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts ↔
      deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∈
        (contractionFaceBoundaryOutsideSubgraph hab R e).verts :=
  Iff.rfl

@[simp]
theorem contractionFaceBoundaryDeleteEndsSubgraph_adj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (x y : {z : V | z ∉ ({a, b} : Set V)}) :
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x y ↔
      (deleteEdgeEndsGraph G a b).Adj x y ∧
        (contractionFaceBoundaryOutsideSubgraph hab R e).Adj
          (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
          (deleteEdgeEndsGraphToCollapseEdgeHom G hab y) :=
  Iff.rfl

theorem contractionFaceBoundaryDeleteEndsSubgraph_map_le_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).map
        (deleteEdgeEndsGraphToCollapseEdgeHom G hab) ≤
      contractionFaceBoundaryOutsideSubgraph hab R e := by
  rw [SimpleGraph.Subgraph.map_le_iff_le_comap]
  rfl

/-- The two-end deletion map into the contraction is injective, since it is
the explicit outside isomorphism on vertices. -/
theorem deleteEdgeEndsGraphToCollapseEdgeHom_injective
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    Function.Injective (deleteEdgeEndsGraphToCollapseEdgeHom G hab) := by
  intro x y hxy
  have hxy' :
      deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab x =
      deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab y := by
    apply Subtype.ext
    rw [← deleteEdgeEndsGraphToCollapseEdgeHom_apply (G := G) hab x,
      ← deleteEdgeEndsGraphToCollapseEdgeHom_apply (G := G) hab y]
    exact hxy
  exact
    (deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab).toEquiv.injective hxy'

/-- The transported boundary subgraph maps into the outside boundary subgraph
of the contraction. -/
noncomputable def contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe →g
      (contractionFaceBoundaryOutsideSubgraph hab R e).coe where
  toFun x :=
    ⟨deleteEdgeEndsGraphToCollapseEdgeHom G hab x.1, x.2⟩
  map_rel' := by
    intro x y hxy
    exact
      ((contractionFaceBoundaryDeleteEndsSubgraph_adj
        (G := G) hab R e x y).mp hxy).2

/-- The boundary-subgraph transport is injective. -/
theorem contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_injective
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    Function.Injective
      (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e) := by
  intro x y hxy
  apply Subtype.ext
  exact
    deleteEdgeEndsGraphToCollapseEdgeHom_injective
      (G := G) hab (congrArg Subtype.val hxy)

/-- A homeomorphic theta contained in the transported two-end boundary is also
a homeomorphic theta in the outside face-boundary subgraph of the contraction. -/
theorem ContainsHomeomorphicTheta.to_contractionFaceBoundaryOutsideSubgraph
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (h :
      ContainsHomeomorphicTheta
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe) :
    ContainsHomeomorphicTheta
      (contractionFaceBoundaryOutsideSubgraph hab R e).coe :=
  ContainsHomeomorphicTheta.map
    (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e)
    (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_injective hab R e)
    h

/-- Contrapositive form of the theta transport from the pulled-back boundary
to the outside contraction boundary. -/
theorem not_containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph_of_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hno :
      Not
        (ContainsHomeomorphicTheta
          (contractionFaceBoundaryOutsideSubgraph hab R e).coe)) :
    Not
      (ContainsHomeomorphicTheta
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe) := by
  intro htheta
  exact hno
    (ContainsHomeomorphicTheta.to_contractionFaceBoundaryOutsideSubgraph
      hab R e htheta)

/-- The general face-orbit no-theta theorem also rules out a homeomorphic
theta in the pulled-back two-end boundary. -/
theorem not_containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    Not
      (ContainsHomeomorphicTheta
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe) :=
  not_containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph_of_outside
    hab R e
    (not_containsHomeomorphicTheta_contractionFaceBoundaryOutsideSubgraph
      hface hab R hplanar e)

/-- Same-vertex form of the pulled-back boundary no-theta theorem.  The
spanning coercion only adds isolated vertices, so any theta there would already
live in the boundary `coe` graph. -/
theorem not_containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph_spanningCoe
    (hface : FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (hplanar : (R.toHypermap).EulerPlanar)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    Not
      (ContainsHomeomorphicTheta
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).spanningCoe) := by
  intro htheta
  exact
    not_containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph
      hface hab R hplanar e
      (ContainsHomeomorphicTheta.coe_of_spanningCoe
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e) htheta)

/-- If the whole two-end deletion contains a homeomorphic theta, but the
selected pulled-back boundary is theta-free by the face-orbit theorem, then
some edge used by the theta lies outside that boundary. -/
theorem exists_deleteEnds_theta_edge_not_boundary_of_faceOrbitNoTheta
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
    Exists fun edge : Sym2 {z : V | z ∉ ({a, b} : Set V)} =>
      edge ∈ (deleteEdgeEndsGraph G a b).edgeSet ∧
        edge ∉
          (contractionFaceBoundaryDeleteEndsSubgraph hab R e).spanningCoe.edgeSet :=
  ContainsHomeomorphicTheta.exists_edge_not_mem_edgeSet_of_not_contains
    htheta
    (not_containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph_spanningCoe
      hface hab R hplanar e)

/-- Endpoint form of `exists_deleteEnds_theta_edge_not_boundary_of_faceOrbitNoTheta`.
This is the Makarychev outside-edge datum in the two-end deletion, unpacked
from the `Sym2` edge so later split-face arguments can talk about the two
endpoints directly. -/
theorem exists_deleteEnds_theta_adj_not_boundary_of_faceOrbitNoTheta
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
    Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
        (deleteEdgeEndsGraph G a b).Adj x y ∧
          Not ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x y) := by
  rcases exists_deleteEnds_theta_edge_not_boundary_of_faceOrbitNoTheta
      hface hab R hplanar e htheta with
    ⟨edge, hedge, hnotBoundary⟩
  revert hedge hnotBoundary
  refine Sym2.ind ?_ edge
  intro x y hedge hnotBoundary
  have hxy : (deleteEdgeEndsGraph G a b).Adj x y := by
    rwa [SimpleGraph.mem_edgeSet] at hedge
  refine ⟨x, y, hxy, ?_⟩
  intro hboundary
  apply hnotBoundary
  rw [SimpleGraph.mem_edgeSet]
  simpa [SimpleGraph.Subgraph.spanningCoe] using hboundary

/-- Deleted-edge dart form of
`exists_deleteEnds_theta_adj_not_boundary_of_faceOrbitNoTheta`.  The outside
theta edge is oriented as a genuine dart of `G - ab`, with its image in the
contraction recorded explicitly. -/
theorem exists_deletedGraph_theta_dart_not_boundary_of_faceOrbitNoTheta
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
    Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
        Exists fun d : OrientedEdge (deletedGraph G a b) =>
          (deleteEdgeEndsGraph G a b).Adj x y ∧
            d.tail = (x : V) ∧
              d.head = (y : V) ∧
                (deletedGraphToCollapseEdgeDart G hab d).tail =
                    deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                  (deletedGraphToCollapseEdgeDart G hab d).head =
                    deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                    Not
                      ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj
                        x y) := by
  rcases exists_deleteEnds_theta_adj_not_boundary_of_faceOrbitNoTheta
      hface hab R hplanar e htheta with
    ⟨x, y, hxy, hnotBoundary⟩
  let d : OrientedEdge (deletedGraph G a b) :=
    ⟨(x, y), (deleteEdgeEndsGraphToDeletedGraphHom G a b).map_rel hxy⟩
  refine ⟨x, y, d, hxy, rfl, rfl, ?_, ?_, hnotBoundary⟩
  · rw [deletedGraphToCollapseEdgeDart_tail]
    rfl
  · rw [deletedGraphToCollapseEdgeDart_head]
    rfl

/-- Stronger deleted-edge dart form: the selected theta dart is outside both
the pulled-back two-end boundary and the corresponding outside edge of the
selected contraction face boundary. -/
theorem exists_deletedGraph_theta_dart_not_boundary_and_not_outsideBoundary_of_faceOrbitNoTheta
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
    Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
        Exists fun d : OrientedEdge (deletedGraph G a b) =>
          (deleteEdgeEndsGraph G a b).Adj x y ∧
            d.tail = (x : V) ∧
              d.head = (y : V) ∧
                (deletedGraphToCollapseEdgeDart G hab d).tail =
                    deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                  (deletedGraphToCollapseEdgeDart G hab d).head =
                    deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                    Not
                      ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj
                        x y) ∧
                      Not
                        ((contractionFaceBoundaryOutsideSubgraph hab R e).Adj
                          (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
                          (deleteEdgeEndsGraphToCollapseEdgeHom G hab y)) := by
  rcases exists_deletedGraph_theta_dart_not_boundary_of_faceOrbitNoTheta
      hface hab R hplanar e htheta with
    ⟨x, y, d, hxy, hd_tail, hd_head, hd_collapse_tail,
      hd_collapse_head, hnotBoundary⟩
  refine
    ⟨x, y, d, hxy, hd_tail, hd_head, hd_collapse_tail,
      hd_collapse_head, hnotBoundary, ?_⟩
  intro hout
  exact hnotBoundary
    ((contractionFaceBoundaryDeleteEndsSubgraph_adj
      (G := G) hab R e x y).mpr ⟨hxy, hout⟩)

/-- If an outside deleted-edge dart maps to an edge that is not in the
outside selected face-boundary subgraph, then the mapped dart is not a member
of the selected face orbit. -/
theorem not_mem_contractionFaceBoundary_of_not_outsideBoundary_adj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x y : {z : V | z ∉ ({a, b} : Set V)}}
    {d : OrientedEdge (deletedGraph G a b)}
    (hd_tail :
      (deletedGraphToCollapseEdgeDart G hab d).tail =
        deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
    (hd_head :
      (deletedGraphToCollapseEdgeDart G hab d).head =
        deleteEdgeEndsGraphToCollapseEdgeHom G hab y)
    (hnotOutside :
      Not
        ((contractionFaceBoundaryOutsideSubgraph hab R e).Adj
          (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
          (deleteEdgeEndsGraphToCollapseEdgeHom G hab y))) :
    deletedGraphToCollapseEdgeDart G hab d ∉
      contractionFaceBoundary hab R e := by
  intro hmem
  have hx_ne :
      deleteEdgeEndsGraphToCollapseEdgeHom G hab x ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    change deletedGraphToCollapseEdgeHom G hab (x : V) ≠
      (none : (GraphContraction.collapseEdge G hab).Target)
    exact (deletedGraphToCollapseEdgeHom_ne_none_iff (G := G) hab).mpr x.2
  have hy_ne :
      deleteEdgeEndsGraphToCollapseEdgeHom G hab y ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    change deletedGraphToCollapseEdgeHom G hab (y : V) ≠
      (none : (GraphContraction.collapseEdge G hab).Target)
    exact (deletedGraphToCollapseEdgeHom_ne_none_iff (G := G) hab).mpr y.2
  exact hnotOutside
    (by
      simpa [hd_tail, hd_head] using
        contractionFaceBoundaryOutsideSubgraph_adj_of_mem
          hab R e (deletedGraphToCollapseEdgeDart G hab d)
          hmem (by simpa [hd_tail] using hx_ne)
          (by simpa [hd_head] using hy_ne))

/-- Face-orbit form of the Makarychev outside-the-boundary theta dart: the
selected theta dart maps to a contraction dart that is not on the selected
face orbit. -/
theorem exists_deletedGraph_theta_dart_not_boundary_and_not_faceBoundary_of_faceOrbitNoTheta
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
    Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
        Exists fun d : OrientedEdge (deletedGraph G a b) =>
          (deleteEdgeEndsGraph G a b).Adj x y ∧
            d.tail = (x : V) ∧
              d.head = (y : V) ∧
                (deletedGraphToCollapseEdgeDart G hab d).tail =
                    deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                  (deletedGraphToCollapseEdgeDart G hab d).head =
                    deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                    Not
                      ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj
                        x y) ∧
                      Not
                        ((contractionFaceBoundaryOutsideSubgraph hab R e).Adj
                          (deleteEdgeEndsGraphToCollapseEdgeHom G hab x)
                          (deleteEdgeEndsGraphToCollapseEdgeHom G hab y)) ∧
                        deletedGraphToCollapseEdgeDart G hab d ∉
                          contractionFaceBoundary hab R e := by
  rcases
      exists_deletedGraph_theta_dart_not_boundary_and_not_outsideBoundary_of_faceOrbitNoTheta
        hface hab R hplanar e htheta with
    ⟨x, y, d, hxy, hd_tail, hd_head, hd_collapse_tail,
      hd_collapse_head, hnotBoundary, hnotOutsideBoundary⟩
  have hnotFace :
      deletedGraphToCollapseEdgeDart G hab d ∉
        contractionFaceBoundary hab R e :=
    not_mem_contractionFaceBoundary_of_not_outsideBoundary_adj
      (G := G) hab R e hd_collapse_tail hd_collapse_head
      hnotOutsideBoundary
  exact
    ⟨x, y, d, hxy, hd_tail, hd_head, hd_collapse_tail,
      hd_collapse_head, hnotBoundary, hnotOutsideBoundary, hnotFace⟩

/-- Any vertex of the outside contraction boundary has a concrete preimage in
the transported two-end-deletion boundary. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_vert_of_outside_vert
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x : (GraphContraction.collapseEdge G hab).Target}
    (hx : x ∈ (contractionFaceBoundaryOutsideSubgraph hab R e).verts) :
    Exists fun x' : {z : V | z ∉ ({a, b} : Set V)} =>
      deleteEdgeEndsGraphToCollapseEdgeHom G hab x' = x ∧
        x' ∈ (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts := by
  have hx_ne :
      x ≠ (none : (GraphContraction.collapseEdge G hab).Target) :=
    contractionFaceBoundaryOutsideSubgraph_vert_ne_none
      (G := G) hab R e hx
  rcases collapseEdgeTarget_outside_of_ne_none
      G hab hx_ne with ⟨xv, hxv, hxv_eq⟩
  let x' : {z : V | z ∉ ({a, b} : Set V)} := ⟨xv, hxv⟩
  have hxmap : deleteEdgeEndsGraphToCollapseEdgeHom G hab x' = x := by
    change deletedGraphToCollapseEdgeHom G hab (xv : V) = x
    rw [deletedGraphToCollapseEdgeHom_apply_outside
      (G := G) hab x']
    simpa [deleteEdgeEndsGraphCollapseEdgeOutsideIso, x'] using hxv_eq.symm
  have hxvert :
      x' ∈ (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts := by
    rw [contractionFaceBoundaryDeleteEndsSubgraph_verts]
    rw [hxmap]
    exact hx
  exact ⟨x', hxmap, hxvert⟩

/-- The transported boundary hom is surjective on vertices: every outside
boundary vertex in the contraction has a two-end-deletion preimage. -/
theorem contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_surjective
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    Function.Surjective
      (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e) := by
  intro x
  rcases exists_contractionFaceBoundaryDeleteEndsSubgraph_vert_of_outside_vert
      (G := G) hab R e x.2 with ⟨x0, hx0map, hx0vert⟩
  refine ⟨⟨x0, hx0vert⟩, ?_⟩
  apply Subtype.ext
  exact hx0map

/-- Any edge of the outside contraction boundary has concrete preimages in
the transported two-end-deletion boundary.  This is the edge-level pullback
used later to lift boundary walks and cycles from `G / ab` back to
`G - a - b`. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_adj_of_outside_adj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x y : (GraphContraction.collapseEdge G hab).Target}
    (hx : x ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hy : y ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hxy : (contractionFaceBoundaryOutsideSubgraph hab R e).Adj x y) :
    Exists fun x' : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y' : {z : V | z ∉ ({a, b} : Set V)} =>
        deleteEdgeEndsGraphToCollapseEdgeHom G hab x' = x ∧
          deleteEdgeEndsGraphToCollapseEdgeHom G hab y' = y ∧
            (contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x' y' := by
  rcases collapseEdgeTarget_outside_of_ne_none
      G hab hx with ⟨xv, hxv, hxv_eq⟩
  rcases collapseEdgeTarget_outside_of_ne_none
      G hab hy with ⟨yv, hyv, hyv_eq⟩
  let x' : {z : V | z ∉ ({a, b} : Set V)} := ⟨xv, hxv⟩
  let y' : {z : V | z ∉ ({a, b} : Set V)} := ⟨yv, hyv⟩
  have hxmap : deleteEdgeEndsGraphToCollapseEdgeHom G hab x' = x := by
    change deletedGraphToCollapseEdgeHom G hab (xv : V) = x
    rw [deletedGraphToCollapseEdgeHom_apply_outside
      (G := G) hab x']
    simpa [deleteEdgeEndsGraphCollapseEdgeOutsideIso, x'] using hxv_eq.symm
  have hymap : deleteEdgeEndsGraphToCollapseEdgeHom G hab y' = y := by
    change deletedGraphToCollapseEdgeHom G hab (yv : V) = y
    rw [deletedGraphToCollapseEdgeHom_apply_outside
      (G := G) hab y']
    simpa [deleteEdgeEndsGraphCollapseEdgeOutsideIso, y'] using hyv_eq.symm
  have hout_xy :
      (contractionFaceBoundaryOutsideSubgraph hab R e).Adj
        (deleteEdgeEndsGraphToCollapseEdgeHom G hab x')
        (deleteEdgeEndsGraphToCollapseEdgeHom G hab y') := by
    rw [hxmap, hymap]
    exact hxy
  have hxiso :
      ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab x' :
        (GraphContraction.collapseEdge G hab).Target)) =
          deleteEdgeEndsGraphToCollapseEdgeHom G hab x' := by
    simpa using
      (deleteEdgeEndsGraphToCollapseEdgeHom_apply (G := G) hab x').symm
  have hyiso :
      ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab y' :
        (GraphContraction.collapseEdge G hab).Target)) =
          deleteEdgeEndsGraphToCollapseEdgeHom G hab y' := by
    simpa using
      (deleteEdgeEndsGraphToCollapseEdgeHom_apply (G := G) hab y').symm
  have htarget_adj :
      ((GraphContraction.collapseEdge G hab).graph.induce
        {z : (GraphContraction.collapseEdge G hab).Target |
          z ≠ (none : (GraphContraction.collapseEdge G hab).Target)}).Adj
        ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab) x')
        ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab) y') := by
    change (GraphContraction.collapseEdge G hab).graph.Adj
      ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab x' :
        (GraphContraction.collapseEdge G hab).Target))
      ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab y' :
        (GraphContraction.collapseEdge G hab).Target))
    rw [hxiso, hyiso]
    exact (contractionFaceBoundaryOutsideSubgraph hab R e).adj_sub hout_xy
  have hdelete_adj : (deleteEdgeEndsGraph G a b).Adj x' y' := by
    exact
      ((deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab).map_adj_iff).mp
        htarget_adj
  have hboundary_adj :
      (contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x' y' :=
    (contractionFaceBoundaryDeleteEndsSubgraph_adj
      (G := G) hab R e x' y').mpr ⟨hdelete_adj, hout_xy⟩
  exact ⟨x', y', hxmap, hymap, hboundary_adj⟩

/-- The transported boundary hom reflects adjacency, so it is an induced
isomorphism onto the outside boundary rather than only an injective hom. -/
theorem contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_adj_iff
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (x y : (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts) :
    (contractionFaceBoundaryOutsideSubgraph hab R e).coe.Adj
        (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e x)
        (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e y) ↔
      (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Adj x y := by
  let Hout := contractionFaceBoundaryOutsideSubgraph hab R e
  let Hdel := contractionFaceBoundaryDeleteEndsSubgraph hab R e
  let φ := contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e
  constructor
  · intro hxy
    have hx_ne :
        ((φ x : Hout.verts) :
            (GraphContraction.collapseEdge G hab).Target) ≠
          (none : (GraphContraction.collapseEdge G hab).Target) :=
      contractionFaceBoundaryOutsideSubgraph_vert_ne_none
        (G := G) hab R e (φ x).2
    have hy_ne :
        ((φ y : Hout.verts) :
            (GraphContraction.collapseEdge G hab).Target) ≠
          (none : (GraphContraction.collapseEdge G hab).Target) :=
      contractionFaceBoundaryOutsideSubgraph_vert_ne_none
        (G := G) hab R e (φ y).2
    have hxy_out :
        Hout.Adj
          ((φ x : Hout.verts) :
            (GraphContraction.collapseEdge G hab).Target)
          ((φ y : Hout.verts) :
            (GraphContraction.collapseEdge G hab).Target) := by
      exact hxy
    rcases exists_contractionFaceBoundaryDeleteEndsSubgraph_adj_of_outside_adj
        (G := G) hab R e hx_ne hy_ne hxy_out with
      ⟨x0, y0, hx0map, hy0map, hdel⟩
    let x0S : Hdel.verts := ⟨x0, Hdel.edge_vert hdel⟩
    let y0S : Hdel.verts := ⟨y0, Hdel.edge_vert hdel.symm⟩
    have hx0S_map : φ x0S = φ x := by
      apply Subtype.ext
      exact hx0map
    have hy0S_map : φ y0S = φ y := by
      apply Subtype.ext
      exact hy0map
    have hx_eq : x0S = x :=
      contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_injective
        (G := G) hab R e hx0S_map
    have hy_eq : y0S = y :=
      contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_injective
        (G := G) hab R e hy0S_map
    have hdel_coe : Hdel.coe.Adj x0S y0S := by
      exact hdel
    simpa [hx_eq, hy_eq] using hdel_coe
  · intro hxy
    exact
      (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e).map_rel
        hxy

/-- The transported boundary in `G - a - b` is graph-isomorphic to the outside
part of the selected contraction face boundary. -/
noncomputable def contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe ≃g
      (contractionFaceBoundaryOutsideSubgraph hab R e).coe where
  toEquiv :=
    Equiv.ofBijective
      (contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e)
      ⟨contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_injective
          (G := G) hab R e,
        contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_surjective
          (G := G) hab R e⟩
  map_rel_iff' := by
    intro x y
    simpa using
      contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_adj_iff
        (G := G) hab R e x y

/-- Connected components of the transported two-end boundary correspond to
connected components of the outside contraction boundary. -/
noncomputable def contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.ConnectedComponent ≃
      (contractionFaceBoundaryOutsideSubgraph hab R e).coe.ConnectedComponent :=
  (contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
    (G := G) hab R e).connectedComponentEquiv

/-- A vertex belongs to a transported-boundary component exactly when its
image belongs to the corresponding outside-boundary component. -/
theorem contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv_mem
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (C :
      (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.ConnectedComponent)
    (x : (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts) :
    (contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
        (G := G) hab R e x) ∈
      (contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv
        (G := G) hab R e C).supp ↔
      x ∈ C.supp := by
  let φ := contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
    (G := G) hab R e
  change
    (contractionFaceBoundaryOutsideSubgraph hab R e).coe.connectedComponentMk
        (φ x) =
      (φ.connectedComponentEquiv C) ↔
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.connectedComponentMk
        x =
      C
  simpa using
    (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
      (φ := φ) (v := x) (C := C))

/-- The transported two-end boundary contains a homeomorphic theta exactly
when the outside contraction boundary does. -/
theorem containsHomeomorphicTheta_contractionFaceBoundaryDeleteEndsSubgraph_iff_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    ContainsHomeomorphicTheta
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe ↔
      ContainsHomeomorphicTheta
        (contractionFaceBoundaryOutsideSubgraph hab R e).coe := by
  constructor
  · intro htheta
    exact
      ContainsHomeomorphicTheta.to_contractionFaceBoundaryOutsideSubgraph
        hab R e htheta
  · intro htheta
    let φ :=
      (contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
        (G := G) hab R e).symm
    exact
      ContainsHomeomorphicTheta.map
        φ.toRelEmbedding.toRelHom φ.toEquiv.injective htheta

/-- Existence of a simple cycle is invariant across the transported-boundary
isomorphism. -/
theorem exists_cycle_contractionFaceBoundaryDeleteEndsSubgraph_iff_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (Exists fun x :
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
      Exists fun c :
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Walk x x =>
        c.IsCycle) ↔
      (Exists fun x :
          (contractionFaceBoundaryOutsideSubgraph hab R e).verts =>
        Exists fun c :
          (contractionFaceBoundaryOutsideSubgraph hab R e).coe.Walk x x =>
          c.IsCycle) := by
  constructor
  · rintro ⟨x, c, hc⟩
    let φ := contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
      (G := G) hab R e
    exact
      ⟨φ x, c.map φ.toHom,
        SimpleGraph.Walk.IsCycle.map
          (p := c) (f := φ.toHom) φ.toEquiv.injective hc⟩
  · rintro ⟨x, c, hc⟩
    let φ := (contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
      (G := G) hab R e).symm
    exact
      ⟨φ x, c.map φ.toHom,
        SimpleGraph.Walk.IsCycle.map
          (p := c) (f := φ.toHom) φ.toEquiv.injective hc⟩

/-- Cycle existence inside a named boundary component is invariant across the
transported-boundary isomorphism. -/
theorem exists_cycle_contractionFaceBoundaryDeleteEndsSubgraph_component_iff_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (C :
      (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.ConnectedComponent) :
    (Exists fun x :
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
      x ∈ C.supp ∧
        Exists fun c :
          (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Walk x x =>
          c.IsCycle) ↔
      (Exists fun x :
          (contractionFaceBoundaryOutsideSubgraph hab R e).verts =>
        x ∈
            (contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv
              (G := G) hab R e C).supp ∧
          Exists fun c :
            (contractionFaceBoundaryOutsideSubgraph hab R e).coe.Walk x x =>
            c.IsCycle) := by
  let φ := contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
    (G := G) hab R e
  constructor
  · rintro ⟨x, hxC, c, hc⟩
    have hxC' :
        φ x ∈
          (contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv
            (G := G) hab R e C).supp := by
      exact
        (contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv_mem
          (G := G) hab R e C x).mpr hxC
    exact
      ⟨φ x, hxC', c.map φ.toHom,
        SimpleGraph.Walk.IsCycle.map
          (p := c) (f := φ.toHom) φ.toEquiv.injective hc⟩
  · rintro ⟨x, hxC, c, hc⟩
    have hxC' : φ.symm x ∈ C.supp := by
      change
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.connectedComponentMk
            (φ.symm x) =
          C
      simpa [contractionFaceBoundaryDeleteEndsSubgraphOutsideComponentEquiv,
        φ] using
        (SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map
          (φ := φ) (v' := x) (C := C)).mpr hxC
    exact
      ⟨φ.symm x, hxC', c.map φ.symm.toHom,
        SimpleGraph.Walk.IsCycle.map
          (p := c) (f := φ.symm.toHom) φ.symm.toEquiv.injective hc⟩


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
