import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.BoundarySubgraph


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- Concrete extraction form: a simple cycle in the outside contraction
boundary selects the corresponding connected component of the transported
two-end boundary and a lifted simple-cycle witness in that component. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_cycle_component_of_outside_cycle
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x : (contractionFaceBoundaryOutsideSubgraph hab R e).verts}
    (c : (contractionFaceBoundaryOutsideSubgraph hab R e).coe.Walk x x)
    (hc : c.IsCycle) :
    Exists fun C :
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.ConnectedComponent =>
      Exists fun x' :
          (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
        x' ∈ C.supp ∧
          contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e x' = x ∧
            Exists fun c' :
              (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Walk x' x' =>
              c'.IsCycle := by
  let φ := contractionFaceBoundaryDeleteEndsSubgraphOutsideIso
    (G := G) hab R e
  let x' : (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts := φ.symm x
  let C : (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.ConnectedComponent :=
    (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.connectedComponentMk x'
  have hx'C : x' ∈ C.supp := by
    simpa [C] using
      (SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        (G := (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe)
        (v := x'))
  have hx'map :
      contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e x' = x := by
    change φ x' = x
    exact φ.toEquiv.apply_symm_apply x
  exact
    ⟨C, x', hx'C, hx'map, c.map φ.symm.toHom,
      SimpleGraph.Walk.IsCycle.map
        (p := c) (f := φ.symm.toHom) φ.symm.toEquiv.injective hc⟩

/-- If the outside contraction boundary contains a homeomorphic theta, then
the transported two-end boundary has a named connected component containing a
simple cycle. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_cycle_component_of_outside_homeomorphicTheta
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hθ :
      ContainsHomeomorphicTheta
        (contractionFaceBoundaryOutsideSubgraph hab R e).coe) :
    Exists fun C :
        (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.ConnectedComponent =>
      Exists fun x' :
          (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
        x' ∈ C.supp ∧
          Exists fun c' :
            (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Walk x' x' =>
            c'.IsCycle := by
  rcases ContainsHomeomorphicTheta.exists_isCycle hθ with ⟨x, c, hc⟩
  rcases
      exists_contractionFaceBoundaryDeleteEndsSubgraph_cycle_component_of_outside_cycle
        (G := G) hab R e c hc with
    ⟨C, x', hx'C, _hx'map, c', hc'⟩
  exact ⟨C, x', hx'C, c', hc'⟩

/-- Walk-level form of the outside-boundary pullback.  Any walk in the
outside face-boundary subgraph of the contraction lifts to a walk in the
transported two-end-deletion boundary, with endpoints mapping to the original
endpoints. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_walk_of_outside_walk
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x y : (contractionFaceBoundaryOutsideSubgraph hab R e).verts}
    (p : (contractionFaceBoundaryOutsideSubgraph hab R e).coe.Walk x y) :
    Exists fun x' : (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
      Exists fun y' :
          (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
        contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e x' = x ∧
          contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e y' = y ∧
            Nonempty
              ((contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Walk
                x' y') := by
  let Hout := contractionFaceBoundaryOutsideSubgraph hab R e
  let Hdel := contractionFaceBoundaryDeleteEndsSubgraph hab R e
  let φ := contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e
  induction p with
  | @nil u =>
      rcases exists_contractionFaceBoundaryDeleteEndsSubgraph_vert_of_outside_vert
          (G := G) hab R e u.2 with ⟨x0, hx0map, hx0vert⟩
      let x0S : Hdel.verts := ⟨x0, hx0vert⟩
      have hx0S_map : φ x0S = u := by
        apply Subtype.ext
        exact hx0map
      exact ⟨x0S, x0S, hx0S_map, hx0S_map, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons u v w huv p ih =>
      have hu_ne :
          (u : (GraphContraction.collapseEdge G hab).Target) ≠
            (none : (GraphContraction.collapseEdge G hab).Target) :=
        contractionFaceBoundaryOutsideSubgraph_vert_ne_none
          (G := G) hab R e u.2
      have hv_ne :
          (v : (GraphContraction.collapseEdge G hab).Target) ≠
            (none : (GraphContraction.collapseEdge G hab).Target) :=
        contractionFaceBoundaryOutsideSubgraph_vert_ne_none
          (G := G) hab R e v.2
      have huv_out :
          (contractionFaceBoundaryOutsideSubgraph hab R e).Adj
            (u : (GraphContraction.collapseEdge G hab).Target)
            (v : (GraphContraction.collapseEdge G hab).Target) := by
        exact huv
      rcases exists_contractionFaceBoundaryDeleteEndsSubgraph_adj_of_outside_adj
          (G := G) hab R e hu_ne hv_ne huv_out with
        ⟨u0, v0, hu0map, hv0map, huv0⟩
      let u0S : Hdel.verts := ⟨u0, Hdel.edge_vert huv0⟩
      let v0S : Hdel.verts := ⟨v0, Hdel.edge_vert huv0.symm⟩
      have huv0_coe : Hdel.coe.Adj u0S v0S := by
        exact huv0
      have hu0S_map : φ u0S = u := by
        apply Subtype.ext
        exact hu0map
      have hv0S_map : φ v0S = v := by
        apply Subtype.ext
        exact hv0map
      rcases ih with ⟨vTail, wTail, hvTail_map, hwTail_map, ⟨qTail⟩⟩
      have hv_eq : v0S = vTail := by
        apply contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom_injective
          (G := G) hab R e
        exact hv0S_map.trans hvTail_map.symm
      subst vTail
      exact
        ⟨u0S, wTail, hu0S_map, hwTail_map,
          ⟨SimpleGraph.Walk.cons huv0_coe qTail⟩⟩

/-- Reachability form of the outside-boundary pullback. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_reachable_of_outside_reachable
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    {x y : (contractionFaceBoundaryOutsideSubgraph hab R e).verts}
    (hxy :
      (contractionFaceBoundaryOutsideSubgraph hab R e).coe.Reachable x y) :
    Exists fun x' : (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
      Exists fun y' :
          (contractionFaceBoundaryDeleteEndsSubgraph hab R e).verts =>
        contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e x' = x ∧
          contractionFaceBoundaryDeleteEndsSubgraphToOutsideHom hab R e y' = y ∧
            (contractionFaceBoundaryDeleteEndsSubgraph hab R e).coe.Reachable
              x' y' := by
  rcases hxy with ⟨p⟩
  rcases exists_contractionFaceBoundaryDeleteEndsSubgraph_walk_of_outside_walk
      (G := G) hab R e p with ⟨x', y', hx', hy', hwalk⟩
  exact ⟨x', y', hx', hy', hwalk⟩

theorem contractionFaceBoundary_face_mem_of_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e) :
    (R.toHypermap).face d ∈ contractionFaceBoundary hab R e := by
  change (R.toHypermap).face d ∈ (R.toHypermap).faceOrbitList e
  exact Hypermap.faceOrbitList_face_mem (G := R.toHypermap)
    (x := e) (y := d) hd

theorem contractionFaceBoundary_face_symm_mem_of_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e) :
    (R.toHypermap).face.symm d ∈ contractionFaceBoundary hab R e := by
  change (R.toHypermap).face.symm d ∈ (R.toHypermap).faceOrbitList e
  exact Hypermap.faceOrbitList_face_symm_mem (G := R.toHypermap)
    (x := e) (y := d) hd

theorem contractionFaceBoundary_face_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (R.toHypermap).face e ∈ contractionFaceBoundary hab R e :=
  contractionFaceBoundary_face_mem_of_mem hab R e e
    (contractionFaceBoundary_self_mem hab R e)

/-- If a boundary dart and its face successor both stay outside the collapsed
vertex at the shared corner, then the outside boundary subgraph contains the
corresponding face-step edge.  This is the local walk step for the selected
face boundary. -/
theorem contractionFaceBoundaryOutsideSubgraph_face_step_adj
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
      d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hnext_head :
      ((R.toHypermap).face d).head ≠
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    (contractionFaceBoundaryOutsideSubgraph hab R e).Adj
      d.head ((R.toHypermap).face d).head := by
  have hnext_mem :
      (R.toHypermap).face d ∈ contractionFaceBoundary hab R e :=
    contractionFaceBoundary_face_mem_of_mem hab R e d hd
  have htail_eq :
      ((R.toHypermap).face d).tail = d.head :=
    RotationSystem.toHypermap_face_tail R d
  have hnext_tail :
      ((R.toHypermap).face d).tail ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    simpa [htail_eq] using hhead
  have hstep :
      (contractionFaceBoundaryOutsideSubgraph hab R e).Adj
        ((R.toHypermap).face d).tail ((R.toHypermap).face d).head :=
    contractionFaceBoundaryOutsideSubgraph_adj_of_mem
      hab R e ((R.toHypermap).face d) hnext_mem hnext_tail hnext_head
  simpa [htail_eq] using hstep

/-- Pull one forward face-boundary step back to the two-end deletion.  The
two produced vertices are the outside preimages of the current corner and the
next face-step head. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_face_step_adj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (hhead :
      d.head ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (hnext_head :
      ((R.toHypermap).face d).head ≠
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
        deleteEdgeEndsGraphToCollapseEdgeHom G hab x = d.head ∧
          deleteEdgeEndsGraphToCollapseEdgeHom G hab y =
            ((R.toHypermap).face d).head ∧
            (contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x y := by
  exact exists_contractionFaceBoundaryDeleteEndsSubgraph_adj_of_outside_adj
    (G := G) hab R e hhead hnext_head
      (contractionFaceBoundaryOutsideSubgraph_face_step_adj
        hab R e d hd hhead hnext_head)

theorem contractionFaceBoundary_face_symm_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (R.toHypermap).face.symm e ∈ contractionFaceBoundary hab R e :=
  contractionFaceBoundary_face_symm_mem_of_mem hab R e e
    (contractionFaceBoundary_self_mem hab R e)

/-- Reverse form of `contractionFaceBoundaryOutsideSubgraph_face_step_adj`:
the face predecessor gives the outside-boundary edge ending at the current
dart tail when the relevant endpoints avoid the collapsed vertex. -/
theorem contractionFaceBoundaryOutsideSubgraph_face_symm_step_adj
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (hprev_tail :
      ((R.toHypermap).face.symm d).tail ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (htail :
      d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    (contractionFaceBoundaryOutsideSubgraph hab R e).Adj
      ((R.toHypermap).face.symm d).tail d.tail := by
  let p : OrientedEdge (GraphContraction.collapseEdge G hab).graph :=
    (R.toHypermap).face.symm d
  have hp_mem : p ∈ contractionFaceBoundary hab R e := by
    change (R.toHypermap).face.symm d ∈ contractionFaceBoundary hab R e
    exact contractionFaceBoundary_face_symm_mem_of_mem hab R e d hd
  have hp_head_eq : p.head = d.tail := by
    have h := RotationSystem.toHypermap_face_tail R p
    simpa [p] using h.symm
  have hp_head :
      p.head ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
    simpa [hp_head_eq] using htail
  have hstep :
      (contractionFaceBoundaryOutsideSubgraph hab R e).Adj p.tail p.head :=
    contractionFaceBoundaryOutsideSubgraph_adj_of_mem
      hab R e p hp_mem (by simpa [p] using hprev_tail) hp_head
  simpa [p, hp_head_eq] using hstep

/-- Pull one reverse face-boundary step back to the two-end deletion.  The
two produced vertices are the outside preimages of the predecessor tail and
the current dart tail. -/
theorem exists_contractionFaceBoundaryDeleteEndsSubgraph_face_symm_step_adj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e)
    (hprev_tail :
      ((R.toHypermap).face.symm d).tail ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (htail :
      d.tail ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
      Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
        deleteEdgeEndsGraphToCollapseEdgeHom G hab x =
          ((R.toHypermap).face.symm d).tail ∧
          deleteEdgeEndsGraphToCollapseEdgeHom G hab y = d.tail ∧
            (contractionFaceBoundaryDeleteEndsSubgraph hab R e).Adj x y := by
  exact exists_contractionFaceBoundaryDeleteEndsSubgraph_adj_of_outside_adj
    (G := G) hab R e hprev_tail htail
      (contractionFaceBoundaryOutsideSubgraph_face_symm_step_adj
        hab R e d hd hprev_tail htail)

/-- If a boundary dart leaves the collapsed vertex, the next dart on the same
face has a named outside tail and remains on the selected boundary. -/
theorem contractionFaceBoundary_face_tail_outside_of_tail_none
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
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        ((R.toHypermap).face d).tail =
            GraphContraction.collapseEdgeOutside G hab v hv ∧
          (R.toHypermap).face d ∈ contractionFaceBoundary hab R e := by
  rcases collapseEdgeDart_head_outside_of_tail_none
      (G := G) hab d htail with ⟨v, hv, hhead⟩
  refine ⟨v, hv, ?_, ?_⟩
  · exact (RotationSystem.toHypermap_face_tail R d).trans hhead
  · exact contractionFaceBoundary_face_mem_of_mem hab R e d hd

/-- If a boundary dart enters the collapsed vertex, the previous dart on the
same face has a named outside head and remains on the selected boundary. -/
theorem contractionFaceBoundary_face_symm_head_outside_of_head_none
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
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        ((R.toHypermap).face.symm d).head =
            GraphContraction.collapseEdgeOutside G hab v hv ∧
          (R.toHypermap).face.symm d ∈ contractionFaceBoundary hab R e := by
  rcases collapseEdgeDart_tail_outside_of_head_none
      (G := G) hab d hhead with ⟨v, hv, htail⟩
  refine ⟨v, hv, ?_, ?_⟩
  · have hprev_head :
        ((R.toHypermap).face.symm d).head = d.tail := by
      have hface :=
        RotationSystem.toHypermap_face_tail R ((R.toHypermap).face.symm d)
      simpa using hface.symm
    exact hprev_head.trans htail
  · exact contractionFaceBoundary_face_symm_mem_of_mem hab R e d hd

/-- Around a contraction face, the predecessor of a dart leaving the collapsed
vertex is a dart entering the collapsed vertex. -/
theorem contractionFaceBoundary_face_symm_head_none_of_tail_none
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
    ((R.toHypermap).face.symm d).head =
        (none : (GraphContraction.collapseEdge G hab).Target) ∧
      (R.toHypermap).face.symm d ∈ contractionFaceBoundary hab R e := by
  have hprev_head :
      ((R.toHypermap).face.symm d).head = d.tail := by
    have hface :=
      RotationSystem.toHypermap_face_tail R ((R.toHypermap).face.symm d)
    simpa using hface.symm
  exact
    ⟨hprev_head.trans htail,
      contractionFaceBoundary_face_symm_mem_of_mem hab R e d hd⟩

/-- Around a contraction face, the successor of a dart entering the collapsed
vertex is a dart leaving the collapsed vertex. -/
theorem contractionFaceBoundary_face_tail_none_of_head_none
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
    ((R.toHypermap).face d).tail =
        (none : (GraphContraction.collapseEdge G hab).Target) ∧
      (R.toHypermap).face d ∈ contractionFaceBoundary hab R e := by
  exact
    ⟨(RotationSystem.toHypermap_face_tail R d).trans hhead,
      contractionFaceBoundary_face_mem_of_mem hab R e d hd⟩

/-- A boundary dart leaving the collapsed vertex has a face-successor lift to
the deleted-edge graph whose tail is outside the split pair. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_face_of_boundary_tail_none
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
    Exists fun d' : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d' = (R.toHypermap).face d ∧
        d'.tail ∉ ({a, b} : Set V) ∧
          (R.toHypermap).face d ∈ contractionFaceBoundary hab R e := by
  rcases contractionFaceBoundary_face_tail_outside_of_tail_none
      (G := G) hab R e d hd htail with ⟨v, hv, hface_tail, hface_mem⟩
  rcases deletedGraphToCollapseEdgeDart_surjective
      (G := G) hab ((R.toHypermap).face d) with ⟨d', hd'⟩
  refine ⟨d', hd', ?_, hface_mem⟩
  have htail_eq :
      (deletedGraphToCollapseEdgeDart G hab d').tail =
        ((R.toHypermap).face d).tail :=
    congrArg OrientedEdge.tail hd'
  have htail_ne :
      (deletedGraphToCollapseEdgeDart G hab d').tail ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    rw [htail_eq, hface_tail]
    intro hnone
    cases hnone
  exact
    (deletedGraphToCollapseEdgeDart_tail_ne_none_iff
      (G := G) hab d').mp htail_ne

/-- A boundary dart entering the collapsed vertex has a face-predecessor lift
to the deleted-edge graph whose head is outside the split pair. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_face_symm_of_boundary_head_none
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
    Exists fun d' : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d' = (R.toHypermap).face.symm d ∧
        d'.head ∉ ({a, b} : Set V) ∧
          (R.toHypermap).face.symm d ∈ contractionFaceBoundary hab R e := by
  rcases contractionFaceBoundary_face_symm_head_outside_of_head_none
      (G := G) hab R e d hd hhead with ⟨v, hv, hface_head, hface_mem⟩
  rcases deletedGraphToCollapseEdgeDart_surjective
      (G := G) hab ((R.toHypermap).face.symm d) with ⟨d', hd'⟩
  refine ⟨d', hd', ?_, hface_mem⟩
  have hhead_eq :
      (deletedGraphToCollapseEdgeDart G hab d').head =
        ((R.toHypermap).face.symm d).head :=
    congrArg OrientedEdge.head hd'
  have hhead_ne :
      (deletedGraphToCollapseEdgeDart G hab d').head ≠
        (none : (GraphContraction.collapseEdge G hab).Target) := by
    rw [hhead_eq, hface_head]
    intro hnone
    cases hnone
  exact
    (deletedGraphToCollapseEdgeDart_head_ne_none_iff
      (G := G) hab d').mp hhead_ne


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
