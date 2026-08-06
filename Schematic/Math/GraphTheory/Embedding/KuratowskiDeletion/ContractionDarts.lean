import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.SubdivisionDeletion


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The two-end deletion is exactly the part of the edge contraction outside
the collapsed endpoint.  This is the graph-theoretic identity used in the
Makarychev/Skopenkov theta branch before the face-boundary argument. -/
noncomputable def deleteEdgeEndsGraphCollapseEdgeOutsideIso
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    deleteEdgeEndsGraph G a b ≃g
      (GraphContraction.collapseEdge G hab).graph.induce
        {y : (GraphContraction.collapseEdge G hab).Target |
          y ≠ (none : (GraphContraction.collapseEdge G hab).Target)} :=
  GraphContraction.collapseEdgeOutsideIso G hab

/-- On vertices outside `a,b`, the quotient map `G - ab → G / ab` agrees
with the explicit outside isomorphism. -/
@[simp]
theorem EdgeDeletion.deletedGraphToCollapseEdgeHom_apply_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (x : {z : V | z ∉ ({a, b} : Set V)}) :
    EdgeDeletion.deletedGraphToCollapseEdgeHom G hab (x : V) =
      (deleteEdgeEndsGraphCollapseEdgeOutsideIso (G := G) hab x :
        (GraphContraction.collapseEdge G hab).Target) := by
  change (GraphContraction.collapseEdge G hab).map (x : V) =
    GraphContraction.collapseEdgeOutside G hab (x : V) x.2
  unfold GraphContraction.collapseEdge GraphContraction.collapseEdgeOutside
    GraphContraction.collapseSubgraph GraphContraction.ofMap
  have hx : (x : V) ≠ a ∧ (x : V) ≠ b := by
    simpa [Set.mem_insert_iff] using x.2
  simp [hx.1, hx.2]

namespace EdgeDeletion

theorem collapseEdgeTarget_outside_of_ne_none
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    {y : (GraphContraction.collapseEdge G hab).Target}
    (hy : y ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        y = GraphContraction.collapseEdgeOutside G hab v hv := by
  classical
  cases hyopt : y with
  | none =>
      exact False.elim (hy hyopt)
  | some yv =>
      let v : V := yv.1
      have hv : v ∉ ({a, b} : Set V) := yv.2
      refine ⟨v, hv, ?_⟩
      simp [v, GraphContraction.collapseEdgeOutside,
        GraphContraction.collapseEdge, GraphContraction.collapseSubgraph]

theorem collapseEdgeDart_head_outside_of_tail_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        e.head = GraphContraction.collapseEdgeOutside G hab v hv := by
  have hhead_ne :
      e.head ≠ (none : (GraphContraction.collapseEdge G hab).Target) := by
    intro hhead
    have hloop :
        (GraphContraction.collapseEdge G hab).graph.Adj
          (none : (GraphContraction.collapseEdge G hab).Target)
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      simpa [htail, hhead] using e.adj
    exact (GraphContraction.collapseEdge G hab).graph.loopless.irrefl _ hloop
  exact collapseEdgeTarget_outside_of_ne_none G hab hhead_ne

theorem collapseEdgeDart_tail_outside_of_head_none
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        e.tail = GraphContraction.collapseEdgeOutside G hab v hv := by
  rcases collapseEdgeDart_head_outside_of_tail_none
      (G := G) hab e.symm (by simpa using hhead) with ⟨v, hv, htail⟩
  exact ⟨v, hv, by simpa using htail⟩

theorem deletedGraph_adj_left_outside_of_adj
    {V : Type u}
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hav : G.Adj a v) :
    (deletedGraph G a b).Adj a v := by
  classical
  rw [deletedGraph, SimpleGraph.deleteEdges_adj]
  refine ⟨hav, ?_⟩
  intro hbad
  simp only [Set.mem_singleton_iff] at hbad
  have hcases :
      (a = a ∧ v = b) ∨ (a = b ∧ v = a) := by
    simpa [Sym2.eq_iff] using hbad
  rcases hcases with hcases | hcases
  · exact hv (by simp [hcases.2])
  · exact hab.ne hcases.1

theorem deletedGraph_adj_right_outside_of_adj
    {V : Type u}
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hbv : G.Adj b v) :
    (deletedGraph G a b).Adj b v := by
  classical
  rw [deletedGraph, SimpleGraph.deleteEdges_adj]
  refine ⟨hbv, ?_⟩
  intro hbad
  simp only [Set.mem_singleton_iff] at hbad
  have hcases :
      (b = a ∧ v = b) ∨ (b = b ∧ v = a) := by
    simpa [Sym2.eq_iff] using hbad
  rcases hcases with hcases | hcases
  · exact hab.ne hcases.1.symm
  · exact hv (by simp [hcases.2])

theorem deletedGraph_adj_outside_outside_of_adj
    {V : Type u}
    {G : SimpleGraph V} {a b u v : V}
    (hu : u ∉ ({a, b} : Set V))
    (hv : v ∉ ({a, b} : Set V))
    (huv : G.Adj u v) :
    (deletedGraph G a b).Adj u v := by
  classical
  rw [deletedGraph, SimpleGraph.deleteEdges_adj]
  refine ⟨huv, ?_⟩
  intro hbad
  simp only [Set.mem_singleton_iff] at hbad
  have hcases :
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
    simpa [Sym2.eq_iff] using hbad
  rcases hcases with hcases | hcases
  · exact hv (by simp [hcases.2])
  · exact hu (by simp [hcases.1])

/-- If a dart of `G - ab` leaves one of the split endpoints, its other
endpoint is outside `{a,b}`. -/
theorem deletedGraph_head_outside_of_tail_source
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (d : OrientedEdge (deletedGraph G a b))
    (htail : d.tail = a ∨ d.tail = b) :
    d.head ∉ ({a, b} : Set V) := by
  classical
  have hdel :
      (G.deleteEdges ({s(a, b)} : Set (Sym2 V))).Adj d.tail d.head := by
    simpa [deletedGraph] using d.adj
  rw [SimpleGraph.deleteEdges_adj] at hdel
  intro hhead
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hhead
  rcases htail with htail | htail <;> rcases hhead with hhead | hhead
  · have hloop : (deletedGraph G a b).Adj a a := by
      simpa [htail, hhead] using d.adj
    exact (deletedGraph G a b).loopless.irrefl a hloop
  · exact hdel.2 (by simp [htail, hhead])
  · exact hdel.2 (by
      have hs : s(d.tail, d.head) = s(a, b) := by
        rw [htail, hhead, Sym2.eq_swap]
      simp [hs])
  · have hloop : (deletedGraph G a b).Adj b b := by
      simpa [htail, hhead] using d.adj
    exact (deletedGraph G a b).loopless.irrefl b hloop

/-- If a dart of `G - ab` enters one of the split endpoints, its other
endpoint is outside `{a,b}`. -/
theorem deletedGraph_tail_outside_of_head_source
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (d : OrientedEdge (deletedGraph G a b))
    (hhead : d.head = a ∨ d.head = b) :
    d.tail ∉ ({a, b} : Set V) := by
  have hsymm :
      (OrientedEdge.symm d).head ∉ ({a, b} : Set V) :=
    deletedGraph_head_outside_of_tail_source
      (G := G) (a := a) (b := b) d.symm (by
        simpa [OrientedEdge.symm, OrientedEdge.tail] using hhead)
  simpa [OrientedEdge.symm, OrientedEdge.head] using hsymm

/-- Explicitly lift a quotient dart between two named outside vertices. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_outside_outside
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b u v : V}
    (hab : G.Adj a b)
    (hu : u ∉ ({a, b} : Set V))
    (hv : v ∉ ({a, b} : Set V))
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = GraphContraction.collapseEdgeOutside G hab u hu)
    (hhead :
      e.head = GraphContraction.collapseEdgeOutside G hab v hv) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        d.tail = u ∧ d.head = v := by
  have hadj_outside :
      (GraphContraction.collapseEdge G hab).graph.Adj
        (GraphContraction.collapseEdgeOutside G hab u hu)
        (GraphContraction.collapseEdgeOutside G hab v hv) := by
    simpa [htail, hhead] using e.adj
  have huv : G.Adj u v :=
    (GraphContraction.collapseEdge_graph_adj_outside_iff
      G hab hu hv).mp hadj_outside
  let d : OrientedEdge (deletedGraph G a b) :=
    ⟨(u, v), deletedGraph_adj_outside_outside_of_adj
      (G := G) hu hv huv⟩
  refine ⟨d, ?_, rfl, rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · have hmap :=
      deletedGraphToCollapseEdgeHom_apply_outside
        (G := G) hab (⟨u, hu⟩ :
          {z : V | z ∉ ({a, b} : Set V)})
    simpa [d] using hmap.trans htail.symm
  · have hmap :=
      deletedGraphToCollapseEdgeHom_apply_outside
        (G := G) hab (⟨v, hv⟩ :
          {z : V | z ∉ ({a, b} : Set V)})
    simpa [d] using hmap.trans hhead.symm

/-- Explicitly lift a quotient dart from the collapsed vertex to an outside
vertex through the left endpoint of the split edge. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_tail_left
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hav : G.Adj a v)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target))
    (hhead :
      e.head = GraphContraction.collapseEdgeOutside G hab v hv) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        d.tail = a ∧ d.head = v := by
  let d : OrientedEdge (deletedGraph G a b) :=
    ⟨(a, v), deletedGraph_adj_left_outside_of_adj
      (G := G) hab hv hav⟩
  refine ⟨d, ?_, rfl, rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · change deletedGraphToCollapseEdgeHom G hab a = e.tail
    exact (deletedGraphToCollapseEdgeHom_apply_left G hab).trans htail.symm
  · have hmap :=
      deletedGraphToCollapseEdgeHom_apply_outside
        (G := G) hab (⟨v, hv⟩ :
          {z : V | z ∉ ({a, b} : Set V)})
    simpa [d] using hmap.trans hhead.symm

/-- Explicitly lift a quotient dart from the collapsed vertex to an outside
vertex through the right endpoint of the split edge. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_tail_right
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hbv : G.Adj b v)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target))
    (hhead :
      e.head = GraphContraction.collapseEdgeOutside G hab v hv) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        d.tail = b ∧ d.head = v := by
  let d : OrientedEdge (deletedGraph G a b) :=
    ⟨(b, v), deletedGraph_adj_right_outside_of_adj
      (G := G) hab hv hbv⟩
  refine ⟨d, ?_, rfl, rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · change deletedGraphToCollapseEdgeHom G hab b = e.tail
    exact (deletedGraphToCollapseEdgeHom_apply_right G hab).trans htail.symm
  · have hmap :=
      deletedGraphToCollapseEdgeHom_apply_outside
        (G := G) hab (⟨v, hv⟩ :
          {z : V | z ∉ ({a, b} : Set V)})
    simpa [d] using hmap.trans hhead.symm

/-- Explicitly lift a quotient dart from an outside vertex into the collapsed
vertex through the left endpoint of the split edge. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_head_left
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hav : G.Adj a v)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = GraphContraction.collapseEdgeOutside G hab v hv)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        d.tail = v ∧ d.head = a := by
  rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_left
      (G := G) hab hv hav e.symm (by simpa using hhead)
        (by simpa using htail) with ⟨d, hd, hdtail, hdhead⟩
  refine ⟨d.symm, ?_, ?_, ?_⟩
  · rw [deletedGraphToCollapseEdgeDart_symm, hd]
    simp
  · simpa using hdhead
  · simpa using hdtail

/-- Explicitly lift a quotient dart from an outside vertex into the collapsed
vertex through the right endpoint of the split edge. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_head_right
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (hbv : G.Adj b v)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = GraphContraction.collapseEdgeOutside G hab v hv)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        d.tail = v ∧ d.head = b := by
  rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_right
      (G := G) hab hv hbv e.symm (by simpa using hhead)
        (by simpa using htail) with ⟨d, hd, hdtail, hdhead⟩
  refine ⟨d.symm, ?_, ?_, ?_⟩
  · rw [deletedGraphToCollapseEdgeDart_symm, hd]
    simp
  · simpa using hdhead
  · simpa using hdtail

/-- A quotient dart leaving the collapsed vertex and ending at a named outside
vertex has a deleted-edge lift through whichever split endpoint is adjacent to
that outside vertex. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_tail_outside_side
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target))
    (hhead :
      e.head = GraphContraction.collapseEdgeOutside G hab v hv) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        ((d.tail = a ∧ d.head = v) ∨
          (d.tail = b ∧ d.head = v)) := by
  have hadj_none :
      (GraphContraction.collapseEdge G hab).graph.Adj
        (none : (GraphContraction.collapseEdge G hab).Target)
        (GraphContraction.collapseEdgeOutside G hab v hv) := by
    simpa [htail, hhead] using e.adj
  rcases
      (GraphContraction.collapseEdge_adj_none_outside_iff
        G hab hv).mp hadj_none with hav | hbv
  · rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_left
      (G := G) hab hv hav e htail hhead with ⟨d, hd, hdt, hdh⟩
    exact ⟨d, hd, Or.inl ⟨hdt, hdh⟩⟩
  · rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_right
      (G := G) hab hv hbv e htail hhead with ⟨d, hd, hdt, hdh⟩
    exact ⟨d, hd, Or.inr ⟨hdt, hdh⟩⟩

/-- A quotient dart entering the collapsed vertex from a named outside vertex
has a deleted-edge lift through whichever split endpoint is adjacent to that
outside vertex. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_head_outside_side
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b)
    (hv : v ∉ ({a, b} : Set V))
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = GraphContraction.collapseEdgeOutside G hab v hv)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        ((d.tail = v ∧ d.head = a) ∨
          (d.tail = v ∧ d.head = b)) := by
  rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_outside_side
      (G := G) hab hv e.symm (by simpa using hhead)
        (by simpa using htail) with ⟨d, hd, hside⟩
  refine ⟨d.symm, ?_, ?_⟩
  · rw [deletedGraphToCollapseEdgeDart_symm, hd]
    simp
  · rcases hside with hside | hside
    · exact Or.inl ⟨by simpa using hside.2, by simpa using hside.1⟩
    · exact Or.inr ⟨by simpa using hside.2, by simpa using hside.1⟩

/-- A quotient dart leaving the collapsed vertex can be unpacked into a named
outside head and then lifted through one of the two split endpoints. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_tail_incident_side
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        Exists fun d : OrientedEdge (deletedGraph G a b) =>
          e.head = GraphContraction.collapseEdgeOutside G hab v hv ∧
            deletedGraphToCollapseEdgeDart G hab d = e ∧
              ((d.tail = a ∧ d.head = v) ∨
                (d.tail = b ∧ d.head = v)) := by
  rcases collapseEdgeDart_head_outside_of_tail_none
      (G := G) hab e htail with ⟨v, hv, hhead⟩
  rcases exists_deletedGraphToCollapseEdgeDart_lift_tail_outside_side
      (G := G) hab hv e htail hhead with ⟨d, hd, hside⟩
  exact ⟨v, hv, d, hhead, hd, hside⟩

/-- A quotient dart entering the collapsed vertex can be unpacked into a named
outside tail and then lifted through one of the two split endpoints. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_head_incident_side
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun v : V =>
      Exists fun hv : v ∉ ({a, b} : Set V) =>
        Exists fun d : OrientedEdge (deletedGraph G a b) =>
          e.tail = GraphContraction.collapseEdgeOutside G hab v hv ∧
            deletedGraphToCollapseEdgeDart G hab d = e ∧
              ((d.tail = v ∧ d.head = a) ∨
                (d.tail = v ∧ d.head = b)) := by
  rcases collapseEdgeDart_tail_outside_of_head_none
      (G := G) hab e hhead with ⟨v, hv, htail⟩
  rcases exists_deletedGraphToCollapseEdgeDart_lift_head_outside_side
      (G := G) hab hv e htail hhead with ⟨d, hd, hside⟩
  exact ⟨v, hv, d, htail, hd, hside⟩


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
