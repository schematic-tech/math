import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.ContractionDarts


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- The finite face boundary in a recursive rotation system of the contraction
`G / ab`, represented as the face orbit of a chosen contraction dart. -/
noncomputable def contractionFaceBoundary
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    List (OrientedEdge (GraphContraction.collapseEdge G hab).graph) :=
  (R.toHypermap).faceOrbitList e

@[simp]
theorem mem_contractionFaceBoundary
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    d ∈ contractionFaceBoundary hab R e ↔
      PermReachable (R.toHypermap).face e d := by
  change d ∈ (R.toHypermap).faceOrbitList e ↔
    PermReachable (R.toHypermap).face e d
  exact Hypermap.mem_faceOrbitList (G := R.toHypermap) (x := e) (y := d)

theorem contractionFaceBoundary_self_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    e ∈ contractionFaceBoundary hab R e := by
  rw [mem_contractionFaceBoundary]
  exact PermReachable.refl (R.toHypermap).face e

theorem contractionFaceBoundary_faceBand_iff
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (R.toHypermap).FaceBand (contractionFaceBoundary hab R e) d ↔
      PermReachable (R.toHypermap).face e d := by
  change (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ↔
    PermReachable (R.toHypermap).face e d
  exact Hypermap.FaceBand.faceOrbitList_iff
    (G := R.toHypermap) (x := e) (u := d)

/-- The graph substructure traced by a selected contraction face boundary:
its vertices are the tails/heads of boundary darts, and its edges are the
unoriented versions of those darts. -/
def contractionFaceBoundarySubgraph
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph) :
    (GraphContraction.collapseEdge G hab).graph.Subgraph where
  verts := {x |
    Exists fun d : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      d ∈ contractionFaceBoundary hab R e ∧ (d.tail = x ∨ d.head = x)}
  Adj x y :=
    Exists fun d : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
      d ∈ contractionFaceBoundary hab R e ∧
        ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x))
  adj_sub := by
    rintro x y ⟨d, _hd, hxy | hyx⟩
    · simpa [hxy.1, hxy.2] using d.adj
    · simpa [hyx.1, hyx.2] using d.adj.symm
  edge_vert := by
    rintro x y ⟨d, hd, hxy | hyx⟩
    · exact ⟨d, hd, Or.inl hxy.1⟩
    · exact ⟨d, hd, Or.inr hyx.2⟩
  symm := by
    rintro x y ⟨d, hd, hxy | hyx⟩
    · exact ⟨d, hd, Or.inr hxy⟩
    · exact ⟨d, hd, Or.inl hyx⟩

theorem contractionFaceBoundarySubgraph_tail_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e) :
    d.tail ∈ (contractionFaceBoundarySubgraph hab R e).verts :=
  ⟨d, hd, Or.inl rfl⟩

theorem contractionFaceBoundarySubgraph_head_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e) :
    d.head ∈ (contractionFaceBoundarySubgraph hab R e).verts :=
  ⟨d, hd, Or.inr rfl⟩

theorem contractionFaceBoundarySubgraph_adj_of_mem
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (R : RotationSystem (GraphContraction.collapseEdge G hab).graph)
    (e d : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hd : d ∈ contractionFaceBoundary hab R e) :
    (contractionFaceBoundarySubgraph hab R e).Adj d.tail d.head :=
  ⟨d, hd, Or.inl ⟨rfl, rfl⟩⟩

/-- A graph subgraph is carried by one face orbit of a rotation system if each
of its vertices and edges is witnessed by a dart from that orbit.  This is the
combinatorial interface for the Skopenkov/Makarychev observation that a face
boundary cannot contain a theta subgraph. -/
def SubgraphCarriedByFaceOrbit
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (S : H.Subgraph) : Prop :=
  (∀ {x : W}, x ∈ S.verts →
    Exists fun d : OrientedEdge H =>
      PermReachable (R.toHypermap).face e d ∧
        (d.tail = x ∨ d.head = x)) ∧
  (∀ {x y : W}, S.Adj x y →
    Exists fun d : OrientedEdge H =>
      PermReachable (R.toHypermap).face e d ∧
        ((d.tail = x ∧ d.head = y) ∨
          (d.tail = y ∧ d.head = x)))

/-- The canonical graph carried by a single face orbit: its vertices are the
endpoints of darts in the orbit, and its edges are exactly the unoriented edges
whose one orientation occurs in that orbit. -/
def faceOrbitSubgraph
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H) : H.Subgraph where
  verts := {x |
    Exists fun d : OrientedEdge H =>
      PermReachable (R.toHypermap).face e d ∧
        (d.tail = x ∨ d.head = x)}
  Adj x y :=
    Exists fun d : OrientedEdge H =>
      PermReachable (R.toHypermap).face e d ∧
        ((d.tail = x ∧ d.head = y) ∨
          (d.tail = y ∧ d.head = x))
  adj_sub := by
    rintro x y ⟨d, _hd, hxy | hyx⟩
    · simpa [hxy.1, hxy.2] using d.adj
    · simpa [hyx.1, hyx.2] using d.adj.symm
  edge_vert := by
    rintro x y ⟨d, hd, hxy | hyx⟩
    · exact ⟨d, hd, Or.inl hxy.1⟩
    · exact ⟨d, hd, Or.inr hyx.2⟩
  symm := by
    rintro x y ⟨d, hd, hxy | hyx⟩
    · exact ⟨d, hd, Or.inr hxy⟩
    · exact ⟨d, hd, Or.inl hyx⟩

/-- The canonical face-orbit subgraph is carried by its defining face orbit. -/
theorem faceOrbitSubgraph_carriedByFaceOrbit
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H) :
    SubgraphCarriedByFaceOrbit R e (faceOrbitSubgraph R e) := by
  constructor
  · intro x hx
    exact hx
  · intro x y hxy
    exact hxy

theorem faceOrbitSubgraph_tail_mem
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H)
    (hd : PermReachable (R.toHypermap).face e d) :
    d.tail ∈ (faceOrbitSubgraph R e).verts :=
  ⟨d, hd, Or.inl rfl⟩

theorem faceOrbitSubgraph_head_mem
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H)
    (hd : PermReachable (R.toHypermap).face e d) :
    d.head ∈ (faceOrbitSubgraph R e).verts :=
  ⟨d, hd, Or.inr rfl⟩

theorem faceOrbitSubgraph_adj_of_faceReachable
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H)
    (hd : PermReachable (R.toHypermap).face e d) :
    (faceOrbitSubgraph R e).Adj d.tail d.head :=
  ⟨d, hd, Or.inl ⟨rfl, rfl⟩⟩

theorem faceOrbitSubgraph_tail_mem_of_mem_faceOrbitList
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H)
    (hd : d ∈ (R.toHypermap).faceOrbitList e) :
    d.tail ∈ (faceOrbitSubgraph R e).verts :=
  faceOrbitSubgraph_tail_mem R e d
    ((Hypermap.mem_faceOrbitList (G := R.toHypermap)
      (x := e) (y := d)).mp hd)

theorem faceOrbitSubgraph_head_mem_of_mem_faceOrbitList
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H)
    (hd : d ∈ (R.toHypermap).faceOrbitList e) :
    d.head ∈ (faceOrbitSubgraph R e).verts :=
  faceOrbitSubgraph_head_mem R e d
    ((Hypermap.mem_faceOrbitList (G := R.toHypermap)
      (x := e) (y := d)).mp hd)

theorem faceOrbitSubgraph_adj_of_mem_faceOrbitList
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H)
    (hd : d ∈ (R.toHypermap).faceOrbitList e) :
    (faceOrbitSubgraph R e).Adj d.tail d.head :=
  faceOrbitSubgraph_adj_of_faceReachable R e d
    ((Hypermap.mem_faceOrbitList (G := R.toHypermap)
      (x := e) (y := d)).mp hd)

theorem faceOrbitSubgraph_faceBand_iff
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e d : OrientedEdge H) :
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ↔
      PermReachable (R.toHypermap).face e d := by
  exact Hypermap.FaceBand.faceOrbitList_iff
    (G := R.toHypermap) (x := e) (u := d)

/-- Canonical orientation form of membership in the face-orbit subgraph.  For
an edge of the coefficient graph, either its outgoing ambient dart or its
reverse belongs to the selected face orbit. -/
theorem faceOrbitSubgraph_coe_adj_faceBand_or_symm
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : (faceOrbitSubgraph R e).verts}
    (hxy : (faceOrbitSubgraph R e).coe.Adj x y) :
    let d : OrientedEdge H :=
      ⟨((x : W), (y : W)),
        (faceOrbitSubgraph R e).coe_adj_sub x y hxy⟩
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∨
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d.symm := by
  let d : OrientedEdge H :=
    ⟨((x : W), (y : W)),
      (faceOrbitSubgraph R e).coe_adj_sub x y hxy⟩
  rcases hxy with ⟨f, hf, hdir | hrev⟩
  · left
    have hfd : f = d := by
      apply Subtype.ext
      exact Prod.ext hdir.1 hdir.2
    exact (faceOrbitSubgraph_faceBand_iff R e d).mpr (by simpa [hfd] using hf)
  · right
    have hfd : f = d.symm := by
      apply Subtype.ext
      exact Prod.ext hrev.1 hrev.2
    exact (faceOrbitSubgraph_faceBand_iff R e d.symm).mpr
      (by simpa [hfd] using hf)


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
