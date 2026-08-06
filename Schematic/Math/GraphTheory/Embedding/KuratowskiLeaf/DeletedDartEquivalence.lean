import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.TailTransport
import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.SmallGraphs

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

/-- Forward map in the deleted-leaf dart decomposition. -/
def orientedEdgeDeleteLeafToFun
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v : V}
    (e : OrientedEdge G) :
    ExtDart (OrientedEdge (G.induce {z : V | z ≠ v})) :=
  if htail : e.tail = v then
    ExtDart.new
  else if hhead : e.head = v then
    ExtDart.newEdge
  else
    ExtDart.old
      (⟨(⟨e.tail, htail⟩, ⟨e.head, hhead⟩), by
        exact e.adj⟩ :
        OrientedEdge (G.induce {z : V | z ≠ v}))

/-- Inverse map in the deleted-leaf dart decomposition. -/
def orientedEdgeDeleteLeafInvFun
    {V : Type u}
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w) :
    ExtDart (OrientedEdge (G.induce {z : V | z ≠ v})) -> OrientedEdge G
  | ExtDart.new => ⟨(v, w), hvw⟩
  | ExtDart.newEdge => ⟨(w, v), hvw.symm⟩
  | ExtDart.old e =>
      ⟨(((e.tail : {z : V // z ≠ v}) : V),
        ((e.head : {z : V // z ≠ v}) : V)), by
          exact e.adj⟩

/-- Oriented edges of a graph with a chosen leaf `v--w` decompose into the two
leaf darts and the old darts of the deleted-leaf graph.  This is the dart
boundary for the actual leaf-reattachment rotation construction. -/
noncomputable def orientedEdgeDeleteLeafEquiv
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1) :
    OrientedEdge G ≃ ExtDart (OrientedEdge (G.induce {z : V | z ≠ v})) where
  toFun := orientedEdgeDeleteLeafToFun (v := v)
  invFun := orientedEdgeDeleteLeafInvFun (v := v) (w := w) hvw
  left_inv := by
    intro e
    by_cases htail : e.tail = v
    · have hhead : e.head = w :=
        neighbor_eq_of_degree_le_one_of_adj
          (G := G) hdegree hvw (by simpa [htail] using e.adj)
      cases e with
      | mk p hp =>
          cases p with
          | mk a b =>
              dsimp [OrientedEdge.tail, OrientedEdge.head] at htail hhead
              subst a
              subst b
              simp [orientedEdgeDeleteLeafToFun, orientedEdgeDeleteLeafInvFun,
                OrientedEdge.tail]
    · by_cases hhead : e.head = v
      · have htail_eq : e.tail = w :=
          neighbor_eq_of_degree_le_one_of_adj
            (G := G) hdegree hvw (by simpa [hhead] using e.adj.symm)
        cases e with
        | mk p hp =>
            cases p with
            | mk a b =>
                dsimp [OrientedEdge.tail, OrientedEdge.head] at htail hhead htail_eq
                subst b
                subst a
                simp [orientedEdgeDeleteLeafToFun, orientedEdgeDeleteLeafInvFun,
                  OrientedEdge.tail, OrientedEdge.head, hvw.ne']
      · cases e with
        | mk p hp =>
            cases p with
            | mk a b =>
                dsimp [OrientedEdge.tail, OrientedEdge.head] at htail hhead
                simp [orientedEdgeDeleteLeafToFun, orientedEdgeDeleteLeafInvFun,
                  OrientedEdge.tail, OrientedEdge.head, htail, hhead]
  right_inv := by
    intro x
    cases x with
    | new =>
        simp [orientedEdgeDeleteLeafToFun, orientedEdgeDeleteLeafInvFun,
          OrientedEdge.tail]
    | newEdge =>
        simp [orientedEdgeDeleteLeafToFun, orientedEdgeDeleteLeafInvFun,
          OrientedEdge.tail, OrientedEdge.head, hvw.ne']
    | old e =>
        cases e with
        | mk p hp =>
            cases p with
            | mk a b =>
                have ha : (a : V) ≠ v := a.property
                have hb : (b : V) ≠ v := b.property
                simp [orientedEdgeDeleteLeafToFun, orientedEdgeDeleteLeafInvFun,
                  OrientedEdge.tail, OrientedEdge.head, ha, hb]

@[simp]
theorem orientedEdgeDeleteLeafEquiv_symm_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (x : ExtDart (OrientedEdge (G.induce {z : V | z ≠ v}))) :
    ((orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree).symm x).tail =
      leafExtTail (G := G) (v := v) (w := w) x := by
  cases x <;> rfl

theorem orientedEdgeDeleteLeafEquiv_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (e : OrientedEdge G) :
    leafExtTail (G := G) (v := v) (w := w)
        ((orientedEdgeDeleteLeafEquiv
          (G := G) (v := v) (w := w) hvw hdegree) e) =
      e.tail := by
  have h :=
    orientedEdgeDeleteLeafEquiv_symm_tail
      (G := G) (v := v) (w := w) hvw hdegree
      ((orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree) e)
  have heq :
      (orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree).symm
          ((orientedEdgeDeleteLeafEquiv
            (G := G) (v := v) (w := w) hvw hdegree) e) = e :=
    (orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree).left_inv e
  rw [heq] at h
  exact h.symm

theorem orientedEdgeDeleteLeafEquiv_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (e : OrientedEdge G) :
    (orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree) e.symm =
      ExtDart.Perm.edge
        (OrientedEdge.edgePerm (G.induce {z : V | z ≠ v}))
        ((orientedEdgeDeleteLeafEquiv
          (G := G) (v := v) (w := w) hvw hdegree) e) := by
  change orientedEdgeDeleteLeafToFun (v := v) e.symm =
    ExtDart.Perm.edge
      (OrientedEdge.edgePerm (G.induce {z : V | z ≠ v}))
      (orientedEdgeDeleteLeafToFun (v := v) e)
  by_cases htail : e.tail = v
  · have hhead : e.head = w :=
      neighbor_eq_of_degree_le_one_of_adj
        (G := G) hdegree hvw (by simpa [htail] using e.adj)
    cases e with
    | mk p hp =>
        cases p with
        | mk a b =>
            dsimp [OrientedEdge.tail, OrientedEdge.head] at htail hhead
            subst a
            subst b
            unfold orientedEdgeDeleteLeafToFun
            simp [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head,
              ExtDart.Perm.edge, hvw.ne']
            change ExtDart.newEdge = ExtDart.newEdge
            rfl
  · by_cases hhead : e.head = v
    · have htail_eq : e.tail = w :=
        neighbor_eq_of_degree_le_one_of_adj
          (G := G) hdegree hvw (by simpa [hhead] using e.adj.symm)
      cases e with
      | mk p hp =>
          cases p with
          | mk a b =>
              dsimp [OrientedEdge.tail, OrientedEdge.head] at htail hhead htail_eq
              subst b
              subst a
              unfold orientedEdgeDeleteLeafToFun
              simp [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head,
                ExtDart.Perm.edge, htail]
              change ExtDart.new = ExtDart.new
              rfl
    · unfold orientedEdgeDeleteLeafToFun
      have htail' : ¬ (e : V × V).1 = v := htail
      have hhead' : ¬ (e : V × V).2 = v := hhead
      simp [OrientedEdge.edgePerm, ExtDart.Perm.edge,
        OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head,
        htail', hhead']
      change ExtDart.old _ = ExtDart.old _
      rfl


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
