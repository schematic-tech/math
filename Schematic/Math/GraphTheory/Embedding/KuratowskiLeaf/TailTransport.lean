import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.EulerGenus
import Schematic.Math.GraphTheory.Embedding.RotationSystem

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace LeafExtension

/-- The old endpoint of a deleted-leaf edge as a vertex of the deleted graph. -/
def deletedLeafOldEndpoint
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w) :
    {z : V // z ≠ v} :=
  ⟨w, hvw.ne'⟩

/-- Tail in the original graph of an extended deleted-leaf dart. -/
def leafExtTail
    {V : Type u} {G : SimpleGraph V}
    {v w : V} :
    ExtDart (OrientedEdge (G.induce {z : V | z ≠ v})) -> V
  | ExtDart.new => v
  | ExtDart.newEdge => w
  | ExtDart.old e => ((e.tail : {z : V // z ≠ v}) : V)

@[simp]
theorem leafExtTail_new
    {V : Type u} {G : SimpleGraph V}
    {v w : V} :
    leafExtTail (G := G) (v := v) (w := w) ExtDart.new = v :=
  rfl

@[simp]
theorem leafExtTail_newEdge
    {V : Type u} {G : SimpleGraph V}
    {v w : V} :
    leafExtTail (G := G) (v := v) (w := w) ExtDart.newEdge = w :=
  rfl

@[simp]
theorem leafExtTail_old
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (e : OrientedEdge (G.induce {z : V | z ≠ v})) :
    leafExtTail (G := G) (v := v) (w := w) (ExtDart.old e) =
      ((e.tail : {z : V // z ≠ v}) : V) :=
  rfl

/-- The splice pivot at the old endpoint, if that endpoint still has an old
outgoing dart after deleting the leaf. -/
noncomputable def leafExtPivot
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w) :
    Option (OrientedEdge (G.induce {z : V | z ≠ v})) :=
  orientedEdgePivot (G := G.induce {z : V | z ≠ v})
    (deletedLeafOldEndpoint (G := G) (v := v) (w := w) hvw)

theorem leafExtPivot_spec_of_eq_some
    {V : Type u} {G : SimpleGraph V}
    {v w : V} {p : OrientedEdge (G.induce {z : V | z ≠ v})}
    (hvw : G.Adj v w)
    (hp : leafExtPivot (G := G) (v := v) (w := w) hvw = some p) :
    ((p.tail : {z : V // z ≠ v}) : V) = w := by
  have htail :=
    orientedEdgePivot_spec_of_eq_some
      (G := G.induce {z : V | z ≠ v})
      (x := deletedLeafOldEndpoint (G := G) (v := v) (w := w) hvw)
      hp
  exact congrArg Subtype.val htail

theorem no_leafExtTail_old_of_pivot_eq_none
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (hp : leafExtPivot (G := G) (v := v) (w := w) hvw = none)
    (e : OrientedEdge (G.induce {z : V | z ≠ v})) :
    ((e.tail : {z : V // z ≠ v}) : V) ≠ w := by
  intro he
  have htail :
      e.tail = deletedLeafOldEndpoint (G := G) (v := v) (w := w) hvw := by
    ext
    exact he
  exact
    (no_orientedEdge_tail_of_pivot_eq_none
      (G := G.induce {z : V | z ≠ v})
      (x := deletedLeafOldEndpoint (G := G) (v := v) (w := w) hvw)
      hp e) htail

theorem insertedLeafNode_leafExtTail
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (x : ExtDart (OrientedEdge (G.induce {z : V | z ≠ v}))) :
    leafExtTail (G := G) (v := v) (w := w)
        (insertedLeafNode R.node
          (leafExtPivot (G := G) (v := v) (w := w) hvw) x) =
      leafExtTail (G := G) (v := v) (w := w) x := by
  cases x with
  | new => rfl
  | newEdge =>
      cases hp : leafExtPivot (G := G) (v := v) (w := w) hvw with
      | none => rfl
      | some p =>
          simp
          calc
            (((R.node p).tail : {z : V // z ≠ v}) : V) =
                ((p.tail : {z : V // z ≠ v}) : V) :=
              congrArg Subtype.val (R.node_tail p)
            _ = w := leafExtPivot_spec_of_eq_some (G := G) (v := v)
              (w := w) hvw hp
  | old e =>
      cases hp : leafExtPivot (G := G) (v := v) (w := w) hvw with
      | none =>
          simp
          exact congrArg Subtype.val (R.node_tail e)
      | some p =>
          by_cases he : e = p
          · subst e
            change
              leafExtTail (G := G) (v := v) (w := w)
                  (if p = p then ExtDart.newEdge else ExtDart.old (R.node p)) =
                leafExtTail (G := G) (v := v) (w := w) (ExtDart.old p)
            simp
            show w = ((p.tail : {z : V // z ≠ v}) : V)
            exact (leafExtPivot_spec_of_eq_some (G := G) (v := v)
              (w := w) hvw hp).symm
          · change
              leafExtTail (G := G) (v := v) (w := w)
                  (if e = p then ExtDart.newEdge else ExtDart.old (R.node e)) =
                leafExtTail (G := G) (v := v) (w := w) (ExtDart.old e)
            rw [if_neg he]
            exact congrArg Subtype.val (R.node_tail e)

theorem insertedLeafNode_leafExtReachable_of_same_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    {x y : ExtDart (OrientedEdge (G.induce {z : V | z ≠ v}))}
    (hxy :
      leafExtTail (G := G) (v := v) (w := w) x =
        leafExtTail (G := G) (v := v) (w := w) y) :
    PermReachable
      (insertedLeafNode R.node
        (leafExtPivot (G := G) (v := v) (w := w) hvw))
      x y := by
  cases x with
  | new =>
      cases y with
      | new =>
          exact PermReachable.refl _ ExtDart.new
      | newEdge =>
          have hvw_eq : v = w := by simpa using hxy
          exact False.elim (hvw.ne hvw_eq)
      | old f =>
          have hvf : v = ((f.tail : {z : V // z ≠ v}) : V) := by
            simpa using hxy
          exact False.elim (f.tail.property hvf.symm)
  | newEdge =>
      cases y with
      | new =>
          have hwv : w = v := by simpa using hxy
          exact False.elim (hvw.ne' hwv)
      | newEdge =>
          exact PermReachable.refl _ ExtDart.newEdge
      | old f =>
          have hwf : w = ((f.tail : {z : V // z ≠ v}) : V) := by
            simpa using hxy
          cases hp : leafExtPivot (G := G) (v := v) (w := w) hvw with
          | none =>
              exact False.elim
                ((no_leafExtTail_old_of_pivot_eq_none
                  (G := G) (v := v) (w := w) hvw hp f) hwf.symm)
          | some p =>
              have hpf : p.tail = f.tail := by
                ext
                exact (leafExtPivot_spec_of_eq_some (G := G) (v := v)
                  (w := w) hvw hp).trans hwf
              have hR : PermReachable R.node p f :=
                R.node_orbit_of_same_tail p f hpf
              simpa [hp] using
                insertedLeafNode_newEdge_reachable_old_of_permReachable
                  R.node hR
  | old e =>
      cases y with
      | new =>
          have hev : ((e.tail : {z : V // z ≠ v}) : V) = v := by
            simpa using hxy
          exact False.elim (e.tail.property hev)
      | newEdge =>
          have hew : ((e.tail : {z : V // z ≠ v}) : V) = w := by
            simpa using hxy
          cases hp : leafExtPivot (G := G) (v := v) (w := w) hvw with
          | none =>
              exact False.elim
                ((no_leafExtTail_old_of_pivot_eq_none
                  (G := G) (v := v) (w := w) hvw hp e) hew)
          | some p =>
              have hpe : p.tail = e.tail := by
                ext
                exact (leafExtPivot_spec_of_eq_some (G := G) (v := v)
                  (w := w) hvw hp).trans hew.symm
              have hR : PermReachable R.node p e :=
                R.node_orbit_of_same_tail p e hpe
              exact
                PermReachable.symm
                  (insertedLeafNode R.node (some p))
                  (by
                    simpa using
                      insertedLeafNode_newEdge_reachable_old_of_permReachable
                        R.node hR)
      | old f =>
          have hef : e.tail = f.tail := by
            ext
            simpa using hxy
          have hR : PermReachable R.node e f :=
            R.node_orbit_of_same_tail e f hef
          exact insertedLeafNode_old_reachable_of_permReachable
            R.node (leafExtPivot (G := G) (v := v) (w := w) hvw) hR


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
