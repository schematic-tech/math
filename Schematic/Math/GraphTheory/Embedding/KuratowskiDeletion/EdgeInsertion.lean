import Schematic.Math.GraphTheory.Embedding.DartExtension
import Schematic.Math.GraphTheory.Embedding.RotationSystemDeletion


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

def dartToExt
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (e : OrientedEdge G) :
    ExtDart (OrientedEdge (deletedGraph G a b)) :=
  if hforward : e.tail = a ∧ e.head = b then
    ExtDart.new
  else if hbackward : e.tail = b ∧ e.head = a then
    ExtDart.newEdge
  else
    ExtDart.old (oldDart (G := G) (a := a) (b := b) e (by
      intro hs
      have hcases :
          (e.tail = a ∧ e.head = b) ∨
            (e.tail = b ∧ e.head = a) := by
        simpa [Sym2.eq_iff] using hs
      exact hcases.elim hforward hbackward))

def extToDart
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    ExtDart (OrientedEdge (deletedGraph G a b)) → OrientedEdge G
  | ExtDart.new => ⟨(a, b), hab⟩
  | ExtDart.newEdge => ⟨(b, a), G.symm hab⟩
  | ExtDart.old e => sourceDart e

def extTail
    {V : Type u} {G : SimpleGraph V} (a b : V) :
    ExtDart (OrientedEdge (deletedGraph G a b)) → V
  | ExtDart.new => a
  | ExtDart.newEdge => b
  | ExtDart.old e => e.tail

def extHead
    {V : Type u} {G : SimpleGraph V} (a b : V) :
    ExtDart (OrientedEdge (deletedGraph G a b)) → V
  | ExtDart.new => b
  | ExtDart.newEdge => a
  | ExtDart.old e => e.head

@[simp]
theorem extTail_edge
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (x : ExtDart (OrientedEdge (deletedGraph G a b))) :
    extTail (G := G) a b
        (ExtDart.Perm.edge
          (OrientedEdge.edgePerm (deletedGraph G a b)) x) =
      extHead (G := G) a b x := by
  cases x <;> rfl

@[simp]
theorem extHead_edge
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (x : ExtDart (OrientedEdge (deletedGraph G a b))) :
    extHead (G := G) a b
        (ExtDart.Perm.edge
          (OrientedEdge.edgePerm (deletedGraph G a b)) x) =
      extTail (G := G) a b x := by
  cases x <;> rfl

@[simp]
theorem dartToExt_forward
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    dartToExt (G := G) (a := a) (b := b)
      (⟨(a, b), hab⟩ : OrientedEdge G) = ExtDart.new := by
  simp [dartToExt, OrientedEdge.tail, OrientedEdge.head]

@[simp]
theorem dartToExt_backward
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    dartToExt (G := G) (a := a) (b := b)
      (⟨(b, a), G.symm hab⟩ : OrientedEdge G) = ExtDart.newEdge := by
  have hba : b ≠ a := hab.ne.symm
  simp [dartToExt, OrientedEdge.tail, OrientedEdge.head, hba]

/-- The dart set of `G` is the two orientations of a deleted edge plus the
darts of the graph with that edge deleted.  This is the graph-facing boundary
needed before the add-edge hypermap extension can be transported back to a
rotation system on `G`. -/
noncomputable def dartEquivExt
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    OrientedEdge G ≃ ExtDart (OrientedEdge (deletedGraph G a b)) where
  toFun := dartToExt (G := G) (a := a) (b := b)
  invFun := extToDart (G := G) (a := a) (b := b) hab
  left_inv := by
    intro e
    by_cases hforward : e.tail = a ∧ e.head = b
    · have hdart :
          dartToExt (G := G) (a := a) (b := b) e = ExtDart.new := by
        simp [dartToExt, hforward]
      rw [hdart]
      dsimp [extToDart]
      apply Subtype.ext
      cases e with
      | mk e he =>
          cases e
          exact Prod.ext hforward.1.symm hforward.2.symm
    · by_cases hbackward : e.tail = b ∧ e.head = a
      · have hdart :
            dartToExt (G := G) (a := a) (b := b) e = ExtDart.newEdge := by
          have hba : b ≠ a := hab.ne.symm
          simp [dartToExt, hbackward, hba]
        rw [hdart]
        dsimp [extToDart]
        apply Subtype.ext
        cases e with
        | mk e he =>
            cases e
            exact Prod.ext hbackward.1.symm hbackward.2.symm
      · simp [dartToExt, hforward, hbackward, extToDart]
  right_inv := by
    intro e
    cases e with
    | new =>
        simp [dartToExt, extToDart, OrientedEdge.tail, OrientedEdge.head]
    | newEdge =>
        have hba : b ≠ a := hab.ne.symm
        simp [dartToExt, extToDart, OrientedEdge.tail, OrientedEdge.head, hba]
    | old e =>
        have hnot :
            s(e.tail, e.head) ≠ s(a, b) := by
          have hdel :
              G.Adj e.tail e.head ∧
                s(e.tail, e.head) ∉ ({s(a, b)} : Set (Sym2 V)) := by
            simpa [deletedGraph, SimpleGraph.deleteEdges_adj] using e.adj
          intro hs
          exact hdel.2 (by simp [hs])
        have hnot_forward :
            ¬ ((sourceDart (G := G) (a := a) (b := b) e).tail = a ∧
              (sourceDart (G := G) (a := a) (b := b) e).head = b) := by
          rintro ⟨htail, hhead⟩
          have ht : e.tail = a := by
            simpa [sourceDart, OrientedEdge.tail] using htail
          have hh : e.head = b := by
            simpa [sourceDart, OrientedEdge.head] using hhead
          exact hnot (by
            simpa [Sym2.eq_iff] using
              (Or.inl ⟨ht, hh⟩ :
                (e.tail = a ∧ e.head = b) ∨
                  (e.tail = b ∧ e.head = a)))
        have hnot_backward :
            ¬ ((sourceDart (G := G) (a := a) (b := b) e).tail = b ∧
              (sourceDart (G := G) (a := a) (b := b) e).head = a) := by
          rintro ⟨htail, hhead⟩
          have ht : e.tail = b := by
            simpa [sourceDart, OrientedEdge.tail] using htail
          have hh : e.head = a := by
            simpa [sourceDart, OrientedEdge.head] using hhead
          exact hnot (by
            simpa [Sym2.eq_iff] using
              (Or.inr ⟨ht, hh⟩ :
                (e.tail = a ∧ e.head = b) ∨
                  (e.tail = b ∧ e.head = a)))
        simp [dartToExt, extToDart, hnot_forward, hnot_backward,
          oldDart_sourceDart]

@[simp]
theorem dartEquivExt_symm
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge G) :
    dartEquivExt (G := G) (a := a) (b := b) hab e.symm =
      ExtDart.Perm.edge
        (OrientedEdge.edgePerm (deletedGraph G a b))
        (dartEquivExt (G := G) (a := a) (b := b) hab e) := by
  classical
  change
    dartToExt (G := G) (a := a) (b := b) e.symm =
      ExtDart.Perm.edge
        (OrientedEdge.edgePerm (deletedGraph G a b))
        (dartToExt (G := G) (a := a) (b := b) e)
  by_cases hforward : e.tail = a ∧ e.head = b
  · have hsymm_backward : e.symm.tail = b ∧ e.symm.head = a := by
      constructor
      · simpa [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head]
          using hforward.2
      · simpa [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head]
          using hforward.1
    have hsymm_not_forward :
        ¬ (e.symm.tail = a ∧ e.symm.head = b) := by
      rintro ⟨ht, _hh⟩
      have hba : b = a := by
        calc
          b = e.head := hforward.2.symm
          _ = e.symm.tail := rfl
          _ = a := ht
      exact hab.ne hba.symm
    have hba : b ≠ a := hab.ne.symm
    simp [dartToExt, hforward, hsymm_backward, hba]
  · by_cases hbackward : e.tail = b ∧ e.head = a
    · have hsymm_forward : e.symm.tail = a ∧ e.symm.head = b := by
        constructor
        · simpa [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head]
            using hbackward.2
        · simpa [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head]
            using hbackward.1
      have hba : b ≠ a := hab.ne.symm
      simp [dartToExt, hbackward, hsymm_forward, hba]
    · have hsymm_not_forward :
          ¬ (e.symm.tail = a ∧ e.symm.head = b) := by
        rintro ⟨ht, hh⟩
        exact hbackward ⟨by simpa [OrientedEdge.tail] using hh,
          by simpa [OrientedEdge.head] using ht⟩
      have hsymm_not_backward :
          ¬ (e.symm.tail = b ∧ e.symm.head = a) := by
        rintro ⟨ht, hh⟩
        exact hforward ⟨by simpa [OrientedEdge.tail] using hh,
          by simpa [OrientedEdge.head] using ht⟩
      have hnot_forward_unfold :
          ¬ (e.head = a ∧ e.tail = b) := by
        simpa [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head]
          using hsymm_not_forward
      have hnot_backward_unfold :
          ¬ (e.head = b ∧ e.tail = a) := by
        simpa [OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head]
          using hsymm_not_backward
      simp [dartToExt, hforward, hbackward, hnot_forward_unfold,
        hnot_backward_unfold, OrientedEdge.edgePerm]

@[simp]
theorem extTail_dartEquivExt
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge G) :
    extTail (G := G) a b (dartEquivExt (G := G) (a := a) (b := b) hab e) =
      e.tail := by
  classical
  change extTail (G := G) a b (dartToExt (G := G) (a := a) (b := b) e) =
    e.tail
  by_cases hforward : e.tail = a ∧ e.head = b
  · simp [dartToExt, hforward, extTail]
  · by_cases hbackward : e.tail = b ∧ e.head = a
    · have hba : b ≠ a := hab.ne.symm
      simp [dartToExt, hbackward, hba, extTail]
    · have hnot : s(e.tail, e.head) ≠ s(a, b) := by
        intro hs
        have hcases :
            (e.tail = a ∧ e.head = b) ∨
              (e.tail = b ∧ e.head = a) := by
          simpa [Sym2.eq_iff] using hs
        exact hcases.elim hforward hbackward
      have hdart :
          dartToExt (G := G) (a := a) (b := b) e =
            ExtDart.old (oldDart (G := G) (a := a) (b := b) e hnot) := by
        simp [dartToExt, hforward, hbackward]
      rw [hdart]
      simp [extTail, oldDart, OrientedEdge.tail]

@[simp]
theorem extHead_dartEquivExt
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge G) :
    extHead (G := G) a b (dartEquivExt (G := G) (a := a) (b := b) hab e) =
      e.head := by
  classical
  change extHead (G := G) a b (dartToExt (G := G) (a := a) (b := b) e) =
    e.head
  by_cases hforward : e.tail = a ∧ e.head = b
  · simp [dartToExt, hforward, extHead]
  · by_cases hbackward : e.tail = b ∧ e.head = a
    · have hba : b ≠ a := hab.ne.symm
      simp [dartToExt, hbackward, hba, extHead]
    · have hnot : s(e.tail, e.head) ≠ s(a, b) := by
        intro hs
        have hcases :
            (e.tail = a ∧ e.head = b) ∨
              (e.tail = b ∧ e.head = a) := by
          simpa [Sym2.eq_iff] using hs
        exact hcases.elim hforward hbackward
      have hdart :
          dartToExt (G := G) (a := a) (b := b) e =
            ExtDart.old (oldDart (G := G) (a := a) (b := b) e hnot) := by
        simp [dartToExt, hforward, hbackward]
      rw [hdart]
      simp [extHead, oldDart, OrientedEdge.head]

/-- Transport an extended deleted-edge node permutation back to a graph
rotation system.  The remaining add-edge deletion branch can now focus on
constructing such an extended node permutation and proving the two local
conditions here: tail preservation and one node orbit per extended tail. -/
noncomputable def rotationSystemOfExtNode
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (N : Equiv.Perm (ExtDart (OrientedEdge (deletedGraph G a b))))
    (hN_tail :
      forall x : ExtDart (OrientedEdge (deletedGraph G a b)),
        extTail (G := G) a b (N x) = extTail (G := G) a b x)
    (hN_orbit :
      forall x y : ExtDart (OrientedEdge (deletedGraph G a b)),
        extTail (G := G) a b x = extTail (G := G) a b y →
          PermReachable N x y) :
    RotationSystem G where
  node :=
    (((dartEquivExt (G := G) (a := a) (b := b) hab).trans N).trans
      (dartEquivExt (G := G) (a := a) (b := b) hab).symm)
  node_tail := by
    intro e
    let E := dartEquivExt (G := G) (a := a) (b := b) hab
    calc
      (E.symm (N (E e))).tail =
          extTail (G := G) a b (E (E.symm (N (E e)))) := by
        exact (extTail_dartEquivExt (G := G) (a := a) (b := b) hab
          (E.symm (N (E e)))).symm
      _ = extTail (G := G) a b (N (E e)) := by simp [E]
      _ = extTail (G := G) a b (E e) := hN_tail (E e)
      _ = e.tail :=
        extTail_dartEquivExt (G := G) (a := a) (b := b) hab e
  node_orbit_of_same_tail := by
    intro e f hef
    let E := dartEquivExt (G := G) (a := a) (b := b) hab
    let S : Equiv.Perm (OrientedEdge G) :=
      (((E.trans N).trans E.symm))
    have hext :
        extTail (G := G) a b (E e) = extTail (G := G) a b (E f) := by
      simpa [E, extTail_dartEquivExt (G := G) (a := a) (b := b) hab]
        using hef
    have hN : PermReachable N (E e) (E f) := hN_orbit (E e) (E f) hext
    have hconj : forall x : OrientedEdge G, E (S x) = N (E x) := by
      intro x
      simp [S, E]
    exact (permReachable_conj_iff E S N hconj).mpr hN

/-- Node permutation for adding back a deleted edge.  `ExtDart.new` is the
fresh dart with tail `a`, and `ExtDart.newEdge` is the fresh dart with tail
`b`.  When a pivot is present, the corresponding fresh dart is inserted
immediately after that old dart in the old rotation cycle; when no pivot is
present, that fresh dart is a singleton node. -/
def insertedEdgeNode
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall p : α, pivotA = some p -> pivotB ≠ some p) :
    Equiv.Perm (ExtDart α) where
  toFun
    | ExtDart.new =>
        match pivotA with
        | none => ExtDart.new
        | some p => ExtDart.old (σ p)
    | ExtDart.newEdge =>
        match pivotB with
        | none => ExtDart.newEdge
        | some p => ExtDart.old (σ p)
    | ExtDart.old x =>
        match pivotA with
        | some p => if x = p then ExtDart.new
            else
              match pivotB with
              | none => ExtDart.old (σ x)
              | some q => if x = q then ExtDart.newEdge else ExtDart.old (σ x)
        | none =>
            match pivotB with
            | none => ExtDart.old (σ x)
            | some q => if x = q then ExtDart.newEdge else ExtDart.old (σ x)
  invFun
    | ExtDart.new =>
        match pivotA with
        | none => ExtDart.new
        | some p => ExtDart.old p
    | ExtDart.newEdge =>
        match pivotB with
        | none => ExtDart.newEdge
        | some p => ExtDart.old p
    | ExtDart.old y =>
        match pivotA with
        | some p => if y = σ p then ExtDart.new
            else
              match pivotB with
              | none => ExtDart.old (σ.symm y)
              | some q =>
                  if y = σ q then ExtDart.newEdge else ExtDart.old (σ.symm y)
        | none =>
            match pivotB with
            | none => ExtDart.old (σ.symm y)
            | some q =>
                if y = σ q then ExtDart.newEdge else ExtDart.old (σ.symm y)
  left_inv := by
    intro x
    cases pivotA with
    | none =>
        cases pivotB with
        | none =>
            cases x <;> simp
        | some q =>
            cases x with
            | new => rfl
            | newEdge => simp
            | old x =>
                by_cases hx : x = q
                · subst x
                  simp
                · have hsx : σ x ≠ σ q := by
                    intro h
                    exact hx (σ.injective h)
                  simp [hx, hsx]
    | some p =>
        cases pivotB with
        | none =>
            cases x with
            | new => simp
            | newEdge => rfl
            | old x =>
                by_cases hx : x = p
                · subst x
                  simp
                · have hsx : σ x ≠ σ p := by
                    intro h
                    exact hx (σ.injective h)
                  simp [hx, hsx]
        | some q =>
            have hpq : p ≠ q := by
              intro hpq
              exact hAB p rfl (by simp [hpq])
            have hqp : q ≠ p := hpq.symm
            cases x with
            | new =>
                simp
            | newEdge =>
                simp [hqp]
            | old x =>
                by_cases hxp : x = p
                · subst x
                  simp
                · by_cases hxq : x = q
                  · subst x
                    simp [hxp]
                  · have hsxp : σ x ≠ σ p := by
                      intro h
                      exact hxp (σ.injective h)
                    have hsxq : σ x ≠ σ q := by
                      intro h
                      exact hxq (σ.injective h)
                    simp [hxp, hxq, hsxp, hsxq]
  right_inv := by
    intro x
    cases pivotA with
    | none =>
        cases pivotB with
        | none =>
            cases x <;> simp
        | some q =>
            cases x with
            | new => rfl
            | newEdge => simp
            | old y =>
                by_cases hy : y = σ q
                · subst y
                  simp
                · have hpre : σ.symm y ≠ q := by
                    intro h
                    apply hy
                    calc
                      y = σ (σ.symm y) := by simp
                      _ = σ q := by rw [h]
                  simp [hy, hpre]
    | some p =>
        cases pivotB with
        | none =>
            cases x with
            | new => simp
            | newEdge => rfl
            | old y =>
                by_cases hy : y = σ p
                · subst y
                  simp
                · have hpre : σ.symm y ≠ p := by
                    intro h
                    apply hy
                    calc
                      y = σ (σ.symm y) := by simp
                      _ = σ p := by rw [h]
                  simp [hy, hpre]
        | some q =>
            have hpq : p ≠ q := by
              intro hpq
              exact hAB p rfl (by simp [hpq])
            have hqp : q ≠ p := hpq.symm
            cases x with
            | new =>
                simp
            | newEdge =>
                simp [hqp]
            | old y =>
                by_cases hyp : y = σ p
                · subst y
                  simp
                · by_cases hyq : y = σ q
                  · subst y
                    simp [hyp]
                  · have hprep : σ.symm y ≠ p := by
                      intro h
                      apply hyp
                      calc
                        y = σ (σ.symm y) := by simp
                        _ = σ p := by rw [h]
                    have hpreq : σ.symm y ≠ q := by
                      intro h
                      apply hyq
                      calc
                        y = σ (σ.symm y) := by simp
                        _ = σ q := by rw [h]
                    simp [hyp, hyq, hprep, hpreq]

@[simp]
theorem insertedEdgeNode_apply
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall p : α, pivotA = some p -> pivotB ≠ some p)
    (x : ExtDart α) :
    insertedEdgeNode σ pivotA pivotB hAB x =
      match x with
      | ExtDart.new =>
          match pivotA with
          | none => ExtDart.new
          | some p => ExtDart.old (σ p)
      | ExtDart.newEdge =>
          match pivotB with
          | none => ExtDart.newEdge
          | some p => ExtDart.old (σ p)
      | ExtDart.old y =>
          match pivotA with
          | some p => if y = p then ExtDart.new
              else
                match pivotB with
                | none => ExtDart.old (σ y)
                | some q =>
                    if y = q then ExtDart.newEdge else ExtDart.old (σ y)
          | none =>
              match pivotB with
              | none => ExtDart.old (σ y)
              | some q =>
                  if y = q then ExtDart.newEdge else ExtDart.old (σ y) := by
  cases pivotA <;> cases pivotB <;> cases x <;> rfl

@[simp]
theorem insertedEdgeNode_new_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotB : Option α)
    (hAB : forall p : α, (none : Option α) = some p -> pivotB ≠ some p) :
    insertedEdgeNode σ none pivotB hAB ExtDart.new = ExtDart.new :=
  rfl

@[simp]
theorem insertedEdgeNode_new_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) (pivotB : Option α)
    (hAB : forall q : α, (some p : Option α) = some q -> pivotB ≠ some q) :
    insertedEdgeNode σ (some p) pivotB hAB ExtDart.new = ExtDart.old (σ p) :=
  rfl

@[simp]
theorem insertedEdgeNode_newEdge_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA : Option α)
    (hAB : forall p : α, pivotA = some p -> (none : Option α) ≠ some p) :
    insertedEdgeNode σ pivotA none hAB ExtDart.newEdge = ExtDart.newEdge := by
  cases pivotA <;> rfl

@[simp]
theorem insertedEdgeNode_newEdge_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA : Option α) (p : α)
    (hAB : forall q : α, pivotA = some q -> (some p : Option α) ≠ some q) :
    insertedEdgeNode σ pivotA (some p) hAB ExtDart.newEdge =
      ExtDart.old (σ p) := by
  cases pivotA <;> rfl

theorem insertedEdgeNode_old_some_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q x : α)
    (hAB : forall r : α, (some p : Option α) = some r ->
      (some q : Option α) ≠ some r) :
    insertedEdgeNode σ (some p) (some q) hAB (ExtDart.old x) =
      if x = p then ExtDart.new
      else if x = q then ExtDart.newEdge
      else ExtDart.old (σ x) :=
  rfl

theorem insertedEdgeNode_old_some_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p x : α)
    (hAB : forall r : α, (some p : Option α) = some r ->
      (none : Option α) ≠ some r) :
    insertedEdgeNode σ (some p) none hAB (ExtDart.old x) =
      if x = p then ExtDart.new else ExtDart.old (σ x) :=
  rfl

theorem insertedEdgeNode_old_none_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (q x : α)
    (hAB : forall r : α, (none : Option α) = some r ->
      (some q : Option α) ≠ some r) :
    insertedEdgeNode σ none (some q) hAB (ExtDart.old x) =
      if x = q then ExtDart.newEdge else ExtDart.old (σ x) :=
  rfl

@[simp]
theorem insertedEdgeNode_old_none_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α)
    (hAB : forall r : α, (none : Option α) = some r ->
      (none : Option α) ≠ some r)
    (x : α) :
    insertedEdgeNode σ none none hAB (ExtDart.old x) =
      ExtDart.old (σ x) :=
  rfl

theorem insertedEdgeNode_old_forward_reachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall p : α, pivotA = some p -> pivotB ≠ some p)
    (x : α) :
    PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
      (ExtDart.old x) (ExtDart.old (σ x)) := by
  cases pivotA with
  | none =>
      cases pivotB with
      | none =>
          simpa using
            (PermReachable.forward
              (insertedEdgeNode σ none none hAB) (ExtDart.old x))
      | some q =>
          by_cases hxq : x = q
          · subst x
            exact
              PermReachable.trans (insertedEdgeNode σ none (some q) hAB)
                (by
                  simpa using
                    (PermReachable.forward
                      (insertedEdgeNode σ none (some q) hAB)
                      (ExtDart.old q)))
                (by
                  simpa using
                    (PermReachable.forward
                      (insertedEdgeNode σ none (some q) hAB)
                      ExtDart.newEdge))
          · simpa [insertedEdgeNode_apply, hxq] using
              (PermReachable.forward
                (insertedEdgeNode σ none (some q) hAB)
                (ExtDart.old x))
  | some p =>
      cases pivotB with
      | none =>
          by_cases hxp : x = p
          · subst x
            exact
              PermReachable.trans (insertedEdgeNode σ (some p) none hAB)
                (by
                  simpa using
                    (PermReachable.forward
                      (insertedEdgeNode σ (some p) none hAB)
                      (ExtDart.old p)))
                (by
                  simpa using
                    (PermReachable.forward
                      (insertedEdgeNode σ (some p) none hAB)
                      ExtDart.new))
          · simpa [insertedEdgeNode_apply, hxp] using
              (PermReachable.forward
                (insertedEdgeNode σ (some p) none hAB)
                (ExtDart.old x))
      | some q =>
          have hpq : p ≠ q := by
            intro hpq
            exact hAB p rfl (by simp [hpq])
          have hqp : q ≠ p := hpq.symm
          by_cases hxp : x = p
          · subst x
            exact
              PermReachable.trans (insertedEdgeNode σ (some p) (some q) hAB)
                (by
                  simpa using
                    (PermReachable.forward
                      (insertedEdgeNode σ (some p) (some q) hAB)
                      (ExtDart.old p)))
                (by
                  simpa using
                    (PermReachable.forward
                      (insertedEdgeNode σ (some p) (some q) hAB)
                      ExtDart.new))
          · by_cases hxq : x = q
            · subst x
              exact
                PermReachable.trans
                  (insertedEdgeNode σ (some p) (some q) hAB)
                  (by
                    simpa [hqp] using
                      (PermReachable.forward
                        (insertedEdgeNode σ (some p) (some q) hAB)
                        (ExtDart.old q)))
                  (by
                    simpa using
                      (PermReachable.forward
                        (insertedEdgeNode σ (some p) (some q) hAB)
                        ExtDart.newEdge))
            · simpa [insertedEdgeNode_apply, hxp, hxq] using
                (PermReachable.forward
                  (insertedEdgeNode σ (some p) (some q) hAB)
                  (ExtDart.old x))

theorem insertedEdgeNode_old_reachable_of_iterate
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall p : α, pivotA = some p -> pivotB ≠ some p) :
    forall (n : ℕ) (x : α),
      PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
        (ExtDart.old x) (ExtDart.old (((σ : α -> α)^[n]) x))
  | 0, x => by
      exact PermReachable.refl
        (insertedEdgeNode σ pivotA pivotB hAB) (ExtDart.old x)
  | n + 1, x => by
      have htail :
          PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
            (ExtDart.old x)
            (ExtDart.old (((σ : α -> α)^[n]) x)) :=
        insertedEdgeNode_old_reachable_of_iterate σ pivotA pivotB hAB n x
      have hstep :
          PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
            (ExtDart.old (((σ : α -> α)^[n]) x))
            (ExtDart.old (σ (((σ : α -> α)^[n]) x))) :=
        insertedEdgeNode_old_forward_reachable σ pivotA pivotB hAB
          (((σ : α -> α)^[n]) x)
      simpa [Function.iterate_succ_apply'] using
        PermReachable.trans (insertedEdgeNode σ pivotA pivotB hAB) htail hstep

theorem insertedEdgeNode_old_reachable_of_permReachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall p : α, pivotA = some p -> pivotB ≠ some p)
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
      (ExtDart.old x) (ExtDart.old y) := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
  simpa [hn] using
    insertedEdgeNode_old_reachable_of_iterate σ pivotA pivotB hAB n x

theorem insertedEdgeNode_new_reachable_old_of_permReachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) (pivotB : Option α)
    (hAB : forall r : α, (some p : Option α) = some r -> pivotB ≠ some r)
    {x : α}
    (hpx : PermReachable σ p x) :
    PermReachable (insertedEdgeNode σ (some p) pivotB hAB)
      ExtDart.new (ExtDart.old x) := by
  have hnew_p :
      PermReachable (insertedEdgeNode σ (some p) pivotB hAB)
        ExtDart.new (ExtDart.old p) := by
    exact
      PermReachable.symm (insertedEdgeNode σ (some p) pivotB hAB)
        (by
          simpa using
            (PermReachable.forward
              (insertedEdgeNode σ (some p) pivotB hAB)
              (ExtDart.old p)))
  exact
    PermReachable.trans (insertedEdgeNode σ (some p) pivotB hAB) hnew_p
      (insertedEdgeNode_old_reachable_of_permReachable
        σ (some p) pivotB hAB hpx)

theorem insertedEdgeNode_new_reachable_old_of_permReachable_of_eq_some
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall r : α, pivotA = some r -> pivotB ≠ some r)
    {p x : α}
    (hp : pivotA = some p)
    (hpx : PermReachable σ p x) :
    PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
      ExtDart.new (ExtDart.old x) := by
  subst pivotA
  exact insertedEdgeNode_new_reachable_old_of_permReachable
    σ p pivotB hAB hpx

theorem insertedEdgeNode_newEdge_reachable_old_of_permReachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA : Option α) (q : α)
    (hAB : forall r : α, pivotA = some r -> (some q : Option α) ≠ some r)
    {x : α}
    (hqx : PermReachable σ q x) :
    PermReachable (insertedEdgeNode σ pivotA (some q) hAB)
      ExtDart.newEdge (ExtDart.old x) := by
  have hnew_q :
      PermReachable (insertedEdgeNode σ pivotA (some q) hAB)
        ExtDart.newEdge (ExtDart.old q) := by
    exact
      PermReachable.symm (insertedEdgeNode σ pivotA (some q) hAB)
        (by
          cases pivotA with
          | none =>
              simpa using
                (PermReachable.forward
                  (insertedEdgeNode σ none (some q) hAB)
                  (ExtDart.old q))
          | some p =>
              have hqp : q ≠ p := by
                intro hqp
                exact hAB p rfl (by simp [hqp])
              simpa [hqp] using
                (PermReachable.forward
                  (insertedEdgeNode σ (some p) (some q) hAB)
                  (ExtDart.old q)))
  exact
    PermReachable.trans (insertedEdgeNode σ pivotA (some q) hAB) hnew_q
      (insertedEdgeNode_old_reachable_of_permReachable
        σ pivotA (some q) hAB hqx)

theorem insertedEdgeNode_newEdge_reachable_old_of_permReachable_of_eq_some
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (pivotA pivotB : Option α)
    (hAB : forall r : α, pivotA = some r -> pivotB ≠ some r)
    {q x : α}
    (hq : pivotB = some q)
    (hqx : PermReachable σ q x) :
    PermReachable (insertedEdgeNode σ pivotA pivotB hAB)
      ExtDart.newEdge (ExtDart.old x) := by
  subst pivotB
  exact insertedEdgeNode_newEdge_reachable_old_of_permReachable
    σ pivotA q hAB hqx

def insertedEdgeNodeSomeSomeOrbitCode
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) :
    ExtDart α -> PermOrbit σ
  | ExtDart.new => PermOrbit.of σ p
  | ExtDart.newEdge => PermOrbit.of σ q
  | ExtDart.old x => PermOrbit.of σ x

theorem insertedEdgeNodeSomeSomeOrbitCode_of_link
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hAB : forall r : α, (some p : Option α) = some r ->
      (some q : Option α) ≠ some r)
    {x y : ExtDart α}
    (hxy : PermLink (insertedEdgeNode σ (some p) (some q) hAB) x y) :
    insertedEdgeNodeSomeSomeOrbitCode σ p q x =
      insertedEdgeNodeSomeSomeOrbitCode σ p q y := by
  have hpq : p ≠ q := by
    intro hpq
    exact hAB p rfl (by simp [hpq])
  have hqp : q ≠ p := hpq.symm
  cases hxy with
  | forward =>
      cases x with
      | new =>
          simp [insertedEdgeNodeSomeSomeOrbitCode]
          exact (PermOrbit.of_apply σ p).symm
      | newEdge =>
          simp [insertedEdgeNodeSomeSomeOrbitCode]
          exact (PermOrbit.of_apply σ q).symm
      | old x =>
          by_cases hxp : x = p
          · subst x
            simp [insertedEdgeNodeSomeSomeOrbitCode]
          · by_cases hxq : x = q
            · subst x
              simp [insertedEdgeNodeSomeSomeOrbitCode, hqp]
            · simp [insertedEdgeNodeSomeSomeOrbitCode,
                insertedEdgeNode_apply, hxp, hxq]
              exact (PermOrbit.of_apply σ x).symm
  | backward =>
      cases x with
      | new =>
          change PermOrbit.of σ p =
            insertedEdgeNodeSomeSomeOrbitCode σ p q
              ((insertedEdgeNode σ (some p) (some q) hAB).symm ExtDart.new)
          simp [insertedEdgeNode, insertedEdgeNodeSomeSomeOrbitCode]
      | newEdge =>
          change PermOrbit.of σ q =
            insertedEdgeNodeSomeSomeOrbitCode σ p q
              ((insertedEdgeNode σ (some p) (some q) hAB).symm ExtDart.newEdge)
          simp [insertedEdgeNode, insertedEdgeNodeSomeSomeOrbitCode]
      | old x =>
          by_cases hxp : x = σ p
          · subst x
            simp [insertedEdgeNode, insertedEdgeNodeSomeSomeOrbitCode]
            exact PermOrbit.of_apply σ p
          · by_cases hxq : x = σ q
            · subst x
              have hsymm_qp : σ q ≠ σ p := by
                intro h
                exact hqp (σ.injective h)
              simp [insertedEdgeNode, insertedEdgeNodeSomeSomeOrbitCode,
                hsymm_qp]
              exact PermOrbit.of_apply σ q
            · have hpre_p : σ.symm x ≠ p := by
                intro h
                apply hxp
                calc
                  x = σ (σ.symm x) := by simp
                  _ = σ p := by rw [h]
              have hpre_q : σ.symm x ≠ q := by
                intro h
                apply hxq
                calc
                  x = σ (σ.symm x) := by simp
                  _ = σ q := by rw [h]
              simp [insertedEdgeNode, insertedEdgeNodeSomeSomeOrbitCode,
                hxp, hxq]
              exact (PermOrbit.of_symm_apply σ x).symm

theorem insertedEdgeNodeSomeSomeOrbitCode_of_reachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hAB : forall r : α, (some p : Option α) = some r ->
      (some q : Option α) ≠ some r)
    {x y : ExtDart α}
    (hxy : PermReachable (insertedEdgeNode σ (some p) (some q) hAB) x y) :
    insertedEdgeNodeSomeSomeOrbitCode σ p q x =
      insertedEdgeNodeSomeSomeOrbitCode σ p q y :=
  hxy.apply_eq (insertedEdgeNodeSomeSomeOrbitCode σ p q)
    (fun {_ _} h => insertedEdgeNodeSomeSomeOrbitCode_of_link σ p q hAB h)

noncomputable def insertedEdgeNodeSomeSomeOrbitEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hAB : forall r : α, (some p : Option α) = some r ->
      (some q : Option α) ≠ some r) :
    PermOrbit (insertedEdgeNode σ (some p) (some q) hAB) ≃
      PermOrbit σ where
  toFun :=
    Quotient.lift
      (insertedEdgeNodeSomeSomeOrbitCode σ p q)
      (by
        intro x y hxy
        exact insertedEdgeNodeSomeSomeOrbitCode_of_reachable σ p q hAB hxy)
  invFun :=
    Quotient.lift
      (fun x => PermOrbit.of
        (insertedEdgeNode σ (some p) (some q) hAB) (ExtDart.old x))
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of (insertedEdgeNode σ (some p) (some q) hAB)
          (insertedEdgeNode_old_reachable_of_permReachable
            σ (some p) (some q) hAB hxy))
  left_inv := by
    intro qorb
    induction qorb using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply PermOrbit.of_eq_of
            exact
              PermReachable.symm (insertedEdgeNode σ (some p) (some q) hAB)
                (insertedEdgeNode_new_reachable_old_of_permReachable
                  σ p (some q) hAB
                  (PermReachable.refl σ p))
        | newEdge =>
            apply PermOrbit.of_eq_of
            exact
              PermReachable.symm (insertedEdgeNode σ (some p) (some q) hAB)
                (insertedEdgeNode_newEdge_reachable_old_of_permReachable
                  σ (some p) q hAB
                  (PermReachable.refl σ q))
        | old x => rfl
  right_inv := by
    intro qorb
    induction qorb using Quotient.inductionOn with
    | h x => rfl

theorem insertedEdgeNodeSomeSome_nodeOrbitCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hAB : forall r : α, (some p : Option α) = some r ->
      (some q : Option α) ≠ some r) :
    Nat.card (PermOrbit (insertedEdgeNode σ (some p) (some q) hAB)) =
      Nat.card (PermOrbit σ) := by
  rw [Nat.card_congr (insertedEdgeNodeSomeSomeOrbitEquiv σ p q hAB)]


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
