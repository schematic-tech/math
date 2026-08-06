import Mathlib.GroupTheory.Perm.Fin
import Schematic.Math.GraphTheory.Embedding.RotationSystem


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Mathlib's `SameCycle` relation implies the local bidirectional
`PermReachable` relation used by the hypermap development. -/
theorem sameCycle_permReachable
    {α : Type u} [Fintype α] {σ : Equiv.Perm α} {x y : α}
    (h : σ.SameCycle x y) :
    PermReachable σ x y := by
  classical
  rcases h.exists_nat_pow_eq with ⟨n, hn⟩
  exact permReachable_of_iterate_eq σ (by simpa [Equiv.Perm.coe_pow] using hn)

/-- Every finite type admits a permutation with a single orbit.  For types of
cardinality at least two this is the usual cyclic permutation, transported
from `Fin n`; for subsingleton types the identity permutation is already
transitive. -/
theorem exists_perm_single_orbit
    (α : Type u) [Fintype α] [DecidableEq α] :
    Exists fun σ : Equiv.Perm α =>
      forall x y : α, PermReachable σ x y := by
  classical
  by_cases hcard : 2 ≤ Fintype.card α
  · let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
    let τ : Equiv.Perm (Fin (Fintype.card α)) := finRotate (Fintype.card α)
    let σ : Equiv.Perm α := e.permCongr τ
    refine ⟨σ, ?_⟩
    intro x y
    have hτcycle : τ.IsCycle := by
      simpa [τ] using (isCycle_finRotate_of_le (n := Fintype.card α) hcard)
    have hτsupport : τ.support = Finset.univ := by
      simpa [τ] using (support_finRotate_of_le (n := Fintype.card α) hcard)
    have hx : τ (e.symm x) ≠ e.symm x := by
      rw [← Equiv.Perm.mem_support]
      rw [hτsupport]
      exact Finset.mem_univ _
    have hy : τ (e.symm y) ≠ e.symm y := by
      rw [← Equiv.Perm.mem_support]
      rw [hτsupport]
      exact Finset.mem_univ _
    have hsame : τ.SameCycle (e.symm x) (e.symm y) :=
      hτcycle.sameCycle hx hy
    have hreachτ : PermReachable τ (e.symm x) (e.symm y) :=
      sameCycle_permReachable hsame
    have hconj :
        forall z : Fin (Fintype.card α), e (τ z) = σ (e z) := by
      intro z
      simp [σ]
    have hreachσ := permReachable_conj e τ σ hconj hreachτ
    simpa using hreachσ
  · have hle : Fintype.card α ≤ 1 := by omega
    haveI : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hle
    refine ⟨1, ?_⟩
    intro x y
    have hxy : x = y := Subsingleton.elim x y
    subst y
    exact PermReachable.refl 1 x

/-- A chosen one-orbit permutation on a finite type. -/
noncomputable def singleOrbitPerm
    (α : Type u) [Fintype α] [DecidableEq α] :
    Equiv.Perm α :=
  Classical.choose (exists_perm_single_orbit α)

theorem singleOrbitPerm_reachable
    (α : Type u) [Fintype α] [DecidableEq α] (x y : α) :
    PermReachable (singleOrbitPerm α) x y :=
  (Classical.choose_spec (exists_perm_single_orbit α)) x y

/-- If a permutation fixes `x`, then the generated orbit from `x` contains
only `x`. -/
theorem permReachable_eq_of_apply_eq_self
    {α : Type u} {σ : Equiv.Perm α} {x y : α}
    (hfix : σ x = x)
    (hxy : PermReachable σ x y) :
    y = x := by
  induction hxy with
  | refl =>
      rfl
  | @tail b c _ hbc ih =>
      subst b
      cases hbc with
      | forward =>
          exact hfix
      | backward =>
          have hsymm : σ.symm x = x := by
            apply σ.injective
            simp [hfix]
          simp [hsymm]

/-- A single undirected permutation link is either the forward step or the
backward step.  Keeping this as an equality lemma avoids dependent case splits
in later graph-edge proofs. -/
theorem permLink_eq_or_eq_symm
    {α : Type u} {σ : Equiv.Perm α} {x y : α}
    (hxy : PermLink σ x y) :
    y = σ x ∨ y = σ.symm x := by
  cases hxy with
  | forward =>
      exact Or.inl rfl
  | backward =>
      exact Or.inr rfl

/-- Apply one chosen cyclic permutation independently on each fibre of a
dependent sum.  This is the abstract version of choosing a cyclic order of the
outgoing darts at every graph vertex. -/
noncomputable def sigmaFiberPerm
    {ι : Type u} (β : ι -> Type v)
    [forall i, Fintype (β i)] [forall i, DecidableEq (β i)] :
    Equiv.Perm (Sigma β) where
  toFun s := ⟨s.1, singleOrbitPerm (β s.1) s.2⟩
  invFun s := ⟨s.1, (singleOrbitPerm (β s.1)).symm s.2⟩
  left_inv := by
    intro s
    cases s
    simp [singleOrbitPerm]
  right_inv := by
    intro s
    cases s
    simp [singleOrbitPerm]

/-- Apply an arbitrary chosen permutation independently on every fibre of a
dependent sum. -/
noncomputable def sigmaPerm
    {ι : Type u} (β : ι -> Type v)
    (π : forall i, Equiv.Perm (β i)) :
    Equiv.Perm (Sigma β) where
  toFun s := ⟨s.1, π s.1 s.2⟩
  invFun s := ⟨s.1, (π s.1).symm s.2⟩
  left_inv := by
    intro s
    cases s
    simp
  right_inv := by
    intro s
    cases s
    simp

theorem sigmaPerm_permLink
    {ι : Type u} {β : ι -> Type v}
    {π : forall i, Equiv.Perm (β i)}
    {x : ι} {a b : β x}
    (h : PermLink (π x) a b) :
    PermLink (sigmaPerm β π) (Sigma.mk x a) (Sigma.mk x b) := by
  cases h with
  | forward =>
      simpa [sigmaPerm] using
        (PermLink.forward (σ := sigmaPerm β π) (Sigma.mk x a))
  | backward =>
      simpa [sigmaPerm] using
        (PermLink.backward (σ := sigmaPerm β π) (Sigma.mk x a))

theorem sigmaPerm_reachable_of_same_base
    {ι : Type u} {β : ι -> Type v}
    {π : forall i, Equiv.Perm (β i)}
    {x : ι} {a b : β x}
    (h : PermReachable (π x) a b) :
    PermReachable (sigmaPerm β π) (Sigma.mk x a) (Sigma.mk x b) := by
  induction h with
  | refl =>
      exact PermReachable.refl (sigmaPerm β π) (Sigma.mk x a)
  | tail _ hlink ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (sigmaPerm_permLink hlink))

/-- Orbits of a fibrewise permutation are exactly the disjoint union of the
orbits of the fibre permutations.  This is the count-level replacement for
component-hypermap representative transport in the component gluing proof. -/
noncomputable def sigmaPermOrbitEquiv
    {ι : Type u} {β : ι -> Type v}
    (π : forall i, Equiv.Perm (β i)) :
    PermOrbit (sigmaPerm β π) ≃
      Sigma fun i : ι => PermOrbit (π i) where
  toFun := Quotient.lift
    (fun s : Sigma β => ⟨s.1, PermOrbit.of (π s.1) s.2⟩)
    (by
      intro s t hst
      induction hst with
      | refl =>
          rfl
      | @tail b c _ hbc ih =>
          have hstep :
              (⟨b.1, PermOrbit.of (π b.1) b.2⟩ :
                  Sigma fun i : ι => PermOrbit (π i)) =
                ⟨c.1, PermOrbit.of (π c.1) c.2⟩ := by
            cases hbc with
            | forward =>
                cases b
                simp [sigmaPerm, PermOrbit.of_apply]
            | backward =>
                cases b
                simp [sigmaPerm, PermOrbit.of_symm_apply]
          exact ih.trans hstep)
  invFun s :=
    Quotient.lift
      (fun a : β s.1 => PermOrbit.of (sigmaPerm β π) (Sigma.mk s.1 a))
      (by
        intro a b hab
        exact PermOrbit.of_eq_of (sigmaPerm β π)
          (sigmaPerm_reachable_of_same_base hab))
      s.2
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro s
    cases s
    rfl
  right_inv := by
    intro s
    cases s with
    | mk i o =>
        refine Quotient.inductionOn o ?_
        intro a
        rfl

theorem sigmaPerm_orbitCount_eq_sum
    {ι : Type u} [Fintype ι] {β : ι -> Type v}
    [forall i, Fintype (β i)]
    (π : forall i, Equiv.Perm (β i)) :
    Nat.card (PermOrbit (sigmaPerm β π)) =
      ∑ i : ι, Nat.card (PermOrbit (π i)) := by
  classical
  rw [Nat.card_congr (sigmaPermOrbitEquiv (β := β) π)]
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp [Nat.card_eq_fintype_card]

theorem sigmaFiberPerm_permLink
    {ι : Type u} {β : ι -> Type v}
    [forall i, Fintype (β i)] [forall i, DecidableEq (β i)]
    {x : ι} {a b : β x}
    (h : PermLink (singleOrbitPerm (β x)) a b) :
    PermLink (sigmaFiberPerm β) (Sigma.mk x a) (Sigma.mk x b) := by
  cases h with
  | forward =>
      simpa [sigmaFiberPerm] using
        (PermLink.forward (σ := sigmaFiberPerm β) (Sigma.mk x a))
  | backward =>
      simpa [sigmaFiberPerm] using
        (PermLink.backward (σ := sigmaFiberPerm β) (Sigma.mk x a))

theorem sigmaFiberPerm_reachable_of_same_base
    {ι : Type u} {β : ι -> Type v}
    [forall i, Fintype (β i)] [forall i, DecidableEq (β i)]
    {x : ι} (a b : β x) :
    PermReachable (sigmaFiberPerm β) (Sigma.mk x a) (Sigma.mk x b) := by
  have hlocal := singleOrbitPerm_reachable (β x) a b
  induction hlocal with
  | refl =>
      exact PermReachable.refl (sigmaFiberPerm β) (Sigma.mk x a)
  | tail _ hlink ih =>
      exact Relation.ReflTransGen.trans ih
        (Relation.ReflTransGen.single (sigmaFiberPerm_permLink hlink))

theorem sigmaFiberPerm_reachable_of_fst_eq
    {ι : Type u} {β : ι -> Type v}
    [forall i, Fintype (β i)] [forall i, DecidableEq (β i)]
    {s t : Sigma β} (hst : s.1 = t.1) :
    PermReachable (sigmaFiberPerm β) s t := by
  cases s with
  | mk x a =>
      cases t with
      | mk y b =>
          dsimp at hst
          subst y
          exact sigmaFiberPerm_reachable_of_same_base a b

/-- Outgoing oriented graph edges at a fixed tail vertex. -/
abbrev OutgoingEdge {V : Type u} (G : SimpleGraph V) (x : V) :=
  {e : OrientedEdge G // e.tail = x}

/-- Oriented graph edges are the dependent sum of their tail fibres. -/
noncomputable def orientedEdgeTailSigmaEquiv
    {V : Type u} {G : SimpleGraph V} :
    OrientedEdge G ≃ Sigma (OutgoingEdge G) where
  toFun e := ⟨e.tail, ⟨e, rfl⟩⟩
  invFun s := s.2.1
  left_inv := by
    intro e
    rfl
  right_inv := by
    intro s
    cases s with
    | mk x e =>
        cases e with
        | mk e he =>
            cases he
            rfl

/-- A completely general rotation system obtained by putting an arbitrary
cyclic order on the outgoing darts of every vertex.  This is the structural
bridge primitive used by later planar embedding arguments: after graph-side
work supplies the Euler/face count, this produces the required hypermap
without any degree-two special casing. -/
noncomputable def arbitraryRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    RotationSystem G where
  node := (orientedEdgeTailSigmaEquiv (G := G)).permCongr.symm
    (sigmaFiberPerm (OutgoingEdge G))
  node_tail := by
    intro e
    simp [orientedEdgeTailSigmaEquiv, sigmaFiberPerm]
    exact (singleOrbitPerm (OutgoingEdge G e.tail) ⟨e, rfl⟩).property
  node_orbit_of_same_tail := by
    intro e f hef
    let E : OrientedEdge G ≃ Sigma (OutgoingEdge G) :=
      orientedEdgeTailSigmaEquiv (G := G)
    let P : Equiv.Perm (Sigma (OutgoingEdge G)) :=
      sigmaFiberPerm (OutgoingEdge G)
    let N : Equiv.Perm (OrientedEdge G) := E.permCongr.symm P
    have hfst : (E e).1 = (E f).1 := by
      simpa [E, orientedEdgeTailSigmaEquiv] using hef
    have hP : PermReachable P (E e) (E f) :=
      sigmaFiberPerm_reachable_of_fst_eq hfst
    have hconj :
        forall s : Sigma (OutgoingEdge G), E.symm (P s) = N (E.symm s) := by
      intro s
      simp [N]
    have hN : PermReachable N (E.symm (E e)) (E.symm (E f)) :=
      permReachable_conj E.symm P N hconj hP
    simpa [E, N] using hN

/-- Deleting an existing edge strictly decreases the finite edge count.  This
is the edge-measure half of the Makarychev/Skopenkov deletion-contraction
induction. -/
theorem edgeFinset_card_deleteEdge_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) :
    (G.deleteEdges ({s(a, b)} : Set (Sym2 V))).edgeFinset.card <
      G.edgeFinset.card := by
  classical
  have hfinset_eq :
      (G.deleteEdges ({s(a, b)} : Set (Sym2 V))).edgeFinset =
        G.edgeFinset \ ({s(a, b)} : Finset (Sym2 V)) := by
    ext e
    simp [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges]
  rw [hfinset_eq]
  rw [Finset.card_sdiff_of_subset]
  · simp
    intro hbot
    rw [hbot] at hab
    simp at hab
  · intro e he
    simp at he
    subst he
    exact (SimpleGraph.mem_edgeFinset).mpr
      ((SimpleGraph.mem_edgeSet G).mpr hab)


end FourColor

end Schematic.Math.GraphTheory
