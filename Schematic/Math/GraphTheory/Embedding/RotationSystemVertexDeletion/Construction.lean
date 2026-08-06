import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.PredicateRestriction
import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.FiberSkipping

/-!
Construction and planarity of a rotation system after deleting one graph vertex.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemVertexDeletion

/-- Original oriented edges whose head survives deletion of `v`. -/
abbrev HeadSurvivingDart
    {V : Type u} (G : SimpleGraph V) (v : V) :=
  {d : OrientedEdge G // d.head ≠ v}

/-- Original oriented edges whose two endpoints survive deletion of `v`. -/
abbrev SurvivingDart
    {V : Type u} (G : SimpleGraph V) (v : V) :=
  {d : HeadSurvivingDart G v // d.1.tail ≠ v}

theorem node_forbidden_unique
    {V : Type u}
    {G : SimpleGraph V} (v : V)
    {x y : OrientedEdge G}
    (htail : x.tail = y.tail)
    (hx : ¬ x.head ≠ v)
    (hy : ¬ y.head ≠ v) :
    x = y := by
  apply Subtype.ext
  apply Prod.ext
  · exact htail
  · exact (not_ne_iff.mp hx).trans (not_ne_iff.mp hy).symm

/-- The original node rotation with the unique dart aimed at `v` skipped in
each surviving tail fibre. -/
def headDeletedNode
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V) :
    Equiv.Perm (HeadSurvivingDart G v) :=
  PermSkipFiber.skip R.node OrientedEdge.tail R.node_tail
    (node_forbidden_unique v)

theorem headDeletedNode_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V)
    (x : HeadSurvivingDart G v) :
    (headDeletedNode R v x).1.tail = x.1.tail :=
  PermSkipFiber.skip_preserves R.node OrientedEdge.tail R.node_tail
    (node_forbidden_unique v) x

theorem headDeletedNode_tail_ne_iff
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V)
    (x : HeadSurvivingDart G v) :
    (headDeletedNode R v x).1.tail ≠ v ↔ x.1.tail ≠ v := by
  rw [headDeletedNode_tail]

/-- Node rotation on original darts with neither endpoint equal to `v`. -/
def survivingNode
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V) :
    Equiv.Perm (SurvivingDart G v) :=
  (headDeletedNode R v).subtypePerm
    (headDeletedNode_tail_ne_iff R v)

theorem survivingNode_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V)
    (x : SurvivingDart G v) :
    (survivingNode R v x).1.1.tail = x.1.1.tail := by
  change (headDeletedNode R v x.1).1.tail = x.1.1.tail
  exact headDeletedNode_tail R v x.1

/-- Oriented edges of the induced vertex-deletion graph are exactly original
darts with both endpoints surviving. -/
def vertexDeletedDartEquiv
    {V : Type u}
    {G : SimpleGraph V} (v : V) :
    OrientedEdge (G.induce {x : V | x ≠ v}) ≃ SurvivingDart G v where
  toFun e :=
    ⟨⟨⟨(((e.tail : {x : V | x ≠ v}) : V),
            ((e.head : {x : V | x ≠ v}) : V)), e.adj⟩,
        e.head.property⟩,
      e.tail.property⟩
  invFun e :=
    ⟨(⟨e.1.1.tail, e.2⟩, ⟨e.1.1.head, e.1.2⟩), e.1.1.adj⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem vertexDeletedDartEquiv_tail
    {V : Type u}
    {G : SimpleGraph V} (v : V)
    (e : OrientedEdge (G.induce {x : V | x ≠ v})) :
    (vertexDeletedDartEquiv v e).1.1.tail = (e.tail : V) :=
  rfl

@[simp]
theorem vertexDeletedDartEquiv_head
    {V : Type u}
    {G : SimpleGraph V} (v : V)
    (e : OrientedEdge (G.induce {x : V | x ≠ v})) :
    (vertexDeletedDartEquiv v e).1.1.head = (e.head : V) :=
  rfl

/-- The node permutation of the vertex-deleted rotation system. -/
def vertexDeletedNode
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V) :
    Equiv.Perm (OrientedEdge (G.induce {x : V | x ≠ v})) :=
  let E := vertexDeletedDartEquiv (G := G) v
  (E.trans (survivingNode R v)).trans E.symm

theorem vertexDeletedNode_conj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V)
    (e : OrientedEdge (G.induce {x : V | x ≠ v})) :
    vertexDeletedDartEquiv v (vertexDeletedNode R v e) =
      survivingNode R v (vertexDeletedDartEquiv v e) := by
  let E := vertexDeletedDartEquiv (G := G) v
  change E (E.symm (survivingNode R v (E e))) =
    survivingNode R v (E e)
  exact E.apply_symm_apply _

theorem survivingNode_reachable_of_same_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    {x y : SurvivingDart G v}
    (hxy : x.1.1.tail = y.1.1.tail) :
    PermReachable (survivingNode R v) x y := by
  have hR : PermReachable R.node x.1.1 y.1.1 :=
    R.node_orbit_of_same_tail x.1.1 y.1.1 hxy
  have hHead :
      PermReachable (headDeletedNode R v) x.1 y.1 := by
    exact
      PermSkipFiber.skip_permReachable_of_permReachable
        R.node OrientedEdge.tail R.node_tail
          (node_forbidden_unique v) hR
  exact
    PermSkipFiber.subtypePerm_permReachable_of_permReachable
      (headDeletedNode R v) (headDeletedNode_tail_ne_iff R v) hHead

theorem vertexDeletedNode_reachable_of_same_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    {e f : OrientedEdge (G.induce {x : V | x ≠ v})}
    (hef : e.tail = f.tail) :
    PermReachable (vertexDeletedNode R v) e f := by
  let E := vertexDeletedDartEquiv (G := G) v
  have htail :
      (E e).1.1.tail = (E f).1.1.tail := by
    exact congrArg Subtype.val hef
  have hsurv :
      PermReachable (survivingNode R v) (E e) (E f) :=
    survivingNode_reachable_of_same_tail R v htail
  have hconj :
      ∀ x : SurvivingDart G v,
        E.symm (survivingNode R v x) =
          vertexDeletedNode R v (E.symm x) := by
    intro x
    apply E.injective
    rw [E.apply_symm_apply]
    exact (vertexDeletedNode_conj R v (E.symm x)).symm
  simpa using
    permReachable_conj E.symm (survivingNode R v)
      (vertexDeletedNode R v) hconj hsurv

/-- Restrict a rotation system to the graph induced away from one vertex.
At every surviving neighbor, the node successor skips the removed dart aimed
at the deleted vertex. -/
def vertexDeletedRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V) :
    RotationSystem (G.induce {x : V | x ≠ v}) where
  node := vertexDeletedNode R v
  node_tail := by
    intro e
    apply Subtype.ext
    calc
      (((vertexDeletedNode R v e).tail :
          {x : V | x ≠ v}) : V) =
          (vertexDeletedDartEquiv v
            (vertexDeletedNode R v e)).1.1.tail := rfl
      _ = (survivingNode R v
            (vertexDeletedDartEquiv v e)).1.1.tail := by
          rw [vertexDeletedNode_conj]
      _ = (vertexDeletedDartEquiv v e).1.1.tail :=
        survivingNode_tail R v _
      _ = ((e.tail : {x : V | x ≠ v}) : V) := rfl
  node_orbit_of_same_tail := by
    intro e f hef
    exact vertexDeletedNode_reachable_of_same_tail R v hef

/-- Direct form of `vertexDeletedDartEquiv`, targeting the predicate used by
Coq `del_node`: both endpoints of the original dart survive. -/
def vertexDeletedPredicateDartEquiv
    {V : Type u}
    {G : SimpleGraph V} (v : V) :
    OrientedEdge (G.induce {x : V | x ≠ v}) ≃
      {d : OrientedEdge G // d.tail ≠ v ∧ d.head ≠ v} where
  toFun e :=
    ⟨⟨(((e.tail : {x : V | x ≠ v}) : V),
        ((e.head : {x : V | x ≠ v}) : V)), e.adj⟩,
      e.tail.property, e.head.property⟩
  invFun e :=
    ⟨(⟨e.1.tail, e.2.1⟩, ⟨e.1.head, e.2.2⟩), e.1.adj⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp]
theorem vertexDeletedPredicateDartEquiv_symm
    {V : Type u}
    {G : SimpleGraph V} (v : V)
    (e : OrientedEdge (G.induce {x : V | x ≠ v})) :
    vertexDeletedPredicateDartEquiv v e.symm =
      ⟨(vertexDeletedPredicateDartEquiv v e).1.symm,
        (vertexDeletedPredicateDartEquiv v e).2.2,
        (vertexDeletedPredicateDartEquiv v e).2.1⟩ := by
  apply Subtype.ext
  rfl

theorem vertexDeletedNode_source
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (R : RotationSystem G) (v : V)
    (e : OrientedEdge (G.induce {x : V | x ≠ v})) :
    (vertexDeletedPredicateDartEquiv v
      (vertexDeletedNode R v e)).1 =
        PermSkipFiber.skipAux
          (keep := fun d : OrientedEdge G => d.head ≠ v)
          R.node (vertexDeletedPredicateDartEquiv v e).1 := by
  apply Subtype.ext
  change
    (vertexDeletedDartEquiv v
      (vertexDeletedNode R v e)).1.1.1 =
      PermSkipFiber.skipAux R.node
        (vertexDeletedDartEquiv v e).1.1
  rw [vertexDeletedNode_conj]
  rfl

/-- For a graph node orbit, general predicate restriction skips exactly the
unique dart aimed at the deleted vertex. -/
theorem predicateSkipNode_eq_fiberSkip
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (x : {d : OrientedEdge G // d.tail ≠ v ∧ d.head ≠ v}) :
    (PermSkipPredicate.skip
      (keep := fun d : OrientedEdge G => d.tail ≠ v ∧ d.head ≠ v)
      R.node x).1 =
        PermSkipFiber.skipAux
          (keep := fun d : OrientedEdge G => d.head ≠ v)
          R.node x.1 := by
  by_cases hnextHead : (R.node x.1).head ≠ v
  · have hnext :
        (R.node x.1).tail ≠ v ∧ (R.node x.1).head ≠ v := by
      exact ⟨R.node_tail x.1 ▸ x.2.1, hnextHead⟩
    rw [PermSkipPredicate.skip_apply_of_next_mem R.node x hnext]
    simp [PermSkipFiber.skipAux, hnextHead]
  · have hnextNot :
        ¬ ((R.node x.1).tail ≠ v ∧ (R.node x.1).head ≠ v) := by
      exact fun h => hnextHead h.2
    have hsecondHead :
        (R.node (R.node x.1)).head ≠ v := by
      simpa [PermSkipFiber.skipAux, hnextHead] using
        (PermSkipFiber.skipAux_mem R.node OrientedEdge.tail R.node_tail
          (node_forbidden_unique v) x.2.2)
    have hsecond :
        (R.node (R.node x.1)).tail ≠ v ∧
          (R.node (R.node x.1)).head ≠ v := by
      exact
        ⟨(R.node_tail (R.node x.1)).trans (R.node_tail x.1) ▸ x.2.1,
          hsecondHead⟩
    have hskip :
        (PermSkipPredicate.skip
          (keep := fun d : OrientedEdge G =>
            d.tail ≠ v ∧ d.head ≠ v)
          R.node x).1 =
            ((R.node : OrientedEdge G → OrientedEdge G)^[1 + 1]) x.1 := by
      apply PermSkipPredicate.skip_eq_of_first (n := 1) R.node x
      · simpa [Function.iterate_succ_apply] using hsecond
      · intro m hm
        by_contra hmLt
        have hmZero : m = 0 := by omega
        subst m
        exact hnextNot (by simpa using hm)
    rw [hskip]
    simp [Function.iterate_succ_apply, PermSkipFiber.skipAux, hnextHead]

/-- The explicit graph vertex-deletion rotation is the Coq-style predicate
restriction of the original hypermap. -/
noncomputable def vertexDeletedRotationSystem_toPredicateRestrictionIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V) :
    Hypermap.Iso ((vertexDeletedRotationSystem R v).toHypermap)
      ((R.toHypermap).predicateRestriction
        (fun d : OrientedEdge G => d.tail ≠ v ∧ d.head ≠ v)) :=
  Hypermap.Iso.ofEdgeNode
    (vertexDeletedPredicateDartEquiv v)
    (by
      intro e
      apply Subtype.ext
      change
        (vertexDeletedPredicateDartEquiv v e.symm).1 =
          (PermSkipPredicate.skip
            (keep := fun d : OrientedEdge G =>
              d.tail ≠ v ∧ d.head ≠ v)
            (OrientedEdge.edgePerm G)
            (vertexDeletedPredicateDartEquiv v e)).1
      rw [PermSkipPredicate.skip_apply_of_next_mem]
      · exact congrArg Subtype.val
          (vertexDeletedPredicateDartEquiv_symm v e)
      · exact
          ⟨(vertexDeletedPredicateDartEquiv v e).2.2,
            (vertexDeletedPredicateDartEquiv v e).2.1⟩)
    (by
      intro e
      apply Subtype.ext
      calc
        (vertexDeletedPredicateDartEquiv v
            ((vertexDeletedRotationSystem R v).toHypermap.node e)).1 =
            PermSkipFiber.skipAux R.node
              (vertexDeletedPredicateDartEquiv v e).1 :=
          vertexDeletedNode_source R v e
        _ = (PermSkipPredicate.skip
              (keep := fun d : OrientedEdge G =>
                d.tail ≠ v ∧ d.head ≠ v)
              R.node (vertexDeletedPredicateDartEquiv v e)).1 :=
          (predicateSkipNode_eq_fiberSkip R v
            (vertexDeletedPredicateDartEquiv v e)).symm)

theorem vertexDeletedRotationSystem_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hR : (R.toHypermap).EulerPlanar) :
    ((vertexDeletedRotationSystem R v).toHypermap).EulerPlanar := by
  let keep : OrientedEdge G → Prop :=
    fun d => d.tail ≠ v ∧ d.head ≠ v
  have hrestricted :
      ((R.toHypermap).predicateRestriction keep).EulerPlanar :=
    Hypermap.predicateRestriction_eulerPlanar R.toHypermap keep hR
  let φ :
      Hypermap.Iso ((vertexDeletedRotationSystem R v).toHypermap)
        ((R.toHypermap).predicateRestriction keep) :=
    vertexDeletedRotationSystem_toPredicateRestrictionIso R v
  exact (φ.eulerPlanar_iff).mpr hrestricted

theorem vertexDeletedRotationSystem_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hR : (R.toHypermap).dual.EulerPlanar) :
    ((vertexDeletedRotationSystem R v).toHypermap).dual.EulerPlanar := by
  have hprimal : (R.toHypermap).EulerPlanar :=
    (R.toHypermap.dual_eulerPlanar_iff).mp hR
  have hdeleted :
      ((vertexDeletedRotationSystem R v).toHypermap).EulerPlanar :=
    vertexDeletedRotationSystem_eulerPlanar R v hprimal
  exact
    ((vertexDeletedRotationSystem R v).toHypermap.dual_eulerPlanar_iff).mpr
      hdeleted

end RotationSystemVertexDeletion

end FourColor

end Schematic.Math.GraphTheory
