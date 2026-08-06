import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.CyclicBoundary
import Schematic.Math.GraphTheory.Embedding.RotationSystem
import Schematic.Math.GraphTheory.PathsTrees
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace CyclicBoundary

/-!
### The canonical boundary cycle

The source definition of a rural society is not bare graph planarity: the
society boundary occurs on one selected face in its prescribed cyclic order.
For a boundary of length at least three, this is encoded combinatorially by
adjoining the corresponding abstract cycle and requiring that cycle to be
facial in an Euler-planar rotation system.  The definitions below are kept
here, next to `CyclicBoundary`, so the eventual rural certificate has one
canonical graph rather than an existentially chosen polygon.
-/

/-- The injective enumeration of a cyclic boundary by its list positions. -/
def embedding (Ω : CyclicBoundary V) : Fin Ω.length ↪ V where
  toFun i := Ω.vertices.get (Fin.cast (by simp [length]) i)
  inj' := by
    intro i j h
    apply Fin.cast_injective
    exact Ω.nodup.injective_get h

/-- Reindex the canonical boundary embedding along a supplied length
identity.  This form is convenient for the `n + 3` cycle API in mathlib. -/
def embeddingOfLength (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n) : Fin n ↪ V where
  toFun i := Ω.embedding (Fin.cast h.symm i)
  inj' := by
    intro i j hij
    have hc : Fin.cast h.symm i = Fin.cast h.symm j :=
      Ω.embedding.injective hij
    exact (Fin.cast_inj h.symm).mp hc

/-- The abstract cycle whose vertices are the boundary vertices in their
listed cyclic order. -/
def cycleGraphOfLength (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n) : SimpleGraph V :=
  (SimpleGraph.cycleGraph n).map (Ω.embeddingOfLength n h)

/-- The canonical boundary cycle graph, without choosing an `n + 3`
presentation of its length. -/
def cycleGraph (Ω : CyclicBoundary V) : SimpleGraph V :=
  (SimpleGraph.cycleGraph Ω.length).map Ω.embedding

/-- The canonical directed traversal of a boundary of length `n + 3`. -/
def cycleWalkOfLength (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    (Ω.cycleGraphOfLength (n + 3) h).Walk
      (Ω.embeddingOfLength (n + 3) h 0)
      (Ω.embeddingOfLength (n + 3) h 0) := by
  simpa [cycleGraphOfLength, SimpleGraph.Embedding.map_apply] using
    (SimpleGraph.cycleGraph.cycle n).map
      (SimpleGraph.Embedding.map (Ω.embeddingOfLength (n + 3) h)
        (SimpleGraph.cycleGraph (n + 3))).toHom

theorem cycleWalkOfLength_isCycle (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    (Ω.cycleWalkOfLength n h).IsCycle := by
  simpa [cycleWalkOfLength, cycleGraphOfLength,
    SimpleGraph.Embedding.map_apply] using
    SimpleGraph.Walk.IsCycle.map
      (SimpleGraph.Embedding.map (Ω.embeddingOfLength (n + 3) h)
        (SimpleGraph.cycleGraph (n + 3))).injective
      (SimpleGraph.cycleGraph.isCycle_cycle (n := n))

/-- Vertex formula for the canonical boundary traversal.  Mathlib's chosen
cycle starts at list position zero and then visits the remaining positions in
reverse order.  Keeping this formula explicit is what lets the GM IX disk
gluing proof identify the common facial segment with the cut path itself. -/
theorem cycleWalkOfLength_getVert
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) (i : Nat) (hi : i <= n + 3) :
    (Ω.cycleWalkOfLength n h).getVert i =
      Ω.embeddingOfLength (n + 3) h
        ⟨((n + 3) - i) % (n + 3), Nat.mod_lt _ (by omega)⟩ := by
  change
    ((SimpleGraph.cycleGraph.cycle n).map
      (SimpleGraph.Embedding.map
        (Ω.embeddingOfLength (n + 3) h)
        (SimpleGraph.cycleGraph (n + 3))).toHom).getVert i = _
  rw [SimpleGraph.Walk.getVert_map,
    SimpleGraph.cycleGraph.getVert_cycle hi]
  rfl

/-- Exact vertex order of the canonical boundary traversal.  The initial
vertex is repeated at the end, as usual for a closed walk. -/
theorem cycleWalkOfLength_support
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    (Ω.cycleWalkOfLength n h).support =
      Ω.vertices.head (by
        intro hnil
        have : Ω.length = 0 := by simp [CyclicBoundary.length, hnil]
        omega) :: Ω.vertices.reverse := by
  have hvertices : Ω.vertices.length = n + 3 := by
    simpa [CyclicBoundary.length] using h
  apply List.ext_getElem
  · change
      ((SimpleGraph.cycleGraph.cycle n).map
          (SimpleGraph.Embedding.map
            (Ω.embeddingOfLength (n + 3) h)
            (SimpleGraph.cycleGraph (n + 3))).toHom).support.length =
        (Ω.vertices.head _ :: Ω.vertices.reverse).length
    rw [SimpleGraph.Walk.length_support,
      SimpleGraph.Walk.length_map,
      SimpleGraph.cycleGraph.length_cycle]
    simp [hvertices]
  · intro i hiLeft hiRight
    have hcycleLength : (Ω.cycleWalkOfLength n h).length = n + 3 := by
      change
        ((SimpleGraph.cycleGraph.cycle n).map
          (SimpleGraph.Embedding.map
            (Ω.embeddingOfLength (n + 3) h)
            (SimpleGraph.cycleGraph (n + 3))).toHom).length = n + 3
      rw [SimpleGraph.Walk.length_map,
        SimpleGraph.cycleGraph.length_cycle]
    have hi : i <= n + 3 := by
      rw [SimpleGraph.Walk.length_support, hcycleLength] at hiLeft
      omega
    rw [← SimpleGraph.Walk.getVert_eq_support_getElem
      (Ω.cycleWalkOfLength n h) (by simpa [hcycleLength] using hi)]
    cases i with
    | zero =>
        rw [Ω.cycleWalkOfLength_getVert n h 0 (by omega)]
        simp only [List.getElem_cons_zero]
        rw [List.head_eq_getElem_zero]
        change Ω.vertices.get _ = Ω.vertices.get _
        congr 1
        apply Fin.ext
        simp
    | succ j =>
        rw [Ω.cycleWalkOfLength_getVert n h (j + 1) hi]
        simp only [List.getElem_cons_succ]
        change
          Ω.vertices.get _ =
            Ω.vertices.reverse.get ⟨j, by simpa using hiRight⟩
        have hj : j < n + 3 := by
          have hj' : j <= n + 2 := by
            simpa [hvertices] using hiRight
          omega
        have hrevBound : Ω.vertices.length - 1 - j < Ω.vertices.length := by
          rw [hvertices]
          omega
        rw [List.get_reverse' Ω.vertices ⟨j, by simpa using hiRight⟩
          hrevBound]
        change Ω.vertices.get _ = Ω.vertices.get _
        congr 1
        apply Fin.ext
        simp only [Fin.val_cast]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

/-- Every listed boundary vertex occurs on the canonical boundary walk.

This is deliberately stated for the walk, rather than only for the support
of the boundary graph: face splitting needs an actual forward cycle dart at
each selected cut endpoint. -/
theorem mem_cycleWalkOfLength_support
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) {v : V}
    (hv : v ∈ Ω.vertexSet) :
    v ∈ (Ω.cycleWalkOfLength n h).support := by
  classical
  change v ∈ Ω.vertices at hv
  rcases List.mem_iff_get.mp hv with ⟨i, hi⟩
  let iΩ : Fin Ω.length :=
    Fin.cast (by simp [CyclicBoundary.length]) i
  let j : Fin (n + 3) := Fin.cast h iΩ
  have hjSource : j ∈ (SimpleGraph.cycleGraph.cycle n).support := by
    by_cases hjZero : j = 0
    · simp [hjZero]
    · have hjPos : 0 < j.val := by
        exact Nat.pos_of_ne_zero (fun hjVal => hjZero (Fin.ext hjVal))
      let m : Nat := n + 3 - j.val
      have hm : m <= n + 3 := Nat.sub_le _ _
      have hmGet :
          (SimpleGraph.cycleGraph.cycle n).getVert m = j := by
        rw [SimpleGraph.cycleGraph.getVert_cycle hm]
        apply Fin.ext
        change (n + 3 - (n + 3 - j.val)) % (n + 3) = j.val
        have hsub : n + 3 - (n + 3 - j.val) = j.val := by omega
        rw [hsub, Nat.mod_eq_of_lt j.isLt]
      have hmLength :
          m <= (SimpleGraph.cycleGraph.cycle n).length := by
        simpa using hm
      exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
        ⟨m, hmGet, hmLength⟩
  change v ∈
    ((SimpleGraph.cycleGraph.cycle n).map
      (SimpleGraph.Embedding.map
        (Ω.embeddingOfLength (n + 3) h)
        (SimpleGraph.cycleGraph (n + 3))).toHom).support
  rw [SimpleGraph.Walk.support_map]
  refine List.mem_map.mpr ⟨j, hjSource, ?_⟩
  change Ω.vertices.get _ = v
  rw [← hi]
  congr 1

/-- The canonical boundary polygon has maximum degree two, including at
ambient vertices outside the boundary embedding. -/
theorem cycleGraphOfLength_degree_le_two
    [Fintype V] [DecidableEq V]
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    letI : DecidableRel (Ω.cycleGraphOfLength (n + 3) h).Adj :=
      Classical.decRel _
    forall v : V, (Ω.cycleGraphOfLength (n + 3) h).degree v <= 2 := by
  classical
  intro v
  let f : Fin (n + 3) ↪ V := Ω.embeddingOfLength (n + 3) h
  by_cases hv : v ∈ Set.range f
  · rcases hv with ⟨i, rfl⟩
    have hneighbor :
        (Ω.cycleGraphOfLength (n + 3) h).neighborSet (f i) =
          f '' (SimpleGraph.cycleGraph (n + 3)).neighborSet i := by
      simp [CyclicBoundary.cycleGraphOfLength, f]
    have hncard :
        ((Ω.cycleGraphOfLength (n + 3) h).neighborSet (f i)).ncard =
          ((SimpleGraph.cycleGraph (n + 3)).neighborSet i).ncard := by
      rw [hneighbor, Set.ncard_image_of_injective _ f.injective]
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      Set.fintypeCard_eq_ncard, hncard,
      ← Set.fintypeCard_eq_ncard,
      SimpleGraph.card_neighborSet_eq_degree,
      SimpleGraph.cycleGraph_degree_three_le]
  · have hneighbor :
        (Ω.cycleGraphOfLength (n + 3) h).neighborSet v = ∅ := by
      ext w
      constructor
      · intro hvw
        have hvRange : v ∈ Set.range f := by
          rcases
              (SimpleGraph.map_adj f (SimpleGraph.cycleGraph (n + 3)) v w).mp
                (by
                  simpa [CyclicBoundary.cycleGraphOfLength, f] using hvw) with
            ⟨i, _j, _hij, hi, _hj⟩
          exact ⟨i, hi⟩
        exact False.elim (hv hvRange)
      · simp
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      Set.fintypeCard_eq_ncard, hneighbor]
    simp

/-- The canonical boundary traversal spans the entire canonical boundary
polygon.  This is the graph identity used by facial-path gluing: selecting a
segment of the marked face selects the corresponding polygon edges, not only
an abstract walk with the same vertices. -/
theorem cycleWalkOfLength_toSubgraph_spanningCoe
    [Fintype V] [DecidableEq V]
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    (Ω.cycleWalkOfLength n h).toSubgraph.spanningCoe =
      Ω.cycleGraphOfLength (n + 3) h := by
  classical
  let C := Ω.cycleGraphOfLength (n + 3) h
  let c : C.Walk _ _ := Ω.cycleWalkOfLength n h
  letI : DecidableRel C.Adj := Classical.decRel _
  have hc : c.IsCycle := Ω.cycleWalkOfLength_isCycle n h
  have hdegree : forall v : V, C.degree v <= 2 := by
    simpa [C] using Ω.cycleGraphOfLength_degree_le_two n h
  have hcycles : C.IsCycles := by
    intro v hv
    have hvSupport : v ∈ C.support := by
      rcases hv with ⟨w, hvw⟩
      exact hvw.left_mem_support
    have hvRange : v ∈ Set.range (Ω.embeddingOfLength (n + 3) h) := by
      have hvImage :
          v ∈ (Ω.embeddingOfLength (n + 3) h) ''
            (SimpleGraph.cycleGraph (n + 3)).support := by
        simpa only [C, CyclicBoundary.cycleGraphOfLength,
          SimpleGraph.support_map] using hvSupport
      rcases hvImage with ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    rcases hvRange with ⟨i, rfl⟩
    have hvBoundary :
        Ω.embeddingOfLength (n + 3) h i ∈ Ω.vertexSet := by
      change Ω.vertices.get _ ∈ Ω.vertices
      exact List.get_mem _ _
    have hvWalk :
        Ω.embeddingOfLength (n + 3) h i ∈ c.support := by
      simpa [c] using Ω.mem_cycleWalkOfLength_support n h hvBoundary
    have htwo :
        (c.toSubgraph.neighborSet
          (Ω.embeddingOfLength (n + 3) h i)).ncard = 2 :=
      hc.ncard_neighborSet_toSubgraph_eq_two hvWalk
    have hsubset :
        c.toSubgraph.neighborSet (Ω.embeddingOfLength (n + 3) h i) ⊆
          C.neighborSet (Ω.embeddingOfLength (n + 3) h i) :=
      c.toSubgraph.neighborSet_subset _
    have hle :
        2 <= (C.neighborSet
          (Ω.embeddingOfLength (n + 3) h i)).ncard := by
      rw [← htwo]
      exact Set.ncard_le_ncard hsubset (Set.toFinite _)
    have hupper :
        (C.neighborSet
          (Ω.embeddingOfLength (n + 3) h i)).ncard <= 2 := by
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
      exact hdegree _
    omega
  apply le_antisymm
  · exact c.toSubgraph.spanningCoe_le
  · intro v w hvw
    have hvSupport : v ∈ C.support := hvw.left_mem_support
    have hvRange : v ∈ Set.range (Ω.embeddingOfLength (n + 3) h) := by
      have hvImage :
          v ∈ (Ω.embeddingOfLength (n + 3) h) ''
            (SimpleGraph.cycleGraph (n + 3)).support := by
        simpa only [C, CyclicBoundary.cycleGraphOfLength,
          SimpleGraph.support_map] using hvSupport
      rcases hvImage with ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    rcases hvRange with ⟨i, rfl⟩
    have hvBoundary :
        Ω.embeddingOfLength (n + 3) h i ∈ Ω.vertexSet := by
      change Ω.vertices.get _ ∈ Ω.vertices
      exact List.get_mem _ _
    have hvWalk :
        Ω.embeddingOfLength (n + 3) h i ∈ c.support := by
      simpa [c] using Ω.mem_cycleWalkOfLength_support n h hvBoundary
    rw [SimpleGraph.Subgraph.spanningCoe_adj]
    exact (hc.adj_toSubgraph_iff_of_isCycles hcycles
      (c.mem_verts_toSubgraph.mpr hvWalk) w).mpr hvw

theorem cycleGraphOfLength_support_eq_vertexSet
    [Fintype V] [DecidableEq V]
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    (Ω.cycleGraphOfLength (n + 3) h).support = Ω.vertexSet := by
  ext v
  constructor
  · intro hv
    rcases (SimpleGraph.mem_support
      (Ω.cycleGraphOfLength (n + 3) h)).mp hv with ⟨w, hvw⟩
    have hvw' :
        (Ω.cycleWalkOfLength n h).toSubgraph.spanningCoe.Adj v w := by
      rw [Ω.cycleWalkOfLength_toSubgraph_spanningCoe n h]
      exact hvw
    have hedge : s(v, w) ∈ (Ω.cycleWalkOfLength n h).edges :=
      (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).mp hvw'
    have hvWalk : v ∈ (Ω.cycleWalkOfLength n h).support :=
      (Ω.cycleWalkOfLength n h).fst_mem_support_of_mem_edges hedge
    rw [Ω.cycleWalkOfLength_support n h] at hvWalk
    rcases List.mem_cons.mp hvWalk with hhead | hreverse
    · subst v
      have hnonempty : Ω.vertices ≠ [] := by
        intro hnil
        have : Ω.length = 0 := by
          simp [CyclicBoundary.length, hnil]
        omega
      simp [CyclicBoundary.vertexSet, List.head_mem hnonempty]
    · simpa [CyclicBoundary.vertexSet] using
        (List.mem_reverse.mp hreverse)
  · intro hv
    exact SimpleGraph.mem_support_of_mem_walk_support
      (Ω.cycleWalkOfLength n h)
      (Ω.cycleWalkOfLength_isCycle n h).not_nil
      (Ω.mem_cycleWalkOfLength_support n h hv)

/-- The non-isolated support of the canonical boundary polygon is connected.
Ambient vertices outside the boundary embedding are isolated and disappear
after restriction to support. -/
theorem cycleGraphOfLength_support_preconnected
    [Fintype V] [DecidableEq V]
    (Ω : CyclicBoundary V) (n : Nat)
    (h : Ω.length = n + 3) :
    ((Ω.cycleGraphOfLength (n + 3) h).induce
      (Ω.cycleGraphOfLength (n + 3) h).support).Preconnected := by
  intro x y
  let f : Fin (n + 3) ↪ V := Ω.embeddingOfLength (n + 3) h
  have hxRange : (x : V) ∈ Set.range f := by
    have hxImage :
        (x : V) ∈ f '' (SimpleGraph.cycleGraph (n + 3)).support := by
      simpa only [CyclicBoundary.cycleGraphOfLength,
        SimpleGraph.support_map] using x.property
    rcases hxImage with ⟨i, _hi, hix⟩
    exact ⟨i, hix⟩
  have hyRange : (y : V) ∈ Set.range f := by
    have hyImage :
        (y : V) ∈ f '' (SimpleGraph.cycleGraph (n + 3)).support := by
      simpa only [CyclicBoundary.cycleGraphOfLength,
        SimpleGraph.support_map] using y.property
    rcases hyImage with ⟨j, _hj, hjy⟩
    exact ⟨j, hjy⟩
  rcases hxRange with ⟨i, hi⟩
  rcases hyRange with ⟨j, hj⟩
  have hreach :
      (Ω.cycleGraphOfLength (n + 3) h).Reachable (f i) (f j) := by
    simpa [CyclicBoundary.cycleGraphOfLength, f,
      SimpleGraph.Embedding.map_apply] using
      SimpleGraph.Reachable.map
        (SimpleGraph.Embedding.map f
          (SimpleGraph.cycleGraph (n + 3))).toHom
        (SimpleGraph.cycleGraph_preconnected i j)
  apply FourColor.RotationSystem.reachable_induce_support_of_reachable
  simpa [hi, hj] using hreach

/-- Transport a finite degree bound across graph equality without identifying
the computational `DecidableRel` instances used to form the two degree
values.  Passing through `Set.ncard` makes the invariant mathematical rather
than dependent on those decision procedures. -/
theorem degree_le_two_of_graph_eq
    {V : Type u} [Fintype V]
    {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G = H)
    (hdegree : forall v : V, H.degree v <= 2) :
    forall v : V, G.degree v <= 2 := by
  intro v
  have hd := hdegree v
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard] at hd
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard]
  subst H
  exact hd

end CyclicBoundary

end Schematic.Math.GraphTheory
