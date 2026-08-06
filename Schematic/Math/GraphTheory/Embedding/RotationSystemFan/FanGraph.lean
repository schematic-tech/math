import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.EdgeInsertion

/-! The graph obtained by adjoining a vertex with a prescribed fan. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- Add one new vertex adjacent exactly to the old vertices in `A`. -/
def addNodeGraph
    {V : Type u} (G : SimpleGraph V) (A : Set V) :
    SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some a, some b => G.Adj a b
    | none, some b => b ∈ A
    | some a, none => a ∈ A
    | none, none => False
  symm := by
    intro x y h
    cases x <;> cases y
    · exact h
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    constructor
    intro x h
    cases x <;> simp at h

@[simp]
theorem addNodeGraph_some_some
    {V : Type u} (G : SimpleGraph V) (A : Set V) (x y : V) :
    (addNodeGraph G A).Adj (some x) (some y) ↔ G.Adj x y :=
  Iff.rfl

@[simp]
theorem addNodeGraph_none_some
    {V : Type u} (G : SimpleGraph V) (A : Set V) (x : V) :
    (addNodeGraph G A).Adj none (some x) ↔ x ∈ A :=
  Iff.rfl

@[simp]
theorem addNodeGraph_some_none
    {V : Type u} (G : SimpleGraph V) (A : Set V) (x : V) :
    (addNodeGraph G A).Adj (some x) none ↔ x ∈ A :=
  Iff.rfl

/-- The canonical inclusion of the old graph into a graph with one new
vertex.  Keeping this map named avoids repeatedly rebuilding the same graph
homomorphism in the face-splitting and disk-gluing arguments. -/
def addNodeGraphSomeHom
    {V : Type u} (G : SimpleGraph V) (A : Set V) :
    G →g addNodeGraph G A where
  toFun := some
  map_rel' := by
    intro x y hxy
    simpa using hxy

@[simp]
theorem addNodeGraph_some_mem_support
    {V : Type u} {G : SimpleGraph V} {A : Set V} {x : V} :
    some x ∈ (addNodeGraph G A).support ↔ x ∈ G.support ∨ x ∈ A := by
  constructor
  · intro hx
    rcases (SimpleGraph.mem_support (addNodeGraph G A)).mp hx with ⟨z, hxz⟩
    cases z with
    | none => exact Or.inr (by simpa [addNodeGraph] using hxz)
    | some y =>
        exact Or.inl
          ((by simpa [addNodeGraph] using hxz : G.Adj x y).left_mem_support)
  · rintro (hx | hx)
    · rcases (SimpleGraph.mem_support G).mp hx with ⟨y, hxy⟩
      exact (by
        apply (SimpleGraph.mem_support (addNodeGraph G A)).mpr
        exact ⟨some y, by simpa [addNodeGraph] using hxy⟩)
    · exact (by
        apply (SimpleGraph.mem_support (addNodeGraph G A)).mpr
        exact ⟨none, by simpa [addNodeGraph] using hx⟩)

@[simp]
theorem addNodeGraph_none_mem_support
    {V : Type u} {G : SimpleGraph V} {A : Set V} :
    none ∈ (addNodeGraph G A).support ↔ A.Nonempty := by
  constructor
  · intro hnone
    rcases (SimpleGraph.mem_support (addNodeGraph G A)).mp hnone with
      ⟨z, hz⟩
    cases z with
    | none => exact False.elim ((addNodeGraph G A).loopless.irrefl none hz)
    | some x => exact ⟨x, by simpa [addNodeGraph] using hz⟩
  · rintro ⟨x, hx⟩
    apply (SimpleGraph.mem_support (addNodeGraph G A)).mpr
    exact ⟨some x, by simpa [addNodeGraph] using hx⟩

/-- Adding one vertex adjacent to two supported vertices preserves
preconnectedness of the graph induced on its support. -/
theorem addNodeGraph_pair_support_preconnected
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (hG : (G.induce G.support).Preconnected)
    (hs : s ∈ G.support) (ht : t ∈ G.support) :
    let H := addNodeGraph G (insert t ({s} : Set V))
    (H.induce H.support).Preconnected := by
  let H := addNodeGraph G (insert t ({s} : Set V))
  have htoStart : forall z : H.support,
      H.Reachable (z : Option V) (some s) := by
    intro z
    cases hz : (z : Option V) with
    | none =>
        exact (by
          have hadj : H.Adj none (some s) := by
            simp [H, addNodeGraph]
          exact hadj.reachable)
    | some x =>
        have hx : x ∈ G.support := by
          rcases (SimpleGraph.mem_support H).mp z.property with ⟨w, hxw⟩
          cases w with
          | none =>
              have hxt : x = t ∨ x = s := by
                simpa [hz, H, addNodeGraph] using hxw
              rcases hxt with rfl | rfl
              · exact ht
              · exact hs
          | some y =>
              have hxy : G.Adj x y := by
                simpa [hz, H, addNodeGraph] using hxw
              exact hxy.left_mem_support
        have hreachInduced :
            (G.induce G.support).Reachable ⟨x, hx⟩ ⟨s, hs⟩ :=
          hG _ _
        have hreach : G.Reachable x s :=
          RotationSystem.reachable_of_reachable_induce_support hreachInduced
        have hmapped := hreach.map
          (addNodeGraphSomeHom G (insert t ({s} : Set V)))
        simpa [hz, H, addNodeGraphSomeHom] using hmapped
  change (H.induce H.support).Preconnected
  intro x y
  apply RotationSystem.reachable_induce_support_of_reachable
  exact (htoStart x).trans (htoStart y).symm

/-- The induced inclusion on oriented edges for `addNodeGraphSomeHom`. -/
noncomputable def addNodeGraphSomeOrientedEdge
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    (d : OrientedEdge G) : OrientedEdge (addNodeGraph G A) :=
  (orientedEdgeDartEquiv (G := addNodeGraph G A)).symm
    ((addNodeGraphSomeHom G A).mapDart
      (orientedEdgeDartEquiv (G := G) d))

@[simp]
theorem addNodeGraphSomeOrientedEdge_tail
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    (d : OrientedEdge G) :
    (addNodeGraphSomeOrientedEdge G A d).tail = some d.tail := by
  rfl

@[simp]
theorem addNodeGraphSomeOrientedEdge_head
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    (d : OrientedEdge G) :
    (addNodeGraphSomeOrientedEdge G A d).head = some d.head := by
  rfl

theorem addNodeGraphSomeOrientedEdge_injective
    {V : Type u} (G : SimpleGraph V) (A : Set V) :
    Function.Injective (addNodeGraphSomeOrientedEdge G A) := by
  intro d e hde
  apply Subtype.ext
  exact Prod.ext
    (Option.some.inj (congrArg OrientedEdge.tail hde))
    (Option.some.inj (congrArg OrientedEdge.head hde))

/-- Close an old `s`-to-`t` path through the fresh vertex adjacent to `s`
and `t`.  The orientation is `some t -> none -> some s`, followed by the old
path from `s` to `t`; this is the common cycle used when two disk drawings
are glued along that path. -/
def addNodeGraphPathCycle
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) :
    let H := addNodeGraph G (insert t ({s} : Set V))
    H.Walk (some t) (some t) := by
  let H := addNodeGraph G (insert t ({s} : Set V))
  have hts : H.Adj (some t) none := by
    simp [H]
  have hss : H.Adj none (some s) := by
    simp [H]
  exact SimpleGraph.Walk.cons hts
    (SimpleGraph.Walk.cons hss
      (p.map (addNodeGraphSomeHom G (insert t ({s} : Set V)))))

/-- The same fresh-node closure based at the fresh vertex itself.  Its
orientation is `none -> some s`, then the old path, then `some t -> none`.
Using this basepoint makes the two cut-side cycles literally opposite. -/
def addNodeGraphPathCycleAtNew
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) :
    let H := addNodeGraph G (insert t ({s} : Set V))
    H.Walk none none := by
  let H := addNodeGraph G (insert t ({s} : Set V))
  have hss : H.Adj none (some s) := by
    simp [H]
  have htt : H.Adj (some t) none := by
    simp [H]
  exact SimpleGraph.Walk.cons hss
    ((p.map (addNodeGraphSomeHom G (insert t ({s} : Set V)))).concat htt)

/-- Fresh-node closure of a path in an arbitrary fan graph whose selected
neighbor set contains both path ends.  This order-independent form is used for
the complementary path of a facial split. -/
def addNodeGraphPathCycleAtNewIn
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    {s t : V} (hs : s ∈ A) (ht : t ∈ A)
    (p : G.Walk s t) :
    (addNodeGraph G A).Walk none none := by
  have hss : (addNodeGraph G A).Adj none (some s) := by
    simp [addNodeGraph, hs]
  have htt : (addNodeGraph G A).Adj (some t) none := by
    simp [addNodeGraph, ht]
  exact SimpleGraph.Walk.cons hss
    ((p.map (addNodeGraphSomeHom G A)).concat htt)

@[simp]
theorem addNodeGraphPathCycleAtNewIn_darts
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    {s t : V} (hs : s ∈ A) (ht : t ∈ A)
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNewIn G A hs ht p).darts =
      ⟨(none, some s), by simp [addNodeGraph, hs]⟩ ::
        (p.map (addNodeGraphSomeHom G A)).darts ++
          [⟨(some t, none), by simp [addNodeGraph, ht]⟩] := by
  let f := addNodeGraphSomeHom G A
  have htt : (addNodeGraph G A).Adj (some t) none := by
    simp [addNodeGraph, ht]
  change
    ⟨(none, some s), _⟩ ::
        ((p.map f).concat htt).darts = _
  congr 1
  simp [f, addNodeGraphSomeHom, List.concat_eq_append,
    _root_.SimpleGraph.Walk.darts_concat]

/-- Oriented-edge list of the order-independent fresh-node path closure. -/
theorem addNodeGraphPathCycleAtNewIn_orientedDarts
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    {s t : V} (hs : s ∈ A) (ht : t ∈ A)
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNewIn G A hs ht p).darts.map
        (orientedEdgeDartEquiv (G := addNodeGraph G A)).symm =
      ⟨(none, some s), by simp [addNodeGraph, hs]⟩ ::
        (p.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
          (addNodeGraphSomeOrientedEdge G A) ++
            [⟨(some t, none), by simp [addNodeGraph, ht]⟩] := by
  let f := addNodeGraphSomeHom G A
  let E₀ := orientedEdgeDartEquiv (G := G)
  let E₁ := orientedEdgeDartEquiv (G := addNodeGraph G A)
  rw [addNodeGraphPathCycleAtNewIn_darts]
  simp only [List.map_cons, List.map_append]
  have hfirst :
      E₁.symm ⟨(none, some s), by simp [addNodeGraph, hs]⟩ =
        ⟨(none, some s), by simp [addNodeGraph, hs]⟩ := by
    apply Subtype.ext
    rfl
  have hlast :
      E₁.symm ⟨(some t, none), by simp [addNodeGraph, ht]⟩ =
        ⟨(some t, none), by simp [addNodeGraph, ht]⟩ := by
    apply Subtype.ext
    rfl
  have hmiddle :
      List.map E₁.symm (p.map f).darts =
        List.map (addNodeGraphSomeOrientedEdge G A)
          (List.map E₀.symm p.darts) := by
    calc
      List.map E₁.symm (p.map f).darts =
          List.map E₁.symm (List.map f.mapDart p.darts) := by
            exact congrArg (List.map E₁.symm)
              (SimpleGraph.Walk.darts_map f p)
      _ = List.map (addNodeGraphSomeOrientedEdge G A)
            (List.map E₀.symm p.darts) := by
          simp [addNodeGraphSomeOrientedEdge, f, E₀, E₁, List.map_map]
  rw [hfirst, hlast, hmiddle]
  simp [E₀]

/-- The order-independent fresh-node closure of a nontrivial simple path is a
simple cycle. -/
theorem addNodeGraphPathCycleAtNewIn_isCycle
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} (A : Set V)
    {s t : V} (hs : s ∈ A) (ht : t ∈ A)
    (hst : s ≠ t) (p : G.Walk s t) (hp : p.IsPath) :
    letI : DecidableRel (addNodeGraph G A).Adj := Classical.decRel _
    (addNodeGraphPathCycleAtNewIn G A hs ht p).IsCycle := by
  classical
  let f := addNodeGraphSomeHom G A
  let q : (addNodeGraph G A).Walk (some s) (some t) := p.map f
  have hf : Function.Injective f := by
    intro x y hxy
    exact Option.some.inj (by simpa [f, addNodeGraphSomeHom] using hxy)
  have hq : q.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective hf hp
  have hnone : none ∉ q.support := by
    rw [show q.support = p.support.map f by
      exact _root_.SimpleGraph.Walk.support_map f p]
    simp only [List.mem_map]
    rintro ⟨x, _hx, hbad⟩
    cases hbad
  have htt : (addNodeGraph G A).Adj (some t) none := by
    simp [addNodeGraph, ht]
  have hrest : (q.concat htt).IsPath := hq.concat hnone htt
  have hss : (addNodeGraph G A).Adj none (some s) := by
    simp [addNodeGraph, hs]
  rw [show addNodeGraphPathCycleAtNewIn G A hs ht p =
      SimpleGraph.Walk.cons hss (q.concat htt) by rfl]
  rw [_root_.SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hrest, ?_⟩
  rw [_root_.SimpleGraph.Walk.edges_concat]
  simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
  rintro (he | he)
  · exact hnone (q.fst_mem_support_of_mem_edges he)
  · have : s = t := by simpa [Sym2.eq_iff] using he
    exact hst this

@[simp]
theorem addNodeGraphPathCycleAtNew_support
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).support =
      none :: p.support.map some ++ [none] := by
  simp [addNodeGraphPathCycleAtNew, SimpleGraph.Walk.support_map,
    addNodeGraphSomeHom]

/-- Oppositely oriented old paths give oppositely oriented fresh-node
closures, even when the paths live in different ambient graphs. -/
theorem addNodeGraphPathCycleAtNew_support_eq_reverse
    {V : Type u} {G K : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (q : K.Walk t s)
    (hsupport : q.support = p.reverse.support) :
    (addNodeGraphPathCycleAtNew q).support =
      (addNodeGraphPathCycleAtNew p).reverse.support := by
  rw [_root_.SimpleGraph.Walk.support_reverse,
    addNodeGraphPathCycleAtNew_support,
    addNodeGraphPathCycleAtNew_support]
  rw [hsupport, _root_.SimpleGraph.Walk.support_reverse]
  simp [List.map_reverse]

/-- The two opposite fresh-node closures span one common simple graph. -/
theorem addNodeGraphPathCycleAtNew_spanningCoe_eq_of_reverse_support
    {V : Type u} {G K : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (q : K.Walk t s)
    (hsupport : q.support = p.reverse.support) :
    (addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe =
      (addNodeGraphPathCycleAtNew q).toSubgraph.spanningCoe := by
  calc
    (addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe =
        (addNodeGraphPathCycleAtNew p).reverse.toSubgraph.spanningCoe := by
      rw [_root_.SimpleGraph.Walk.toSubgraph_reverse]
    _ = (addNodeGraphPathCycleAtNew q).toSubgraph.spanningCoe :=
      SimpleGraph.Walk.toSubgraph_spanningCoe_eq_of_support_eq
        (addNodeGraphPathCycleAtNew p).reverse
        (addNodeGraphPathCycleAtNew q)
        (addNodeGraphPathCycleAtNew_support_eq_reverse p q hsupport).symm

@[simp]
theorem addNodeGraphPathCycleAtNew_some_some_adj
    {V : Type u} {G : SimpleGraph V} {s t x y : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe.Adj
        (some x) (some y) ↔
      p.toSubgraph.spanningCoe.Adj x y := by
  rw [SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges,
    SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  simp [addNodeGraphPathCycleAtNew, addNodeGraphSomeHom]
  constructor
  · rintro ⟨a, ha, hmap⟩
    have hmap' : Sym2.map some a = Sym2.map some s(x, y) := by
      simpa using hmap
    have haEq : a = s(x, y) :=
      Sym2.map.injective (Option.some_injective _) hmap'
    simpa [haEq] using ha
  · intro hxy
    exact ⟨s(x, y), hxy, by simp⟩

@[simp]
theorem addNodeGraphPathCycleAtNew_none_some_adj
    {V : Type u} {G : SimpleGraph V} {s t y : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe.Adj none (some y) ↔
      y = s ∨ y = t := by
  rw [SimpleGraph.Subgraph.spanningCoe_adj,
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  simp [addNodeGraphPathCycleAtNew, addNodeGraphSomeHom]
  constructor
  · rintro (hys | hmiddle | hyt)
    · exact Or.inl hys
    · rcases hmiddle with ⟨a, _ha, hmap⟩
      induction a using Sym2.ind with
      | h a b => simp at hmap
    · exact Or.inr hyt
  · rintro (hys | hyt)
    · exact Or.inl hys
    · exact Or.inr (Or.inr hyt)

@[simp]
theorem addNodeGraphPathCycleAtNew_some_none_adj
    {V : Type u} {G : SimpleGraph V} {s t x : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).toSubgraph.spanningCoe.Adj (some x) none ↔
      x = s ∨ x = t := by
  constructor
  · intro h
    exact (addNodeGraphPathCycleAtNew_none_some_adj p).mp h.symm
  · intro h
    exact ((addNodeGraphPathCycleAtNew_none_some_adj p).mpr h).symm

@[simp]
theorem addNodeGraphPathCycleAtNew_darts
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).darts =
      ⟨(none, some s), by simp [addNodeGraph]⟩ ::
        (p.map (addNodeGraphSomeHom G
          (insert t ({s} : Set V)))).darts ++
          [⟨(some t, none), by simp [addNodeGraph]⟩] := by
  let f := addNodeGraphSomeHom G (insert t ({s} : Set V))
  have htt : (addNodeGraph G (insert t ({s} : Set V))).Adj
      (some t) none := by simp [addNodeGraph]
  change
    ⟨(none, some s), _⟩ :: ((p.map f).concat htt).darts =
      ⟨(none, some s), _⟩ :: (p.map f).darts ++ [⟨(some t, none), _⟩]
  congr 1
  simp [f, addNodeGraphSomeHom, List.concat_eq_append,
    _root_.SimpleGraph.Walk.darts_concat]

/-- Oriented-edge list of the canonical two-neighbor fresh-node closure. -/
theorem addNodeGraphPathCycleAtNew_orientedDarts
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).darts.map
        (orientedEdgeDartEquiv
          (G := addNodeGraph G (insert t ({s} : Set V)))).symm =
      ⟨(none, some s), by simp [addNodeGraph]⟩ ::
        (p.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
          (addNodeGraphSomeOrientedEdge G (insert t ({s} : Set V))) ++
            [⟨(some t, none), by simp [addNodeGraph]⟩] := by
  exact addNodeGraphPathCycleAtNewIn_orientedDarts G
    (insert t ({s} : Set V)) (by simp) (by simp) p

theorem addNodeGraphPathCycleAtNew_isCycle
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {s t : V}
    (hst : s ≠ t) (p : G.Walk s t) (hp : p.IsPath) :
    let H := addNodeGraph G (insert t ({s} : Set V))
    letI : DecidableRel H.Adj := Classical.decRel _
    (addNodeGraphPathCycleAtNew p).IsCycle := by
  classical
  let H := addNodeGraph G (insert t ({s} : Set V))
  let f := addNodeGraphSomeHom G (insert t ({s} : Set V))
  let q : H.Walk (some s) (some t) := p.map f
  have hf : Function.Injective f := by
    intro x y hxy
    exact Option.some.inj (by simpa [f, addNodeGraphSomeHom] using hxy)
  have hq : q.IsPath :=
    SimpleGraph.Walk.map_isPath_of_injective hf hp
  have hnone : none ∉ q.support := by
    have hsupport : q.support = p.support.map f :=
      _root_.SimpleGraph.Walk.support_map f p
    rw [hsupport]
    simp [f, addNodeGraphSomeHom]
  have hss : H.Adj none (some s) := by simp [H, addNodeGraph]
  have htt : H.Adj (some t) none := by simp [H, addNodeGraph]
  have hrest : (q.concat htt).IsPath := hq.concat hnone htt
  rw [show addNodeGraphPathCycleAtNew p =
      SimpleGraph.Walk.cons hss (q.concat htt) by rfl]
  rw [_root_.SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hrest, ?_⟩
  rw [_root_.SimpleGraph.Walk.edges_concat]
  simp only [List.concat_eq_append, List.mem_append, List.mem_singleton]
  rintro (he | he)
  · exact hnone (q.fst_mem_support_of_mem_edges he)
  · have : s = t := by
      simpa [Sym2.eq_iff] using he
    exact hst this

/-- The fresh-vertex-based cycle is a cyclic rotation of the cycle returned
by the face-splitting construction. -/
theorem addNodeGraphPathCycleAtNew_darts_isRotated
    {V : Type u} {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) :
    (addNodeGraphPathCycleAtNew p).darts.IsRotated
      (addNodeGraphPathCycle p).darts := by
  let f := addNodeGraphSomeHom G (insert t ({s} : Set V))
  let first : (addNodeGraph G (insert t ({s} : Set V))).Dart :=
    ⟨(none, some s), by simp [addNodeGraph]⟩
  let closing : (addNodeGraph G (insert t ({s} : Set V))).Dart :=
    ⟨(some t, none), by simp [addNodeGraph]⟩
  have hnew :
      (addNodeGraphPathCycleAtNew p).darts =
        first :: (p.map f).darts ++ [closing] := by
    simpa only [first, closing, f] using
      addNodeGraphPathCycleAtNew_darts p
  have hold :
      (addNodeGraphPathCycle p).darts =
        closing :: first :: (p.map f).darts := by
    simp only [addNodeGraphPathCycle,
      _root_.SimpleGraph.Walk.darts_cons]
    rfl
  rw [hnew, hold]
  simpa only [List.singleton_append, List.cons_append] using
    (List.isRotated_append
      (l := [closing])
      (l' := first :: (p.map f).darts)).symm

theorem addNodeGraphPathCycle_isCycle
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {s t : V}
    (hst : s ≠ t) (p : G.Walk s t) (hp : p.IsPath) :
    let H := addNodeGraph G (insert t ({s} : Set V))
    letI : DecidableRel H.Adj := Classical.decRel _
    (addNodeGraphPathCycle p).IsCycle := by
  classical
  let H := addNodeGraph G (insert t ({s} : Set V))
  let f := addNodeGraphSomeHom G (insert t ({s} : Set V))
  have hts : H.Adj (some t) none := by
    simp [H]
  have hss : H.Adj none (some s) := by
    simp [H]
  let q : H.Walk (some s) (some t) := p.map f
  have hf : Function.Injective f := by
    intro x y hxy
    exact Option.some.inj (by simpa [f, addNodeGraphSomeHom] using hxy)
  have hq : q.IsPath := by
    exact SimpleGraph.Walk.map_isPath_of_injective hf hp
  have hnone : none ∉ q.support := by
    have hsupport : q.support = p.support.map f :=
      SimpleGraph.Walk.support_map f p
    rw [hsupport]
    simp only [List.mem_map]
    rintro ⟨x, _hx, hbad⟩
    change some x = none at hbad
    cases hbad
  have hinner : (SimpleGraph.Walk.cons hss q).IsPath := hq.cons hnone
  rw [show addNodeGraphPathCycle p =
      SimpleGraph.Walk.cons hts (SimpleGraph.Walk.cons hss q) by rfl]
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨hinner, ?_⟩
  simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
  rintro (heq | he)
  ·
    have : t = s := by
      simpa [Sym2.eq_iff] using heq
    exact hst this.symm
  ·
    exact hnone (q.snd_mem_support_of_mem_edges he)

/-- Rebase the selected split face at the fresh vertex. -/
theorem isFacialCycle_addNodeGraphPathCycleAtNew
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {s t : V}
    (R : RotationSystem (addNodeGraph G (insert t ({s} : Set V))))
    (p : G.Walk s t) (hp : p.IsPath) (hst : s ≠ t) :
    letI : DecidableRel
        (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
    RotationSystemGluing.IsFacialCycle R
        (addNodeGraphPathCycle p)
        (addNodeGraphPathCycle_isCycle hst p hp) ->
      RotationSystemGluing.IsFacialCycle R
        (addNodeGraphPathCycleAtNew p)
        (addNodeGraphPathCycleAtNew_isCycle hst p hp) := by
  classical
  intro hfacial
  exact isFacialCycle_of_darts_isRotated R
    (addNodeGraphPathCycle p)
    (addNodeGraphPathCycle_isCycle hst p hp)
    hfacial
    (addNodeGraphPathCycleAtNew p)
    (addNodeGraphPathCycleAtNew_isCycle hst p hp)
    (addNodeGraphPathCycleAtNew_darts_isRotated p)

/-- Deleting a newly inserted spoke recovers the smaller fan graph exactly. -/
theorem deletedGraph_addNodeGraph_insert
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (A : Set V) (y : V) (hy : y ∉ A) :
    EdgeDeletion.deletedGraph (addNodeGraph G (insert y A)) none (some y) =
      addNodeGraph G A := by
  apply SimpleGraph.ext
  funext a b
  apply propext
  cases a with
  | none =>
      cases b with
      | none => simp [EdgeDeletion.deletedGraph]
      | some z =>
          have hedge : s(none, some z) = s(none, some y) ↔ z = y := by
            simp
          simp only [EdgeDeletion.deletedGraph, SimpleGraph.deleteEdges_adj,
            addNodeGraph_none_some, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          change ((z = y ∨ z ∈ A) ∧ s(none, some z) ≠ s(none, some y)) ↔
            z ∈ A
          constructor
          · rintro ⟨hz | hz, hne⟩
            · exact False.elim (hne (hedge.mpr hz))
            · exact hz
          · intro hz
            exact ⟨Or.inr hz, fun hzy => hy ((hedge.mp hzy) ▸ hz)⟩
  | some z =>
      cases b with
      | none =>
          have hedge : s(some z, none) = s(none, some y) ↔ z = y := by
            simp
          simp only [EdgeDeletion.deletedGraph, SimpleGraph.deleteEdges_adj,
            addNodeGraph_some_none, Set.mem_insert_iff,
            Set.mem_singleton_iff]
          change ((z = y ∨ z ∈ A) ∧ s(some z, none) ≠ s(none, some y)) ↔
            z ∈ A
          constructor
          · rintro ⟨hz | hz, hne⟩
            · exact False.elim (hne (hedge.mpr hz))
            · exact hz
          · intro hz
            exact ⟨Or.inr hz, fun hzy => hy ((hedge.mp hzy) ▸ hz)⟩
      | some t =>
          simp [EdgeDeletion.deletedGraph, SimpleGraph.deleteEdges_adj]

/-- Identity graph isomorphism induced by equality of graph structures on the
same vertex type. -/
def graphIsoOfEq
    {V : Type u} {G H : SimpleGraph V} (h : G = H) : G ≃g H where
  toEquiv := Equiv.refl V
  map_rel_iff' := by
    intro x y
    rw [h]
    rfl

/-- One retained-face spoke insertion specialized to `addNodeGraph`. -/
theorem exists_addNodeGraph_insertRetained
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Set V) [DecidableRel (addNodeGraph G A).Adj]
    (y : V) (hy : y ∉ A)
    (R : RotationSystem (addNodeGraph G A))
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge (addNodeGraph G A))
    (pre post : List (OrientedEdge (addNodeGraph G A)))
    (hrest : B.rest = pre ++ q :: post)
    (hfirst : B.first.tail = none)
    (hq : q.tail = some y) :
    letI : DecidableRel (addNodeGraph G (insert y A)).Adj := Classical.decRel _
    Exists fun S : RotationSystem (addNodeGraph G (insert y A)) =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun C : FaceBoundary S.toHypermap =>
          C.first.tail = none ∧
            Exists fun lift : OrientedEdge (addNodeGraph G A) ->
                OrientedEdge (addNodeGraph G (insert y A)) =>
              (forall d, (lift d).tail = d.tail) ∧
                C.rest = lift q :: post.map lift := by
  classical
  let H := addNodeGraph G (insert y A)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hny : H.Adj none (some y) := by simp [H]
  have hdel : EdgeDeletion.deletedGraph H none (some y) = addNodeGraph G A := by
    exact deletedGraph_addNodeGraph_insert G A y hy
  let D := EdgeDeletion.deletedGraph H none (some y)
  letI : DecidableRel D.Adj := inferInstance
  let phi : D ≃g addNodeGraph G A := graphIsoOfEq hdel
  let RD : RotationSystem D := RotationSystem.ofIso phi R
  let psi : Hypermap.Iso RD.toHypermap R.toHypermap :=
    RotationSystem.ofIso_toHypermapIso phi R
  have hRD : (RD.toHypermap).dual.EulerPlanar := by
    have hprimal : R.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
    have hsource : RD.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hprimal
    exact (Hypermap.dual_eulerPlanar_iff (G := RD.toHypermap)).mpr hsource
  let BD : FaceBoundary RD.toHypermap := B.mapIso psi.symm
  let dartPhi := orientedEdgeEquivOfGraphIso phi
  let qD : OrientedEdge D := dartPhi.symm q
  let preD : List (OrientedEdge D) := pre.map dartPhi.symm
  let postD : List (OrientedEdge D) := post.map dartPhi.symm
  have hrestD : BD.rest = preD ++ qD :: postD := by
    change B.rest.map dartPhi.symm =
      pre.map dartPhi.symm ++ dartPhi.symm q :: post.map dartPhi.symm
    rw [hrest, List.map_append, List.map_cons]
  have hfirstD : BD.first.tail = none := by
    change (dartPhi.symm B.first).tail = none
    simpa [dartPhi, phi, graphIsoOfEq] using hfirst
  have hqD : qD.tail = some y := by
    change (dartPhi.symm q).tail = some y
    simpa [dartPhi, phi, graphIsoOfEq] using hq
  rcases exists_addEdgeRetained hny RD hRD BD qD preD postD hrestD hfirstD hqD with
    ⟨S, hS, C, hCfirst, liftD, hliftDtail, hCrest⟩
  let lift : OrientedEdge (addNodeGraph G A) ->
      OrientedEdge (addNodeGraph G (insert y A)) :=
    fun d => liftD (dartPhi.symm d)
  refine ⟨S, hS, C, hCfirst, lift, ?_, ?_⟩
  · intro d
    calc
      (lift d).tail = (dartPhi.symm d).tail := hliftDtail _
      _ = d.tail := by rfl
  · rw [hCrest]
    change liftD (dartPhi.symm q) ::
        (post.map dartPhi.symm).map liftD =
      lift q :: post.map lift
    simp [lift, List.map_map]

/-- Two-face version of `exists_addNodeGraph_insertRetained`.  It exposes
both sides of the newly inserted spoke, which is the operation needed when a
fresh degree-two vertex is used to turn a facial path into a facial cycle. -/
theorem exists_addNodeGraph_insertSplitBoundaries
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Set V) [DecidableRel (addNodeGraph G A).Adj]
    (y : V) (hy : y ∉ A)
    (R : RotationSystem (addNodeGraph G A))
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge (addNodeGraph G A))
    (pre post : List (OrientedEdge (addNodeGraph G A)))
    (hrest : B.rest = pre ++ q :: post)
    (hfirst : B.first.tail = none)
    (hq : q.tail = some y) :
    letI : DecidableRel (addNodeGraph G (insert y A)).Adj := Classical.decRel _
    Exists fun S : RotationSystem (addNodeGraph G (insert y A)) =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun retained : FaceBoundary S.toHypermap =>
          Exists fun complementary : FaceBoundary S.toHypermap =>
            retained.first.tail = none ∧
              complementary.first.tail = some y ∧
                Exists fun lift : OrientedEdge (addNodeGraph G A) ->
                    OrientedEdge (addNodeGraph G (insert y A)) =>
                  (forall d, (lift d).tail = d.tail) ∧
                    (forall d, (lift d).head = d.head) ∧
                      retained.rest = lift q :: post.map lift ∧
                        complementary.rest =
                          lift B.first :: pre.map lift := by
  classical
  let H := addNodeGraph G (insert y A)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hny : H.Adj none (some y) := by simp [H]
  have hdel : EdgeDeletion.deletedGraph H none (some y) = addNodeGraph G A :=
    deletedGraph_addNodeGraph_insert G A y hy
  let D := EdgeDeletion.deletedGraph H none (some y)
  letI : DecidableRel D.Adj := inferInstance
  let phi : D ≃g addNodeGraph G A := graphIsoOfEq hdel
  let RD : RotationSystem D := RotationSystem.ofIso phi R
  let psi : Hypermap.Iso RD.toHypermap R.toHypermap :=
    RotationSystem.ofIso_toHypermapIso phi R
  have hRD : (RD.toHypermap).dual.EulerPlanar := by
    have hprimal : R.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
    have hsource : RD.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hprimal
    exact (Hypermap.dual_eulerPlanar_iff (G := RD.toHypermap)).mpr hsource
  let BD : FaceBoundary RD.toHypermap := B.mapIso psi.symm
  let dartPhi := orientedEdgeEquivOfGraphIso phi
  let qD : OrientedEdge D := dartPhi.symm q
  let preD : List (OrientedEdge D) := pre.map dartPhi.symm
  let postD : List (OrientedEdge D) := post.map dartPhi.symm
  have hrestD : BD.rest = preD ++ qD :: postD := by
    change B.rest.map dartPhi.symm =
      pre.map dartPhi.symm ++ dartPhi.symm q :: post.map dartPhi.symm
    rw [hrest, List.map_append, List.map_cons]
  have hfirstD : BD.first.tail = none := by
    change (dartPhi.symm B.first).tail = none
    simpa [dartPhi, phi, graphIsoOfEq] using hfirst
  have hqD : qD.tail = some y := by
    change (dartPhi.symm q).tail = some y
    simpa [dartPhi, phi, graphIsoOfEq] using hq
  rcases exists_addEdgeSplitBoundaries hny RD hRD BD qD preD postD
      hrestD hfirstD hqD with
    ⟨S, hS, retained, complementary, hretained, hcomplementary,
      liftD, hliftDtail, hliftDhead, hretainedRest, hcomplementaryRest⟩
  let lift : OrientedEdge (addNodeGraph G A) ->
      OrientedEdge (addNodeGraph G (insert y A)) :=
    fun d => liftD (dartPhi.symm d)
  refine ⟨S, hS, retained, complementary, hretained, hcomplementary,
    lift, ?_, ?_, ?_, ?_⟩
  · intro d
    calc
      (lift d).tail = (dartPhi.symm d).tail := hliftDtail _
      _ = d.tail := by rfl
  · intro d
    calc
      (lift d).head = (dartPhi.symm d).head := hliftDhead _
      _ = d.head := by rfl
  · rw [hretainedRest]
    change liftD (dartPhi.symm q) ::
        (post.map dartPhi.symm).map liftD =
      lift q :: post.map lift
    simp [lift, List.map_map]
  · rw [hcomplementaryRest]
    change liftD (dartPhi.symm B.first) ::
        (pre.map dartPhi.symm).map liftD =
      lift B.first :: pre.map lift
    simp [lift, List.map_map]


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
