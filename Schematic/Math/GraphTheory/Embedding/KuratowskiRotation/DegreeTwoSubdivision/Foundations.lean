import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.EdgeSubdivision

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace DegreeTwoSubdivision

/-!
Graph-facing boundary for the degree-two uncontraction branch.

If `v` has exactly the two neighbours `w` and `u`, and `w` is not adjacent to
`u`, then contracting `v--w` produces a quotient edge from the collapsed
vertex to `u`.  Recovering `G` from the quotient is exactly subdivision of
that quotient edge, with the collapsed quotient vertex interpreted as the
retained endpoint `w` and the new subdivision vertex interpreted as `v`.
-/

/-- Interpret a vertex of `G / vw` as the corresponding old vertex of `G`,
using `w` for the collapsed quotient vertex. -/
def collapsedVertexToOriginal
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w) :
    (GraphContraction.collapseEdge G hvw).Target -> V
  | none => w
  | some x => x

@[simp]
theorem collapsedVertexToOriginal_none
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w) :
    collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
        (none : (GraphContraction.collapseEdge G hvw).Target) = w :=
  rfl

@[simp]
theorem collapsedVertexToOriginal_outside
    {V : Type u} {G : SimpleGraph V}
    {v w x : V}
    (hvw : G.Adj v w)
    (hx : x ∉ ({v, w} : Set V)) :
    collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
        (GraphContraction.collapseEdgeOutside G hvw x hx) = x :=
  rfl

@[simp]
theorem collapseEdge_map_collapsedVertexToOriginal
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (y : (GraphContraction.collapseEdge G hvw).Target) :
    (GraphContraction.collapseEdge G hvw).map
        (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw y) =
      y := by
  classical
  cases y with
  | none =>
      simp [collapsedVertexToOriginal, GraphContraction.collapseEdge,
        GraphContraction.collapseSubgraph, GraphContraction.ofMap]
  | some x =>
      have hx : (x : V) ∉ ({v, w} : Set V) := by
        simpa using x.2
      simp [collapsedVertexToOriginal, GraphContraction.collapseEdge,
        GraphContraction.collapseSubgraph, GraphContraction.ofMap, hx]

@[simp]
theorem collapsedVertexToOriginal_map_of_ne
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w x : V}
    (hvw : G.Adj v w)
    (hx : x ≠ v) :
    collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
        ((GraphContraction.collapseEdge G hvw).map x) = x := by
  classical
  by_cases hxw : x = w
  · subst x
    simp [collapsedVertexToOriginal, GraphContraction.collapseEdge,
      GraphContraction.collapseSubgraph, GraphContraction.ofMap]
  · have hxpair : x ∉ ({v, w} : Set V) := by
      simp [hx, hxw]
    have hmap :
        (GraphContraction.collapseEdge G hvw).map x =
          GraphContraction.collapseEdgeOutside G hvw x hxpair := by
      simp [GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
        GraphContraction.ofMap, GraphContraction.collapseEdgeOutside, hxpair]
    rw [hmap]
    rfl

theorem collapsedVertexToOriginal_ne_left
    {V : Type u}
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (y : (GraphContraction.collapseEdge G hvw).Target) :
    collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw y ≠ v := by
  cases y with
  | none =>
      exact hvw.ne'
  | some x =>
      intro h
      exact x.2 (by
        change (x : V) ∈ ({v, w} : Set V)
        exact Or.inl h)

theorem collapseEdgeOutside_ne_none
    {V : Type u} {G : SimpleGraph V}
    {v w x : V}
    (hvw : G.Adj v w)
    (hx : x ∉ ({v, w} : Set V)) :
    GraphContraction.collapseEdgeOutside G hvw x hx ≠
      (none : (GraphContraction.collapseEdge G hvw).Target) := by
  intro h
  cases h

/-- The quotient dart `none -> u` that is split when the degree-two vertex
`v` is restored. -/
def splitDart
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    OrientedEdge (GraphContraction.collapseEdge G hvw).graph :=
  ⟨((none : (GraphContraction.collapseEdge G hvw).Target),
      GraphContraction.collapseEdgeOutside G hvw u hu),
    (GraphContraction.collapseEdge_adj_none_outside_iff
      (G := G) hvw hu).mpr (Or.inl hvu)⟩

@[simp]
theorem splitDart_tail
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).tail =
      (none : (GraphContraction.collapseEdge G hvw).Target) :=
  rfl

@[simp]
theorem splitDart_head
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).head =
      GraphContraction.collapseEdgeOutside G hvw u hu :=
  rfl

@[simp]
theorem splitDart_symm_tail
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    ((splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm).tail =
      GraphContraction.collapseEdgeOutside G hvw u hu :=
  rfl

@[simp]
theorem splitDart_symm_head
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    ((splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm).head =
      (none : (GraphContraction.collapseEdge G hvw).Target) :=
  rfl

theorem outside_eq_of_collapseEdgeOutside_eq
    {V : Type u} {G : SimpleGraph V}
    {v w x y : V}
    (hvw : G.Adj v w)
    (hx : x ∉ ({v, w} : Set V))
    (hy : y ∉ ({v, w} : Set V))
    (h :
      GraphContraction.collapseEdgeOutside G hvw x hx =
        GraphContraction.collapseEdgeOutside G hvw y hy) :
    x = y := by
  simpa [GraphContraction.collapseEdgeOutside] using congrArg
    (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw) h

theorem splitDart_eq_of_tail_none_head_u
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hvw).Target))
    (hhead :
      e.head = GraphContraction.collapseEdgeOutside G hvw u hu) :
    e = splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu := by
  exact orientedEdge_eq_of_tail_head htail hhead

theorem splitDart_symm_eq_of_tail_u_head_none
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (htail :
      e.tail = GraphContraction.collapseEdgeOutside G hvw u hu)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hvw).Target)) :
    e = (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm := by
  exact orientedEdge_eq_of_tail_head htail hhead

/-- Lift quotient-dart adjacency through a contraction once adjacency from the
collapsed endpoint has an old representative.  Reversal handles the opposite
orientation, while outside-to-outside darts lift uniformly. -/
theorem collapsedVertexToOriginal_adj_of_endpoint_lift
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (P : OrientedEdge (GraphContraction.collapseEdge G hvw).graph -> Prop)
    (hlift :
      forall (d : OrientedEdge (GraphContraction.collapseEdge G hvw).graph),
        P d -> forall (x : V) (hx : x ∉ ({v, w} : Set V)),
          d.tail = (none : (GraphContraction.collapseEdge G hvw).Target) ->
          d.head = GraphContraction.collapseEdgeOutside G hvw x hx ->
          G.Adj w x)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (he : P e) (he_symm : P e.symm) :
    G.Adj
      (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail)
      (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head) := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  cases htail : e.tail with
  | none =>
      cases hhead : e.head with
      | none =>
          have hloop : C.graph.Adj
              (none : C.Target) (none : C.Target) := by
            simpa [C, htail, hhead] using e.adj
          exact False.elim (C.graph.loopless.irrefl _ hloop)
      | some x =>
          have hx : (x : V) ∉ ({v, w} : Set V) := by
            simpa [C] using x.2
          have hhead_outside :
              e.head = GraphContraction.collapseEdgeOutside G hvw (x : V) hx := by
            simpa [C, GraphContraction.collapseEdgeOutside] using hhead
          simpa [collapsedVertexToOriginal, htail, hhead, C] using
            hlift e he (x : V) hx htail hhead_outside
  | some x =>
      have hx : (x : V) ∉ ({v, w} : Set V) := by
        simpa [C] using x.2
      cases hhead : e.head with
      | none =>
          have htail_outside :
              e.symm.head =
                GraphContraction.collapseEdgeOutside G hvw (x : V) hx := by
            simpa [C, GraphContraction.collapseEdgeOutside] using htail
          simpa [collapsedVertexToOriginal, htail, hhead, C] using
            (hlift e.symm he_symm (x : V) hx hhead htail_outside).symm
      | some y =>
          have hy : (y : V) ∉ ({v, w} : Set V) := by
            simpa [C] using y.2
          have hadj :
              C.graph.Adj
                (GraphContraction.collapseEdgeOutside G hvw (x : V) hx)
                (GraphContraction.collapseEdgeOutside G hvw (y : V) hy) := by
            simpa [C, htail, hhead, GraphContraction.collapseEdgeOutside] using e.adj
          rcases hadj with ⟨_hneq, a, b, ha, hb, hab⟩
          have hx_map :
              C.map (x : V) =
                GraphContraction.collapseEdgeOutside G hvw (x : V) hx := by
            simp [C, GraphContraction.collapseEdge,
              GraphContraction.collapseSubgraph, GraphContraction.ofMap,
              GraphContraction.collapseEdgeOutside, hx]
          have hy_map :
              C.map (y : V) =
                GraphContraction.collapseEdgeOutside G hvw (y : V) hy := by
            simp [C, GraphContraction.collapseEdge,
              GraphContraction.collapseSubgraph, GraphContraction.ofMap,
              GraphContraction.collapseEdgeOutside, hy]
          have ha_eq : a = (x : V) := by
            rcases
                (GraphContraction.collapseEdge_map_eq_iff
                  (G := G) hvw (v := a) (w := (x : V))).mp
                  (ha.trans hx_map.symm) with
              hpair | hout
            · exact False.elim (hx hpair.2)
            · exact hout.1
          have hb_eq : b = (y : V) := by
            rcases
                (GraphContraction.collapseEdge_map_eq_iff
                  (G := G) hvw (v := b) (w := (y : V))).mp
                  (hb.trans hy_map.symm) with
              hpair | hout
            · exact False.elim (hy hpair.2)
            · exact hout.1
          simpa [collapsedVertexToOriginal, htail, hhead, ha_eq, hb_eq, C] using hab

/-- Every quotient dart except the split edge and its reverse is already an
old edge of the original graph, after interpreting the collapsed quotient
vertex as the retained endpoint `w`.

The quotient-edge lift and the two-neighbor classification suffice here; the
non-adjacency assumption used by the surrounding subdivision case is not
needed for this local edge reconstruction. -/
theorem oldDart_adj_of_ne_split
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (hne :
      e ≠ splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
    (hne_symm :
      e ≠ (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm) :
    G.Adj
      (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail)
      (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head) := by
  classical
  let z := splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  apply collapsedVertexToOriginal_adj_of_endpoint_lift hvw
      (fun d => d ≠ z) ?_ hne
  · intro h
    apply hne_symm
    have := congrArg OrientedEdge.symm h
    simpa [z] using this
  · intro d hd x hx htail hhead
    have hadj :
        (GraphContraction.collapseEdge G hvw).graph.Adj
          (none : (GraphContraction.collapseEdge G hvw).Target)
          (GraphContraction.collapseEdgeOutside G hvw x hx) := by
      simpa [htail, hhead] using d.adj
    rcases
        (GraphContraction.collapseEdge_adj_none_outside_iff
          (G := G) hvw hx).mp hadj with
      hvx | hwx
    · rcases hneigh x hvx with hxw | hxu
      · exact False.elim (hx (by simp [hxw]))
      · exfalso
        apply hd
        apply splitDart_eq_of_tail_none_head_u
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu htail
        simpa [hxu] using hhead
    · exact hwx

/-- Interpret an old quotient dart as a dart of the original graph in the
non-adjacent degree-two subdivision case.  The named split dart and its
reverse are sent to the two old half-edges incident with the restored
degree-two vertex; all other quotient darts use `oldDart_adj_of_ne_split`. -/
noncomputable def oldDartToOriginal
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :
    OrientedEdge G :=
  if hsplit :
      e = splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu then
    ⟨(w, v), hvw.symm⟩
  else if hsplit_symm :
      e = (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm then
    ⟨(u, v), hvu.symm⟩
  else
    ⟨(collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail,
      collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head),
      oldDart_adj_of_ne_split
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hsplit hsplit_symm⟩

@[simp]
theorem oldDartToOriginal_splitDart
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u) :
    oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu) =
      (⟨(w, v), hvw.symm⟩ : OrientedEdge G) := by
  simp [oldDartToOriginal]

@[simp]
theorem oldDartToOriginal_splitDart_symm
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u) :
    oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh
        ((splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm) =
      (⟨(u, v), hvu.symm⟩ : OrientedEdge G) := by
  have hne :
      (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm ≠
        splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu := by
    intro h
    have htail :
        GraphContraction.collapseEdgeOutside G hvw u hu =
          (none : (GraphContraction.collapseEdge G hvw).Target) := by
      simpa using congrArg OrientedEdge.tail h
    exact collapseEdgeOutside_ne_none (G := G) hvw hu htail
  simp [oldDartToOriginal, hne]

theorem oldDartToOriginal_of_ne_split
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (hne :
      e ≠ splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
    (hne_symm :
      e ≠ (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm) :
    oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh e =
      ⟨(collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail,
        collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head),
        oldDart_adj_of_ne_split
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hne hne_symm⟩ := by
  simp [oldDartToOriginal, hne, hne_symm]

theorem oldDartToOriginal_tail_of_tail_eq_map
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u a : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (ha : a ≠ v)
    (htail : e.tail = (GraphContraction.collapseEdge G hvw).map a) :
    (oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh e).tail = a := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  by_cases hsplit :
      e = splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  · subst e
    have hmap : C.map a = C.map w := by
      have hnone : C.map a = (none : C.Target) := by
        simpa [C] using htail.symm
      have hw_none : C.map w = (none : C.Target) := by
        simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
          GraphContraction.ofMap]
      exact hnone.trans hw_none.symm
    have haw : a = w := by
      rcases
          (GraphContraction.collapseEdge_map_eq_iff
            (G := G) hvw (v := a) (w := w)).mp hmap with
        hpair | hout
      · rcases (by simpa using hpair.1 : a = v ∨ a = w) with hav | haw
        · exact False.elim (ha hav)
        · exact haw
      · exact hout.1
    rw [haw, oldDartToOriginal_splitDart
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh]
    rfl
  · by_cases hsplit_symm :
      e = (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm
    · subst e
      have hmap : C.map a = C.map u := by
        have ha_map :
            C.map a = GraphContraction.collapseEdgeOutside G hvw u hu := by
          simpa [C] using htail.symm
        have hu_map :
            C.map u = GraphContraction.collapseEdgeOutside G hvw u hu := by
          simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
            GraphContraction.ofMap, GraphContraction.collapseEdgeOutside, hu]
        exact ha_map.trans hu_map.symm
      have hau : a = u := by
        rcases
            (GraphContraction.collapseEdge_map_eq_iff
              (G := G) hvw (v := a) (w := u)).mp hmap with
          hpair | hout
        · exact False.elim (hu hpair.2)
        · exact hout.1
      rw [hau, oldDartToOriginal_splitDart_symm
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh]
      rfl
    · rw [oldDartToOriginal_of_ne_split
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hsplit hsplit_symm]
      change
        collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail = a
      rw [htail]
      exact collapsedVertexToOriginal_map_of_ne
        (G := G) (v := v) (w := w) hvw ha

/-- Inverse map from the pure edge-subdivision dart extension to original
oriented edges. -/
noncomputable def subdivisionExtInvFun
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u) :
    ExtDart (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) ->
      OrientedEdge G
  | ExtDart.new => ⟨(v, u), hvu⟩
  | ExtDart.newEdge => ⟨(v, w), hvw⟩
  | ExtDart.old e =>
      oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh e

@[simp]
theorem subdivisionExtInvFun_new
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u) :
    subdivisionExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh ExtDart.new =
      (⟨(v, u), hvu⟩ : OrientedEdge G) :=
  rfl

@[simp]
theorem subdivisionExtInvFun_newEdge
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u) :
    subdivisionExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh ExtDart.newEdge =
      (⟨(v, w), hvw⟩ : OrientedEdge G) :=
  rfl

@[simp]
theorem subdivisionExtInvFun_old
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :
    subdivisionExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh (ExtDart.old e) =
      oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh e :=
  rfl

/-- Original darts not incident with the restored degree-two vertex descend to
old quotient darts. -/
noncomputable def quotientDartOfOriginalOld
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v)
    (hhead : e.head ≠ v) :
    OrientedEdge (GraphContraction.collapseEdge G hvw).graph := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  have hneq : C.map e.tail ≠ C.map e.head := by
    intro hsame
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hvw (v := e.tail) (w := e.head)).mp hsame with
      hpair | hout
    · have htail_pair : e.tail = v ∨ e.tail = w := by
        simpa using hpair.1
      have hhead_pair : e.head = v ∨ e.head = w := by
        simpa using hpair.2
      rcases htail_pair with htail_v | htail_w
      · exact htail htail_v
      · rcases hhead_pair with hhead_v | hhead_w
        · exact hhead hhead_v
        · exact e.adj.ne (htail_w.trans hhead_w.symm)
    · exact e.adj.ne hout.1
  have hadj : C.graph.Adj (C.map e.tail) (C.map e.head) := by
    rcases C.map_adj e.adj with hsame | hadj
    · exact False.elim (hneq hsame)
    · exact hadj
  exact ⟨(C.map e.tail, C.map e.head), hadj⟩

@[simp]
theorem quotientDartOfOriginalOld_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v)
    (hhead : e.head ≠ v) :
    (quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e htail hhead).tail =
      (GraphContraction.collapseEdge G hvw).map e.tail :=
  rfl

@[simp]
theorem quotientDartOfOriginalOld_head
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v)
    (hhead : e.head ≠ v) :
    (quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e htail hhead).head =
      (GraphContraction.collapseEdge G hvw).map e.head :=
  rfl

@[simp]
theorem quotientDartOfOriginalOld_symm
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v)
    (hhead : e.head ≠ v) :
    quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e.symm hhead htail =
      (quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e htail hhead).symm := by
  apply orientedEdge_eq_of_tail_head <;> rfl

end DegreeTwoSubdivision

end FourColor

end Schematic.Math.GraphTheory
