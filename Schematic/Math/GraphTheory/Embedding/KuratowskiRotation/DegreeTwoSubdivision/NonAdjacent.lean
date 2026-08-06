import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.DegreeTwoSubdivision.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace DegreeTwoSubdivision

/-- Forward map from original oriented edges to the pure edge-subdivision dart
extension of the contracted graph. -/
noncomputable def subdivisionExtToFun
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (_hvu : G.Adj v u)
    (_hu : u ∉ ({v, w} : Set V))
    (e : OrientedEdge G) :
    ExtDart (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :=
  if htail : e.tail = v then
    if e.head = u then ExtDart.new else ExtDart.newEdge
  else if hhead : e.head = v then
    if e.tail = u then
      ExtDart.old
        ((splitDart (G := G) (v := v) (w := w) (u := u)
          hvw _hvu _hu).symm)
    else
      ExtDart.old
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw _hvu _hu)
  else
    ExtDart.old
      (quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e htail hhead)

@[simp]
theorem subdivisionExtToFun_vu
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(v, u), hvu⟩ : OrientedEdge G) =
      ExtDart.new := by
  simp [subdivisionExtToFun, OrientedEdge.tail, OrientedEdge.head]

@[simp]
theorem subdivisionExtToFun_vw
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(v, w), hvw⟩ : OrientedEdge G) =
      ExtDart.newEdge := by
  have hwu : w ≠ u := by
    intro h
    exact hu (by simp [h])
  simp [subdivisionExtToFun, OrientedEdge.tail, OrientedEdge.head, hwu]

@[simp]
theorem subdivisionExtToFun_uv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(u, v), hvu.symm⟩ : OrientedEdge G) =
      ExtDart.old
        ((splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm) := by
  have huv : u ≠ v := by
    intro h
    exact hu (by simp [h])
  simp [subdivisionExtToFun, OrientedEdge.tail, OrientedEdge.head, huv]

@[simp]
theorem subdivisionExtToFun_wv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(w, v), hvw.symm⟩ : OrientedEdge G) =
      ExtDart.old
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu) := by
  have hwv : w ≠ v := hvw.ne'
  have hwu : w ≠ u := by
    intro h
    exact hu (by simp [h])
  simp [subdivisionExtToFun, OrientedEdge.tail, OrientedEdge.head, hwv, hwu]

theorem subdivisionExtToFun_old_of_tail_ne
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v) :
    Exists fun q : OrientedEdge (GraphContraction.collapseEdge G hvw).graph =>
      subdivisionExtToFun
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
        ExtDart.old q ∧
      q.tail = (GraphContraction.collapseEdge G hvw).map e.tail := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  by_cases hhead : e.head = v
  · by_cases htailu : e.tail = u
    · refine ⟨
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm,
        ?_, ?_⟩
      · have huv : u ≠ v := by
          intro h
          exact hu (by simp [h])
        simp [subdivisionExtToFun, hhead, htailu, huv]
      · have hu_map :
            C.map u = GraphContraction.collapseEdgeOutside G hvw u hu := by
          simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
            GraphContraction.ofMap, GraphContraction.collapseEdgeOutside, hu]
        simpa [C, htailu] using hu_map.symm
    · have htailw : e.tail = w := by
        rcases hneigh e.tail (by simpa [hhead] using e.adj.symm) with hw | hu'
        · exact hw
        · exact False.elim (htailu hu')
      refine ⟨
        splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu,
        ?_, ?_⟩
      · simp [subdivisionExtToFun, htail, hhead, htailu]
      · have hw_map : C.map w = (none : C.Target) := by
          simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
            GraphContraction.ofMap]
        simpa [C, htailw] using hw_map.symm
  · refine ⟨
      quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e htail hhead,
      ?_, ?_⟩
    · simp [subdivisionExtToFun, htail, hhead]
    · rw [quotientDartOfOriginalOld_tail]

theorem quotientDartOfOriginalOld_ne_split
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hnonadj : ¬ G.Adj w u)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v)
    (hhead : e.head ≠ v) :
    quotientDartOfOriginalOld (G := G) (v := v) (w := w)
        hvw e htail hhead ≠
      splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu := by
  classical
  intro h
  let C := GraphContraction.collapseEdge G hvw
  have htail_none :
      C.map e.tail = (none : C.Target) := by
    simpa [C] using congrArg OrientedEdge.tail h
  have hmap_w : C.map w = (none : C.Target) := by
    simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
      GraphContraction.ofMap]
  have htail_w : e.tail = w := by
    have hsame : C.map e.tail = C.map w := htail_none.trans hmap_w.symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hvw (v := e.tail) (w := w)).mp hsame with
      hpair | hout
    · rcases (by simpa using hpair.1 : e.tail = v ∨ e.tail = w) with hv | hw
      · exact False.elim (htail hv)
      · exact hw
    · exact hout.1
  have hhead_u : e.head = u := by
    have hhead_map :
        C.map e.head = GraphContraction.collapseEdgeOutside G hvw u hu := by
      simpa [C] using congrArg OrientedEdge.head h
    have hmap_u :
        C.map u = GraphContraction.collapseEdgeOutside G hvw u hu := by
      simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
        GraphContraction.ofMap, GraphContraction.collapseEdgeOutside, hu]
    have hsame : C.map e.head = C.map u := hhead_map.trans hmap_u.symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hvw (v := e.head) (w := u)).mp hsame with
      hpair | hout
    · exact False.elim (hu hpair.2)
    · exact hout.1
  exact hnonadj (by simpa [htail_w, hhead_u] using e.adj)

theorem quotientDartOfOriginalOld_ne_split_symm
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hnonadj : ¬ G.Adj w u)
    (e : OrientedEdge G)
    (htail : e.tail ≠ v)
    (hhead : e.head ≠ v) :
    quotientDartOfOriginalOld (G := G) (v := v) (w := w)
        hvw e htail hhead ≠
      (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm := by
  classical
  intro h
  let C := GraphContraction.collapseEdge G hvw
  have htail_u : e.tail = u := by
    have htail_map :
        C.map e.tail = GraphContraction.collapseEdgeOutside G hvw u hu := by
      simpa [C] using congrArg OrientedEdge.tail h
    have hmap_u :
        C.map u = GraphContraction.collapseEdgeOutside G hvw u hu := by
      simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
        GraphContraction.ofMap, GraphContraction.collapseEdgeOutside, hu]
    have hsame : C.map e.tail = C.map u := htail_map.trans hmap_u.symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hvw (v := e.tail) (w := u)).mp hsame with
      hpair | hout
    · exact False.elim (hu hpair.2)
    · exact hout.1
  have hhead_w : e.head = w := by
    have hhead_none :
        C.map e.head = (none : C.Target) := by
      simpa [C] using congrArg OrientedEdge.head h
    have hmap_w : C.map w = (none : C.Target) := by
      simp [C, GraphContraction.collapseEdge, GraphContraction.collapseSubgraph,
        GraphContraction.ofMap]
    have hsame : C.map e.head = C.map w := hhead_none.trans hmap_w.symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hvw (v := e.head) (w := w)).mp hsame with
      hpair | hout
    · rcases (by simpa using hpair.1 : e.head = v ∨ e.head = w) with hv | hw
      · exact False.elim (hhead hv)
      · exact hw
    · exact hout.1
  exact hnonadj (by simpa [htail_u, hhead_w] using e.adj.symm)

theorem subdivisionExt_left_inv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (e : OrientedEdge G) :
    subdivisionExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh
        (subdivisionExtToFun
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu e) =
      e := by
  classical
  by_cases htail : e.tail = v
  ·
    by_cases hheadu : e.head = u
    · have hmap :
          subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.new := by
        simp [subdivisionExtToFun, htail, hheadu]
      rw [hmap]
      apply orientedEdge_eq_of_tail_head
      · exact htail.symm
      · exact hheadu.symm
    · have hmap :
          subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.newEdge := by
        simp [subdivisionExtToFun, htail, hheadu]
      rw [hmap]
      have hheadw : e.head = w := by
        rcases hneigh e.head (by simpa [htail] using e.adj) with hw | hu'
        · exact hw
        · exact False.elim (hheadu hu')
      apply orientedEdge_eq_of_tail_head
      · exact htail.symm
      · exact hheadw.symm
  ·
    by_cases hhead : e.head = v
    ·
      by_cases htailu : e.tail = u
      · have hmap :
            subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
              ExtDart.old
                ((splitDart
                  (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm) := by
          have huv : u ≠ v := by
            intro h
            exact hu (by simp [h])
          simp [subdivisionExtToFun, hhead, htailu, huv]
        rw [hmap]
        rw [subdivisionExtInvFun_old,
          oldDartToOriginal_splitDart_symm
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hneigh]
        apply orientedEdge_eq_of_tail_head
        · exact htailu.symm
        · exact hhead.symm
      · have hmap :
            subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
              ExtDart.old
                (splitDart
                  (G := G) (v := v) (w := w) (u := u) hvw hvu hu) := by
          simp [subdivisionExtToFun, htail, hhead, htailu]
        rw [hmap]
        rw [subdivisionExtInvFun_old,
          oldDartToOriginal_splitDart
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hneigh]
        have htailw : e.tail = w := by
          rcases hneigh e.tail (by simpa [hhead] using e.adj.symm) with hw | hu'
          · exact hw
          · exact False.elim (htailu hu')
        apply orientedEdge_eq_of_tail_head
        · exact htailw.symm
        · exact hhead.symm
    ·
      let q :=
        quotientDartOfOriginalOld
          (G := G) (v := v) (w := w) hvw e htail hhead
      have hmap :
          subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.old q := by
        simp [subdivisionExtToFun, htail, hhead, q]
      rw [hmap]
      have hq_ne :
          q ≠ splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu :=
        quotientDartOfOriginalOld_ne_split
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hnonadj e htail hhead
      have hq_ne_symm :
          q ≠ (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm :=
        quotientDartOfOriginalOld_ne_split_symm
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hnonadj e htail hhead
      have htail_eq :
          (oldDartToOriginal
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hneigh q).tail = e.tail := by
        rw [oldDartToOriginal_of_ne_split
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hq_ne hq_ne_symm]
        change
          collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
              ((GraphContraction.collapseEdge G hvw).map e.tail) =
            e.tail
        exact collapsedVertexToOriginal_map_of_ne
          (G := G) (v := v) (w := w) hvw htail
      have hhead_eq :
          (oldDartToOriginal
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hneigh q).head = e.head := by
        rw [oldDartToOriginal_of_ne_split
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hq_ne hq_ne_symm]
        change
          collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
              ((GraphContraction.collapseEdge G hvw).map e.head) =
            e.head
        exact collapsedVertexToOriginal_map_of_ne
          (G := G) (v := v) (w := w) hvw hhead
      exact orientedEdge_eq_of_tail_head htail_eq hhead_eq

theorem subdivisionExt_right_inv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (x : ExtDart (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)) :
    subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (subdivisionExtInvFun
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh x) =
      x := by
  classical
  cases x with
  | new =>
      simp [subdivisionExtInvFun, subdivisionExtToFun_vu]
  | newEdge =>
      simp [subdivisionExtInvFun, subdivisionExtToFun_vw]
  | old e =>
      by_cases hsplit :
          e = splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
      · subst e
        simp [subdivisionExtInvFun, subdivisionExtToFun_wv]
      · by_cases hsplit_symm :
            e = (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu).symm
        · subst e
          simp [subdivisionExtInvFun, subdivisionExtToFun_uv]
        · let o : OrientedEdge G :=
            oldDartToOriginal
              (G := G) (v := v) (w := w) (u := u)
              hvw hvu hu hneigh e
          have ho_eq :
              o =
                ⟨(collapsedVertexToOriginal
                    (G := G) (v := v) (w := w) hvw e.tail,
                  collapsedVertexToOriginal
                    (G := G) (v := v) (w := w) hvw e.head),
                  oldDart_adj_of_ne_split
                    (G := G) (v := v) (w := w) (u := u)
                    hvw hvu hu hneigh hsplit hsplit_symm⟩ := by
            exact oldDartToOriginal_of_ne_split
              (G := G) (v := v) (w := w) (u := u)
              hvw hvu hu hneigh hsplit hsplit_symm
          have hotail_ne : o.tail ≠ v := by
            rw [ho_eq]
            exact collapsedVertexToOriginal_ne_left
              (G := G) (v := v) (w := w) hvw e.tail
          have hohead_ne : o.head ≠ v := by
            rw [ho_eq]
            exact collapsedVertexToOriginal_ne_left
              (G := G) (v := v) (w := w) hvw e.head
          have hmap :
              subdivisionExtToFun
                  (G := G) (v := v) (w := w) (u := u) hvw hvu hu o =
                ExtDart.old
                  (quotientDartOfOriginalOld
                    (G := G) (v := v) (w := w) hvw o hotail_ne hohead_ne) := by
            simp [subdivisionExtToFun, hotail_ne, hohead_ne]
          rw [subdivisionExtInvFun_old]
          change subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu o =
            ExtDart.old e
          rw [hmap]
          congr
          have hotail_eq :
              o.tail =
                collapsedVertexToOriginal
                  (G := G) (v := v) (w := w) hvw e.tail := by
            rw [ho_eq]
            rfl
          have hohead_eq :
              o.head =
                collapsedVertexToOriginal
                  (G := G) (v := v) (w := w) hvw e.head := by
            rw [ho_eq]
            rfl
          apply orientedEdge_eq_of_tail_head
          · rw [quotientDartOfOriginalOld_tail, hotail_eq]
            exact collapseEdge_map_collapsedVertexToOriginal
              (G := G) (v := v) (w := w) hvw e.tail
          · rw [quotientDartOfOriginalOld_head, hohead_eq]
            exact collapseEdge_map_collapsedVertexToOriginal
              (G := G) (v := v) (w := w) hvw e.head

/-- Oriented-edge equivalence for the non-adjacent degree-two subdivision
case.  The original graph's darts are exactly the two fresh darts at `v` plus
the quotient darts of `G / vw`, with the quotient dart `none -> u` split. -/
noncomputable def orientedEdgeEquiv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u) :
    OrientedEdge G ≃
      ExtDart (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) where
  toFun :=
    subdivisionExtToFun (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  invFun :=
    subdivisionExtInvFun
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh
  left_inv :=
    subdivisionExt_left_inv
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh hnonadj
  right_inv :=
    subdivisionExt_right_inv
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh

@[simp]
theorem orientedEdgeEquiv_apply
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (e : OrientedEdge G) :
    orientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj e =
      subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu e :=
  rfl

@[simp]
theorem orientedEdgeEquiv_symm_apply
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (x : ExtDart (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)) :
    (orientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj).symm x =
      subdivisionExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh x :=
  rfl

private theorem orientedEdgeEquiv_edge_of_head_ne
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) (hhead : e.head ≠ v) :
    orientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj e.symm =
      EdgeSubdivision.edge R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        R.toHypermap_plain
        (orientedEdgeEquiv
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hnonadj e) := by
  classical
  let z : OrientedEdge (GraphContraction.collapseEdge G hvw).graph :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  by_cases htail : e.tail = v
  · by_cases hheadu : e.head = u
    · have he : e = (⟨(v, u), hvu⟩ : OrientedEdge G) :=
        orientedEdge_eq_of_tail_head htail hheadu
      subst e
      simp only [orientedEdgeEquiv_apply]
      change
        subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu
            (⟨(u, v), hvu.symm⟩ : OrientedEdge G) =
          EdgeSubdivision.edge R.toHypermap z R.toHypermap_plain
            (subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu
              (⟨(v, u), hvu⟩ : OrientedEdge G))
      rw [subdivisionExtToFun_uv
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu,
        subdivisionExtToFun_vu
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu]
      change ExtDart.old z.symm =
        EdgeSubdivision.edge R.toHypermap z R.toHypermap_plain ExtDart.new
      rw [EdgeSubdivision.edge_new]
      rfl
    · have hheadw : e.head = w := by
        rcases hneigh e.head (by simpa [htail] using e.adj) with hw | hu'
        · exact hw
        · exact False.elim (hheadu hu')
      have he : e = (⟨(v, w), hvw⟩ : OrientedEdge G) :=
        orientedEdge_eq_of_tail_head htail hheadw
      subst e
      simp only [orientedEdgeEquiv_apply]
      change
        subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu
            (⟨(w, v), hvw.symm⟩ : OrientedEdge G) =
          EdgeSubdivision.edge R.toHypermap z R.toHypermap_plain
            (subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu
              (⟨(v, w), hvw⟩ : OrientedEdge G))
      rw [subdivisionExtToFun_wv
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu,
        subdivisionExtToFun_vw
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu]
      change ExtDart.old z =
        EdgeSubdivision.edge R.toHypermap z R.toHypermap_plain ExtDart.newEdge
      rw [EdgeSubdivision.edge_newEdge]
      rfl
  · let q :=
        quotientDartOfOriginalOld
          (G := G) (v := v) (w := w) hvw e htail hhead
    have hq_ne : q ≠ z := by
      simpa [z] using
        quotientDartOfOriginalOld_ne_split
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hnonadj e htail hhead
    have hq_ne_symm : q ≠ R.toHypermap.edge z := by
      have hq_ne_symm' : q ≠ z.symm := by
        simpa [z] using
          quotientDartOfOriginalOld_ne_split_symm
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hnonadj e htail hhead
      simpa [RotationSystem.toHypermap, OrientedEdge.edgePerm, z] using hq_ne_symm'
    have hmap :
        orientedEdgeEquiv
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hneigh hnonadj e = ExtDart.old q := by
      simp [orientedEdgeEquiv, subdivisionExtToFun, htail, hhead, q]
    have hmap_symm :
        orientedEdgeEquiv
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu hneigh hnonadj e.symm =
          ExtDart.old q.symm := by
      simp [orientedEdgeEquiv, subdivisionExtToFun, htail, hhead, q]
    rw [hmap, hmap_symm]
    change ExtDart.old q.symm =
      EdgeSubdivision.edge R.toHypermap z R.toHypermap_plain (ExtDart.old q)
    calc
      ExtDart.old q.symm = ExtDart.old (R.toHypermap.edge q) := rfl
      _ = EdgeSubdivision.edge R.toHypermap z R.toHypermap_plain
          (ExtDart.old q) := by
        rw [EdgeSubdivision.edge_old_ne R.toHypermap z q R.toHypermap_plain
          hq_ne hq_ne_symm]

theorem orientedEdgeEquiv_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) :
    orientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj e.symm =
      EdgeSubdivision.edge R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        R.toHypermap_plain
        (orientedEdgeEquiv
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hnonadj e) := by
  classical
  by_cases hhead : e.head = v
  · have htail : e.tail ≠ v := by
      intro h
      exact e.adj.ne (h.trans hhead.symm)
    have hreverse := orientedEdgeEquiv_edge_of_head_ne
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hnonadj R e.symm (by simpa using htail)
    let z := splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
    exact (EdgeSubdivision.edgeToFun_involutive R.toHypermap z
      R.toHypermap_plain).eq_iff.mp (by simpa [z] using hreverse.symm)
  · exact orientedEdgeEquiv_edge_of_head_ne
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hnonadj R e hhead

theorem subdivisionExt_node_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) :
    (subdivisionExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh
        (EdgeSubdivision.node R.toHypermap
          (subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu e))).tail = e.tail := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  by_cases htail : e.tail = v
  · by_cases hheadu : e.head = u
    · have hmap :
          subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.new := by
        simp [subdivisionExtToFun, htail, hheadu]
      rw [hmap]
      change OrientedEdge.tail (⟨(v, w), hvw⟩ : OrientedEdge G) = e.tail
      exact htail.symm
    · have hheadw : e.head = w := by
        rcases hneigh e.head (by simpa [htail] using e.adj) with hw | hu'
        · exact hw
        · exact False.elim (hheadu hu')
      have hmap :
          subdivisionExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.newEdge := by
        simp [subdivisionExtToFun, htail, hheadu]
      rw [hmap]
      change OrientedEdge.tail (⟨(v, u), hvu⟩ : OrientedEdge G) = e.tail
      exact htail.symm
  · rcases
      subdivisionExtToFun_old_of_tail_ne
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh e htail with
      ⟨q, hmap, hqtail⟩
    rw [hmap]
    change
      (oldDartToOriginal
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh (R.node q)).tail = e.tail
    refine oldDartToOriginal_tail_of_tail_eq_map
      (G := G) (v := v) (w := w) (u := u) (a := e.tail)
      hvw hvu hu hneigh htail ?_
    calc
      (R.node q).tail = q.tail := R.node_tail q
      _ = C.map e.tail := hqtail

theorem subdivisionExt_nodeReachable_of_tail_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    {e f : OrientedEdge G}
    (hef : e.tail = f.tail) :
    PermReachable (EdgeSubdivision.node R.toHypermap)
      (subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu e)
      (subdivisionExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu f) := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let N := EdgeSubdivision.node R.toHypermap
  by_cases htail : e.tail = v
  · have hftail : f.tail = v := hef.symm.trans htail
    have he_to_new :
        PermReachable N
          (subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e)
          ExtDart.new := by
      by_cases hheadu : e.head = u
      · have hmap :
            subdivisionExtToFun
                (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
              ExtDart.new := by
          simp [subdivisionExtToFun, htail, hheadu]
        rw [hmap]
        exact PermReachable.refl N ExtDart.new
      · have hmap :
            subdivisionExtToFun
                (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
              ExtDart.newEdge := by
          simp [subdivisionExtToFun, htail, hheadu]
        rw [hmap]
        simpa [N, EdgeSubdivision.node] using
          (PermReachable.forward N ExtDart.newEdge)
    have hnew_to_f :
        PermReachable N ExtDart.new
          (subdivisionExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu f) := by
      by_cases hheadu : f.head = u
      · have hmap :
            subdivisionExtToFun
                (G := G) (v := v) (w := w) (u := u) hvw hvu hu f =
              ExtDart.new := by
          simp [subdivisionExtToFun, hftail, hheadu]
        rw [hmap]
        exact PermReachable.refl N ExtDart.new
      · have hmap :
            subdivisionExtToFun
                (G := G) (v := v) (w := w) (u := u) hvw hvu hu f =
              ExtDart.newEdge := by
          simp [subdivisionExtToFun, hftail, hheadu]
        rw [hmap]
        simpa [N, EdgeSubdivision.node] using
          (PermReachable.forward N ExtDart.new)
    exact PermReachable.trans N he_to_new hnew_to_f
  · have hftail_ne : f.tail ≠ v := by
      intro hf
      exact htail (hef.trans hf)
    rcases
      subdivisionExtToFun_old_of_tail_ne
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh e htail with
      ⟨qe, hemap, hqetail⟩
    rcases
      subdivisionExtToFun_old_of_tail_ne
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh f hftail_ne with
      ⟨qf, hfmap, hqftail⟩
    rw [hemap, hfmap]
    refine EdgeSubdivision.old_nodeReachable_of_nodeReachable
      R.toHypermap
      (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
      R.toHypermap_plain ?_
    exact R.node_orbit_of_same_tail qe qf (by
      calc
        qe.tail = C.map e.tail := hqetail
        _ = C.map f.tail := by rw [hef]
        _ = qf.tail := hqftail.symm)

/-- Pull back the pure edge-subdivision node across the checked dart
equivalence in the non-adjacent degree-two case. -/
noncomputable def nonAdjacentSubdivisionRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    RotationSystem G :=
  let E := orientedEdgeEquiv
    (G := G) (v := v) (w := w) (u := u)
    hvw hvu hu hneigh hnonadj
  let N := EdgeSubdivision.node R.toHypermap
  RotationSystem.pullbackDartEquiv E N
    (by
      intro e
      exact subdivisionExt_node_tail
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh R e)
    (by
      intro e f hef
      exact subdivisionExt_nodeReachable_of_tail_eq
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh R hef)

@[simp]
theorem nonAdjacentSubdivisionRotationSystem_node_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) :
    (orientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj)
      ((nonAdjacentSubdivisionRotationSystem
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj R).node e) =
    EdgeSubdivision.node R.toHypermap
      ((orientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj) e) := by
  simp [nonAdjacentSubdivisionRotationSystem]
  rfl

theorem edgeSubdivision_edge_symm_eq_edge
    (G : Hypermap) (z : G.Dart) (hplain : G.Plain)
    (x : ExtDart G.Dart) :
    (EdgeSubdivision.edge G z hplain).symm x =
      EdgeSubdivision.edge G z hplain x :=
  rfl

/-- The hypermap of the transported non-adjacent subdivision rotation system
is isomorphic to the pure edge-subdivision hypermap of the contracted graph. -/
noncomputable def nonAdjacentSubdivisionRotationSystem_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    Hypermap.Iso
      ((nonAdjacentSubdivisionRotationSystem
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj R).toHypermap)
      (EdgeSubdivision.hypermap R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        R.toHypermap_plain) := by
  let E := orientedEdgeEquiv
    (G := G) (v := v) (w := w) (u := u)
    hvw hvu hu hneigh hnonadj
  let z := splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  let H := EdgeSubdivision.hypermap R.toHypermap z R.toHypermap_plain
  exact RotationSystem.pullbackDartEquivToHypermapIso H E
    (EdgeSubdivision.hypermap_plain R.toHypermap z R.toHypermap_plain)
    (by
      intro e
      exact subdivisionExt_node_tail
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh R e)
    (by
      intro e f hef
      exact subdivisionExt_nodeReachable_of_tail_eq
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh R hef)
    (by
      intro e
      exact orientedEdgeEquiv_edge
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hnonadj R e)

theorem nonAdjacentSubdivisionRotationSystem_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hnonadj : ¬ G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (hR : (R.toHypermap).dual.EulerPlanar) :
    ((nonAdjacentSubdivisionRotationSystem
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hnonadj R).toHypermap).dual.EulerPlanar := by
  let S :=
    nonAdjacentSubdivisionRotationSystem
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hnonadj R
  let z : OrientedEdge (GraphContraction.collapseEdge G hvw).graph :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  have hold : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hsub :
      (EdgeSubdivision.hypermap R.toHypermap z R.toHypermap_plain).EulerPlanar :=
    (EdgeSubdivision.eulerPlanar_iff R.toHypermap z R.toHypermap_plain).mpr hold
  have hsource : S.toHypermap.EulerPlanar := by
      let φ :=
        nonAdjacentSubdivisionRotationSystem_toHypermapIso
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hnonadj R
      exact (φ.eulerPlanar_iff).mpr hsub
  exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hsource

end DegreeTwoSubdivision

end FourColor

end Schematic.Math.GraphTheory
