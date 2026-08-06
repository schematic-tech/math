import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.DegreeTwoSubdivision.Foundations
import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.TriangleExtension

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace DegreeTwoSubdivision

/-- In the adjacent degree-two case, every quotient dart of `G / vw` has an
old interpretation in `G`: the collapsed vertex is read as `w`, and the
distinguished quotient edge `none -- u` is backed by the old edge `w -- u`. -/
theorem oldDart_adj_of_adjacent
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph} :
    G.Adj
      (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail)
      (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head) := by
  classical
  apply collapsedVertexToOriginal_adj_of_endpoint_lift hvw
      (fun _ => G.Adj v u ∧ u ∉ ({v, w} : Set V)) ?_ ⟨hvu, hu⟩ ⟨hvu, hu⟩
  intro d _ x hx htail hhead
  have hadjC :
      (GraphContraction.collapseEdge G hvw).graph.Adj
        (none : (GraphContraction.collapseEdge G hvw).Target)
        (GraphContraction.collapseEdgeOutside G hvw x hx) := by
    simpa [htail, hhead] using d.adj
  rcases
      (GraphContraction.collapseEdge_adj_none_outside_iff
        (G := G) hvw hx).mp hadjC with
    hvx | hwx
  · rcases hneigh x hvx with hxw | hxu
    · exact False.elim (hx (by simp [hxw]))
    · simpa [hxu] using hadj
  · exact hwx

/-- Interpret quotient darts as old darts of the original graph in the adjacent
degree-two triangle case. -/
noncomputable def oldDartToOriginalAdjacent
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :
    OrientedEdge G :=
  ⟨(collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail,
    collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head),
    oldDart_adj_of_adjacent
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hadj⟩

@[simp]
theorem oldDartToOriginalAdjacent_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :
    (oldDartToOriginalAdjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e).tail =
      collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail :=
  rfl

@[simp]
theorem oldDartToOriginalAdjacent_head
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :
    (oldDartToOriginalAdjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e).head =
      collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head :=
  rfl

theorem oldDartToOriginalAdjacent_tail_of_tail_eq_map
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u a : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (ha : a ≠ v)
    (htail : e.tail = (GraphContraction.collapseEdge G hvw).map a) :
    (oldDartToOriginalAdjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e).tail = a := by
  change collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail = a
  rw [htail]
  exact collapsedVertexToOriginal_map_of_ne
    (G := G) (v := v) (w := w) hvw ha

theorem oldDartToOriginalAdjacent_head_of_head_eq_map
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u a : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    {e : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (ha : a ≠ v)
    (hhead : e.head = (GraphContraction.collapseEdge G hvw).map a) :
    (oldDartToOriginalAdjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e).head = a := by
  change collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.head = a
  rw [hhead]
  exact collapsedVertexToOriginal_map_of_ne
    (G := G) (v := v) (w := w) hvw ha

/-- Inverse map from the pure triangle-extension dart type to original
oriented edges in the adjacent degree-two case. -/
noncomputable def triangleExtInvFun
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u) :
    TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) ->
      OrientedEdge G
  | ExtDart.new => ⟨(w, v), hvw.symm⟩
  | ExtDart.newEdge => ⟨(v, w), hvw⟩
  | ExtDart.old ExtDart.new => ⟨(v, u), hvu⟩
  | ExtDart.old ExtDart.newEdge => ⟨(u, v), hvu.symm⟩
  | ExtDart.old (ExtDart.old e) =>
      oldDartToOriginalAdjacent
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e

/-- Forward map from original oriented edges to the pure triangle-extension
dart type in the adjacent degree-two case. -/
noncomputable def triangleExtToFun
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (_hvu : G.Adj v u)
    (_hu : u ∉ ({v, w} : Set V))
    (e : OrientedEdge G) :
    TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) :=
  if htail : e.tail = v then
    if e.head = u then ExtDart.old ExtDart.new else ExtDart.newEdge
  else if hhead : e.head = v then
    if e.tail = u then ExtDart.old ExtDart.newEdge else ExtDart.new
  else
    TriangleExtension.old
      (quotientDartOfOriginalOld
        (G := G) (v := v) (w := w) hvw e htail hhead)

@[simp]
theorem triangleExtToFun_vu
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    triangleExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(v, u), hvu⟩ : OrientedEdge G) =
      ExtDart.old ExtDart.new := by
  simp [triangleExtToFun, OrientedEdge.tail, OrientedEdge.head]

@[simp]
theorem triangleExtToFun_vw
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    triangleExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(v, w), hvw⟩ : OrientedEdge G) =
      ExtDart.newEdge := by
  have hwu : w ≠ u := by
    intro h
    exact hu (by simp [h])
  simp [triangleExtToFun, OrientedEdge.tail, OrientedEdge.head, hwu]

@[simp]
theorem triangleExtToFun_uv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    triangleExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(u, v), hvu.symm⟩ : OrientedEdge G) =
      ExtDart.old ExtDart.newEdge := by
  have huv : u ≠ v := by
    intro h
    exact hu (by simp [h])
  simp [triangleExtToFun, OrientedEdge.tail, OrientedEdge.head, huv]

@[simp]
theorem triangleExtToFun_wv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V)) :
    triangleExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (⟨(w, v), hvw.symm⟩ : OrientedEdge G) =
      ExtDart.new := by
  have hwv : w ≠ v := hvw.ne'
  have hwu : w ≠ u := by
    intro h
    exact hu (by simp [h])
  simp [triangleExtToFun, OrientedEdge.tail, OrientedEdge.head, hwv, hwu]

theorem triangleExt_left_inv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (e : OrientedEdge G) :
    triangleExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj
        (triangleExtToFun
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu e) =
      e := by
  classical
  by_cases htail : e.tail = v
  · by_cases hheadu : e.head = u
    · have hmap :
          triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.old ExtDart.new := by
        simp [triangleExtToFun, htail, hheadu]
      rw [hmap]
      apply orientedEdge_eq_of_tail_head
      · exact htail.symm
      · exact hheadu.symm
    · have hheadw : e.head = w := by
        rcases hneigh e.head (by simpa [htail] using e.adj) with hw | hu'
        · exact hw
        · exact False.elim (hheadu hu')
      have hmap :
          triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            ExtDart.newEdge := by
        simp [triangleExtToFun, htail, hheadu]
      rw [hmap]
      apply orientedEdge_eq_of_tail_head
      · exact htail.symm
      · exact hheadw.symm
  · by_cases hhead : e.head = v
    · by_cases htailu : e.tail = u
      · have hmap :
            triangleExtToFun
                (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
              ExtDart.old ExtDart.newEdge := by
          have huv : u ≠ v := by
            intro h
            exact hu (by simp [h])
          simp [triangleExtToFun, hhead, htailu, huv]
        rw [hmap]
        apply orientedEdge_eq_of_tail_head
        · exact htailu.symm
        · exact hhead.symm
      · have htailw : e.tail = w := by
          rcases hneigh e.tail (by simpa [hhead] using e.adj.symm) with hw | hu'
          · exact hw
          · exact False.elim (htailu hu')
        have hmap :
            triangleExtToFun
                (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
              ExtDart.new := by
          simp [triangleExtToFun, htail, hhead, htailu]
        rw [hmap]
        apply orientedEdge_eq_of_tail_head
        · exact htailw.symm
        · exact hhead.symm
    · let q :=
        quotientDartOfOriginalOld
          (G := G) (v := v) (w := w) hvw e htail hhead
      have hmap :
          triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
            TriangleExtension.old q := by
        simp [triangleExtToFun, htail, hhead, q, TriangleExtension.old]
      rw [hmap]
      change oldDartToOriginalAdjacent
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hadj q = e
      apply orientedEdge_eq_of_tail_head
      · refine oldDartToOriginalAdjacent_tail_of_tail_eq_map
          (G := G) (v := v) (w := w) (u := u) (a := e.tail)
          hvw hvu hu hneigh hadj htail ?_
        change
          (quotientDartOfOriginalOld
            (G := G) (v := v) (w := w) hvw e htail hhead).tail =
          (GraphContraction.collapseEdge G hvw).map e.tail
        rw [quotientDartOfOriginalOld_tail]
      · refine oldDartToOriginalAdjacent_head_of_head_eq_map
          (G := G) (v := v) (w := w) (u := u) (a := e.head)
          hvw hvu hu hneigh hadj hhead ?_
        change
          (quotientDartOfOriginalOld
            (G := G) (v := v) (w := w) hvw e htail hhead).head =
          (GraphContraction.collapseEdge G hvw).map e.head
        rw [quotientDartOfOriginalOld_head]

theorem triangleExt_right_inv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (x : TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)) :
    triangleExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu
        (triangleExtInvFun
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hadj x) =
      x := by
  classical
  cases x with
  | new =>
      simp [triangleExtInvFun, triangleExtToFun_wv]
  | newEdge =>
      simp [triangleExtInvFun, triangleExtToFun_vw]
  | old x =>
      cases x with
      | new =>
          simp [triangleExtInvFun, triangleExtToFun_vu]
      | newEdge =>
          simp [triangleExtInvFun, triangleExtToFun_uv]
      | old e =>
          let o : OrientedEdge G :=
            oldDartToOriginalAdjacent
              (G := G) (v := v) (w := w) (u := u)
              hvw hvu hu hneigh hadj e
          have hotail_ne : o.tail ≠ v := by
            rw [oldDartToOriginalAdjacent_tail]
            exact collapsedVertexToOriginal_ne_left
              (G := G) (v := v) (w := w) hvw e.tail
          have hohead_ne : o.head ≠ v := by
            rw [oldDartToOriginalAdjacent_head]
            exact collapsedVertexToOriginal_ne_left
              (G := G) (v := v) (w := w) hvw e.head
          have hmap :
              triangleExtToFun
                  (G := G) (v := v) (w := w) (u := u) hvw hvu hu o =
                TriangleExtension.old
                  (quotientDartOfOriginalOld
                    (G := G) (v := v) (w := w) hvw o hotail_ne hohead_ne) := by
            simp [triangleExtToFun, hotail_ne, hohead_ne, TriangleExtension.old]
          change triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu o =
            TriangleExtension.old e
          rw [hmap]
          congr
          apply orientedEdge_eq_of_tail_head
          · rw [quotientDartOfOriginalOld_tail]
            rw [oldDartToOriginalAdjacent_tail]
            exact (collapseEdge_map_collapsedVertexToOriginal
              (G := G) (v := v) (w := w) hvw e.tail)
          · rw [quotientDartOfOriginalOld_head]
            rw [oldDartToOriginalAdjacent_head]
            exact (collapseEdge_map_collapsedVertexToOriginal
              (G := G) (v := v) (w := w) hvw e.head)

/-- Oriented-edge equivalence for the adjacent degree-two triangle case. -/
noncomputable def triangleOrientedEdgeEquiv
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u) :
    OrientedEdge G ≃
      TriangleExtension.Dart
        (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) where
  toFun :=
    triangleExtToFun (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  invFun :=
    triangleExtInvFun
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh hadj
  left_inv :=
    triangleExt_left_inv
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh hadj
  right_inv :=
    triangleExt_right_inv
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh hadj

@[simp]
theorem triangleOrientedEdgeEquiv_apply
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (e : OrientedEdge G) :
    triangleOrientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e =
      triangleExtToFun
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu e :=
  rfl

@[simp]
theorem triangleOrientedEdgeEquiv_symm_apply
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (x : TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)) :
    (triangleOrientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj).symm x =
      triangleExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj x :=
  rfl

private theorem triangleOrientedEdgeEquiv_edge_of_head_ne
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) (hhead : e.head ≠ v) :
    triangleOrientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e.symm =
      TriangleExtension.edge R.toHypermap
        ((triangleOrientedEdgeEquiv
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hadj) e) := by
  classical
  by_cases htail : e.tail = v
  · by_cases hheadu : e.head = u
    · have he : e = (⟨(v, u), hvu⟩ : OrientedEdge G) :=
        orientedEdge_eq_of_tail_head htail hheadu
      subst e
      simp only [triangleOrientedEdgeEquiv_apply]
      change
        triangleExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu
            (⟨(u, v), hvu.symm⟩ : OrientedEdge G) =
          TriangleExtension.edge R.toHypermap
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu
              (⟨(v, u), hvu⟩ : OrientedEdge G))
      rw [triangleExtToFun_uv
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu,
        triangleExtToFun_vu
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu]
      rfl
    · have hheadw : e.head = w := by
        rcases hneigh e.head (by simpa [htail] using e.adj) with hw | hu'
        · exact hw
        · exact False.elim (hheadu hu')
      have he : e = (⟨(v, w), hvw⟩ : OrientedEdge G) :=
        orientedEdge_eq_of_tail_head htail hheadw
      subst e
      simp only [triangleOrientedEdgeEquiv_apply]
      change
        triangleExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu
            (⟨(w, v), hvw.symm⟩ : OrientedEdge G) =
          TriangleExtension.edge R.toHypermap
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu
              (⟨(v, w), hvw⟩ : OrientedEdge G))
      rw [triangleExtToFun_wv
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu,
        triangleExtToFun_vw
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu]
      rfl
  · let q :=
        quotientDartOfOriginalOld
          (G := G) (v := v) (w := w) hvw e htail hhead
    have htail_symm : e.symm.tail ≠ v := by
      simpa using hhead
    have hhead_symm : e.symm.head ≠ v := by
      simpa using htail
    have hmap :
        triangleExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e =
          TriangleExtension.old q := by
      simp [triangleExtToFun, htail, hhead, q, TriangleExtension.old]
    have hmap_symm :
        triangleExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e.symm =
          TriangleExtension.old q.symm := by
      simp [triangleExtToFun, htail, hhead, q,
        quotientDartOfOriginalOld_symm, TriangleExtension.old]
    rw [triangleOrientedEdgeEquiv_apply,
      triangleOrientedEdgeEquiv_apply, hmap, hmap_symm]
    change TriangleExtension.old (R.toHypermap.edge q) =
      TriangleExtension.edge R.toHypermap (TriangleExtension.old q)
    rfl

theorem triangleOrientedEdgeEquiv_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) :
    triangleOrientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj e.symm =
      TriangleExtension.edge R.toHypermap
        ((triangleOrientedEdgeEquiv
          (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu hneigh hadj) e) := by
  classical
  by_cases hhead : e.head = v
  · have htail : e.tail ≠ v := by
      intro h
      exact e.adj.ne (h.trans hhead.symm)
    have hreverse := triangleOrientedEdgeEquiv_edge_of_head_ne
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hadj R e.symm (by simpa using htail)
    exact (TriangleExtension.edge_involutive R.toHypermap
      R.toHypermap_plain).eq_iff.mp (by simpa using hreverse.symm)
  · exact triangleOrientedEdgeEquiv_edge_of_head_ne
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hadj R e hhead

theorem triangle_split_edge_ne
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    R.toHypermap.edge
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu) ≠
      splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu :=
  (R.toHypermap_plain
    (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)).2

theorem triangle_split_node_ne_edge
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    R.toHypermap.node
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu) ≠
      R.toHypermap.edge
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu) := by
  intro h
  let C := GraphContraction.collapseEdge G hvw
  let z : OrientedEdge C.graph :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  have hz_eq : R.toHypermap.node z = R.toHypermap.edge z := by
    simpa [z] using h
  have htail :
      (R.toHypermap.node z).tail = (R.toHypermap.edge z).tail :=
    congrArg (fun e : OrientedEdge C.graph => e.tail) hz_eq
  have hnode_tail : (R.toHypermap.node z).tail =
      (none : C.Target) := by
    change (R.node z).tail = z.tail
    rw [R.node_tail z]
  have hedge_tail : (R.toHypermap.edge z).tail =
      GraphContraction.collapseEdgeOutside G hvw u hu := by
    rfl
  rw [hnode_tail, hedge_tail] at htail
  exact collapseEdgeOutside_ne_none (G := G) hvw hu htail.symm

theorem rotationSystem_node_symm_tail
    {V : Type u} {G : SimpleGraph V}
    (R : RotationSystem G) (e : OrientedEdge G) :
    (R.node.symm e).tail = e.tail := by
  have h := R.node_tail (R.node.symm e)
  simpa using h.symm

/-- The original-graph tail represented by a pure triangle-extension dart in
the adjacent degree-two uncontraction case. -/
noncomputable def triangleExtTail
    {V : Type u}
    {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w) :
    TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph) -> V
  | ExtDart.new => w
  | ExtDart.newEdge => v
  | ExtDart.old ExtDart.new => v
  | ExtDart.old ExtDart.newEdge => u
  | ExtDart.old (ExtDart.old e) =>
      collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw e.tail

@[simp]
theorem triangleExtInvFun_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (x : TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)) :
    (triangleExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj x).tail =
      triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw x := by
  cases x with
  | new => rfl
  | newEdge => rfl
  | old x =>
      cases x <;> rfl

theorem triangleExtToFun_tail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (e : OrientedEdge G) :
    triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
        (triangleExtToFun
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu e) =
      e.tail := by
  classical
  by_cases htail : e.tail = v
  · by_cases hheadu : e.head = u
    · simp [triangleExtToFun, triangleExtTail, htail, hheadu]
    · simp [triangleExtToFun, triangleExtTail, htail, hheadu]
  · by_cases hhead : e.head = v
    · by_cases htailu : e.tail = u
      · have huv : u ≠ v := by
          intro h
          exact hu (by simp [h])
        simp [triangleExtToFun, triangleExtTail, hhead, htailu, huv]
      · have htailw : e.tail = w := by
          rcases hneigh e.tail (by simpa [hhead] using e.adj.symm) with hw | hu'
          · exact hw
          · exact False.elim (htailu hu')
        have hwv : w ≠ v := hvw.ne'
        have hwu : w ≠ u := by
          intro h
          exact hu (by simp [h])
        simp [triangleExtToFun, triangleExtTail, hhead, htailw, hwv, hwu]
    · simp [triangleExtToFun, triangleExtTail, htail, hhead]
      exact collapsedVertexToOriginal_map_of_ne
        (G := G) (v := v) (w := w) hvw htail

theorem triangleExtNode_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (x : TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)) :
    triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
        (TriangleExtension.node R.toHypermap
          (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
          (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu R)
          (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu R)
          x) =
      triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw x := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let z : OrientedEdge C.graph :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  let hedge_ne :=
    triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu R
  let hnode_ne :=
    triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu R
  cases x with
  | new =>
      change
        collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
            (R.node z).tail = w
      rw [R.node_tail z]
      rfl
  | newEdge =>
      rfl
  | old x =>
      cases x with
      | new =>
          rfl
      | newEdge =>
          change
            collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
                (R.toHypermap.edge z).tail = u
          rfl
      | old q =>
          change
            triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
                (if q = z then ExtDart.new
                 else if q = R.toHypermap.node.symm (R.toHypermap.edge z) then
                   ExtDart.old ExtDart.newEdge
                 else TriangleExtension.old (R.toHypermap.node q)) =
              collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw q.tail
          by_cases hqz : q = z
          · subst q
            rw [if_pos rfl]
            change w =
              collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw z.tail
            rw [show z.tail = (none : C.Target) by rfl]
            rfl
          · by_cases hqspecial :
                q = R.toHypermap.node.symm (R.toHypermap.edge z)
            · subst q
              have htail :
                  (R.toHypermap.node.symm (R.toHypermap.edge z)).tail =
                    (R.toHypermap.edge z).tail :=
                rotationSystem_node_symm_tail R (R.toHypermap.edge z)
              rw [if_neg hqz, if_pos rfl]
              change u =
                collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
                  (R.toHypermap.node.symm (R.toHypermap.edge z)).tail
              rw [htail]
              rfl
            · have htail : (R.toHypermap.node q).tail = q.tail :=
                R.node_tail q
              rw [if_neg hqz, if_neg hqspecial]
              change
                collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
                    (R.toHypermap.node q).tail =
                  collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw
                    q.tail
              rw [htail]

theorem triangleExt_node_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) :
    (triangleExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj
        (TriangleExtension.node R.toHypermap
          (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
          (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu R)
          (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu R)
          (triangleExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e))).tail =
      e.tail := by
  calc
    (triangleExtInvFun
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj
        (TriangleExtension.node R.toHypermap
          (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
          (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu R)
          (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
            hvw hvu hu R)
          (triangleExtToFun
            (G := G) (v := v) (w := w) (u := u) hvw hvu hu e))).tail =
        triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
          (TriangleExtension.node R.toHypermap
            (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
            (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
              hvw hvu hu R)
            (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
              hvw hvu hu R)
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e)) := by
      rw [triangleExtInvFun_tail]
    _ = triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
        (triangleExtToFun
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu e) :=
      triangleExtNode_tail
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu R _
    _ = e.tail :=
      triangleExtToFun_tail
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh e

theorem triangleExt_old_reachable_old_of_tail_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    {p q : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (hpq : p.tail = q.tail) :
    PermReachable
      (TriangleExtension.node R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)
        (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R))
      (TriangleExtension.old p) (TriangleExtension.old q) := by
  exact
    TriangleExtension.old_nodeReachable_of_nodeReachable
      R.toHypermap
      (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
      (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (R.node_orbit_of_same_tail p q hpq)

theorem triangleExt_old_reachable_new_of_tail_w
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    {q : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (hq : collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw q.tail = w) :
    PermReachable
      (TriangleExtension.node R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)
        (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R))
      (TriangleExtension.old q) ExtDart.new := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let z : OrientedEdge C.graph :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  let N :=
    TriangleExtension.node R.toHypermap z
      (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
  have htail : q.tail = z.tail := by
    calc
      q.tail =
          C.map (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw q.tail) :=
        (collapseEdge_map_collapsedVertexToOriginal
          (G := G) (v := v) (w := w) hvw q.tail).symm
      _ = C.map w := by rw [hq]
      _ = z.tail := by
        simp [C, z, GraphContraction.collapseEdge,
          GraphContraction.collapseSubgraph, GraphContraction.ofMap]
        rfl
  have hqz :
      PermReachable N (TriangleExtension.old q) (TriangleExtension.old z) :=
    triangleExt_old_reachable_old_of_tail_eq
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu R htail
  have hznew :
      PermReachable N (TriangleExtension.old z) ExtDart.new := by
    have h := PermReachable.forward N (TriangleExtension.old z)
    change PermReachable N (TriangleExtension.old z)
      (TriangleExtension.nodeToFun R.toHypermap z (TriangleExtension.old z)) at h
    simpa [TriangleExtension.nodeToFun, TriangleExtension.old] using h
  exact PermReachable.trans N hqz hznew

theorem triangleExt_old_reachable_oldNewEdge_of_tail_u
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    {q : OrientedEdge (GraphContraction.collapseEdge G hvw).graph}
    (hq : collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw q.tail = u) :
    PermReachable
      (TriangleExtension.node R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)
        (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R))
      (TriangleExtension.old q) (ExtDart.old ExtDart.newEdge) := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let z : OrientedEdge C.graph :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  let N :=
    TriangleExtension.node R.toHypermap z
      (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
  have htail : q.tail = (R.toHypermap.edge z).tail := by
    calc
      q.tail =
          C.map (collapsedVertexToOriginal (G := G) (v := v) (w := w) hvw q.tail) :=
        (collapseEdge_map_collapsedVertexToOriginal
          (G := G) (v := v) (w := w) hvw q.tail).symm
      _ = C.map u := by rw [hq]
      _ = (R.toHypermap.edge z).tail := by
        change C.map u = z.head
        simp [C, z, GraphContraction.collapseEdge,
          GraphContraction.collapseSubgraph, GraphContraction.ofMap, hu]
        rfl
  have hqedge :
      PermReachable N (TriangleExtension.old q)
        (TriangleExtension.old (R.toHypermap.edge z)) :=
    triangleExt_old_reachable_old_of_tail_eq
      (G := G) (v := v) (w := w) (u := u) hvw hvu hu R htail
  have hnewEdge_edge :
      PermReachable N (ExtDart.old ExtDart.newEdge)
        (TriangleExtension.old (R.toHypermap.edge z)) := by
    have h := PermReachable.forward N (ExtDart.old ExtDart.newEdge)
    change PermReachable N (ExtDart.old ExtDart.newEdge)
      (TriangleExtension.nodeToFun R.toHypermap z
        (ExtDart.old ExtDart.newEdge)) at h
    simpa [TriangleExtension.nodeToFun, TriangleExtension.old] using h
  exact PermReachable.trans N hqedge
    (PermReachable.symm N hnewEdge_edge)

theorem triangleExtNodeReachable_of_tail_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    {x y : TriangleExtension.Dart
      (OrientedEdge (GraphContraction.collapseEdge G hvw).graph)}
    (hxy :
      triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw x =
        triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw y) :
    PermReachable
      (TriangleExtension.node R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)
        (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R))
      x y := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let N :=
    TriangleExtension.node R.toHypermap
      (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
      (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
  have huv : u ≠ v := by
    intro h
    exact hu (by simp [h])
  have hvu_ne : v ≠ u := by
    intro h
    exact huv h.symm
  have hwu : w ≠ u := by
    intro h
    exact hu (by simp [h])
  have huw : u ≠ w := by
    intro h
    exact hwu h.symm
  cases x with
  | new =>
      cases y with
      | new =>
          exact PermReachable.refl N ExtDart.new
      | newEdge =>
          exact False.elim (hvw.ne' hxy)
      | old y =>
          cases y with
          | new =>
              exact False.elim (hvw.ne' hxy)
          | newEdge =>
              exact False.elim (hwu hxy)
          | old q =>
              exact PermReachable.symm N
                (triangleExt_old_reachable_new_of_tail_w
                  (G := G) (v := v) (w := w) (u := u)
                  hvw hvu hu R hxy.symm)
  | newEdge =>
      cases y with
      | new =>
          exact False.elim (hvw.ne hxy)
      | newEdge =>
          exact PermReachable.refl N ExtDart.newEdge
      | old y =>
          cases y with
          | new =>
              simpa [N] using
                (PermReachable.forward N ExtDart.newEdge)
          | newEdge =>
              exact False.elim (hvu_ne hxy)
          | old q =>
              exact False.elim
                ((collapsedVertexToOriginal_ne_left
                  (G := G) (v := v) (w := w) hvw q.tail) hxy.symm)
  | old x =>
      cases x with
      | new =>
          cases y with
          | new =>
              exact False.elim (hvw.ne hxy)
          | newEdge =>
              simpa [N] using
                (PermReachable.forward N (ExtDart.old ExtDart.new))
          | old y =>
              cases y with
              | new =>
                  exact PermReachable.refl N (ExtDart.old ExtDart.new)
              | newEdge =>
                  exact False.elim (hvu_ne hxy)
              | old q =>
                  exact False.elim
                    ((collapsedVertexToOriginal_ne_left
                      (G := G) (v := v) (w := w) hvw q.tail) hxy.symm)
      | newEdge =>
          cases y with
          | new =>
              exact False.elim (huw hxy)
          | newEdge =>
              exact False.elim (huv hxy)
          | old y =>
              cases y with
              | new =>
                  exact False.elim (huv hxy)
              | newEdge =>
                  exact PermReachable.refl N (ExtDart.old ExtDart.newEdge)
              | old q =>
                  exact PermReachable.symm N
                    (triangleExt_old_reachable_oldNewEdge_of_tail_u
                      (G := G) (v := v) (w := w) (u := u)
                      hvw hvu hu R hxy.symm)
      | old p =>
          cases y with
          | new =>
              exact triangleExt_old_reachable_new_of_tail_w
                (G := G) (v := v) (w := w) (u := u)
                hvw hvu hu R hxy
          | newEdge =>
              exact False.elim
                ((collapsedVertexToOriginal_ne_left
                  (G := G) (v := v) (w := w) hvw p.tail) hxy)
          | old y =>
              cases y with
              | new =>
                  exact False.elim
                    ((collapsedVertexToOriginal_ne_left
                      (G := G) (v := v) (w := w) hvw p.tail) hxy)
              | newEdge =>
                  exact triangleExt_old_reachable_oldNewEdge_of_tail_u
                    (G := G) (v := v) (w := w) (u := u)
                    hvw hvu hu R hxy
              | old q =>
                  have htail_eq :
                      collapsedVertexToOriginal
                          (G := G) (v := v) (w := w) hvw p.tail =
                        collapsedVertexToOriginal
                          (G := G) (v := v) (w := w) hvw q.tail := by
                    simpa [triangleExtTail, TriangleExtension.old] using hxy
                  have hpq : p.tail = q.tail := by
                    calc
                      p.tail =
                          C.map (collapsedVertexToOriginal
                            (G := G) (v := v) (w := w) hvw p.tail) :=
                        (collapseEdge_map_collapsedVertexToOriginal
                          (G := G) (v := v) (w := w) hvw p.tail).symm
                      _ = C.map (collapsedVertexToOriginal
                            (G := G) (v := v) (w := w) hvw q.tail) := by
                        rw [htail_eq]
                      _ = q.tail :=
                        collapseEdge_map_collapsedVertexToOriginal
                          (G := G) (v := v) (w := w) hvw q.tail
                  exact triangleExt_old_reachable_old_of_tail_eq
                    (G := G) (v := v) (w := w) (u := u)
                    hvw hvu hu R hpq

/-- Pull back the pure triangle-expansion node across the adjacent
degree-two dart equivalence. -/
noncomputable def adjacentTriangleRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    RotationSystem G :=
  let E := triangleOrientedEdgeEquiv
    (G := G) (v := v) (w := w) (u := u)
    hvw hvu hu hneigh hadj
  let z := splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  let N := TriangleExtension.node R.toHypermap z
    (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu R)
    (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu R)
  RotationSystem.pullbackDartEquiv E N
    (by
      intro e
      exact triangleExt_node_tail
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R e)
    (by
      intro e f hef
      apply triangleExtNodeReachable_of_tail_eq
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu R
      change
        triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e) =
          triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu f)
      rw [triangleExtToFun_tail
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh e,
        triangleExtToFun_tail
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh f,
        hef])

@[simp]
theorem adjacentTriangleRotationSystem_node_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (e : OrientedEdge G) :
    (triangleOrientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj)
      ((adjacentTriangleRotationSystem
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R).node e) =
    TriangleExtension.node R.toHypermap
      (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
      (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      ((triangleOrientedEdgeEquiv
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj) e) := by
  simp [adjacentTriangleRotationSystem]
  rfl

theorem triangleExtension_edge_symm_eq_edge
    (G : Hypermap) (hplain : G.Plain)
    (x : TriangleExtension.Dart G.Dart) :
    (TriangleExtension.edge G).symm x =
      TriangleExtension.edge G x := by
  apply (TriangleExtension.edge G).injective
  rw [(TriangleExtension.edge G).apply_symm_apply,
    TriangleExtension.edge_involutive G hplain x]

/-- The hypermap of the transported adjacent-triangle rotation system is
isomorphic to the pure triangle-expansion hypermap of the contracted graph. -/
noncomputable def adjacentTriangleRotationSystem_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph) :
    Hypermap.Iso
      ((adjacentTriangleRotationSystem
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R).toHypermap)
      (TriangleExtension.hypermap R.toHypermap
        (splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu)
        (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)
        (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)) := by
  let E := triangleOrientedEdgeEquiv
    (G := G) (v := v) (w := w) (u := u)
    hvw hvu hu hneigh hadj
  let z := splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  let hedge_ne := triangle_split_edge_ne
    (G := G) (v := v) (w := w) (u := u) hvw hvu hu R
  let hnode_ne := triangle_split_node_ne_edge
    (G := G) (v := v) (w := w) (u := u) hvw hvu hu R
  let H := TriangleExtension.hypermap R.toHypermap z hedge_ne hnode_ne
  exact RotationSystem.pullbackDartEquivToHypermapIso H E
    (TriangleExtension.hypermap_plain R.toHypermap z hedge_ne hnode_ne
      R.toHypermap_plain)
    (by
      intro e
      exact triangleExt_node_tail
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R e)
    (by
      intro e f hef
      apply triangleExtNodeReachable_of_tail_eq
        (G := G) (v := v) (w := w) (u := u) hvw hvu hu R
      change
        triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu e) =
          triangleExtTail (G := G) (v := v) (w := w) (u := u) hvw
            (triangleExtToFun
              (G := G) (v := v) (w := w) (u := u) hvw hvu hu f)
      rw [triangleExtToFun_tail
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh e,
        triangleExtToFun_tail
          (G := G) (v := v) (w := w) (u := u) hvw hvu hu hneigh f,
        hef])
    (by
      intro e
      exact triangleOrientedEdgeEquiv_edge
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R e)

theorem adjacentTriangleRotationSystem_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w u : V}
    (hvw : G.Adj v w)
    [DecidableRel (GraphContraction.collapseEdge G hvw).graph.Adj]
    (hvu : G.Adj v u)
    (hu : u ∉ ({v, w} : Set V))
    (hneigh : forall t : V, G.Adj v t -> t = w ∨ t = u)
    (hadj : G.Adj w u)
    (R : RotationSystem (GraphContraction.collapseEdge G hvw).graph)
    (hR : (R.toHypermap).dual.EulerPlanar) :
    ((adjacentTriangleRotationSystem
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hadj R).toHypermap).dual.EulerPlanar := by
  let S :=
    adjacentTriangleRotationSystem
      (G := G) (v := v) (w := w) (u := u)
      hvw hvu hu hneigh hadj R
  let z :=
    splitDart (G := G) (v := v) (w := w) (u := u) hvw hvu hu
  have hold : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have htri :
      (TriangleExtension.hypermap R.toHypermap z
        (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)
        (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
          hvw hvu hu R)).EulerPlanar :=
    (TriangleExtension.eulerPlanar_iff R.toHypermap z
      (triangle_split_edge_ne (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      (triangle_split_node_ne_edge (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu R)
      R.toHypermap_plain).mpr hold
  have hsource : S.toHypermap.EulerPlanar := by
    let φ :=
      adjacentTriangleRotationSystem_toHypermapIso
        (G := G) (v := v) (w := w) (u := u)
        hvw hvu hu hneigh hadj R
    exact (φ.eulerPlanar_iff).mpr htri
  exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hsource

end DegreeTwoSubdivision

end FourColor

end Schematic.Math.GraphTheory
