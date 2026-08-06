import Schematic.Math.GraphTheory.Contractions
import Schematic.Math.GraphTheory.Subdivisions
import Schematic.Math.GraphTheory.Embedding.RotationSystemDeletion


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem ContainsStrictSubdivision.deleteEdges_of_edge_avoids
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (hK : ContainsStrictSubdivision K G)
    (S : Set (Sym2 V))
    (havoid :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges -> e ∉ S) :
    ContainsStrictSubdivision K (G.deleteEdges S) := by
  classical
  exact hK.edgeRestrict (by
    intro x y hxy e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨(Classical.choice hK).edgePath hxy |>.edges_subset_edgeSet he,
      havoid hxy e he⟩)

theorem ContainsStrictSubdivision.deleteEdge_or_model_uses_edge
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    (hK : ContainsStrictSubdivision K G)
    (e : Sym2 V) :
    ContainsStrictSubdivision K (G.deleteEdges ({e} : Set (Sym2 V))) ∨
      Exists fun x : W =>
        Exists fun y : W =>
          Exists fun hxy : K.Adj x y =>
            e ∈ ((Classical.choice hK).edgePath hxy).edges := by
  classical
  by_cases havoid :
      forall {x y : W} (hxy : K.Adj x y),
        e ∉ ((Classical.choice hK).edgePath hxy).edges
  · left
    exact ContainsStrictSubdivision.deleteEdges_of_edge_avoids
      hK ({e} : Set (Sym2 V)) (by
      intro x y hxy e' he' heS
      simp at heS
      exact havoid hxy (by simpa [heS] using he'))
  · right
    push Not at havoid
    rcases havoid with ⟨x, y, hxy, he⟩
    exact ⟨x, y, hxy, he⟩

abbrev deleteEdgeEndsGraph
    {V : Type u}
    (G : SimpleGraph V)
    (x y : V) : SimpleGraph ({z : V | z ∉ ({x, y} : Set V)}) :=
  G.induce ({x, y} : Set V)ᶜ

/-- The two-end deletion `G - a - b` embeds in the one-edge deletion
`G - ab`: deleting only the edge `ab` does not remove any edge whose endpoints
both avoid `a` and `b`. -/
def deleteEdgeEndsGraphToDeletedGraphHom
    {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) (a b : V) :
    deleteEdgeEndsGraph G a b →g EdgeDeletion.deletedGraph G a b where
  toFun := fun x => x.1
  map_rel' := by
    intro x y hxy
    rw [EdgeDeletion.deletedGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨hxy, ?_⟩
    intro hbad
    simp only [Set.mem_singleton_iff] at hbad
    rw [Sym2.eq_iff] at hbad
    rcases hbad with hbad | hbad
    · exact x.2 (by simp [hbad.1])
    · exact x.2 (by simp [hbad.1])

/-- A homeomorphic theta found after deleting both endpoints is also present
after deleting only the edge between those endpoints.  This is the graph
inclusion used in the contraction face-boundary branch. -/
theorem ContainsHomeomorphicTheta.to_deletedGraph
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (h : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    ContainsHomeomorphicTheta (EdgeDeletion.deletedGraph G a b) :=
  ContainsHomeomorphicTheta.map
    (deleteEdgeEndsGraphToDeletedGraphHom G a b)
    (by
      intro x y hxy
      exact Subtype.ext hxy)
    h

/-- Contrapositive form of `ContainsHomeomorphicTheta.to_deletedGraph`. -/
theorem not_containsHomeomorphicTheta_deleteEdgeEndsGraph_of_deletedGraph
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hno : Not (ContainsHomeomorphicTheta (EdgeDeletion.deletedGraph G a b))) :
    Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) := by
  intro htheta
  exact hno (ContainsHomeomorphicTheta.to_deletedGraph htheta)

namespace EdgeDeletion

/-- The quotient map from the edge-deleted graph `G - ab` to the contraction
`G / ab`.  This is not injective: it identifies `a` and `b`, and is the
graph-side map used when comparing the deleted-edge embedding target with the
contracted drawing. -/
noncomputable def deletedGraphToCollapseEdgeHom
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    deletedGraph G a b →g (GraphContraction.collapseEdge G hab).graph where
  toFun v := (GraphContraction.collapseEdge G hab).map v
  map_rel' := by
    intro x y hxy
    have hdel := hxy
    rw [deletedGraph, SimpleGraph.deleteEdges_adj] at hdel
    have hnot : s(x, y) ≠ s(a, b) := by
      intro hbad
      exact hdel.2 (by simp [hbad])
    have hneq :
        (GraphContraction.collapseEdge G hab).map x ≠
          (GraphContraction.collapseEdge G hab).map y := by
      intro hsame
      rcases
          (GraphContraction.collapseEdge_map_eq_iff
            (G := G) hab (v := x) (w := y)).mp hsame with
        hpair | houtside
      · have hxpair : x = a ∨ x = b := by
          simpa using hpair.1
        have hypair : y = a ∨ y = b := by
          simpa using hpair.2
        rcases hxpair with rfl | rfl <;> rcases hypair with rfl | rfl
        · exact hdel.1.ne rfl
        · exact hnot rfl
        · exact hnot (by rw [Sym2.eq_swap])
        · exact hdel.1.ne rfl
      · exact hdel.1.ne houtside.1
    rcases (GraphContraction.collapseEdge G hab).map_adj hdel.1 with
      hsame | hadj
    · exact False.elim (hneq hsame)
    · exact hadj

@[simp]
theorem deletedGraphToCollapseEdgeHom_apply_left
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    deletedGraphToCollapseEdgeHom G hab a =
      (none : (GraphContraction.collapseEdge G hab).Target) := by
  classical
  change (GraphContraction.collapseEdge G hab).map a =
    (none : (GraphContraction.collapseEdge G hab).Target)
  unfold GraphContraction.collapseEdge GraphContraction.collapseSubgraph
    GraphContraction.ofMap
  simp

@[simp]
theorem deletedGraphToCollapseEdgeHom_apply_right
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    deletedGraphToCollapseEdgeHom G hab b =
      (none : (GraphContraction.collapseEdge G hab).Target) := by
  classical
  change (GraphContraction.collapseEdge G hab).map b =
    (none : (GraphContraction.collapseEdge G hab).Target)
  unfold GraphContraction.collapseEdge GraphContraction.collapseSubgraph
    GraphContraction.ofMap
  simp

/-- The quotient map `G - ab → G / ab` is onto. -/
theorem deletedGraphToCollapseEdgeHom_surjective
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    Function.Surjective (deletedGraphToCollapseEdgeHom G hab) := by
  intro y
  rcases (GraphContraction.collapseEdge G hab).surjective y with ⟨v, hv⟩
  exact ⟨v, hv⟩

/-- Every contraction edge has a representative edge in the one-edge deletion
`G - ab`.  Edges whose only representative would be `ab` become loops after
contraction, so they cannot occur in the simple quotient graph. -/
theorem deletedGraphToCollapseEdgeHom_edge_lift
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    {y z : (GraphContraction.collapseEdge G hab).Target}
    (hyz : (GraphContraction.collapseEdge G hab).graph.Adj y z) :
    Exists fun v : V =>
      Exists fun w : V =>
        deletedGraphToCollapseEdgeHom G hab v = y ∧
          deletedGraphToCollapseEdgeHom G hab w = z ∧
            (deletedGraph G a b).Adj v w := by
  classical
  let C := GraphContraction.collapseEdge G hab
  rcases C.edge_lift hyz with ⟨v, w, hv, hw, hvw⟩
  refine ⟨v, w, hv, hw, ?_⟩
  rw [deletedGraph, SimpleGraph.deleteEdges_adj]
  refine ⟨hvw, ?_⟩
  intro hbad
  simp only [Set.mem_singleton_iff] at hbad
  rw [Sym2.eq_iff] at hbad
  have hmap_eq : C.map v = C.map w := by
    rw [GraphContraction.collapseEdge_map_eq_iff (G := G) hab]
    rcases hbad with hbad | hbad
    · left
      exact ⟨by simp [hbad.1], by simp [hbad.2]⟩
    · left
      exact ⟨by simp [hbad.1], by simp [hbad.2]⟩
  exact hyz.ne (hv.symm.trans (hmap_eq.trans hw))

/-- The quotient map on oriented darts from `G - ab` to `G / ab`. -/
noncomputable def deletedGraphToCollapseEdgeDart
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b) :
    OrientedEdge (deletedGraph G a b) →
      OrientedEdge (GraphContraction.collapseEdge G hab).graph :=
  fun e =>
    ⟨(deletedGraphToCollapseEdgeHom G hab e.tail,
      deletedGraphToCollapseEdgeHom G hab e.head),
      (deletedGraphToCollapseEdgeHom G hab).map_rel e.adj⟩

@[simp]
theorem deletedGraphToCollapseEdgeDart_tail
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    (deletedGraphToCollapseEdgeDart G hab e).tail =
      deletedGraphToCollapseEdgeHom G hab e.tail :=
  rfl

@[simp]
theorem deletedGraphToCollapseEdgeDart_head
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    (deletedGraphToCollapseEdgeDart G hab e).head =
      deletedGraphToCollapseEdgeHom G hab e.head :=
  rfl

@[simp]
theorem deletedGraphToCollapseEdgeDart_symm
    {V : Type u}
    (G : SimpleGraph V) {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    deletedGraphToCollapseEdgeDart G hab e.symm =
      (deletedGraphToCollapseEdgeDart G hab e).symm := by
  rfl

/-- Every oriented dart of the contraction has a lifted oriented dart in
`G - ab`. -/
theorem deletedGraphToCollapseEdgeDart_surjective
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    Function.Surjective (deletedGraphToCollapseEdgeDart G hab) := by
  intro e
  rcases deletedGraphToCollapseEdgeHom_edge_lift
      (G := G) hab (y := e.tail) (z := e.head) e.adj with
    ⟨v, w, hv, hw, hvw⟩
  refine ⟨(⟨(v, w), hvw⟩ : OrientedEdge (deletedGraph G a b)), ?_⟩
  apply Subtype.ext
  exact Prod.ext hv hw

theorem deletedGraphToCollapseEdgeDart_tail_eq_none_iff
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    (deletedGraphToCollapseEdgeDart G hab e).tail =
        (none : (GraphContraction.collapseEdge G hab).Target) ↔
      e.tail = a ∨ e.tail = b := by
  classical
  let F := deletedGraphToCollapseEdgeHom G hab
  constructor
  · intro htail
    have hmap :
        F e.tail = F a := by
      simpa [F, deletedGraphToCollapseEdgeDart] using
        htail.trans (deletedGraphToCollapseEdgeHom_apply_left G hab).symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := e.tail) (w := a)).mp hmap with
      hpair | houtside
    · simpa using hpair.1
    · exact False.elim (houtside.2.2 (by simp))
  · rintro (htail | htail)
    · change deletedGraphToCollapseEdgeHom G hab e.tail =
        (none : (GraphContraction.collapseEdge G hab).Target)
      simp [htail, deletedGraphToCollapseEdgeHom_apply_left]
    · change deletedGraphToCollapseEdgeHom G hab e.tail =
        (none : (GraphContraction.collapseEdge G hab).Target)
      simp [htail, deletedGraphToCollapseEdgeHom_apply_right]

theorem deletedGraphToCollapseEdgeDart_head_eq_none_iff
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    (deletedGraphToCollapseEdgeDart G hab e).head =
        (none : (GraphContraction.collapseEdge G hab).Target) ↔
      e.head = a ∨ e.head = b := by
  classical
  let F := deletedGraphToCollapseEdgeHom G hab
  constructor
  · intro hhead
    have hmap :
        F e.head = F a := by
      simpa [F, deletedGraphToCollapseEdgeDart] using
        hhead.trans (deletedGraphToCollapseEdgeHom_apply_left G hab).symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := e.head) (w := a)).mp hmap with
      hpair | houtside
    · simpa using hpair.1
    · exact False.elim (houtside.2.2 (by simp))
  · rintro (hhead | hhead)
    · change deletedGraphToCollapseEdgeHom G hab e.head =
        (none : (GraphContraction.collapseEdge G hab).Target)
      simp [hhead, deletedGraphToCollapseEdgeHom_apply_left]
    · change deletedGraphToCollapseEdgeHom G hab e.head =
        (none : (GraphContraction.collapseEdge G hab).Target)
      simp [hhead, deletedGraphToCollapseEdgeHom_apply_right]

theorem deletedGraphToCollapseEdgeHom_eq_none_iff
    {V : Type u}
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b) :
    deletedGraphToCollapseEdgeHom G hab v =
        (none : (GraphContraction.collapseEdge G hab).Target) ↔
      v = a ∨ v = b := by
  classical
  let F := deletedGraphToCollapseEdgeHom G hab
  constructor
  · intro hv
    have hmap :
        F v = F a := by
      simpa [F] using
        hv.trans (deletedGraphToCollapseEdgeHom_apply_left G hab).symm
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := v) (w := a)).mp hmap with
      hpair | houtside
    · simpa using hpair.1
    · exact False.elim (houtside.2.2 (by simp))
  · rintro (rfl | rfl)
    · exact deletedGraphToCollapseEdgeHom_apply_left G hab
    · exact deletedGraphToCollapseEdgeHom_apply_right G hab

theorem deletedGraphToCollapseEdgeHom_ne_none_iff
    {V : Type u}
    {G : SimpleGraph V} {a b v : V}
    (hab : G.Adj a b) :
    deletedGraphToCollapseEdgeHom G hab v ≠
        (none : (GraphContraction.collapseEdge G hab).Target) ↔
      v ∉ ({a, b} : Set V) := by
  rw [ne_eq, deletedGraphToCollapseEdgeHom_eq_none_iff (G := G) hab]
  constructor
  · intro hnot hv
    exact hnot (by simpa using hv)
  · intro hnot h
    exact hnot (by simpa using h)

theorem deletedGraphToCollapseEdgeDart_tail_ne_none_iff
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    (deletedGraphToCollapseEdgeDart G hab e).tail ≠
        (none : (GraphContraction.collapseEdge G hab).Target) ↔
      e.tail ∉ ({a, b} : Set V) := by
  rw [deletedGraphToCollapseEdgeDart_tail,
    deletedGraphToCollapseEdgeHom_ne_none_iff (G := G) hab]

theorem deletedGraphToCollapseEdgeDart_head_ne_none_iff
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (deletedGraph G a b)) :
    (deletedGraphToCollapseEdgeDart G hab e).head ≠
        (none : (GraphContraction.collapseEdge G hab).Target) ↔
      e.head ∉ ({a, b} : Set V) := by
  rw [deletedGraphToCollapseEdgeDart_head,
    deletedGraphToCollapseEdgeHom_ne_none_iff (G := G) hab]

/-- Every contraction dart leaving the collapsed endpoint has a lift whose
source tail is one of the two split endpoints. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_tail_left_or_right
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (htail :
      e.tail = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        (d.tail = a ∨ d.tail = b) := by
  rcases deletedGraphToCollapseEdgeDart_surjective
      (G := G) hab e with ⟨d, hd⟩
  refine ⟨d, hd, ?_⟩
  exact
    (deletedGraphToCollapseEdgeDart_tail_eq_none_iff
      (G := G) hab d).mp (by simpa [hd] using htail)

/-- Every contraction dart entering the collapsed endpoint has a lift whose
source head is one of the two split endpoints. -/
theorem exists_deletedGraphToCollapseEdgeDart_lift_head_left_or_right
    {V : Type u}
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (e : OrientedEdge (GraphContraction.collapseEdge G hab).graph)
    (hhead :
      e.head = (none : (GraphContraction.collapseEdge G hab).Target)) :
    Exists fun d : OrientedEdge (deletedGraph G a b) =>
      deletedGraphToCollapseEdgeDart G hab d = e ∧
        (d.head = a ∨ d.head = b) := by
  rcases deletedGraphToCollapseEdgeDart_surjective
      (G := G) hab e with ⟨d, hd⟩
  refine ⟨d, hd, ?_⟩
  exact
    (deletedGraphToCollapseEdgeDart_head_eq_none_iff
      (G := G) hab d).mp (by simpa [hd] using hhead)

end EdgeDeletion


end FourColor

end Schematic.Math.GraphTheory
