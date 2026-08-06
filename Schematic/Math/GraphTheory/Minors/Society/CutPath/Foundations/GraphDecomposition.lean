import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Sides

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

def cutGraphDeletingSide {S : GeneralSociety V}
    (P : GMIX24CutPath S) (deleteSide : Set V) : SimpleGraph V where
  Adj u v :=
    S.graph.Adj u v ∧
      u ∉ deleteSide ∧ v ∉ deleteSide ∧ s(u, v) ∉ P.path.edges
  symm := by
    intro u v h
    refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
    simpa [Sym2.eq_swap] using h.2.2.2
  loopless := ⟨by
    intro v h
    exact S.graph.irrefl h.1⟩

@[simp]
theorem cutGraphDeletingSide_adj {S : GeneralSociety V}
    (P : GMIX24CutPath S) (deleteSide : Set V) {u v : V} :
    (P.cutGraphDeletingSide deleteSide).Adj u v ↔
      S.graph.Adj u v ∧
        u ∉ deleteSide ∧ v ∉ deleteSide ∧ s(u, v) ∉ P.path.edges :=
  Iff.rfl

theorem cutGraphDeletingSide_le {S : GeneralSociety V}
    (P : GMIX24CutPath S) (deleteSide : Set V) :
    P.cutGraphDeletingSide deleteSide ≤ S.graph := by
  intro u v h
  exact h.1

@[simp]
theorem reverse_cutGraphDeletingSide {S : GeneralSociety V}
    (P : GMIX24CutPath S) (deleteSide : Set V) :
    P.reverse.cutGraphDeletingSide deleteSide =
      P.cutGraphDeletingSide deleteSide := by
  ext u v
  simp only [cutGraphDeletingSide_adj, reverse_path]
  have hmem : s(u, v) ∈ P.path.reverse.edges ↔ s(u, v) ∈ P.path.edges := by
    constructor
    · intro he
      have he' : s(u, v) ∈ P.path.edges.reverse := by
        simpa [P.path.edges_reverse] using he
      exact List.mem_reverse.mp he'
    · intro he
      have he' : s(u, v) ∈ P.path.edges.reverse := List.mem_reverse.mpr he
      simpa [P.path.edges_reverse] using he'
  constructor
  · rintro ⟨huv, hu, hv, he⟩
    exact ⟨huv, hu, hv, fun he' => he (hmem.mpr he')⟩
  · rintro ⟨huv, hu, hv, he⟩
    exact ⟨huv, hu, hv, fun he' => he (hmem.mp he')⟩

def leftGraph [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : SimpleGraph V :=
  P.cutGraphDeletingSide P.rightSide

def rightGraph [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : SimpleGraph V :=
  P.cutGraphDeletingSide P.leftSide

@[simp]
theorem reverse_leftGraph [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.leftGraph = P.rightGraph := by
  simp [leftGraph, rightGraph]

@[simp]
theorem reverse_rightGraph [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.reverse.rightGraph = P.leftGraph := by
  simp [leftGraph, rightGraph]

def pathEdgeGraph {S : GeneralSociety V}
    (P : GMIX24CutPath S) : SimpleGraph V where
  Adj u v := S.graph.Adj u v ∧ s(u, v) ∈ P.path.edges
  symm := by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    simpa [Sym2.eq_swap] using h.2
  loopless := ⟨by
    intro v h
    exact S.graph.irrefl h.1⟩

@[simp]
theorem leftGraph_adj [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {u v : V} :
    P.leftGraph.Adj u v ↔
      S.graph.Adj u v ∧
        u ∉ P.rightSide ∧ v ∉ P.rightSide ∧
          s(u, v) ∉ P.path.edges := by
  rfl

@[simp]
theorem rightGraph_adj [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {u v : V} :
    P.rightGraph.Adj u v ↔
      S.graph.Adj u v ∧
        u ∉ P.leftSide ∧ v ∉ P.leftSide ∧
          s(u, v) ∉ P.path.edges := by
  rfl

@[simp]
theorem pathEdgeGraph_adj {S : GeneralSociety V}
    (P : GMIX24CutPath S) {u v : V} :
    P.pathEdgeGraph.Adj u v ↔
      S.graph.Adj u v ∧ s(u, v) ∈ P.path.edges :=
  Iff.rfl

theorem adj_leftGraph_or_rightGraph_of_not_path_edge [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (huv : S.graph.Adj u v)
    (he_not_path : s(u, v) ∉ P.path.edges) :
    P.leftGraph.Adj u v ∨ P.rightGraph.Adj u v := by
  have hsides := P.leftSide_disjoint_rightSide_of_no_cross hno_cross
  by_cases huR : u ∈ P.rightSide
  · by_cases hvR : v ∈ P.rightSide
    · right
      have hu_not_left : u ∉ P.leftSide := by
        intro huL
        exact Set.disjoint_left.mp hsides huL huR
      have hv_not_left : v ∉ P.leftSide := by
        intro hvL
        exact Set.disjoint_left.mp hsides hvL hvR
      exact ⟨huv, hu_not_left, hv_not_left, he_not_path⟩
    · by_cases hvL : v ∈ P.leftSide
      · exact False.elim
          (P.not_adj_leftSide_rightSide_of_no_cross hno_cross
            hvL huR huv.symm)
      · right
        have hu_not_left : u ∉ P.leftSide := by
          intro huL
          exact Set.disjoint_left.mp hsides huL huR
        exact ⟨huv, hu_not_left, hvL, he_not_path⟩
  · by_cases hvR : v ∈ P.rightSide
    · by_cases huL : u ∈ P.leftSide
      · exact False.elim
          (P.not_adj_leftSide_rightSide_of_no_cross hno_cross
            huL hvR huv)
      · right
        have hv_not_left : v ∉ P.leftSide := by
          intro hvL
          exact Set.disjoint_left.mp hsides hvL hvR
        exact ⟨huv, huL, hv_not_left, he_not_path⟩
    · left
      exact ⟨huv, huR, hvR, he_not_path⟩

theorem leftGraph_le [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftGraph ≤ S.graph :=
  P.cutGraphDeletingSide_le P.rightSide

theorem rightGraph_le [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightGraph ≤ S.graph :=
  P.cutGraphDeletingSide_le P.leftSide

theorem leftSide_walk_edges_subset_leftGraph [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (q : S.graph.Walk u v)
    (hq_left : forall z : V, z ∈ q.support -> z ∈ P.leftSide) :
    forall e : Sym2 V, e ∈ q.edges -> e ∈ P.leftGraph.edgeSet := by
  classical
  induction q with
  | nil =>
      intro e he
      simp at he
  | cons h p ih =>
      intro e he
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he_head | he_tail
      · subst e
        rw [SimpleGraph.mem_edgeSet]
        have huLeft : _ ∈ P.leftSide :=
          hq_left _ (by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inl rfl)
        have hvLeft : _ ∈ P.leftSide :=
          hq_left _ (by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr p.start_mem_support)
        have hsides := P.leftSide_disjoint_rightSide_of_no_cross hno_cross
        exact ⟨h,
          Set.disjoint_left.mp hsides huLeft,
          Set.disjoint_left.mp hsides hvLeft,
          by
            intro hePath
            have huPath := P.path.fst_mem_support_of_mem_edges hePath
            exact (P.leftSide_subset_outside huLeft).2
              (by simpa [GMIX24CutPath.pathSet] using huPath)⟩
      · exact ih (by
          intro z hz
          exact hq_left z (by
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
            exact Or.inr hz)) e he_tail

theorem rightSide_walk_edges_subset_rightGraph [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (q : S.graph.Walk u v)
    (hq_right : forall z : V, z ∈ q.support -> z ∈ P.rightSide) :
    forall e : Sym2 V, e ∈ q.edges -> e ∈ P.rightGraph.edgeSet := by
  simpa using
    P.reverse.leftSide_walk_edges_subset_leftGraph hno_cross q
      (by
        intro z hz
        simpa using hq_right z hz)

theorem leftSide_walk_transfer_internal_leftCutBoundary_empty
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (q : S.graph.Walk u v)
    (hq_left : forall z : V, z ∈ q.support -> z ∈ P.leftSide)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅) :
    Walk.InternalVertices
        (q.transfer P.leftGraph
          (P.leftSide_walk_edges_subset_leftGraph hno_cross q hq_left)) ∩
      P.leftCutBoundarySet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzq : z ∈ Walk.InternalVertices q := by
    simpa [Walk.internalVertices_transfer] using hz.1
  rcases hz.2 with hzArc | hzPath
  · have hzBoundary : z ∈ S.boundarySet := P.leftBoundaryArc_subset hzArc
    have hbad : z ∈ Walk.InternalVertices q ∩ S.boundarySet :=
      ⟨hzq, hzBoundary⟩
    rw [hq_boundary] at hbad
    exact hbad
  · exact (hq_outside z hzq.1).2
      (by simpa [GMIX24CutPath.pathSet] using hzPath)

theorem rightSide_walk_transfer_internal_rightCutBoundary_empty
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (q : S.graph.Walk u v)
    (hq_right : forall z : V, z ∈ q.support -> z ∈ P.rightSide)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hq_boundary : Walk.InternalVertices q ∩ S.boundarySet = ∅) :
    Walk.InternalVertices
        (q.transfer P.rightGraph
          (P.rightSide_walk_edges_subset_rightGraph hno_cross q hq_right)) ∩
      P.rightCutBoundarySet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hzq : z ∈ Walk.InternalVertices q := by
    simpa [Walk.internalVertices_transfer] using hz.1
  rcases hz.2 with hzArc | hzPath
  · have hzBoundary : z ∈ S.boundarySet := P.rightBoundaryArc_subset hzArc
    have hbad : z ∈ Walk.InternalVertices q ∩ S.boundarySet :=
      ⟨hzq, hzBoundary⟩
    rw [hq_boundary] at hbad
    exact hbad
  · exact (hq_outside z hzq.1).2
      (by simpa [GMIX24CutPath.pathSet] using hzPath)

theorem pathEdgeGraph_le {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.pathEdgeGraph ≤ S.graph := by
  intro u v h
  exact h.1

theorem pathEdgeGraph_support_subset_pathSet {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.pathEdgeGraph.support ⊆ P.pathSet := by
  intro v hv
  rcases (SimpleGraph.mem_support (G := P.pathEdgeGraph) (v := v)).mp hv with
    ⟨w, hvw⟩
  have he : s(v, w) ∈ P.path.edges := hvw.2
  exact P.path.fst_mem_support_of_mem_edges he

theorem pathEdgeGraph_le_path_toSubgraph_spanningCoe
    {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.pathEdgeGraph ≤ P.path.toSubgraph.spanningCoe := by
  intro u v h
  exact (SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges).mpr h.2

/-- The induced cut walk spans exactly the canonical cut-path edge graph. -/
theorem path_toSubgraph_spanningCoe_eq_pathEdgeGraph
    {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.path.toSubgraph.spanningCoe = P.pathEdgeGraph := by
  ext u v
  constructor
  · intro huv
    have he : s(u, v) ∈ P.path.edges :=
      SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp huv
    exact ⟨P.path.edges_subset_edgeSet he, he⟩
  · intro huv
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr huv.2

theorem pathEdgeGraph_degree_le_two
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V} [DecidableRel S.graph.Adj]
    (P : GMIX24CutPath S) [DecidableRel P.pathEdgeGraph.Adj]
    (v : V) :
    P.pathEdgeGraph.degree v <= 2 := by
  classical
  letI : DecidableRel P.path.toSubgraph.spanningCoe.Adj :=
    Classical.decRel _
  letI : Fintype (P.path.toSubgraph.neighborSet v) :=
    (P.path.toSubgraph.neighborSet v).toFinite.fintype
  have htarget : P.path.toSubgraph.spanningCoe.degree v <= 2 := by
    have hsubdeg : P.path.toSubgraph.degree v <= 2 := by
      by_cases hv : v ∈ P.path.support
      · have hcard :=
          Walk.IsPath.ncard_neighborSet_toSubgraph_le_two_of_mem_support
            P.path_isPath hv
        simpa [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
          using hcard
      · have hnot : v ∉ P.path.toSubgraph.verts := by
          simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hv
        have hdeg0 : P.path.toSubgraph.degree v = 0 :=
          SimpleGraph.Subgraph.degree_of_notMem_verts hnot
        omega
    simpa [SimpleGraph.Subgraph.degree_spanningCoe] using hsubdeg
  exact
    (SimpleGraph.degree_le_of_le
      P.pathEdgeGraph_le_path_toSubgraph_spanningCoe).trans htarget

theorem pathEdgeGraph_isPlanar
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V} [DecidableRel S.graph.Adj]
    (P : GMIX24CutPath S) [DecidableRel P.pathEdgeGraph.Adj] :
    IsPlanar P.pathEdgeGraph := by
  classical
  apply isPlanar_of_highDegree_bounds
  · have hnone : {v : V | 4 <= P.pathEdgeGraph.degree v} = ∅ := by
      ext v
      constructor
      · intro hv
        have hlarge : 4 <= P.pathEdgeGraph.degree v := by
          simpa using hv
        have hdeg := P.pathEdgeGraph_degree_le_two v
        omega
      · intro hv
        exact False.elim (by simp at hv)
    simp [hnone]
  · have hnone : {v : V | 3 <= P.pathEdgeGraph.degree v} = ∅ := by
      ext v
      constructor
      · intro hv
        have hlarge : 3 <= P.pathEdgeGraph.degree v := by
          simpa using hv
        have hdeg := P.pathEdgeGraph_degree_le_two v
        omega
      · intro hv
        exact False.elim (by simp at hv)
    simp [hnone]

/-- The cut-path graph cannot contain a strict `K_5` subdivision. -/
theorem pathEdgeGraph_no_K5_subdivision
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V} [DecidableRel S.graph.Adj]
    (P : GMIX24CutPath S) [DecidableRel P.pathEdgeGraph.Adj] :
    Not (ContainsStrictSubdivision K5Graph P.pathEdgeGraph) :=
  (P.pathEdgeGraph_isPlanar).no_K5_subdivision

/-- The cut-path graph cannot contain a strict `K_{3,3}` subdivision. -/
theorem pathEdgeGraph_no_K33_subdivision
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V} [DecidableRel S.graph.Adj]
    (P : GMIX24CutPath S) [DecidableRel P.pathEdgeGraph.Adj] :
    Not (ContainsStrictSubdivision K33Graph P.pathEdgeGraph) :=
  (P.pathEdgeGraph_isPlanar).no_K33_subdivision

theorem leftGraph_not_adj_between_path_vertices
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hu : u ∈ P.pathSet) (hv : v ∈ P.pathSet) :
    Not (P.leftGraph.Adj u v) := by
  intro huv
  have he_path : s(u, v) ∈ P.path.edges :=
    P.path_induced.mem_edges
      (by simpa [pathSet] using hu)
      (by simpa [pathSet] using hv)
      huv.1
  exact huv.2.2.2 he_path

theorem rightGraph_not_adj_between_path_vertices
    [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hu : u ∈ P.pathSet) (hv : v ∈ P.pathSet) :
    Not (P.rightGraph.Adj u v) := by
  simpa using
    P.reverse.leftGraph_not_adj_between_path_vertices
      (by simpa using hu) (by simpa using hv)

theorem adj_iff_leftGraph_or_rightGraph_or_pathEdgeGraph [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V} :
    S.graph.Adj u v ↔
      P.leftGraph.Adj u v ∨
        P.rightGraph.Adj u v ∨ P.pathEdgeGraph.Adj u v := by
  constructor
  · intro huv
    by_cases he : s(u, v) ∈ P.path.edges
    · exact Or.inr (Or.inr ⟨huv, he⟩)
    · rcases P.adj_leftGraph_or_rightGraph_of_not_path_edge
          hno_cross huv he with hleft | hright
      · exact Or.inl hleft
      · exact Or.inr (Or.inl hright)
  · intro h
    rcases h with hleft | hrest
    · exact P.leftGraph_le hleft
    · rcases hrest with hright | hpath
      · exact P.rightGraph_le hright
      · exact hpath.1

theorem graph_eq_leftGraph_sup_rightGraph_sup_pathEdgeGraph [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    S.graph = P.leftGraph ⊔ P.rightGraph ⊔ P.pathEdgeGraph := by
  ext u v
  constructor
  · intro huv
    have hparts :
        P.leftGraph.Adj u v ∨
          P.rightGraph.Adj u v ∨ P.pathEdgeGraph.Adj u v :=
      (P.adj_iff_leftGraph_or_rightGraph_or_pathEdgeGraph hno_cross).mp huv
    simpa [SimpleGraph.sup_adj, or_assoc] using hparts
  · intro hparts
    have hparts' :
        P.leftGraph.Adj u v ∨
          P.rightGraph.Adj u v ∨ P.pathEdgeGraph.Adj u v := by
      simpa [SimpleGraph.sup_adj, or_assoc] using hparts
    exact
      (P.adj_iff_leftGraph_or_rightGraph_or_pathEdgeGraph hno_cross).mpr
        hparts'

theorem leftGraph_not_adj_of_path_edge [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (he : s(u, v) ∈ P.path.edges) :
    Not (P.leftGraph.Adj u v) := by
  intro h
  exact h.2.2.2 he

theorem rightGraph_not_adj_of_path_edge [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (he : s(u, v) ∈ P.path.edges) :
    Not (P.rightGraph.Adj u v) := by
  have herev : s(u, v) ∈ P.reverse.path.edges := by
    have he' : s(u, v) ∈ P.path.edges.reverse := List.mem_reverse.mpr he
    change s(u, v) ∈ P.path.reverse.edges
    exact P.path.edges_reverse.symm ▸ he'
  simpa using P.reverse.leftGraph_not_adj_of_path_edge herev

theorem leftGraph_not_adj_of_rightGraph_adj [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hright : P.rightGraph.Adj u v) :
    Not (P.leftGraph.Adj u v) := by
  intro hleft
  have huPath : u ∈ P.pathSet := by
    by_contra hu_not_path
    have huOutside : u ∈ P.outside := by
      refine ⟨?_, ?_⟩
      · exact Or.inl hleft.1.left_mem_support
      · simpa [GMIX24CutPath.pathSet] using hu_not_path
    rcases P.outside_subset_leftSide_union_rightSide huOutside with huLeft | huRight
    · exact hright.2.1 huLeft
    · exact hleft.2.1 huRight
  have hvPath : v ∈ P.pathSet := by
    by_contra hv_not_path
    have hvOutside : v ∈ P.outside := by
      refine ⟨?_, ?_⟩
      · exact Or.inl hleft.1.right_mem_support
      · simpa [GMIX24CutPath.pathSet] using hv_not_path
    rcases P.outside_subset_leftSide_union_rightSide hvOutside with hvLeft | hvRight
    · exact hright.2.2.1 hvLeft
    · exact hleft.2.2.1 hvRight
  exact P.leftGraph_not_adj_between_path_vertices huPath hvPath hleft

theorem rightGraph_not_adj_of_leftGraph_adj [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hleft : P.leftGraph.Adj u v) :
    Not (P.rightGraph.Adj u v) := by
  intro hright
  exact P.leftGraph_not_adj_of_rightGraph_adj hright hleft

theorem leftGraph_not_adj_of_pathEdgeGraph_adj [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hpath : P.pathEdgeGraph.Adj u v) :
    Not (P.leftGraph.Adj u v) :=
  P.leftGraph_not_adj_of_path_edge hpath.2

theorem rightGraph_not_adj_of_pathEdgeGraph_adj [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hpath : P.pathEdgeGraph.Adj u v) :
    Not (P.rightGraph.Adj u v) :=
  P.rightGraph_not_adj_of_path_edge hpath.2

theorem pathEdgeGraph_not_adj_of_leftGraph_adj [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hleft : P.leftGraph.Adj u v) :
    Not (P.pathEdgeGraph.Adj u v) := by
  intro hpath
  exact P.leftGraph_not_adj_of_pathEdgeGraph_adj hpath hleft

theorem pathEdgeGraph_not_adj_of_rightGraph_adj [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V}
    (hright : P.rightGraph.Adj u v) :
    Not (P.pathEdgeGraph.Adj u v) := by
  intro hpath
  exact P.rightGraph_not_adj_of_pathEdgeGraph_adj hpath hright

theorem leftGraph_support_subset [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftGraph.support ⊆ P.leftSide ∪ P.pathSet := by
  intro v hv
  rcases (SimpleGraph.mem_support (G := P.leftGraph) (v := v)).mp hv with
    ⟨w, hvw⟩
  have hv_not_right : v ∉ P.rightSide := hvw.2.1
  by_cases hvpath : v ∈ P.pathSet
  · exact Or.inr hvpath
  · have hvout : v ∈ P.outside := by
      exact ⟨Or.inl hvw.1.left_mem_support, by
        simpa [pathSet] using hvpath⟩
    rcases P.outside_subset_leftSide_union_rightSide hvout with hvleft | hvright
    · exact Or.inl hvleft
    · exact False.elim (hv_not_right hvright)

theorem rightGraph_support_subset [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightGraph.support ⊆ P.rightSide ∪ P.pathSet := by
  simpa using P.reverse.leftGraph_support_subset

theorem supportIndex_reverse_lt_iff [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {x y : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) :
    Walk.supportIndex P.reverse.path x < Walk.supportIndex P.reverse.path y ↔
      Walk.supportIndex P.path y < Walk.supportIndex P.path x := by
  have hxSupport : x ∈ P.path.support := by
    simpa [pathSet] using hx
  have hySupport : y ∈ P.path.support := by
    simpa [pathSet] using hy
  simp only [reverse, Walk.supportIndex, SimpleGraph.Walk.support_reverse]
  rw [List.idxOf_reverse_of_nodup P.path_isPath.support_nodup hxSupport,
    List.idxOf_reverse_of_nodup P.path_isPath.support_nodup hySupport]
  have hxLt : P.path.support.idxOf x < P.path.support.length :=
    List.idxOf_lt_length_iff.mpr hxSupport
  have hyLt : P.path.support.idxOf y < P.path.support.length :=
    List.idxOf_lt_length_iff.mpr hySupport
  omega


end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
