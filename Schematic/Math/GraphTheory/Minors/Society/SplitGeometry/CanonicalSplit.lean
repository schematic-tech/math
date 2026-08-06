import Schematic.Math.GraphTheory.Minors.Society.CutPath

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The two sides produced after cutting a society along the path `P`.

In the paper, `leftBoundaryArc` and `rightBoundaryArc` are `Ω(s,t)` and
`Ω(t,s)`.  The two side vertex sets are the unions of components of
`G \ V(P)` meeting the corresponding boundary arc. -/
structure GMIX24Split (S : GeneralSociety V) (P : GMIX24CutPath S) where
  leftBoundaryArc : Set V
  rightBoundaryArc : Set V
  leftBoundaryArc_subset : leftBoundaryArc ⊆ S.boundarySet
  rightBoundaryArc_subset : rightBoundaryArc ⊆ S.boundarySet
  leftBoundaryArc_union :
    leftBoundaryArc ∪ rightBoundaryArc =
      S.boundarySet \ ({P.s, P.t} : Set V)
  leftBoundaryArc_disjoint :
    Disjoint leftBoundaryArc rightBoundaryArc
  leftSide : Set V
  rightSide : Set V
  leftSide_subset_outside : leftSide ⊆ P.outside
  rightSide_subset_outside : rightSide ⊆ P.outside
  outside_subset_sides : P.outside ⊆ leftSide ∪ rightSide
  sides_disjoint : Disjoint leftSide rightSide
  leftSide_caught :
    Catches S.graph leftBoundaryArc leftSide
  rightSide_caught :
    Catches S.graph rightBoundaryArc rightSide
  leftSociety : GeneralSociety V
  rightSociety : GeneralSociety V
  leftSociety_graph_le :
    leftSociety.graph ≤ S.graph
  rightSociety_graph_le :
    rightSociety.graph ≤ S.graph
  leftSociety_vertices :
    leftSociety.graph.support ⊆ leftSide ∪ P.pathSet
  rightSociety_vertices :
    rightSociety.graph.support ⊆ rightSide ∪ P.pathSet

namespace GMIX24Split

def ofCanonical [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hsides : Disjoint P.leftSide P.rightSide)
    (leftSociety rightSociety : GeneralSociety V)
    (leftSociety_graph_le : leftSociety.graph ≤ S.graph)
    (rightSociety_graph_le : rightSociety.graph ≤ S.graph)
    (leftSociety_vertices :
      leftSociety.graph.support ⊆ P.leftSide ∪ P.pathSet)
    (rightSociety_vertices :
      rightSociety.graph.support ⊆ P.rightSide ∪ P.pathSet) :
    GMIX24Split S P where
  leftBoundaryArc := P.leftBoundaryArc
  rightBoundaryArc := P.rightBoundaryArc
  leftBoundaryArc_subset := P.leftBoundaryArc_subset
  rightBoundaryArc_subset := P.rightBoundaryArc_subset
  leftBoundaryArc_union := P.leftBoundaryArc_union_right
  leftBoundaryArc_disjoint := P.leftBoundaryArc_disjoint_right
  leftSide := P.leftSide
  rightSide := P.rightSide
  leftSide_subset_outside := P.leftSide_subset_outside
  rightSide_subset_outside := P.rightSide_subset_outside
  outside_subset_sides := P.outside_subset_leftSide_union_rightSide
  sides_disjoint := hsides
  leftSide_caught := P.leftSide_caught
  rightSide_caught := P.rightSide_caught
  leftSociety := leftSociety
  rightSociety := rightSociety
  leftSociety_graph_le := leftSociety_graph_le
  rightSociety_graph_le := rightSociety_graph_le
  leftSociety_vertices := leftSociety_vertices
  rightSociety_vertices := rightSociety_vertices

def ofCanonicalGraphs [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hsides : Disjoint P.leftSide P.rightSide)
    (leftBoundary rightBoundary : CyclicBoundary V) :
    GMIX24Split S P :=
  ofCanonical P hsides
    { graph := P.leftGraph, boundary := leftBoundary }
    { graph := P.rightGraph, boundary := rightBoundary }
    P.leftGraph_le
    P.rightGraph_le
    P.leftGraph_support_subset
    P.rightGraph_support_subset

def ofCanonicalGraphsOfNoCross [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (leftBoundary rightBoundary : CyclicBoundary V) :
    GMIX24Split S P :=
  ofCanonicalGraphs P
    (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
    leftBoundary rightBoundary

noncomputable def canonicalOfNoCross [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    GMIX24Split S P :=
  ofCanonicalGraphsOfNoCross P hno_cross
    P.leftOrderedCutBoundary P.rightOrderedCutBoundary

@[simp]
theorem canonicalOfNoCross_reverse_leftSociety
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety := by
  ext <;> simp [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical]

@[simp]
theorem canonicalOfNoCross_reverse_rightSociety
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).rightSociety =
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety := by
  ext <;> simp [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical]

@[simp]
private theorem reverse_pathEdgeGraph
    {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.reverse.pathEdgeGraph = P.pathEdgeGraph := by
  ext u v
  simp [GMIX24CutPath.pathEdgeGraph_adj, GMIX24CutPath.reverse,
    SimpleGraph.Walk.edges_reverse]

/-- Regard a cross in the right canonical piece as a cross in the left piece
of the reversed cut path. -/
def canonicalOfNoCross.rightCrossOnReverse
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Cross :=
  (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm ▸ X

@[simp]
theorem canonicalOfNoCross.rightCrossOnReverse_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (i : Fin 4) :
    (canonicalOfNoCross.rightCrossOnReverse P hno_cross X).endpoints.endpoint i =
      X.endpoints.endpoint i :=
  Cross.cast_endpoint
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm X i

@[simp]
theorem canonicalOfNoCross.rightCrossOnReverse_endpointFunction
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    (canonicalOfNoCross.rightCrossOnReverse P hno_cross X).endpoints.endpoint =
      X.endpoints.endpoint :=
  funext (canonicalOfNoCross.rightCrossOnReverse_endpoint P hno_cross X)

@[simp]
theorem canonicalOfNoCross.rightCrossOnReverse_firstPath_support
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    (canonicalOfNoCross.rightCrossOnReverse P hno_cross X).firstPath.support =
      X.firstPath.support :=
  Cross.cast_firstPath_support
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm X

@[simp]
theorem canonicalOfNoCross.rightCrossOnReverse_secondPath_support
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    (canonicalOfNoCross.rightCrossOnReverse P hno_cross X).secondPath.support =
      X.secondPath.support :=
  Cross.cast_secondPath_support
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm X

/-- Regard a tripod in the right canonical piece as a tripod in the left piece
of the reversed cut path. -/
def canonicalOfNoCross.rightTripodOnReverse
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod) :
    (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
  (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm ▸ T

@[simp]
theorem canonicalOfNoCross.rightTripodOnReverse_boundary
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    (canonicalOfNoCross.rightTripodOnReverse P hno_cross T).boundary i =
      T.boundary i :=
  Tripod.cast_boundary
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm T i

@[simp]
theorem canonicalOfNoCross.rightTripodOnReverse_rim_support
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    ((canonicalOfNoCross.rightTripodOnReverse P hno_cross T).rim i).support =
      (T.rim i).support :=
  Tripod.cast_rim_support
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm T i

@[simp]
theorem canonicalOfNoCross.rightTripodOnReverse_leg_support
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    ((canonicalOfNoCross.rightTripodOnReverse P hno_cross T).leg i).support =
      (T.leg i).support :=
  Tripod.cast_leg_support
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm T i

theorem canonicalOfNoCross_graph_eq_split_sup_pathEdgeGraph
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    S.graph =
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph ⊔
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph ⊔
          P.pathEdgeGraph := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.graph_eq_leftGraph_sup_rightGraph_sup_pathEdgeGraph hno_cross

/-- Edge-set form of the canonical split decomposition.

This is the bookkeeping needed by the Kuratowski localization argument:
strict subdivision models quantify over `Sym2` edges of their model paths, so
the graph decomposition must be available directly as a trichotomy for
ambient edges. -/
theorem canonicalOfNoCross_edge_mem_left_or_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (he : e ∈ S.graph.edgeSet) :
    e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∨
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∨
        e ∈ P.pathEdgeGraph.edgeSet := by
  classical
  have hgraph :
      S.graph =
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph ⊔
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph ⊔
            P.pathEdgeGraph :=
    GMIX24Split.canonicalOfNoCross_graph_eq_split_sup_pathEdgeGraph
      P hno_cross
  have he' :
      e ∈
        ((GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph ⊔
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph ⊔
            P.pathEdgeGraph).edgeSet := by
    simpa [hgraph] using he
  simpa [SimpleGraph.edgeSet_sup, or_assoc] using he'

/-- No edge belongs simultaneously to the left and right side graphs of the
canonical split. -/
theorem canonicalOfNoCross_disjoint_left_right_edgeSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    Disjoint
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet := by
  classical
  rw [Set.disjoint_left]
  intro e heLeft heRight
  induction e using Sym2.ind with
  | h u v =>
      have hleftAdj :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Adj
            u v := by
        simpa [SimpleGraph.mem_edgeSet] using heLeft
      have hrightAdj :
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.Adj
            u v := by
        simpa [SimpleGraph.mem_edgeSet] using heRight
      exact
        P.leftGraph_not_adj_of_rightGraph_adj
          (by
            simpa [GMIX24Split.canonicalOfNoCross,
              GMIX24Split.ofCanonicalGraphsOfNoCross,
              GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical]
              using hrightAdj)
          (by
            simpa [GMIX24Split.canonicalOfNoCross,
              GMIX24Split.ofCanonicalGraphsOfNoCross,
              GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical]
              using hleftAdj)

/-- No edge belongs simultaneously to the left side graph and the cut-path
edge graph of the canonical split. -/
theorem canonicalOfNoCross_disjoint_left_path_edgeSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    Disjoint
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet
      P.pathEdgeGraph.edgeSet := by
  classical
  rw [Set.disjoint_left]
  intro e heLeft hePath
  induction e using Sym2.ind with
  | h u v =>
      have hleftAdj :
          (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.Adj
            u v := by
        simpa [SimpleGraph.mem_edgeSet] using heLeft
      have hpathAdj : P.pathEdgeGraph.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using hePath
      exact
        P.leftGraph_not_adj_of_pathEdgeGraph_adj hpathAdj
          (by
            simpa [GMIX24Split.canonicalOfNoCross,
              GMIX24Split.ofCanonicalGraphsOfNoCross,
              GMIX24Split.ofCanonicalGraphs, GMIX24Split.ofCanonical]
              using hleftAdj)

/-- No edge belongs simultaneously to the right side graph and the cut-path
edge graph of the canonical split. -/
theorem canonicalOfNoCross_disjoint_right_path_edgeSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    Disjoint
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet
      P.pathEdgeGraph.edgeSet := by
  simpa using
    (GMIX24Split.canonicalOfNoCross_disjoint_left_path_edgeSet
      P.reverse hno_cross)

/-- Every edge used by a strict-subdivision model in the ambient graph lies in
one of the three edge-disjoint pieces of the canonical split. -/
theorem canonicalOfNoCross_model_edge_mem_left_or_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (M : StrictSubdivisionModel K S.graph)
    {x y : W} (hxy : K.Adj x y)
    {e : Sym2 V}
    (he : e ∈ (M.edgePath hxy).edges) :
    e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∨
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∨
        e ∈ P.pathEdgeGraph.edgeSet := by
  exact
    GMIX24Split.canonicalOfNoCross_edge_mem_left_or_right_or_path
      P hno_cross ((M.edgePath hxy).edges_subset_edgeSet he)

/-- Contains-subdivision version of
`canonicalOfNoCross_model_edge_mem_left_or_right_or_path`. -/
theorem canonicalOfNoCross_contains_edge_mem_left_or_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    {x y : W} (hxy : K.Adj x y)
    {e : Sym2 V}
    (he : e ∈ ((Classical.choice hK).edgePath hxy).edges) :
    e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet ∨
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet ∨
        e ∈ P.pathEdgeGraph.edgeSet := by
  classical
  exact
    GMIX24Split.canonicalOfNoCross_model_edge_mem_left_or_right_or_path
      P hno_cross (Classical.choice hK) hxy he

theorem canonicalOfNoCross_not_right_edge_of_left_edge
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (heLeft :
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet) :
    e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet := by
  intro heRight
  exact
    Set.disjoint_left.mp
      (GMIX24Split.canonicalOfNoCross_disjoint_left_right_edgeSet
        P hno_cross)
      heLeft heRight

theorem canonicalOfNoCross_not_path_edge_of_left_edge
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (heLeft :
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet) :
    e ∉ P.pathEdgeGraph.edgeSet := by
  intro hePath
  exact
    Set.disjoint_left.mp
      (GMIX24Split.canonicalOfNoCross_disjoint_left_path_edgeSet
        P hno_cross)
      heLeft hePath

theorem canonicalOfNoCross_not_path_edge_of_right_edge
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (heRight :
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet) :
    e ∉ P.pathEdgeGraph.edgeSet := by
  intro hePath
  exact
    Set.disjoint_left.mp
      (GMIX24Split.canonicalOfNoCross_disjoint_right_path_edgeSet
        P hno_cross)
      heRight hePath

theorem canonicalOfNoCross_not_left_edge_of_right_edge
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (heRight :
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet) :
    e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet := by
  intro heLeft
  exact
    GMIX24Split.canonicalOfNoCross_not_right_edge_of_left_edge
      P hno_cross heLeft heRight

theorem canonicalOfNoCross_not_left_edge_of_path_edge
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (hePath : e ∈ P.pathEdgeGraph.edgeSet) :
    e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet := by
  intro heLeft
  exact
    GMIX24Split.canonicalOfNoCross_not_path_edge_of_left_edge
      P hno_cross heLeft hePath

theorem canonicalOfNoCross_not_right_edge_of_path_edge
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (hePath : e ∈ P.pathEdgeGraph.edgeSet) :
    e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet := by
  intro heRight
  exact
    GMIX24Split.canonicalOfNoCross_not_path_edge_of_right_edge
      P hno_cross heRight hePath

/-- The two chosen representatives of an edge lie in the graph support. -/
theorem edgeSet_out_mem_support {G : SimpleGraph V} {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    e.out.1 ∈ G.support ∧ e.out.2 ∈ G.support := by
  induction e using Sym2.ind with
  | h u v =>
      have huv : G.Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using he
      constructor
      · have hout : (s(u, v) : Sym2 V).out.1 = u ∨
            (s(u, v) : Sym2 V).out.1 = v := by
          simpa [Sym2.mem_iff] using
            (Sym2.out_fst_mem (s(u, v) : Sym2 V))
        rcases hout with h | h
        · simpa [h] using huv.left_mem_support
        · simpa [h] using huv.right_mem_support
      · have hout : (s(u, v) : Sym2 V).out.2 = u ∨
            (s(u, v) : Sym2 V).out.2 = v := by
          simpa [Sym2.mem_iff] using
            (Sym2.out_snd_mem (s(u, v) : Sym2 V))
        rcases hout with h | h
        · simpa [h] using huv.left_mem_support
        · simpa [h] using huv.right_mem_support

/-- Endpoints of a canonical left-piece edge are left-side or cut-path vertices. -/
theorem canonicalOfNoCross_left_edge_out_mem_leftSide_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (he :
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet) :
    e.out.1 ∈ P.leftSide ∪ P.pathSet ∧
      e.out.2 ∈ P.leftSide ∪ P.pathSet := by
  have hend :=
    edgeSet_out_mem_support
      (G := (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph)
      he
  exact ⟨
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices hend.1,
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_vertices hend.2⟩

/-- Endpoints of a canonical right-piece edge are right-side or cut-path vertices. -/
theorem canonicalOfNoCross_right_edge_out_mem_rightSide_or_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {e : Sym2 V}
    (he :
      e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet) :
    e.out.1 ∈ P.rightSide ∪ P.pathSet ∧
      e.out.2 ∈ P.rightSide ∪ P.pathSet := by
  simpa using
    (GMIX24Split.canonicalOfNoCross_left_edge_out_mem_leftSide_or_path
      P.reverse hno_cross (by simpa using he))

/-- Endpoints of a cut-path edge lie on the cut path. -/
theorem pathEdgeGraph_edge_out_mem_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {e : Sym2 V}
    (he : e ∈ P.pathEdgeGraph.edgeSet) :
    e.out.1 ∈ P.pathSet ∧ e.out.2 ∈ P.pathSet := by
  have hend := edgeSet_out_mem_support (G := P.pathEdgeGraph) he
  exact ⟨P.pathEdgeGraph_support_subset_pathSet hend.1,
    P.pathEdgeGraph_support_subset_pathSet hend.2⟩


/-- Localize a strict subdivision to the left piece of the canonical split
once every edge of every model path is known to be a left-piece edge. -/
theorem canonicalOfNoCross_containsStrictSubdivision_left_of_edge_paths_left
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hedge :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet) :
    ContainsStrictSubdivision K
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph :=
  ContainsStrictSubdivision.edgeRestrict hK hedge

/-- Localize a strict subdivision to the right piece of the canonical split
once every edge of every model path is known to be a right-piece edge. -/
theorem canonicalOfNoCross_containsStrictSubdivision_right_of_edge_paths_right
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hedge :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∈ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet) :
    ContainsStrictSubdivision K
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph :=
  ContainsStrictSubdivision.edgeRestrict hK hedge

/-- Localize a strict subdivision to the induced cut-path edge graph once
every edge of every model path is known to be a path edge. -/
theorem containsStrictSubdivision_pathEdgeGraph_of_edge_paths_path
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hedge :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∈ P.pathEdgeGraph.edgeSet) :
    ContainsStrictSubdivision K P.pathEdgeGraph :=
  ContainsStrictSubdivision.edgeRestrict hK hedge

/-- Localize a strict subdivision to the left piece by ruling out all right
and cut-path edges on its model paths.  The canonical edge trichotomy supplies
the remaining left membership. -/
theorem canonicalOfNoCross_containsStrictSubdivision_left_of_no_right_no_path_edges
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hnot_right :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet)
    (hnot_path :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∉ P.pathEdgeGraph.edgeSet) :
    ContainsStrictSubdivision K
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_containsStrictSubdivision_left_of_edge_paths_left
      P hno_cross hK ?_
  intro x y hxy e he
  rcases
      GMIX24Split.canonicalOfNoCross_contains_edge_mem_left_or_right_or_path
        P hno_cross hK hxy he with heLeft | heRest
  · exact heLeft
  · rcases heRest with heRight | hePath
    · exact False.elim (hnot_right hxy e he heRight)
    · exact False.elim (hnot_path hxy e he hePath)

/-- Localize a strict subdivision to the right piece by ruling out all left
and cut-path edges on its model paths. -/
theorem canonicalOfNoCross_containsStrictSubdivision_right_of_no_left_no_path_edges
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hnot_left :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet)
    (hnot_path :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∉ P.pathEdgeGraph.edgeSet) :
    ContainsStrictSubdivision K
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph := by
  classical
  refine
    GMIX24Split.canonicalOfNoCross_containsStrictSubdivision_right_of_edge_paths_right
      P hno_cross hK ?_
  intro x y hxy e he
  rcases
      GMIX24Split.canonicalOfNoCross_contains_edge_mem_left_or_right_or_path
        P hno_cross hK hxy he with heLeft | heRest
  · exact False.elim (hnot_left hxy e he heLeft)
  · rcases heRest with heRight | hePath
    · exact heRight
    · exact False.elim (hnot_path hxy e he hePath)

/-- Localize a strict subdivision to the cut-path graph by ruling out all side
edges on its model paths. -/
theorem containsStrictSubdivision_pathEdgeGraph_of_no_left_no_right_edges
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {W : Type*} {K : SimpleGraph W}
    (hK : ContainsStrictSubdivision K S.graph)
    (hnot_left :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.graph.edgeSet)
    (hnot_right :
      forall {x y : W} (hxy : K.Adj x y) (e : Sym2 V),
        e ∈ ((Classical.choice hK).edgePath hxy).edges ->
          e ∉ (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.graph.edgeSet) :
    ContainsStrictSubdivision K P.pathEdgeGraph := by
  classical
  refine
    GMIX24Split.containsStrictSubdivision_pathEdgeGraph_of_edge_paths_path
      P hK ?_
  intro x y hxy e he
  rcases
      GMIX24Split.canonicalOfNoCross_contains_edge_mem_left_or_right_or_path
        P hno_cross hK hxy he with heLeft | heRest
  · exact False.elim (hnot_left hxy e he heLeft)
  · rcases heRest with heRight | hePath
    · exact False.elim (hnot_right hxy e he heRight)
    · exact hePath


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
