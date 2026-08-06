import Schematic.Math.GraphTheory.Minors.Society.RuralGluing.CertificateAssembly

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The theorem package that the literal GM IX `(2.4)` induction needs at the
recursive step.  Both smaller societies must be three-connected, cross-free,
tripod-free, and rural; then their rural drawings glue along the common path.

This structure is deliberately separate from `GMIX24Statement`, because it is
the reusable background lemma needed to formalize the proof exactly as written
in the paper. -/
structure GMIX24InductionStep (S : GeneralSociety V) where
  cutPath : GMIX24CutPath S
  split : GMIX24Split S cutPath
  left_three_connected : split.leftSociety.ThreeConnected
  right_three_connected : split.rightSociety.ThreeConnected
  left_cross_free : Not (Nonempty split.leftSociety.Cross)
  right_cross_free : Not (Nonempty split.rightSociety.Cross)
  left_tripod_free : Not (Nonempty split.leftSociety.Tripod)
  right_tripod_free : Not (Nonempty split.rightSociety.Tripod)
  glues_rural :
    Nonempty split.leftSociety.Rural ->
      Nonempty split.rightSociety.Rural ->
        Nonempty S.Rural

/-- The current formal target corresponding to the planarity consequence of
GM IX `(2.4)`.

The printed theorem says that the society is rural in the disk-boundary sense.
Because `Rural` is currently a Kuratowski-style planarity shadow, this statement
is not the literal full disk-rural theorem; it is the strongest statement that
the present local planarity interface can express without adding a full
embedding/disk drawing development. -/
def GMIX24Statement : Prop :=
  forall (S : GeneralSociety V),
    S.ThreeConnected ->
      Not (Nonempty S.Cross) ->
        Not (Nonempty S.Tripod) ->
          Nonempty S.Rural

/-- The GM IX induction measure: the number of edges of the society graph. -/
private noncomputable def graphEdgeCount
    [Fintype (Sym2 V)] (G : SimpleGraph V) : Nat := by
  classical
  exact G.edgeFinset.card

noncomputable def edgeCount [Fintype (Sym2 V)] (S : GeneralSociety V) :
    Nat := graphEdgeCount S.graph

private theorem edgeFinset_card_lt_of_le_of_adj_not_adj
    [Fintype (Sym2 V)]
    {G H : SimpleGraph V} (hHG : H ≤ G) {x y : V}
    (hG : G.Adj x y) (hH : Not (H.Adj x y)) :
    graphEdgeCount H < graphEdgeCount G := by
  classical
  simp only [graphEdgeCount]
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨SimpleGraph.edgeFinset_mono hHG, ?_⟩
  intro hEq
  apply hH
  have hxy : s(x, y) ∈ H.edgeFinset := by
    rw [hEq]
    exact SimpleGraph.mem_edgeFinset.mpr hG
  simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy

theorem GMIX24CutPath.leftGraph_edgeCount_lt
    [Fintype (Sym2 V)] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (leftBoundary : CyclicBoundary V) :
    edgeCount { graph := P.leftGraph, boundary := leftBoundary } <
      edgeCount S := by
  classical
  have hnot_nil : ¬ P.path.Nil :=
    SimpleGraph.Walk.not_nil_of_ne P.s_ne_t
  have he_path : s(P.s, P.path.snd) ∈ P.path.edges :=
    P.path.mk_start_snd_mem_edges hnot_nil
  simpa [edgeCount] using
    edgeFinset_card_lt_of_le_of_adj_not_adj P.leftGraph_le
      (P.path.edges_subset_edgeSet he_path)
      (fun hAdjCut => hAdjCut.2.2.2 he_path)

theorem GMIX24CutPath.rightGraph_edgeCount_lt
    [Fintype (Sym2 V)] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (rightBoundary : CyclicBoundary V) :
    edgeCount { graph := P.rightGraph, boundary := rightBoundary } <
      edgeCount S := by
  classical
  have hnot_nil : ¬ P.path.Nil :=
    SimpleGraph.Walk.not_nil_of_ne P.s_ne_t
  have he_path : s(P.s, P.path.snd) ∈ P.path.edges :=
    P.path.mk_start_snd_mem_edges hnot_nil
  simpa [edgeCount] using
    edgeFinset_card_lt_of_le_of_adj_not_adj P.rightGraph_le
      (P.path.edges_subset_edgeSet he_path)
      (fun hAdjCut => hAdjCut.2.2.2 he_path)

theorem GMIX24Split.canonicalOfNoCross_left_edgeCount_lt
    [Fintype (Sym2 V)] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    edgeCount (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety <
      edgeCount S := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.leftGraph_edgeCount_lt P.leftOrderedCutBoundary

theorem GMIX24Split.canonicalOfNoCross_right_edgeCount_lt
    [Fintype (Sym2 V)] [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    edgeCount (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety <
      edgeCount S := by
  simpa [GMIX24Split.canonicalOfNoCross,
    GMIX24Split.ofCanonicalGraphsOfNoCross, GMIX24Split.ofCanonicalGraphs,
    GMIX24Split.ofCanonical] using
    P.rightGraph_edgeCount_lt P.rightOrderedCutBoundary

/-- The well-founded induction core of GM IX `(2.4)`.

This theorem isolates exactly the recursive part of the source proof.  Once a
society can either be drawn rurally immediately, or be cut along the induced
path `P` into two strictly smaller societies satisfying the same hypotheses,
the theorem follows by induction on any supplied natural-valued height.  For
the paper proof, the height is `|E(G)|`; keeping it parametric lets the
edge-count lemmas for the concrete split be proved independently. -/
theorem GMIX24Statement.of_measure_induction
    (height : GeneralSociety V -> Nat)
    (hstep :
      forall (S : GeneralSociety V),
        S.ThreeConnected ->
          Not (Nonempty S.Cross) ->
            Not (Nonempty S.Tripod) ->
              Nonempty S.Rural ∨
                Exists fun R : GMIX24InductionStep S =>
                  height R.split.leftSociety < height S ∧
                    height R.split.rightSociety < height S) :
    GMIX24Statement (V := V) := by
  intro S hthree hcross htripod
  let Q : Nat -> Prop := fun n =>
    forall S : GeneralSociety V,
      height S = n ->
        S.ThreeConnected ->
          Not (Nonempty S.Cross) ->
            Not (Nonempty S.Tripod) ->
              Nonempty S.Rural
  have hQ : forall n : Nat, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hheight hthree hcross htripod
      rcases hstep S hthree hcross htripod with hrural | ⟨R, hleft, hright⟩
      · exact hrural
      · exact R.glues_rural
          (ih (height R.split.leftSociety) (by simpa [hheight] using hleft)
            R.split.leftSociety rfl
            R.left_three_connected R.left_cross_free R.left_tripod_free)
          (ih (height R.split.rightSociety) (by simpa [hheight] using hright)
            R.split.rightSociety rfl
            R.right_three_connected R.right_cross_free R.right_tripod_free)
  exact hQ (height S) S rfl hthree hcross htripod

/-- The same induction core, specialized to the paper's edge-count measure. -/
theorem GMIX24Statement.of_edge_induction [Fintype (Sym2 V)]
    (hstep :
      forall (S : GeneralSociety V),
        S.ThreeConnected ->
          Not (Nonempty S.Cross) ->
            Not (Nonempty S.Tripod) ->
              Nonempty S.Rural ∨
                Exists fun R : GMIX24InductionStep S =>
                  edgeCount R.split.leftSociety < edgeCount S ∧
                    edgeCount R.split.rightSociety < edgeCount S) :
    GMIX24Statement (V := V) :=
  GMIX24Statement.of_measure_induction edgeCount hstep

/-- A source-aligned version of the GM IX `(2.4)` induction.

Unlike `GMIX24Statement.of_edge_induction`, this theorem does not allow an
arbitrary recursive split.  In the non-rural case it requires the canonical
split obtained from the GM IX `(2.1)` cut path and the no-cross proof that the
two component-union sides are disjoint.  The remaining hypotheses are exactly
the source proof obligations for that canonical split. -/
theorem GMIX24Statement.of_canonical_edge_induction
    [Fintype (Sym2 V)] [DecidableEq V]
    (hstep :
      forall (S : GeneralSociety V)
        (_hthree : S.ThreeConnected)
        (hno_cross : Not (Nonempty S.Cross))
        (_hno_tripod : Not (Nonempty S.Tripod)),
        Not (Nonempty S.Rural) ->
          Exists fun P : GMIX24CutPath S =>
            let D := GMIX24Split.canonicalOfNoCross P hno_cross
            D.leftSociety.ThreeConnected ∧
              D.rightSociety.ThreeConnected ∧
                Not (Nonempty D.leftSociety.Cross) ∧
                  Not (Nonempty D.rightSociety.Cross) ∧
                    Not (Nonempty D.leftSociety.Tripod) ∧
                      Not (Nonempty D.rightSociety.Tripod) ∧
                        (Nonempty D.leftSociety.Rural ->
                          Nonempty D.rightSociety.Rural ->
                            Nonempty S.Rural)) :
    GMIX24Statement (V := V) := by
  classical
  refine GMIX24Statement.of_edge_induction (V := V) ?_
  intro S hthree hno_cross hno_tripod
  by_cases hrural : Nonempty S.Rural
  · exact Or.inl hrural
  · rcases hstep S hthree hno_cross hno_tripod hrural with
      ⟨P, hleft_three, hright_three, hleft_cross, hright_cross,
        hleft_tripod, hright_tripod, hglue⟩
    let D := GMIX24Split.canonicalOfNoCross P hno_cross
    refine Or.inr ⟨{
      cutPath := P
      split := D
      left_three_connected := ?_
      right_three_connected := ?_
      left_cross_free := ?_
      right_cross_free := ?_
      left_tripod_free := ?_
      right_tripod_free := ?_
      glues_rural := ?_
    }, ?_, ?_⟩
    · exact hleft_three
    · exact hright_three
    · exact hleft_cross
    · exact hright_cross
    · exact hleft_tripod
    · exact hright_tripod
    · exact hglue
    · simpa [D] using
        GMIX24Split.canonicalOfNoCross_left_edgeCount_lt P hno_cross
    · simpa [D] using
        GMIX24Split.canonicalOfNoCross_right_edgeCount_lt P hno_cross

/-- GM IX `(2.4)` from the source-level local conclusions.

This is the route matching the printed proof.  After the GM IX `(2.1)` cut
path has been chosen, the remaining local work is:

* the two canonical sides have no tripod;
* the two rural side drawings glue back to a rural drawing of the original
  society.

The older `K_5`/`K_{3,3}` mixed-obstruction packages are an implementation
device for the current weakened `Rural = IsPlanar` interface, not separate
statements in GM IX `(2.4)`, so this endpoint exposes the gluing theorem
directly. -/
theorem GMIX24Statement.of_side_tripod_free_rural_gluing
    [Fintype V] [Fintype (Sym2 V)] [DecidableEq V]
    (hdec : forall S : GeneralSociety V, DecidableRel S.graph.Adj)
    (hstep :
      forall (S : GeneralSociety V)
        (_hthree : S.ThreeConnected)
        (hno_cross : Not (Nonempty S.Cross))
        (_hno_tripod : Not (Nonempty S.Tripod)),
        3 <= S.boundarySet.ncard ->
        Not (Nonempty S.Rural) ->
        forall P : GMIX24CutPath S,
          Not (Nonempty
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) ∧
          Not (Nonempty
            (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod) ∧
          (Nonempty
              (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Rural ->
            Nonempty
              (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Rural ->
              Nonempty S.Rural)) :
    GMIX24Statement (V := V) := by
  classical
  refine GMIX24Statement.of_canonical_edge_induction (V := V) ?_
  intro S hthree hno_cross hno_tripod hnot_rural
  by_cases hsmall : S.boundarySet.ncard <= 2
  · exact False.elim
      (hnot_rural (rural_of_boundarySet_ncard_le_two S hthree hsmall))
  · have hlarge : 3 <= S.boundarySet.ncard := by
      omega
    letI : DecidableRel S.graph.Adj := hdec S
    obtain ⟨s, t, hs, ht, hst, q0, hq0_path, hq0_avoid⟩ :=
      hthree.exists_boundary_clean_path_avoiding_remainder_of_nonrural
        hnot_rural
    obtain ⟨P⟩ :=
      GMIX24CutPath.exists_of_threeConnected_boundary_path
        S hthree hs ht hst q0 hq0_path hq0_avoid
    rcases hstep S hthree hno_cross hno_tripod hlarge hnot_rural P with
      ⟨hleft_free, hright_reverse_free, hglue⟩
    have hright_free :
        Not (Nonempty
          (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod) := by
      intro hT
      rcases hT with ⟨Tside⟩
      have hSoc :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
            (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
        GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
      let Trev :
          (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
        hSoc.symm ▸ Tside
      exact hright_reverse_free ⟨Trev⟩
    refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using
        GMIX24Split.canonicalOfNoCross_left_three_connected
          P hno_cross hthree
    · simpa using
        GMIX24Split.canonicalOfNoCross_right_three_connected
          P hno_cross hthree
    · exact
        GMIX24Split.canonicalOfNoCross_left_cross_free_of_no_tripod
          P hno_cross hno_tripod
    · exact
        GMIX24Split.canonicalOfNoCross_right_cross_free_of_no_tripod
          P hno_cross hno_tripod
    · exact hleft_free
    · exact hright_free
    · exact hglue

end GeneralSociety

end Schematic.Math.GraphTheory
