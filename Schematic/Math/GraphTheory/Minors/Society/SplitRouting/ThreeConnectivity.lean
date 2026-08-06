import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.MaximalSources
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.TripodCases

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_source_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    GMIX24Split.LeftMaximalCrossSourceCases P hno_cross X := by
  constructor
  · intro l hl h_off hothers_path x y r hx_first hy_second hr_path
      hclean_first hclean_second _hr_side hr_outside
    rcases hl with hl | hl
    · subst l
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_tripod
          P hno_cross X h_off hothers_path r hx_first hy_second hr_path
          hclean_first hclean_second hr_outside
    · subst l
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint3_first_tripod
          P hno_cross X h_off hothers_path r hx_first hy_second hr_path
          hclean_first hclean_second hr_outside
  · intro l hl h_off hothers_path x y r hx_second hy_first hr_path
      hclean_second hclean_first _hr_side hr_outside
    rcases hl with hl | hl
    · subst l
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint0_second_tripod
          P hno_cross X h_off hothers_path r hx_second hy_first hr_path
          hclean_second hclean_first hr_outside
    · subst l
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint2_second_tripod
          P hno_cross X h_off hothers_path r hx_second hy_first hr_path
          hclean_second hclean_first hr_outside

theorem canonicalOfNoCross_right_cross_source_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    GMIX24Split.RightMaximalCrossSourceCases P hno_cross X := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety =
        (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety :=
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm
  let Xrev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Cross :=
    hSoc ▸ X
  have hcases :
      GMIX24Split.LeftMaximalCrossSourceCases P.reverse hno_cross Xrev :=
    GMIX24Split.canonicalOfNoCross_left_cross_source_cases
      P.reverse hno_cross Xrev
  simpa [GMIX24Split.RightMaximalCrossSourceCases,
    GMIX24Split.LeftMaximalCrossSourceCases, Xrev] using hcases

theorem canonicalOfNoCross_left_cross_free_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod)) :
    Not (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) := by
  intro hcross
  obtain ⟨X, hmax, _hcount_cases⟩ :=
    GMIX24Split.exists_left_crossOffPathCountMaximal_with_count_cases_of_nonempty
      P hno_cross hcross
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_source_cases
        P hno_cross X with
    ⟨htripod_first, htripod_second⟩
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_obstruction_of_maximal_from_source_cases
        P hno_cross X hmax htripod_first htripod_second with hcrossS | htripodS
  · exact hno_cross hcrossS
  · exact hno_tripod htripodS

theorem canonicalOfNoCross_right_cross_free_of_no_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod)) :
    Not (Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) := by
  simpa using
    (GMIX24Split.canonicalOfNoCross_left_cross_free_of_no_tripod
      P.reverse hno_cross hno_tripod)

theorem canonicalOfNoCross_left_cross_has_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet := by
  by_contra hnone
  push Not at hnone
  exact hno_cross
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_of_all_endpoints_off_path_from_side_order
      P hno_cross X hnone)

theorem canonicalOfNoCross_right_cross_has_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_has_path_endpoint
      P.reverse hno_cross Xrev)

theorem canonicalOfNoCross_left_cross_lift_or_has_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross) :
    Nonempty S.Cross ∨
      Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet := by
  by_cases hsome : Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet
  · exact Or.inr hsome
  · left
    push Not at hsome
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_lift_of_all_endpoints_off_path_from_side_order
        P hno_cross X hsome

theorem canonicalOfNoCross_right_cross_lift_or_has_path_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross) :
    Nonempty S.Cross ∨
      Exists fun i : Fin 4 => X.endpoints.endpoint i ∈ P.pathSet := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross] using
    (GMIX24Split.canonicalOfNoCross_left_cross_lift_or_has_path_endpoint
      P.reverse hno_cross Xrev)

theorem canonicalOfNoCross_left_three_connected
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hthree : S.ThreeConnected) :
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.ThreeConnected := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  change D.leftSociety.ThreeConnected
  intro T hboundary hright horder
  have hD_boundary : D.leftSociety.boundarySet = P.leftCutBoundarySet := by
    simp [D,
      GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross
    ]
  have hleftArc_Tleft : P.leftBoundaryArc ⊆ T.left := by
    intro v hv
    exact hboundary (by
      rw [hD_boundary]
      exact Or.inl hv)
  have hpath_Tleft : P.pathSet ⊆ T.left := by
    intro v hv
    exact hboundary (by
      rw [hD_boundary]
      exact Or.inr hv)
  let U : Separation S.graph := {
    left := T.left ∪ P.rightSide
    right := T.right \ P.rightSide
    covers := by
      ext v
      constructor
      · intro _hv
        exact Set.mem_univ v
      · intro _hv
        by_cases hvRight : v ∈ P.rightSide
        · exact Or.inl (Or.inr hvRight)
        · rcases T.mem_left_or_right v with hvTLeft | hvTRight
          · exact Or.inl (Or.inl hvTLeft)
          · exact Or.inr ⟨hvTRight, hvRight⟩
    no_cross := by
      intro a b haU haNotURight hbU hbNotULeft hab
      have hbTRight : b ∈ T.right := hbU.1
      have hbNotRightSide : b ∉ P.rightSide := hbU.2
      have hbNotTLeft : b ∉ T.left := by
        intro hbTLeft
        exact hbNotULeft (Or.inl hbTLeft)
      have hbNotPath : b ∉ P.pathSet := by
        intro hbPath
        exact hbNotTLeft (hpath_Tleft hbPath)
      have hbOutside : b ∈ P.outside := by
        exact ⟨Or.inl hab.right_mem_support, by
          simpa [GMIX24CutPath.pathSet] using hbNotPath⟩
      have hbLeftSide : b ∈ P.leftSide := by
        rcases P.outside_subset_leftSide_union_rightSide hbOutside with hbLeft | hbRight
        · exact hbLeft
        · exact False.elim (hbNotRightSide hbRight)
      by_cases haRightSide : a ∈ P.rightSide
      · exact (P.not_adj_leftSide_rightSide_of_no_cross hno_cross
          hbLeftSide haRightSide) hab.symm
      · have haTLeft : a ∈ T.left := by
          rcases haU with haTLeft | haRight
          · exact haTLeft
          · exact False.elim (haRightSide haRight)
        have haNotTRight : a ∉ T.right := by
          intro haTRight
          exact haNotURight ⟨haTRight, haRightSide⟩
        have heNotPath : s(a, b) ∉ P.path.edges := by
          intro he
          exact hbNotPath (P.path.snd_mem_support_of_mem_edges he)
        have habLeft : P.leftGraph.Adj a b :=
          ⟨hab, haRightSide, hbNotRightSide, heNotPath⟩
        exact T.no_cross haTLeft haNotTRight hbTRight hbNotTLeft habLeft
  }
  refine hthree U ?_ ?_ ?_
  · intro v hvBoundary
    by_cases hvs : v = P.s
    · exact Or.inl (hpath_Tleft (by simp [GMIX24CutPath.pathSet, hvs]))
    · by_cases hvt : v = P.t
      · exact Or.inl (hpath_Tleft (by simp [GMIX24CutPath.pathSet, hvt]))
      · have hvArc : v ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
          rw [P.leftBoundaryArc_union_right]
          exact ⟨hvBoundary, by
            intro hvst
            rcases hvst with hvs' | hvt'
            · exact hvs hvs'
            · exact hvt hvt'⟩
        rcases hvArc with hvLeft | hvRight
        · exact Or.inl (hleftArc_Tleft hvLeft)
        · exact Or.inr (P.rightBoundaryArc_subset_rightSide hvRight)
  · rcases hright with ⟨v, hvDiff, hvActive⟩
    have hvNotRightSide : v ∉ P.rightSide := by
      exact Set.disjoint_left.mp
        (GMIX24Split.canonicalOfNoCross_leftSociety_activeSet_disjoint_rightSide
          P hno_cross) hvActive
    have hvActiveS : v ∈ S.activeSet := by
      dsimp [GeneralSociety.activeSet] at hvActive ⊢
      rcases hvActive with hvSupport | hvBoundary
      · exact Or.inl
          (SimpleGraph.support_mono
            (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
            hvSupport)
      · have hvCut : v ∈ P.leftCutBoundarySet := by
          rw [← hD_boundary]
          exact hvBoundary
        rcases hvCut with hvArc | hvPath
        · exact Or.inr (P.leftBoundaryArc_subset hvArc)
        · exact Or.inl
            (SimpleGraph.mem_support_of_mem_walk_support P.path
              (SimpleGraph.Walk.not_nil_of_ne P.s_ne_t)
              (by simpa [GMIX24CutPath.pathSet] using hvPath))
    refine ⟨v, ?_, hvActiveS⟩
    · exact ⟨⟨hvDiff.1, hvNotRightSide⟩, by
        intro hvLeft
        rcases hvLeft with hvTLeft | hvRight
        · exact hvDiff.2 hvTLeft
        · exact hvNotRightSide hvRight⟩
  · rcases horder with ⟨F, hF, hFcard⟩
    refine ⟨F.filter (fun v => v ∉ P.rightSide), ?_, ?_⟩
    · ext v
      by_cases hvR : v ∈ P.rightSide
      · simp [Separation.separator, U, hvR]
      · have hvF : v ∈ F ↔ v ∈ T.separator := by
          change v ∈ (F : Set V) ↔ v ∈ T.separator
          rw [hF]
        simp [Separation.separator, U, hvR, hvF, and_comm]
    · exact (Finset.card_filter_le _ _).trans hFcard

theorem canonicalOfNoCross_right_three_connected
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hthree : S.ThreeConnected) :
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.ThreeConnected := by
  simpa using
    (GMIX24Split.canonicalOfNoCross_left_three_connected
      P.reverse hno_cross hthree)

theorem canonicalOfNoCross_left_tripod_lift_of_boundary_mem
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hboundary : forall i : Fin 3, T.boundary i ∈ S.boundarySet) :
    Nonempty S.Tripod :=
  ⟨T.lift_of_le
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    hboundary⟩

theorem canonicalOfNoCross_right_tripod_lift_of_boundary_mem
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hboundary : forall i : Fin 3, T.boundary i ∈ S.boundarySet) :
    Nonempty S.Tripod :=
  ⟨T.lift_of_le
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le
    hboundary⟩

theorem canonicalOfNoCross_left_tripod_lift_of_all_feet_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hoffPath : forall i : Fin 3, T.boundary i ∉ P.pathSet) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_boundary_mem
    P hno_cross T (by
      intro i
      exact P.leftBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
          P hno_cross T i).mp (hoffPath i)))

theorem canonicalOfNoCross_right_tripod_lift_of_all_feet_off_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hoffPath : forall i : Fin 3, T.boundary i ∉ P.pathSet) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_of_boundary_mem
    P hno_cross T (by
      intro i
      exact P.rightBoundaryArc_subset
        ((GMIX24Split.canonicalOfNoCross_right_tripod_boundary_not_path_iff_arc
          P hno_cross T i).mp (hoffPath i)))

/-- Left-side multi-foot tripod lift for the canonical GM IX split.

This is the direct split-level form of `Tripod.liftAppendBoundaryTails`.
It is used when several side-tripod feet lie on the cut path, so no single
one-foot replacement lemma has the right side conditions. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundary_tails
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (newBoundary : Fin 3 -> V)
    (hnew_boundary : forall i : Fin 3, newBoundary i ∈ S.boundarySet)
    (hnew_injective : Function.Injective newBoundary)
    (tail : forall i : Fin 3, S.graph.Walk (T.boundary i) (newBoundary i))
    (htail_path : forall i : Fin 3, (tail i).IsPath)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (tail i).support -> z ∈ T.vertexSet -> z = T.boundary i)
    (htail_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint {z : V | z ∈ (tail i).support}
          {z : V | z ∈ (tail j).support}) :
    Nonempty S.Tripod :=
  ⟨T.liftAppendBoundaryTails
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    newBoundary hnew_boundary hnew_injective tail htail_path
    htail_clean htail_disjoint⟩

/-- Right-side multi-foot tripod lift for the canonical GM IX split. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundary_tails
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (newBoundary : Fin 3 -> V)
    (hnew_boundary : forall i : Fin 3, newBoundary i ∈ S.boundarySet)
    (hnew_injective : Function.Injective newBoundary)
    (tail : forall i : Fin 3, S.graph.Walk (T.boundary i) (newBoundary i))
    (htail_path : forall i : Fin 3, (tail i).IsPath)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (tail i).support -> z ∈ T.vertexSet -> z = T.boundary i)
    (htail_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint {z : V | z ∈ (tail i).support}
          {z : V | z ∈ (tail j).support}) :
    Nonempty S.Tripod :=
  ⟨T.liftAppendBoundaryTails
    (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety_graph_le
    newBoundary hnew_boundary hnew_injective tail htail_path
    htail_clean htail_disjoint⟩



end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

