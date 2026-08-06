import Schematic.Math.GraphTheory.Minors.Society.Terminal.ComponentEscapes.CrossPaths

/-!
Boundary-arc ordering and cross constructions from disjoint component paths.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- First mutual-contact normalization for two simple escape paths.

Starting from the second path, stop at its first vertex on the first path.
The resulting prefix is contained in the second path and meets the complete
first path only at its terminal vertex.  This is the precise uncrossing datum
used in the shared-component branch of the source side-tripod argument. -/
theorem exists_first_mutual_contact_prefix
    [DecidableEq V]
    {G : SimpleGraph V}
    {u a v b : V}
    (qLeft : G.Walk u a)
    (qRight : G.Walk v b)
    (hqRight_path : qRight.IsPath)
    (hcontact : Exists fun c : V =>
      c ∈ qLeft.support ∧ c ∈ qRight.support) :
    Exists fun c : V =>
      c ∈ qLeft.support ∧
        Exists fun initialPrefix : G.Walk v c =>
          initialPrefix.IsPath ∧
            (forall z : V,
              z ∈ initialPrefix.support -> z ∈ qRight.support) ∧
              forall z : V,
                z ∈ initialPrefix.support -> z ∈ qLeft.support -> z = c := by
  classical
  rcases hcontact with ⟨w, hwLeft, hwRight⟩
  let initial : G.Walk v w := qRight.takeUntil w hwRight
  have hinitial_path : initial.IsPath := by
    simpa [initial] using hqRight_path.takeUntil hwRight
  obtain ⟨c, hcInitial, hcLeft, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem (G := G) hinitial_path
      {z : V | z ∈ qLeft.support} (by simpa [initial] using hwLeft)
  let initialPrefix : G.Walk v c := initial.takeUntil c hcInitial
  have hprefix_subset_initial :
      forall z : V, z ∈ initialPrefix.support -> z ∈ initial.support := by
    intro z hz
    exact SimpleGraph.Walk.support_takeUntil_subset initial hcInitial hz
  have hinitial_subset_right :
      forall z : V, z ∈ initial.support -> z ∈ qRight.support := by
    intro z hz
    exact SimpleGraph.Walk.support_takeUntil_subset qRight hwRight
      (by simpa [initial] using hz)
  refine ⟨c, hcLeft, initialPrefix, ?_, ?_, ?_⟩
  · simpa [initialPrefix] using hinitial_path.takeUntil hcInitial
  · intro z hz
    exact hinitial_subset_right z (hprefix_subset_initial z hz)
  · intro z hzPrefix hzLeft
    exact hfirst z (by simpa [initialPrefix] using hzPrefix) hzLeft

/-- Two distinct vertices of the left boundary arc occur in one of the two
linear orders between the ends of the cut path.  Written cyclically, these are
exactly the two endpoint alternations used by the disjoint-tail cross in the
last case of the GM IX `(2.4)` side-tripod argument. -/
theorem GMIX24CutPath.leftBoundaryArc_pair_alternating
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {a b : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hab : a ≠ b) :
    (@CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s b a ∧
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary b P.s P.t) ∨
    (@CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s a b ∧
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary a P.s P.t) := by
  classical
  have haSide : a ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.leftBoundaryArc_subset_leftOrderedCutBoundary ha
  have hbSide : b ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.leftBoundaryArc_subset_leftOrderedCutBoundary hb
  have hsSide : P.s ∈ P.leftOrderedCutBoundary.vertexSet :=
    P.pathSet_subset_leftOrderedCutBoundary P.s_mem_pathSet
  have ha_lt_s :
      P.leftOrderedCutBoundary.indexOf a <
        P.leftOrderedCutBoundary.indexOf P.s :=
    P.leftOrderedCutBoundary_index_arc_lt_path ha P.s_mem_pathSet
  have hb_lt_s :
      P.leftOrderedCutBoundary.indexOf b <
        P.leftOrderedCutBoundary.indexOf P.s :=
    P.leftOrderedCutBoundary_index_arc_lt_path hb P.s_mem_pathSet
  have ha_lt_s_classical :
      @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary a <
        @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary P.s := by
    simpa [CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using ha_lt_s
  have hb_lt_s_classical :
      @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary b <
        @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary P.s := by
    simpa [CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hb_lt_s
  have hidx_ne :
      @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary a ≠
        @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary b :=
    @CyclicBoundary.indexOf_ne_of_ne V (Classical.decEq V)
      P.leftOrderedCutBoundary a b haSide hab
  have haOrig :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s P.t a := by
    simpa [GMIX24CutPath.leftBoundaryArc,
      CyclicBoundary.clockwiseArcSet,
      CyclicBoundary.ClockwiseOpenBetween,
      CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using ha
  have hbOrig :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s P.t b := by
    simpa [GMIX24CutPath.leftBoundaryArc,
      CyclicBoundary.clockwiseArcSet,
      CyclicBoundary.ClockwiseOpenBetween,
      CyclicBoundary.ClockwiseBetween, CyclicBoundary.indexOf,
      CyclicBoundary.list_idxOf_eq_classical] using hb
  by_cases hab_idx :
      @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary a <
        @CyclicBoundary.indexOf V (Classical.decEq V)
          P.leftOrderedCutBoundary b
  · left
    have hside :
        @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
          P.leftOrderedCutBoundary P.s b a := by
      apply GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
        P.leftOrderedCutBoundary haSide
      · omega
      · exact Or.inr (Nat.le_of_lt hab_idx)
      · exact P.leftBoundaryArc_ne_s ha
      · exact hab
    exact
      ⟨GMIX24Split.GMIX24CutPath.leftOrdered_clockwiseOpenBetween_original_of_arc_or_start P
          (Or.inr rfl) (Or.inl hb) (Or.inl ha)
          (P.leftBoundaryArc_ne_s hb).symm hside,
        GMIX24Split.CyclicBoundary.clockwiseOpenBetween_rotate_right
          P.s_mem_boundary P.t_mem_boundary hbOrig⟩
  · right
    have hba_idx :
        @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary b <
          @CyclicBoundary.indexOf V (Classical.decEq V)
            P.leftOrderedCutBoundary a := by
      omega
    have hside :
        @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
          P.leftOrderedCutBoundary P.s a b := by
      apply GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
        P.leftOrderedCutBoundary hbSide
      · omega
      · exact Or.inr (Nat.le_of_lt hba_idx)
      · exact P.leftBoundaryArc_ne_s hb
      · exact hab.symm
    exact
      ⟨GMIX24Split.GMIX24CutPath.leftOrdered_clockwiseOpenBetween_original_of_arc_or_start P
          (Or.inr rfl) (Or.inl ha) (Or.inl hb)
          (P.leftBoundaryArc_ne_s ha).symm hside,
        GMIX24Split.CyclicBoundary.clockwiseOpenBetween_rotate_right
          P.s_mem_boundary P.t_mem_boundary haOrig⟩

/-- Two disjoint paths from opposite ends of the induced cut path to two
vertices of its caught boundary arc form a cross in the indicated linear
order on that arc. -/
theorem GMIX24CutPath.crossOfDisjointArcPaths_leftOrder
    [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {a b : V}
    (firstPath : S.graph.Walk P.s a)
    (secondPath : S.graph.Walk b P.t)
    (ha : a ∈ P.leftBoundaryArc)
    (hb : b ∈ P.leftBoundaryArc)
    (hfirstPath : firstPath.IsPath)
    (hsecondPath : secondPath.IsPath)
    (hdisjoint :
      Disjoint {z : V | z ∈ firstPath.support}
        {z : V | z ∈ secondPath.support})
    (hfirst_order :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary P.s a b)
    (hsecond_order :
      @CyclicBoundary.ClockwiseOpenBetween V (Classical.decEq V)
        S.boundary a P.s P.t) :
    Nonempty S.Cross := by
  classical
  let endpoint : Fin 4 -> V
    | 0 => P.s
    | 1 => b
    | 2 => a
    | 3 => P.t
  have endpoint_mem : forall r : Fin 4, endpoint r ∈ S.boundarySet := by
    intro r
    fin_cases r
    · exact P.s_mem_boundary
    · exact P.leftBoundaryArc_subset hb
    · exact P.leftBoundaryArc_subset ha
    · exact P.t_mem_boundary
  have endpoint_injective : Function.Injective endpoint := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp only [endpoint] at hrs ⊢ <;>
      first
      | rfl
      | exact False.elim (hfirst_order.2.1 hrs.symm)
      | exact False.elim (hfirst_order.2.1 hrs)
      | exact False.elim (P.leftBoundaryArc_ne_s ha hrs.symm)
      | exact False.elim (P.leftBoundaryArc_ne_s ha hrs)
      | exact False.elim (P.s_ne_t hrs)
      | exact False.elim (P.s_ne_t hrs.symm)
      | exact False.elim (hfirst_order.2.2 hrs)
      | exact False.elim (hfirst_order.2.2 hrs.symm)
      | exact False.elim (P.leftBoundaryArc_ne_t hb hrs)
      | exact False.elim (P.leftBoundaryArc_ne_t hb hrs.symm)
      | exact False.elim (P.leftBoundaryArc_ne_t ha hrs)
      | exact False.elim (P.leftBoundaryArc_ne_t ha hrs.symm)
  let E : CrossEndpoints S.boundary := {
    endpoint := endpoint
    endpoint_mem := endpoint_mem
    endpoint_injective := endpoint_injective
    cyclic_alternating := by
      dsimp [CrossEndpointAlternating, endpoint]
      exact ⟨hfirst_order, hsecond_order⟩
  }
  exact Cross.of_disjoint_alternating_paths E hfirstPath hsecondPath hdisjoint

/-- If the two old common ends lie in distinct components after deleting the
induced cut path, the two caught-component escapes give an ambient cross.

The last-arm-contact splice lemmas make the two complete paths simple.  Their
supports are disjoint because the initial and final cut-path tails are
disjoint, every component piece lies outside the cut path, and distinct
components of the induced outside graph have disjoint supports.  The two
possible orders of the escape endpoints on the caught boundary arc are
handled by flipping the old tripod. -/
theorem Tripod.crossOfDistinctCommonEndpointComponents
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (Cleft : (S.graph.induce P.outside).ConnectedComponent)
    (hleftOutside : T.left ∈ P.outside)
    (hleftC : (⟨T.left, hleftOutside⟩ : P.outside) ∈ Cleft.supp)
    {a : V} (qLeft : S.graph.Walk T.left a)
    (ha : a ∈ P.leftBoundaryArc)
    (hqLeftPath : qLeft.IsPath)
    (hqLeftComponent : forall z : V, z ∈ qLeft.support ->
      z ∈ induceComponentSupport (G := S.graph) Cleft)
    (Cright : (S.graph.induce P.outside).ConnectedComponent)
    (hrightOutside : T.right ∈ P.outside)
    (hrightC : (⟨T.right, hrightOutside⟩ : P.outside) ∈ Cright.supp)
    {b : V} (qRight : S.graph.Walk T.right b)
    (hb : b ∈ P.leftBoundaryArc)
    (hqRightPath : qRight.IsPath)
    (hqRightComponent : forall z : V, z ∈ qRight.support ->
      z ∈ induceComponentSupport (G := S.graph) Cright)
    (hcomponents : Cleft ≠ Cright) :
    Nonempty S.Cross := by
  classical
  have hdisjoint_of_decompositions
      {a' b' : V}
      {Cfirst Csecond : (S.graph.induce P.outside).ConnectedComponent}
      (hCne : Cfirst ≠ Csecond)
      (firstPath : S.graph.Walk P.s a')
      (secondPath : S.graph.Walk b' P.t)
      (hfirstSupport : forall z : V, z ∈ firstPath.support ->
        z ∈ (P.pathTailToStart hi).support ∨
          z ∈ induceComponentSupport (G := S.graph) Cfirst)
      (hsecondSupport : forall z : V, z ∈ secondPath.support ->
        z ∈ (P.pathTailToEnd hk).support ∨
          z ∈ induceComponentSupport (G := S.graph) Csecond) :
      Disjoint {z : V | z ∈ firstPath.support}
        {z : V | z ∈ secondPath.support} := by
    rw [Set.disjoint_left]
    intro z hzFirst hzSecond
    rcases hfirstSupport z hzFirst with hzStart | hzFirstC <;>
      rcases hsecondSupport z hzSecond with hzEnd | hzSecondC
    · exact Set.disjoint_left.mp
        (P.pathTailToStart_support_disjoint_pathTailToEnd
          hi hk (lt_trans hij_order hjk_order)) hzStart hzEnd
    · exact
        ((induceComponentSupport_subset (G := S.graph) Csecond hzSecondC).2
          (P.pathTailToStart_support_subset_pathSet hi z hzStart))
    · exact
        ((induceComponentSupport_subset (G := S.graph) Cfirst hzFirstC).2
          (P.pathTailToEnd_support_subset_pathSet hk z hzEnd))
    · exact Set.disjoint_left.mp
        (induceComponentSupport_disjoint_of_ne (G := S.graph) hCne)
        hzFirstC hzSecondC
  have hab : a ≠ b := by
    intro hab
    exact Set.disjoint_left.mp
      (induceComponentSupport_disjoint_of_ne (G := S.graph) hcomponents)
      (hqLeftComponent a qLeft.end_mem_support)
      (hqRightComponent a (by simp [hab]))
  rcases
      GMIX24SourceProof.GMIX24CutPath.leftBoundaryArc_pair_alternating
        (S := S) P ha hb hab with
    hrightOrder | hleftOrder
  · let U :
        (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod :=
      T.flip
    let qFirst : S.graph.Walk U.left b :=
      qRight.copy (by simp [U]) rfl
    let qSecond : S.graph.Walk U.right a :=
      qLeft.copy (by simp [U]) rfl
    have hpath_contacts_U :
        forall z : V, z ∈ P.pathSet -> z ∈ U.vertexSet ->
          Exists fun m : Fin 3 => z = U.boundary m := by
      simpa [U] using T.pathContacts_flip hpath_contacts
    have hrightOutside_U : U.left ∈ P.outside := by
      simpa [U] using hrightOutside
    have hleftOutside_U : U.right ∈ P.outside := by
      simpa [U] using hleftOutside
    have hrightC_U :
        (⟨U.left, hrightOutside_U⟩ : P.outside) ∈ Cright.supp := by
      simpa [U] using hrightC
    have hleftC_U :
        (⟨U.right, hleftOutside_U⟩ : P.outside) ∈ Cleft.supp := by
      simpa [U] using hleftC
    have hqFirstPath : qFirst.IsPath := by
      simpa [qFirst] using
        (SimpleGraph.Walk.isPath_copy qRight (by simp) rfl).mpr
          hqRightPath
    have hqSecondPath : qSecond.IsPath := by
      simpa [qSecond] using
        (SimpleGraph.Walk.isPath_copy qLeft (by simp) rfl).mpr
          hqLeftPath
    have hqFirstComponent : forall z : V, z ∈ qFirst.support ->
        z ∈ induceComponentSupport (G := S.graph) Cright := by
      intro z hz
      exact hqRightComponent z (by
        simpa [qFirst, SimpleGraph.Walk.support_copy] using hz)
    have hqSecondComponent : forall z : V, z ∈ qSecond.support ->
        z ∈ induceComponentSupport (G := S.graph) Cleft := by
      intro z hz
      exact hqLeftComponent z (by
        simpa [qSecond, SimpleGraph.Walk.support_copy] using hz)
    obtain ⟨firstPath, hfirstPath, hfirstSupport⟩ :=
      GMIX24SourceProof.Tripod.exists_leftComponentCrossPath hno_cross P U
        (by simpa [U] using hi) (by simpa [U] using hleg_i_nil)
        hpath_contacts_U Cright hrightOutside_U hrightC_U qFirst
        hqFirstPath hqFirstComponent
    obtain ⟨secondPath, hsecondPath, hsecondSupport⟩ :=
      GMIX24SourceProof.Tripod.exists_rightComponentCrossPath hno_cross P U
        (by simpa [U] using hk) (by simpa [U] using hleg_k_nil)
        hpath_contacts_U Cleft hleftOutside_U hleftC_U qSecond
        hqSecondPath hqSecondComponent
    exact GMIX24SourceProof.GMIX24CutPath.crossOfDisjointArcPaths_leftOrder
      P firstPath secondPath hb ha
      hfirstPath hsecondPath
      (hdisjoint_of_decompositions hcomponents.symm firstPath secondPath
        hfirstSupport hsecondSupport)
      hrightOrder.1 hrightOrder.2
  · obtain ⟨firstPath, hfirstPath, hfirstSupport⟩ :=
      GMIX24SourceProof.Tripod.exists_leftComponentCrossPath hno_cross P T
        hi hleg_i_nil
        hpath_contacts Cleft hleftOutside hleftC qLeft hqLeftPath
        hqLeftComponent
    obtain ⟨secondPath, hsecondPath, hsecondSupport⟩ :=
      GMIX24SourceProof.Tripod.exists_rightComponentCrossPath hno_cross P T
        hk hleg_k_nil
        hpath_contacts Cright hrightOutside hrightC qRight hqRightPath
        hqRightComponent
    exact GMIX24SourceProof.GMIX24CutPath.crossOfDisjointArcPaths_leftOrder
      P firstPath secondPath ha hb
      hfirstPath hsecondPath
      (hdisjoint_of_decompositions hcomponents firstPath secondPath
        hfirstSupport hsecondSupport)
      hleftOrder.1 hleftOrder.2

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
