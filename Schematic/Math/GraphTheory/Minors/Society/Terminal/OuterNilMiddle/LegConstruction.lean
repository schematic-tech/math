import Schematic.Math.GraphTheory.Minors.Society.Terminal.OuterNilMiddle.RimConstruction

/-!
Rebuilt leg definitions, path properties, and pairwise disjointness.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Ambient legs for the nontrivial-middle rebuilt theta.

The outer attachments run to the two ends of the induced cut path.  The
middle attachment runs back along its old left arm and then follows the clean
outside path to the old boundary arc. -/
def Tripod.outerNilMiddleNonNilCommonLeftLeg
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk
        (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
          T i j k r)
        (P.boundaryTriple a r)
  | 0 =>
      (P.pathTailToStart hi).copy
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl
  | 1 => ((T.leftToAttach j).reverse.mapLe hgraph).append q
  | 2 =>
      (P.pathTailToEnd hk).copy
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl

/-- The three ambient legs in the nontrivial-middle rebuilt theta are simple
paths.  The only non-immediate case is the middle leg: its old left rim arm
meets the clean outside tail only at their common endpoint `T.left`. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = T.left) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
        P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToStart hi)
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl).mpr
        (P.pathTailToStart_isPath hi)
  · change (((T.leftToAttach j).reverse.mapLe hgraph).append q).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (SimpleGraph.Walk.IsPath.mapLe hgraph
        (T.leftToAttach_isPath j).reverse)
      hq_path ?_
    intro z hzArm hzq
    apply hq_clean z hzq
    apply T.rim_mem_vertexSet
    apply T.leftToAttach_support_subset_rim j
    have hzReverse : z ∈ (T.leftToAttach j).reverse.support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    simpa [SimpleGraph.Walk.support_reverse] using hzReverse
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToEnd hk)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
        (P.pathTailToEnd_isPath hk)

/-- Path criterion for the rebuilt legs using only the exact middle-arm
contact condition.  This weaker form is needed when the outside path is
prefixed by an old outer rim arm and is therefore not clean against the whole
old tripod. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_isPath_of_leftArm_clean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath)
    (hq_leftArm_clean :
      forall z : V, z ∈ q.support -> z ∈ (T.leftToAttach j).support ->
        z = T.left) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
        P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToStart hi)
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl).mpr
        (P.pathTailToStart_isPath hi)
  · change (((T.leftToAttach j).reverse.mapLe hgraph).append q).IsPath
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (SimpleGraph.Walk.IsPath.mapLe hgraph
        (T.leftToAttach_isPath j).reverse)
      hq_path ?_
    intro z hzArm hzq
    apply hq_leftArm_clean z hzq
    have hzReverse : z ∈ (T.leftToAttach j).reverse.support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    simpa [SimpleGraph.Walk.support_reverse] using hzReverse
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg] using
      (SimpleGraph.Walk.isPath_copy
        (P.pathTailToEnd hk)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
        (P.pathTailToEnd_isPath hk)

/-- Support decomposition for the rebuilt middle leg. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLeg_one_support_cases
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a z : V}
    (q : S.graph.Walk T.left a)
    (hz : z ∈
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
        P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 1).support) :
    z ∈ (T.leftToAttach j).support ∨ z ∈ q.support := by
  change z ∈ (((T.leftToAttach j).reverse.mapLe hgraph).append q).support at hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hzArm | hzq
  · left
    have hzReverse : z ∈ (T.leftToAttach j).reverse.support := by
      simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    simpa [SimpleGraph.Walk.support_reverse] using hzReverse
  · exact Or.inr hzq

/-- The three ambient legs in the nontrivial-middle rebuilt theta are
pairwise vertex-disjoint. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftLegs_pairwise_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V}
    (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
            P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q r).support}
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
            P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q s).support} := by
  have h01 :
      Disjoint
        {z : V | z ∈ (P.pathTailToStart hi).support}
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
            P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 1).support} := by
    rw [Set.disjoint_left]
    intro z hzTail hzMiddle
    rcases
        GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_one_support_cases
          P T hgraph hleg_i_nil hleg_k_nil hi hk q hzMiddle with
      hzArm | hzq
    · have hzRim : z ∈ (T.rim j).support :=
        T.leftToAttach_support_subset_rim j hzArm
      have hzi : z = T.boundary i :=
        P.pathTailToStart_clean_first_foot_of_path_contacts
          T hij hik hjk hi hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet (i := j) hzRim)
      exact T.boundary_not_mem_rim_of_ne_index hij
        (by simpa [hzi] using hzRim)
    · have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hzTail
      exact (hq_outside z hzq).2 hzPath
  have h12 :
      Disjoint
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg
            P T hgraph (j := j) hleg_i_nil hleg_k_nil hi hk q 1).support}
        {z : V | z ∈ (P.pathTailToEnd hk).support} := by
    rw [Set.disjoint_left]
    intro z hzMiddle hzTail
    rcases
        GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftLeg_one_support_cases
          P T hgraph hleg_i_nil hleg_k_nil hi hk q hzMiddle with
      hzArm | hzq
    · have hzRim : z ∈ (T.rim j).support :=
        T.leftToAttach_support_subset_rim j hzArm
      have hzk : z = T.boundary k :=
        P.pathTailToEnd_clean_last_foot_of_path_contacts
          T hij hik hjk hk hij_order hjk_order hpath_contacts hzTail
          (T.rim_mem_vertexSet (i := j) hzRim)
      exact T.boundary_not_mem_rim_of_ne_index (fun h => hjk h.symm)
        (by simpa [hzk] using hzRim)
    · have hzPath : z ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hk z hzTail
      exact (hq_outside z hzq).2 hzPath
  have h02 :
      Disjoint
        {z : V | z ∈ (P.pathTailToStart hi).support}
        {z : V | z ∈ (P.pathTailToEnd hk).support} :=
    P.pathTailToStart_support_disjoint_pathTailToEnd
      hi hk (lt_trans hij_order hjk_order)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg,
      SimpleGraph.Walk.support_copy] using h01
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg,
      SimpleGraph.Walk.support_copy] using h02
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg,
      SimpleGraph.Walk.support_copy] using h01.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg,
      SimpleGraph.Walk.support_copy] using h12
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg,
      SimpleGraph.Walk.support_copy] using h02.symm
  · simpa [Tripod.outerNilMiddleNonNilCommonLeftLeg,
      SimpleGraph.Walk.support_copy] using h12.symm
  · exact False.elim (hrs rfl)


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
