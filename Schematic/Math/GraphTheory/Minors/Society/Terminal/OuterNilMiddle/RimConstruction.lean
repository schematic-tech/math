import Schematic.Math.GraphTheory.Minors.Society.Terminal.Symmetry

/-!
Rebuilt rim definitions and path properties for the outer-nil, middle-non-nil branch.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

/-- Rebuilt theta for the double-outer-collapsed branch when the middle leg is
nontrivial and the clean outside path starts at the old left common end.

The new theta runs from the old right common end to the middle cut-path foot.
Its two outer rims use the old right arms followed by the two cut-path
intervals, while its middle rim uses the old middle right arm followed by the
old middle leg.  Nontriviality of that middle leg makes its old attachment an
internal vertex of the middle rebuilt rim. -/
def Tripod.outerNilMiddleNonNilCommonLeftRim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    Fin 3 -> S.graph.Walk T.right (T.boundary j)
  | 0 =>
      T.rightToBoundaryViaLegTail hgraph i
        (P.pathSegmentBetween hi hj (Nat.le_of_lt hij_order))
  | 1 =>
      T.rightToBoundaryViaLegTail hgraph j (SimpleGraph.Walk.nil)
  | 2 =>
      T.rightToBoundaryViaLegTail hgraph k
        (P.pathSegmentBetween hj hk (Nat.le_of_lt hjk_order)).reverse

/-- Reindex-aware form of the attachments used by the rebuilt theta. -/
def Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
    {H : GeneralSociety V} (T : H.Tripod)
    (i j k : Fin 3) : Fin 3 -> V
  | 0 => T.attach i
  | 1 => T.attach j
  | 2 => T.attach k

/-- Branch-local path criterion for extending a right rim arm through its old
leg.  Unlike `rightToBoundaryViaLegTail_isPath`, this only asks the new tail
to avoid the branch being extended.  That is the exact condition needed when
the tail ends at a selected foot on another old branch. -/
theorem Tripod.rightToBoundaryViaLegTail_isPath_of_branch_clean
    [DecidableEq V]
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    (r : Fin 3)
    {y : V}
    (tail : S.graph.Walk (T.boundary r) y)
    (htail_path : tail.IsPath)
    (htail_clean :
      forall z : V, z ∈ tail.support ->
        (z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
          z = T.boundary r) :
    (T.rightToBoundaryViaLegTail hgraph r tail).IsPath := by
  let arm : S.graph.Walk T.right (T.attach r) :=
    (T.rightToAttach r).mapLe hgraph
  let oldLeg : S.graph.Walk (T.attach r) (T.boundary r) :=
    (T.leg r).mapLe hgraph
  have harm_path : arm.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.rightToAttach_isPath r)
  have holdLeg_path : oldLeg.IsPath :=
    SimpleGraph.Walk.IsPath.mapLe hgraph (T.leg_isPath r)
  have hfirst : (arm.append oldLeg).IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      harm_path holdLeg_path ?_
    intro z hzArm hzLeg
    have hzRim : z ∈ (T.rim r).support := by
      apply T.rightToAttach_support_subset_rim r
      simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    have hzLegOld : z ∈ (T.leg r).support := by
      simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
    exact T.legs_meet_rims_only_at_attach r r z hzLegOld hzRim
  change (arm.append (oldLeg.append tail)).IsPath
  rw [SimpleGraph.Walk.append_assoc]
  refine Walk.IsPath.append_of_support_inter_eq_endpoint hfirst htail_path ?_
  intro z hzFirst hzTail
  rw [SimpleGraph.Walk.mem_support_append_iff] at hzFirst
  rcases hzFirst with hzArm | hzLeg
  · have hzRim : z ∈ (T.rim r).support := by
      apply T.rightToAttach_support_subset_rim r
      simpa [arm, SimpleGraph.Walk.support_mapLe_eq_support] using hzArm
    exact htail_clean z hzTail (Or.inl hzRim)
  · have hzLegOld : z ∈ (T.leg r).support := by
      simpa [oldLeg, SimpleGraph.Walk.support_mapLe_eq_support] using hzLeg
    exact htail_clean z hzTail (Or.inr hzLegOld)

/-- A selected foot can lie on the rim or leg of only its own branch. -/
theorem Tripod.boundary_index_eq_of_mem_rim_or_leg
    {H : GeneralSociety V}
    (T : H.Tripod) {m r : Fin 3}
    (hmem : T.boundary m ∈ (T.rim r).support ∨
      T.boundary m ∈ (T.leg r).support) :
    m = r := by
  by_contra hmr
  rcases hmem with hrim | hleg
  · exact T.boundary_not_mem_rim_of_ne_index hmr hrim
  · exact Set.disjoint_left.mp
      (T.legs_pairwise_disjoint r m (fun h => hmr h.symm))
      hleg (T.leg m).end_mem_support

/-- The three right-based rebuilt rims are simple paths. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftRim_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
        P T hgraph hi hj hk
        hij_order hjk_order r).IsPath := by
  intro r
  fin_cases r
  · apply
      GMIX24SourceProof.Tripod.rightToBoundaryViaLegTail_isPath_of_branch_clean
        T hgraph i
    · exact P.pathSegmentBetween_isPath hi hj (Nat.le_of_lt hij_order)
    · intro z hzSegment hzBranch
      have hzT : z ∈ T.vertexSet := by
        rcases hzBranch with hzRim | hzLeg
        · exact T.rim_mem_vertexSet hzRim
        · exact T.leg_mem_vertexSet hzLeg
      rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts
            T hij hik hjk hi hj hij_order hjk_order hpath_contacts
            hzSegment hzT with hzi | hzj
      · exact hzi
      · have hji : j = i :=
          GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
            (by simpa [hzj] using hzBranch)
        exact False.elim (hij hji.symm)
  · apply
      GMIX24SourceProof.Tripod.rightToBoundaryViaLegTail_isPath_of_branch_clean
        T hgraph j
    · exact SimpleGraph.Walk.IsPath.nil
    · intro z hz _hzBranch
      simpa using hz
  · apply
      GMIX24SourceProof.Tripod.rightToBoundaryViaLegTail_isPath_of_branch_clean
        T hgraph k
    · exact (P.pathSegmentBetween_isPath hj hk
          (Nat.le_of_lt hjk_order)).reverse
    · intro z hzSegmentReverse hzBranch
      have hzSegment :
          z ∈ (P.pathSegmentBetween hj hk
            (Nat.le_of_lt hjk_order)).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hzSegmentReverse
      have hzT : z ∈ T.vertexSet := by
        rcases hzBranch with hzRim | hzLeg
        · exact T.rim_mem_vertexSet hzRim
        · exact T.leg_mem_vertexSet hzLeg
      rcases
          P.pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
            T hij hik hjk hj hk hij_order hjk_order hpath_contacts
            hzSegment hzT with hzj | hzk
      · have hjk' : j = k :=
          GMIX24SourceProof.Tripod.boundary_index_eq_of_mem_rim_or_leg T
            (by simpa [hzj] using hzBranch)
        exact False.elim (hjk hjk')
      · exact hzk

/-- The three old attachments are internal vertices of the corresponding
right-based rebuilt rims.  The nontrivial middle-leg hypothesis is used only
for the middle rim; the two outer rims continue along nonempty cut intervals. -/
theorem Tripod.outerNilMiddleNonNilCommonLeftAttach_mem_rim
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph <= S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_j_not_nil : Not (T.leg j).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    forall r : Fin 3,
      GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftAttachOrdered
          T i j k r ∈
        Walk.InternalVertices
          (GMIX24SourceProof.Tripod.outerNilMiddleNonNilCommonLeftRim
            P T hgraph hi hj hk
            hij_order hjk_order r) := by
  intro r
  have hmem (m : Fin 3) {y : V}
      (tail : S.graph.Walk (T.boundary m) y) :
      T.attach m ∈ (T.rightToBoundaryViaLegTail hgraph m tail).support := by
    rw [Tripod.rightToBoundaryViaLegTail,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (by
      simp [SimpleGraph.Walk.support_mapLe_eq_support])
  fin_cases r
  · refine ⟨hmem i _, (T.attach_mem_rim i).2.2, ?_⟩
    have hbi : T.boundary i = T.attach i :=
      (T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil
    intro hai_bj
    exact hij (T.boundary_injective (hbi.trans hai_bj))
  · refine ⟨hmem j _, (T.attach_mem_rim j).2.2, ?_⟩
    intro haj_bj
    exact hleg_j_not_nil
      ((T.boundary_eq_attach_iff_leg_nil j).mp haj_bj.symm)
  · refine ⟨hmem k _, (T.attach_mem_rim k).2.2, ?_⟩
    have hbk : T.boundary k = T.attach k :=
      (T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil
    intro hak_bj
    exact hjk (T.boundary_injective (hbk.trans hak_bj).symm)


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
