import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.PathAssembly
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.Attachments
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.LegDisjointness
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.LegZeroRimContacts
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.LegOneRimContacts
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.LegTwoRimContacts
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod.RimDisjointness

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_endpoint1_first_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h1_off : X.endpoints.endpoint 1 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V}
    (r : S.graph.Walk x y)
    (hx_first : x ∈ X.firstPath.support)
    (hy_second : y ∈ X.secondPath.support)
    (hr_path : r.IsPath)
    (hclean_first :
      forall w : V, w ∈ r.support ->
        w ∈ X.firstPath.support -> w = x)
    (hclean_second :
      forall w : V, w ∈ r.support ->
        w ∈ X.secondPath.support -> w = y)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    Nonempty S.Tripod := by
  classical
  let D := GMIX24Split.canonicalOfNoCross P hno_cross
  let F : S.graph.Walk (X.endpoints.endpoint 0) (X.endpoints.endpoint 2) :=
    X.firstPath.mapLe D.leftSociety_graph_le
  let G : S.graph.Walk (X.endpoints.endpoint 1) (X.endpoints.endpoint 3) :=
    X.secondPath.mapLe D.leftSociety_graph_le
  have h0P : X.endpoints.endpoint 0 ∈ P.pathSet :=
    hothers_path 0 (by decide)
  have h2P : X.endpoints.endpoint 2 ∈ P.pathSet :=
    hothers_path 2 (by decide)
  have h3P : X.endpoints.endpoint 3 ∈ P.pathSet :=
    hothers_path 3 (by decide)
  have hxF : x ∈ F.support := by
    simpa [F, SimpleGraph.Walk.support_mapLe_eq_support] using hx_first
  have hyG : y ∈ G.support := by
    simpa [G, SimpleGraph.Walk.support_mapLe_eq_support] using hy_second
  let rim0 : S.graph.Walk x (X.endpoints.endpoint 3) :=
    ((F.takeUntil x hxF).reverse).append
      (Walk.segmentBetween P.path
        (by simpa [GMIX24CutPath.pathSet] using h0P)
        (by simpa [GMIX24CutPath.pathSet] using h3P)
        (Nat.le_of_lt
          (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
            P hno_cross X h1_off hothers_path).1))
  let rim1 : S.graph.Walk x (X.endpoints.endpoint 3) :=
    (F.dropUntil x hxF).append
      (Walk.segmentBetween P.path
        (by simpa [GMIX24CutPath.pathSet] using h3P)
        (by simpa [GMIX24CutPath.pathSet] using h2P)
        (Nat.le_of_lt
          (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_off_path_path_order
            P hno_cross X h1_off hothers_path).2)).reverse
  let rim2 : S.graph.Walk x (X.endpoints.endpoint 3) :=
    r.append (G.dropUntil y hyG)
  let rim : Fin 3 -> S.graph.Walk x (X.endpoints.endpoint 3) :=
    fun i => if i = 0 then rim0 else if i = 1 then rim1 else rim2
  let attach : Fin 3 -> V
    | ⟨0, _⟩ => X.endpoints.endpoint 0
    | ⟨1, _⟩ => X.endpoints.endpoint 2
    | ⟨2, _⟩ => y
  let boundary : Fin 3 -> V
    | ⟨0, _⟩ => P.s
    | ⟨1, _⟩ => P.t
    | ⟨2, _⟩ => X.endpoints.endpoint 1
  let leg : forall i : Fin 3, S.graph.Walk (attach i) (boundary i)
    | ⟨0, _⟩ => by
      simpa [attach, boundary]
        using (P.pathTailToStart h0P)
    | ⟨1, _⟩ => by
      simpa [attach, boundary]
        using (P.pathTailToEnd h2P)
    | ⟨2, _⟩ => by
      simpa [attach, boundary, G]
        using ((G.takeUntil y hyG).reverse)
  refine ⟨{
    left := x
    right := X.endpoints.endpoint 3
    left_ne_right :=
      GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_left_ne_right
        P hno_cross X hothers_path
        (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
    rim := rim
    rim_isPath := ?_
    attach := attach
    attach_mem_rim := ?_
    boundary := boundary
    boundary_mem := ?_
    boundary_injective := ?_
    leg := leg
    leg_isPath := ?_
    rim_internals_disjoint := ?_
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }⟩
  · intro i
    fin_cases i
    · simpa [rim, rim0, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim0_isPath
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
    · simpa [rim, rim1, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim1_isPath
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
    · simpa [rim, rim2, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim2_isPath
          P hno_cross X r hy_second hr_path hclean_second
  · intro i
    fin_cases i
    · simpa [rim, rim0, attach, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim0_attach0_internal
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
    · simpa [rim, rim1, attach, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim1_attach1_internal
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
    · simpa [rim, rim2, attach, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim2_attach2_internal
          P hno_cross X hothers_path r hx_first hy_second hr_outside
  · intro i
    fin_cases i
    · simpa [boundary] using P.s_mem_boundary
    · simpa [boundary] using P.t_mem_boundary
    · simpa [boundary, GeneralSociety.boundarySet] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint_mem_original_of_off_path
          P hno_cross X h1_off
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [boundary] at hij ⊢
    · exact False.elim (P.s_ne_t hij)
    · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
        rw [← hij]
        exact P.s_mem_pathSet
      exact False.elim (h1_off hpath)
    · exact False.elim (P.s_ne_t hij.symm)
    · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
        rw [← hij]
        exact P.t_mem_pathSet
      exact False.elim (h1_off hpath)
    · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
        rw [hij]
        exact P.s_mem_pathSet
      exact False.elim (h1_off hpath)
    · have hpath : X.endpoints.endpoint 1 ∈ P.pathSet := by
        rw [hij]
        exact P.t_mem_pathSet
      exact False.elim (h1_off hpath)
  · intro i
    fin_cases i
    · simpa [leg] using P.pathTailToStart_isPath h0P
    · simpa [leg] using P.pathTailToEnd_isPath h2P
    · simpa [leg, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg2_isPath
          P hno_cross X hy_second
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · simpa [rim, rim0, rim1, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim0_rim1_internals_disjoint
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
    · simpa [rim, rim0, rim2, F, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim0_rim2_internals_disjoint
          P hno_cross X h1_off hothers_path r hx_first hy_second
          hclean_first hr_outside
    · simpa [rim, rim0, rim1, F, D] using
        (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim0_rim1_internals_disjoint
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1).symm
    · simpa [rim, rim1, rim2, F, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim1_rim2_internals_disjoint
          P hno_cross X h1_off hothers_path r hx_first hy_second
          hclean_first hr_outside
    · simpa [rim, rim0, rim2, F, G, D] using
        (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim0_rim2_internals_disjoint
          P hno_cross X h1_off hothers_path r hx_first hy_second
          hclean_first hr_outside).symm
    · simpa [rim, rim1, rim2, F, G, D] using
      (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_rim1_rim2_internals_disjoint
          P hno_cross X h1_off hothers_path r hx_first hy_second
          hclean_first hr_outside).symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · simpa [leg] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_leg1_disjoint
          P hno_cross X h1_off hothers_path
    · simpa [leg, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_leg2_disjoint
          P hno_cross X h1_off hothers_path hy_second
    · simpa [leg] using
      (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_leg1_disjoint
          P hno_cross X h1_off hothers_path).symm
    · simpa [leg, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg1_leg2_disjoint
          P hno_cross X h1_off hothers_path hy_second
    · simpa [leg, G, D] using
        (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_leg2_disjoint
          P hno_cross X h1_off hothers_path hy_second).symm
    · simpa [leg, G, D] using
      (GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg1_leg2_disjoint
          P hno_cross X h1_off hothers_path hy_second).symm
  · intro i j z hz_leg hz_rim
    fin_cases i <;> fin_cases j
    · simpa [leg, rim, rim0, attach, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_meets_rim0_only_attach
          P hno_cross X h1_off hothers_path hx_first hz_leg hz_rim
    · simpa [leg, rim, rim1, attach, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_meets_rim1_only_attach
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
          hz_leg hz_rim
    · simpa [leg, rim, rim2, attach, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg0_meets_rim2_only_attach
          P hno_cross X h1_off hothers_path r hy_second hr_outside
          hz_leg hz_rim
    · simpa [leg, rim, rim0, attach, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg1_meets_rim0_only_attach
          P hno_cross X h1_off hothers_path hx_first
          (cross_clean_branch_endpoint_not_path (P := P) r hr_outside).1
          hz_leg hz_rim
    · simpa [leg, rim, rim1, attach, F, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg1_meets_rim1_only_attach
          P hno_cross X h1_off hothers_path hx_first hz_leg hz_rim
    · simpa [leg, rim, rim2, attach, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg1_meets_rim2_only_attach
          P hno_cross X h1_off hothers_path r hy_second hr_outside
          hz_leg hz_rim
    · simpa [leg, rim, rim0, attach, F, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg2_meets_rim0_only_attach
          P hno_cross X h1_off hothers_path r hx_first hy_second
          hr_outside hz_leg hz_rim
    · simpa [leg, rim, rim1, attach, F, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg2_meets_rim1_only_attach
          P hno_cross X h1_off hothers_path r hx_first hy_second
          hr_outside hz_leg hz_rim
    · simpa [leg, rim, rim2, attach, G, D] using
        GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_leg2_meets_rim2_only_attach
          P hno_cross X r hy_second hclean_second hz_leg hz_rim


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
