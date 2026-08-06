import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.EndpointOneTripod

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_endpoint3_first_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h3_off : X.endpoints.endpoint 3 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∈ P.pathSet)
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
  let Xr := X.rotate2
  have h1_off : Xr.endpoints.endpoint 1 ∉ P.pathSet := by
    simpa [Xr, Cross.rotate2] using h3_off
  have hothers_rot :
      forall i : Fin 4, i ≠ 1 -> Xr.endpoints.endpoint i ∈ P.pathSet := by
    intro i hi
    fin_cases i
    · simpa [Xr, Cross.rotate2] using hothers_path 2 (by decide)
    · exact False.elim (hi rfl)
    · simpa [Xr, Cross.rotate2] using hothers_path 0 (by decide)
    · simpa [Xr, Cross.rotate2] using hothers_path 1 (by decide)
  have hx_first_rot : x ∈ Xr.firstPath.support := by
    simpa [Xr, Cross.rotate2, SimpleGraph.Walk.support_reverse] using
      (List.mem_reverse.mpr hx_first)
  have hy_second_rot : y ∈ Xr.secondPath.support := by
    simpa [Xr, Cross.rotate2, SimpleGraph.Walk.support_reverse] using
      (List.mem_reverse.mpr hy_second)
  have hclean_first_rot :
      forall w : V, w ∈ r.support ->
        w ∈ Xr.firstPath.support -> w = x := by
    intro w hw hwrot
    have hwrev : w ∈ X.firstPath.reverse.support := by
      simpa [Xr, Cross.rotate2] using hwrot
    rw [SimpleGraph.Walk.support_reverse] at hwrev
    exact hclean_first w hw (List.mem_reverse.mp hwrev)
  have hclean_second_rot :
      forall w : V, w ∈ r.support ->
        w ∈ Xr.secondPath.support -> w = y := by
    intro w hw hwrot
    have hwrev : w ∈ X.secondPath.reverse.support := by
      simpa [Xr, Cross.rotate2] using hwrot
    rw [SimpleGraph.Walk.support_reverse] at hwrev
    exact hclean_second w hw (List.mem_reverse.mp hwrev)
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_tripod
      P hno_cross Xr h1_off hothers_rot r hx_first_rot hy_second_rot
      hr_path hclean_first_rot hclean_second_rot hr_outside

theorem canonicalOfNoCross_left_cross_endpoint2_second_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h2_off : X.endpoints.endpoint 2 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V}
    (r : S.graph.Walk x y)
    (hx_second : x ∈ X.secondPath.support)
    (hy_first : y ∈ X.firstPath.support)
    (hr_path : r.IsPath)
    (hclean_second :
      forall w : V, w ∈ r.support ->
        w ∈ X.secondPath.support -> w = x)
    (hclean_first :
      forall w : V, w ∈ r.support ->
        w ∈ X.firstPath.support -> w = y)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    Nonempty S.Tripod := by
  classical
  let Xr := X.rotate1
  have h1_off : Xr.endpoints.endpoint 1 ∉ P.pathSet := by
    simpa [Xr, Cross.rotate1] using h2_off
  have hothers_rot :
      forall i : Fin 4, i ≠ 1 -> Xr.endpoints.endpoint i ∈ P.pathSet := by
    intro i hi
    fin_cases i
    · simpa [Xr, Cross.rotate1] using hothers_path 1 (by decide)
    · exact False.elim (hi rfl)
    · simpa [Xr, Cross.rotate1] using hothers_path 3 (by decide)
    · simpa [Xr, Cross.rotate1] using hothers_path 0 (by decide)
  have hx_first_rot : x ∈ Xr.firstPath.support := by
    simpa [Xr, Cross.rotate1] using hx_second
  have hy_second_rot : y ∈ Xr.secondPath.support := by
    simpa [Xr, Cross.rotate1, SimpleGraph.Walk.support_reverse] using
      (List.mem_reverse.mpr hy_first)
  have hclean_first_rot :
      forall w : V, w ∈ r.support ->
        w ∈ Xr.firstPath.support -> w = x := by
    intro w hw hwrot
    exact hclean_second w hw (by simpa [Xr, Cross.rotate1] using hwrot)
  have hclean_second_rot :
      forall w : V, w ∈ r.support ->
        w ∈ Xr.secondPath.support -> w = y := by
    intro w hw hwrot
    have hwrev : w ∈ X.firstPath.reverse.support := by
      simpa [Xr, Cross.rotate1] using hwrot
    rw [SimpleGraph.Walk.support_reverse] at hwrev
    exact hclean_first w hw (List.mem_reverse.mp hwrev)
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint1_first_tripod
      P hno_cross Xr h1_off hothers_rot r hx_first_rot hy_second_rot
      hr_path hclean_first_rot hclean_second_rot hr_outside

theorem canonicalOfNoCross_left_cross_endpoint0_second_tripod
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (h0_off : X.endpoints.endpoint 0 ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∈ P.pathSet)
    {x y : V}
    (r : S.graph.Walk x y)
    (hx_second : x ∈ X.secondPath.support)
    (hy_first : y ∈ X.firstPath.support)
    (hr_path : r.IsPath)
    (hclean_second :
      forall w : V, w ∈ r.support ->
        w ∈ X.secondPath.support -> w = x)
    (hclean_first :
      forall w : V, w ∈ r.support ->
        w ∈ X.firstPath.support -> w = y)
    (hr_outside : forall w : V, w ∈ r.support -> w ∈ P.outside) :
    Nonempty S.Tripod := by
  classical
  let Xr := X.rotate1
  have h3_off : Xr.endpoints.endpoint 3 ∉ P.pathSet := by
    simpa [Xr, Cross.rotate1] using h0_off
  have hothers_rot :
      forall i : Fin 4, i ≠ 3 -> Xr.endpoints.endpoint i ∈ P.pathSet := by
    intro i hi
    fin_cases i
    · simpa [Xr, Cross.rotate1] using hothers_path 1 (by decide)
    · simpa [Xr, Cross.rotate1] using hothers_path 2 (by decide)
    · simpa [Xr, Cross.rotate1] using hothers_path 3 (by decide)
    · exact False.elim (hi rfl)
  have hx_first_rot : x ∈ Xr.firstPath.support := by
    simpa [Xr, Cross.rotate1] using hx_second
  have hy_second_rot : y ∈ Xr.secondPath.support := by
    simpa [Xr, Cross.rotate1, SimpleGraph.Walk.support_reverse] using
      (List.mem_reverse.mpr hy_first)
  have hclean_first_rot :
      forall w : V, w ∈ r.support ->
        w ∈ Xr.firstPath.support -> w = x := by
    intro w hw hwrot
    exact hclean_second w hw (by simpa [Xr, Cross.rotate1] using hwrot)
  have hclean_second_rot :
      forall w : V, w ∈ r.support ->
        w ∈ Xr.secondPath.support -> w = y := by
    intro w hw hwrot
    have hwrev : w ∈ X.firstPath.reverse.support := by
      simpa [Xr, Cross.rotate1] using hwrot
    rw [SimpleGraph.Walk.support_reverse] at hwrev
    exact hclean_first w hw (List.mem_reverse.mp hwrev)
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_endpoint3_first_tripod
      P hno_cross Xr h3_off hothers_rot r hx_first_rot hy_second_rot
      hr_path hclean_first_rot hclean_second_rot hr_outside


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

