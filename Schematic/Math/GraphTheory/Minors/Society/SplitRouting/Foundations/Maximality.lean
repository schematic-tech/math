import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.EndpointCounts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem CrossOffPathCountMaximal.not_lt_candidate
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X Y : H.Cross}
    (hmax : CrossOffPathCountMaximal P X)
    (hcount :
      crossOffPathEndpointCount X P <
        crossOffPathEndpointCount Y P) :
    False := by
  have hle := hmax Y
  omega

theorem CrossOffPathCountMaximal.transport
    [DecidableEq V]
    {S T H K : GeneralSociety V}
    {P : GMIX24CutPath S} {Q : GMIX24CutPath T}
    {X : H.Cross}
    (hmax : CrossOffPathCountMaximal P X)
    (hHK : H = K)
    (hpath : Q.pathSet = P.pathSet) :
    CrossOffPathCountMaximal Q (hHK ▸ X) := by
  subst K
  intro Y
  have hle := hmax Y
  unfold crossOffPathEndpointCount crossOffPathEndpointFinset at hle ⊢
  rw [hpath]
  exact hle

theorem CrossOffPathCountMaximal.reverseRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    (hno_cross : Not (Nonempty S.Cross))
    {X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross}
    (hmax : CrossOffPathCountMaximal P X) :
    CrossOffPathCountMaximal P.reverse
      (GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X) :=
  hmax.transport
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm
    (GMIX24CutPath.reverse_pathSet P)

theorem CrossOffPathCountMaximal.not_replaceEndpoint2_with_tail_of_count_lt
    [DecidableEq V]
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : H.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint2 a i ∈ H.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint2 a))
    (halternating :
      CrossEndpointAlternating H.boundary (X.replaceEndpoint2 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ H.boundarySet = ∅)
    (hx_not_boundary : x ∉ H.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint2 a) P) :
    False := by
  let Y : H.Cross :=
    X.replaceEndpoint2_with_tail hx q hendpoint_mem hendpoint_injective
      halternating hq_path hq_boundary hx_not_boundary hq_clean
  have hYcount :
      crossOffPathEndpointCount Y P =
        endpointOffPathCount (X.replaceEndpoint2 a) P := by
    simpa [Y] using
      crossOffPathEndpointCount_replaceEndpoint2_with_tail_eq
        P X hx q hendpoint_mem hendpoint_injective halternating hq_path
        hq_boundary hx_not_boundary hq_clean
  exact hmax.not_lt_candidate (Y := Y) (by omega)

theorem CrossOffPathCountMaximal.not_replaceEndpoint0_with_tail_of_count_lt
    [DecidableEq V]
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.firstPath.support)
    (q : H.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint0 a i ∈ H.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint0 a))
    (halternating :
      CrossEndpointAlternating H.boundary (X.replaceEndpoint0 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ H.boundarySet = ∅)
    (hx_not_boundary : x ∉ H.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint0 a) P) :
    False := by
  let Y : H.Cross :=
    X.replaceEndpoint0_with_tail hx q hendpoint_mem hendpoint_injective
      halternating hq_path hq_boundary hx_not_boundary hq_clean
  have hYcount :
      crossOffPathEndpointCount Y P =
        endpointOffPathCount (X.replaceEndpoint0 a) P := by
    simpa [Y] using
      crossOffPathEndpointCount_replaceEndpoint0_with_tail_eq
        P X hx q hendpoint_mem hendpoint_injective halternating hq_path
        hq_boundary hx_not_boundary hq_clean
  exact hmax.not_lt_candidate (Y := Y) (by omega)

theorem CrossOffPathCountMaximal.not_replaceEndpoint3_with_tail_of_count_lt
    [DecidableEq V]
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : H.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint3 a i ∈ H.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint3 a))
    (halternating :
      CrossEndpointAlternating H.boundary (X.replaceEndpoint3 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ H.boundarySet = ∅)
    (hx_not_boundary : x ∉ H.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint3 a) P) :
    False := by
  let Y : H.Cross :=
    X.replaceEndpoint3_with_tail hx q hendpoint_mem hendpoint_injective
      halternating hq_path hq_boundary hx_not_boundary hq_clean
  have hYcount :
      crossOffPathEndpointCount Y P =
        endpointOffPathCount (X.replaceEndpoint3 a) P := by
    simpa [Y] using
      crossOffPathEndpointCount_replaceEndpoint3_with_tail_eq
        P X hx q hendpoint_mem hendpoint_injective halternating hq_path
        hq_boundary hx_not_boundary hq_clean
  exact hmax.not_lt_candidate (Y := Y) (by omega)

theorem CrossOffPathCountMaximal.not_replaceEndpoint1_with_tail_of_count_lt
    [DecidableEq V]
    {S H : GeneralSociety V} {P : GMIX24CutPath S} {X : H.Cross}
    (hmax : CrossOffPathCountMaximal P X)
    {x a : V}
    (hx : x ∈ X.secondPath.support)
    (q : H.graph.Walk x a)
    (hendpoint_mem :
      forall i : Fin 4, X.replaceEndpoint1 a i ∈ H.boundarySet)
    (hendpoint_injective :
      Function.Injective (X.replaceEndpoint1 a))
    (halternating :
      CrossEndpointAlternating H.boundary (X.replaceEndpoint1 a))
    (hq_path : q.IsPath)
    (hq_boundary : Walk.InternalVertices q ∩ H.boundarySet = ∅)
    (hx_not_boundary : x ∉ H.boundarySet)
    (hq_clean :
      forall w : V,
        w ∈ q.support ->
          (w ∈ X.firstPath.support ∨ w ∈ X.secondPath.support) ->
            w = x)
    (hcount :
      crossOffPathEndpointCount X P <
        endpointOffPathCount (X.replaceEndpoint1 a) P) :
    False := by
  let Y : H.Cross :=
    X.replaceEndpoint1_with_tail hx q hendpoint_mem hendpoint_injective
      halternating hq_path hq_boundary hx_not_boundary hq_clean
  have hYcount :
      crossOffPathEndpointCount Y P =
        endpointOffPathCount (X.replaceEndpoint1 a) P := by
    simpa [Y] using
      crossOffPathEndpointCount_replaceEndpoint1_with_tail_eq
        P X hx q hendpoint_mem hendpoint_injective halternating hq_path
        hq_boundary hx_not_boundary hq_clean
  exact hmax.not_lt_candidate (Y := Y) (by omega)

theorem mem_crossOffPathEndpointFinset_iff
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross) {i : Fin 4} :
    i ∈ crossOffPathEndpointFinset X P ↔ X.endpoints.endpoint i ∉ P.pathSet := by
  classical
  simp [crossOffPathEndpointFinset]

theorem crossOffPathEndpointCount_eq_four_of_all_off
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross)
    (hoff : forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet) :
    crossOffPathEndpointCount X P = 4 := by
  classical
  have hfinset : crossOffPathEndpointFinset X P = Finset.univ := by
    ext i
    simp [crossOffPathEndpointFinset, hoff i]
  simp [crossOffPathEndpointCount, hfinset]

theorem crossOffPathEndpointCount_eq_three_of_only_endpoint2_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross)
    (hpath : X.endpoints.endpoint 2 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 2 -> X.endpoints.endpoint i ∉ P.pathSet) :
    crossOffPathEndpointCount X P = 3 := by
  classical
  have hfinset : crossOffPathEndpointFinset X P = Finset.univ.erase (2 : Fin 4) := by
    ext i
    by_cases hi : i = 2
    · subst i
      simp [crossOffPathEndpointFinset, hpath]
    · simp [crossOffPathEndpointFinset, hi, hoff i hi]
  simp [crossOffPathEndpointCount, hfinset]

theorem crossOffPathEndpointCount_eq_three_of_only_endpoint0_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross)
    (hpath : X.endpoints.endpoint 0 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 0 -> X.endpoints.endpoint i ∉ P.pathSet) :
    crossOffPathEndpointCount X P = 3 := by
  classical
  have hfinset : crossOffPathEndpointFinset X P = Finset.univ.erase (0 : Fin 4) := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [crossOffPathEndpointFinset, hpath]
    · simp [crossOffPathEndpointFinset, hi, hoff i hi]
  simp [crossOffPathEndpointCount, hfinset]

theorem crossOffPathEndpointCount_eq_three_of_only_endpoint3_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross)
    (hpath : X.endpoints.endpoint 3 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 3 -> X.endpoints.endpoint i ∉ P.pathSet) :
    crossOffPathEndpointCount X P = 3 := by
  classical
  have hfinset : crossOffPathEndpointFinset X P = Finset.univ.erase (3 : Fin 4) := by
    ext i
    by_cases hi : i = 3
    · subst i
      simp [crossOffPathEndpointFinset, hpath]
    · simp [crossOffPathEndpointFinset, hi, hoff i hi]
  simp [crossOffPathEndpointCount, hfinset]

theorem crossOffPathEndpointCount_eq_three_of_only_endpoint1_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross)
    (hpath : X.endpoints.endpoint 1 ∈ P.pathSet)
    (hoff : forall i : Fin 4, i ≠ 1 -> X.endpoints.endpoint i ∉ P.pathSet) :
    crossOffPathEndpointCount X P = 3 := by
  classical
  have hfinset : crossOffPathEndpointFinset X P = Finset.univ.erase (1 : Fin 4) := by
    ext i
    by_cases hi : i = 1
    · subst i
      simp [crossOffPathEndpointFinset, hpath]
    · simp [crossOffPathEndpointFinset, hi, hoff i hi]
  simp [crossOffPathEndpointCount, hfinset]


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
