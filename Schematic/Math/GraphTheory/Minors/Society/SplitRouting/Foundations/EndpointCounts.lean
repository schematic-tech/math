import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.Foundations.BoundaryAlternation

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem crossOffPathEndpointFinset_eq_endpointOffPathFinset
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross) :
    crossOffPathEndpointFinset X P =
      endpointOffPathFinset X.endpoints.endpoint P := by
  rfl

theorem crossOffPathEndpointCount_eq_endpointOffPathCount
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {H : GeneralSociety V} (X : H.Cross) :
    crossOffPathEndpointCount X P =
      endpointOffPathCount X.endpoints.endpoint P := by
  rfl

theorem mem_endpointOffPathFinset_iff
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {i : Fin 4} :
    i ∈ endpointOffPathFinset endpoint P ↔ endpoint i ∉ P.pathSet := by
  classical
  simp [endpointOffPathFinset]

theorem endpointOffPathCount_replaceEndpointAt_eq_one_of_all_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {k : Fin 4} {a : V}
    (hall_path : forall i : Fin 4, endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    endpointOffPathCount (replaceEndpointAt endpoint k a) P = 1 := by
  classical
  have hfinset :
      endpointOffPathFinset (replaceEndpointAt endpoint k a) P = {k} := by
    ext i
    by_cases hi : i = k
    · subst i
      simp [endpointOffPathFinset, replaceEndpointAt, ha_off]
    · simp [endpointOffPathFinset, replaceEndpointAt, hi, hall_path i]
  simp [endpointOffPathCount, hfinset]

theorem endpointOffPathCount_eq_zero_of_all_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V}
    (hall_path : forall i : Fin 4, endpoint i ∈ P.pathSet) :
    endpointOffPathCount endpoint P = 0 := by
  classical
  have hfinset : endpointOffPathFinset endpoint P = ∅ := by
    ext i
    simp [endpointOffPathFinset, hall_path i]
  simp [endpointOffPathCount, hfinset]

theorem endpointOffPathCount_eq_zero_iff_all_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} :
    endpointOffPathCount endpoint P = 0 ↔
      forall i : Fin 4, endpoint i ∈ P.pathSet := by
  classical
  constructor
  · intro h i
    by_contra hoff
    have hi : i ∈ endpointOffPathFinset endpoint P := by
      exact (mem_endpointOffPathFinset_iff P).mpr hoff
    have hfin_empty :
        endpointOffPathFinset endpoint P = ∅ := by
      exact Finset.card_eq_zero.mp (by simpa [endpointOffPathCount] using h)
    simp [hfin_empty] at hi
  · intro hall
    exact endpointOffPathCount_eq_zero_of_all_on_path P hall

theorem crossOffPathEndpointCount_eq_zero_iff_all_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    crossOffPathEndpointCount X P = 0 ↔
      forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet := by
  simpa [crossOffPathEndpointCount_eq_endpointOffPathCount P X] using
    endpointOffPathCount_eq_zero_iff_all_on_path
      (P := P) (endpoint := X.endpoints.endpoint)

theorem endpointOffPathCount_replaceEndpointAt_eq_two_of_single_old_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {k l : Fin 4} {a : V}
    (hkl : k ≠ l)
    (hl_off : endpoint l ∉ P.pathSet)
    (hothers_path : forall i : Fin 4, i ≠ l -> endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    endpointOffPathCount (replaceEndpointAt endpoint k a) P = 2 := by
  classical
  have hfinset :
      endpointOffPathFinset (replaceEndpointAt endpoint k a) P = {k, l} := by
    ext i
    by_cases hik : i = k
    · subst i
      simp [endpointOffPathFinset, replaceEndpointAt, hkl, ha_off]
    · by_cases hil : i = l
      · subst i
        simp [endpointOffPathFinset, replaceEndpointAt, hkl.symm, hl_off]
      · simp [endpointOffPathFinset, replaceEndpointAt, hik,
          hothers_path i hil, hil]
  rw [endpointOffPathCount, hfinset]
  exact Finset.card_pair hkl

theorem endpointOffPathCount_eq_one_of_single_old_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {l : Fin 4}
    (hl_off : endpoint l ∉ P.pathSet)
    (hothers_path : forall i : Fin 4, i ≠ l -> endpoint i ∈ P.pathSet) :
    endpointOffPathCount endpoint P = 1 := by
  classical
  have hfinset : endpointOffPathFinset endpoint P = {l} := by
    ext i
    by_cases hil : i = l
    · subst i
      simp [endpointOffPathFinset, hl_off]
    · simp [endpointOffPathFinset, hil, hothers_path i hil]
  simp [endpointOffPathCount, hfinset]

theorem endpointOffPathCount_eq_one_iff_exists_single_old_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} :
    endpointOffPathCount endpoint P = 1 ↔
      Exists fun l : Fin 4 =>
        endpoint l ∉ P.pathSet ∧
          forall i : Fin 4, i ≠ l -> endpoint i ∈ P.pathSet := by
  classical
  constructor
  · intro h
    have hcard :
        (endpointOffPathFinset endpoint P).card = 1 := by
      simpa [endpointOffPathCount] using h
    rcases Finset.card_eq_one.mp hcard with ⟨l, hl⟩
    refine ⟨l, ?_, ?_⟩
    · have hl_mem : l ∈ endpointOffPathFinset endpoint P := by
        rw [hl]
        simp
      exact (mem_endpointOffPathFinset_iff P).mp hl_mem
    · intro i hil
      by_contra hoff
      have hi_mem : i ∈ endpointOffPathFinset endpoint P := by
        exact (mem_endpointOffPathFinset_iff P).mpr hoff
      rw [hl] at hi_mem
      simp at hi_mem
      exact hil hi_mem
  · rintro ⟨l, hl_off, hothers⟩
    exact endpointOffPathCount_eq_one_of_single_old_off_path
      P hl_off hothers

theorem crossOffPathEndpointCount_eq_one_iff_exists_single_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    crossOffPathEndpointCount X P = 1 ↔
      Exists fun l : Fin 4 =>
        X.endpoints.endpoint l ∉ P.pathSet ∧
          forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet := by
  simpa [crossOffPathEndpointCount_eq_endpointOffPathCount P X] using
    endpointOffPathCount_eq_one_iff_exists_single_old_off_path
      (P := P) (endpoint := X.endpoints.endpoint)

theorem endpointOffPathCount_eq_two_of_two_old_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {k l : Fin 4}
    (hkl : k ≠ l)
    (hk_off : endpoint k ∉ P.pathSet)
    (hl_off : endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ k -> i ≠ l -> endpoint i ∈ P.pathSet) :
    endpointOffPathCount endpoint P = 2 := by
  classical
  have hfinset : endpointOffPathFinset endpoint P = {k, l} := by
    ext i
    by_cases hik : i = k
    · subst i
      simp [endpointOffPathFinset, hk_off]
    · by_cases hil : i = l
      · subst i
        simp [endpointOffPathFinset, hl_off]
      · simp [endpointOffPathFinset, hik, hil,
          hothers_path i hik hil]
  rw [endpointOffPathCount, hfinset]
  simp [hkl]

theorem endpointOffPathCount_eq_two_iff_exists_two_old_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} :
    endpointOffPathCount endpoint P = 2 ↔
      Exists fun k : Fin 4 =>
        Exists fun l : Fin 4 =>
          k ≠ l ∧ endpoint k ∉ P.pathSet ∧
            endpoint l ∉ P.pathSet ∧
              forall i : Fin 4, i ≠ k -> i ≠ l ->
                endpoint i ∈ P.pathSet := by
  classical
  constructor
  · intro h
    have hcard :
        (endpointOffPathFinset endpoint P).card = 2 := by
      simpa [endpointOffPathCount] using h
    rcases Finset.card_eq_two.mp hcard with ⟨k, l, hkl, hfin⟩
    have hk_mem : k ∈ endpointOffPathFinset endpoint P := by
      rw [hfin]
      simp [hkl]
    have hl_mem : l ∈ endpointOffPathFinset endpoint P := by
      rw [hfin]
      simp
    refine ⟨k, l, hkl, ?_, ?_, ?_⟩
    · exact (mem_endpointOffPathFinset_iff P).mp hk_mem
    · exact (mem_endpointOffPathFinset_iff P).mp hl_mem
    · intro i hik hil
      by_contra hoff
      have hi_mem : i ∈ endpointOffPathFinset endpoint P :=
        (mem_endpointOffPathFinset_iff P).mpr hoff
      rw [hfin] at hi_mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
      rcases hi_mem with hik' | hil'
      · exact hik hik'
      · exact hil hil'
  · rintro ⟨k, l, hkl, hk_off, hl_off, hothers_path⟩
    exact endpointOffPathCount_eq_two_of_two_old_off_path
      P hkl hk_off hl_off hothers_path

theorem crossOffPathEndpointCount_eq_two_iff_exists_two_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    crossOffPathEndpointCount X P = 2 ↔
      Exists fun k : Fin 4 =>
        Exists fun l : Fin 4 =>
          k ≠ l ∧ X.endpoints.endpoint k ∉ P.pathSet ∧
            X.endpoints.endpoint l ∉ P.pathSet ∧
              forall i : Fin 4, i ≠ k -> i ≠ l ->
                X.endpoints.endpoint i ∈ P.pathSet := by
  simpa [crossOffPathEndpointCount_eq_endpointOffPathCount P X] using
    endpointOffPathCount_eq_two_iff_exists_two_old_off_path
      (P := P) (endpoint := X.endpoints.endpoint)

theorem endpointOffPathCount_lt_replaceEndpointAt_of_all_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {k : Fin 4} {a : V}
    (hall_path : forall i : Fin 4, endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    endpointOffPathCount endpoint P <
      endpointOffPathCount (replaceEndpointAt endpoint k a) P := by
  rw [endpointOffPathCount_eq_zero_of_all_on_path P hall_path,
    endpointOffPathCount_replaceEndpointAt_eq_one_of_all_on_path P
      hall_path ha_off]
  exact Nat.zero_lt_one

theorem endpointOffPathCount_lt_replaceEndpointAt_of_single_old_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {k l : Fin 4} {a : V}
    (hkl : k ≠ l)
    (hl_off : endpoint l ∉ P.pathSet)
    (hothers_path : forall i : Fin 4, i ≠ l -> endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    endpointOffPathCount endpoint P <
      endpointOffPathCount (replaceEndpointAt endpoint k a) P := by
  rw [endpointOffPathCount_eq_one_of_single_old_off_path P hl_off
      hothers_path,
    endpointOffPathCount_replaceEndpointAt_eq_two_of_single_old_off_path P
      hkl hl_off hothers_path ha_off]
  omega

theorem crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {k : Fin 4} {a : V}
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (replaceEndpointAt X.endpoints.endpoint k a) P := by
  rw [crossOffPathEndpointCount_eq_endpointOffPathCount P X]
  exact endpointOffPathCount_lt_replaceEndpointAt_of_all_on_path
    P hall_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {k l : Fin 4} {a : V}
    (hkl : k ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (replaceEndpointAt X.endpoints.endpoint k a) P := by
  rw [crossOffPathEndpointCount_eq_endpointOffPathCount P X]
  exact endpointOffPathCount_lt_replaceEndpointAt_of_single_old_off_path
    P hkl hl_off hothers_path ha_off

theorem Cross.replaceEndpoint0_eq_replaceEndpointAt
    {S : GeneralSociety V} (X : S.Cross) (a : V) :
    X.replaceEndpoint0 a = replaceEndpointAt X.endpoints.endpoint 0 a := by
  funext i
  simp [replaceEndpointAt, Cross.replaceEndpoint0]

theorem Cross.replaceEndpoint1_eq_replaceEndpointAt
    {S : GeneralSociety V} (X : S.Cross) (a : V) :
    X.replaceEndpoint1 a = replaceEndpointAt X.endpoints.endpoint 1 a := by
  funext i
  simp [replaceEndpointAt, Cross.replaceEndpoint1]

theorem Cross.replaceEndpoint2_eq_replaceEndpointAt
    {S : GeneralSociety V} (X : S.Cross) (a : V) :
    X.replaceEndpoint2 a = replaceEndpointAt X.endpoints.endpoint 2 a := by
  funext i
  simp [replaceEndpointAt, Cross.replaceEndpoint2]

theorem Cross.replaceEndpoint3_eq_replaceEndpointAt
    {S : GeneralSociety V} (X : S.Cross) (a : V) :
    X.replaceEndpoint3 a = replaceEndpointAt X.endpoints.endpoint 3 a := by
  funext i
  simp [replaceEndpointAt, Cross.replaceEndpoint3]

theorem crossOffPathEndpointCount_lt_replaceEndpoint0_of_all_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {a : V}
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint0 a) P := by
  simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
      P X (k := 0) hall_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint1_of_all_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {a : V}
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint1 a) P := by
  simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
      P X (k := 1) hall_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint2_of_all_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {a : V}
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint2 a) P := by
  simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
      P X (k := 2) hall_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint3_of_all_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {a : V}
    (hall_path : forall i : Fin 4, X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint3 a) P := by
  simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_all_on_path
      P X (k := 3) hall_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint0_of_single_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {l : Fin 4} {a : V}
    (h0l : (0 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint0 a) P := by
  simpa [Cross.replaceEndpoint0_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
      P X (k := 0) (l := l) h0l hl_off hothers_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint1_of_single_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {l : Fin 4} {a : V}
    (h1l : (1 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint1 a) P := by
  simpa [Cross.replaceEndpoint1_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
      P X (k := 1) (l := l) h1l hl_off hothers_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint2_of_single_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {l : Fin 4} {a : V}
    (h2l : (2 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint2 a) P := by
  simpa [Cross.replaceEndpoint2_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
      P X (k := 2) (l := l) h2l hl_off hothers_path ha_off

theorem crossOffPathEndpointCount_lt_replaceEndpoint3_of_single_old_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {l : Fin 4} {a : V}
    (h3l : (3 : Fin 4) ≠ l)
    (hl_off : X.endpoints.endpoint l ∉ P.pathSet)
    (hothers_path :
      forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∈ P.pathSet)
    (ha_off : a ∉ P.pathSet) :
    crossOffPathEndpointCount X P <
      endpointOffPathCount (X.replaceEndpoint3 a) P := by
  simpa [Cross.replaceEndpoint3_eq_replaceEndpointAt] using
    crossOffPathEndpointCount_lt_replaceEndpointAt_of_single_old_off_path
      P X (k := 3) (l := l) h3l hl_off hothers_path ha_off

theorem crossOffPathEndpointCount_replaceEndpoint2_with_tail_eq
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {x a : V}
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
            w = x) :
    crossOffPathEndpointCount
        (X.replaceEndpoint2_with_tail hx q hendpoint_mem hendpoint_injective
          halternating hq_path hq_boundary hx_not_boundary hq_clean) P =
      endpointOffPathCount (X.replaceEndpoint2 a) P := by
  rfl

theorem crossOffPathEndpointCount_replaceEndpoint0_with_tail_eq
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {x a : V}
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
            w = x) :
    crossOffPathEndpointCount
        (X.replaceEndpoint0_with_tail hx q hendpoint_mem hendpoint_injective
          halternating hq_path hq_boundary hx_not_boundary hq_clean) P =
      endpointOffPathCount (X.replaceEndpoint0 a) P := by
  rfl

theorem crossOffPathEndpointCount_replaceEndpoint3_with_tail_eq
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {x a : V}
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
            w = x) :
    crossOffPathEndpointCount
        (X.replaceEndpoint3_with_tail hx q hendpoint_mem hendpoint_injective
          halternating hq_path hq_boundary hx_not_boundary hq_clean) P =
      endpointOffPathCount (X.replaceEndpoint3 a) P := by
  rfl

theorem crossOffPathEndpointCount_replaceEndpoint1_with_tail_eq
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (X : H.Cross) {x a : V}
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
            w = x) :
    crossOffPathEndpointCount
        (X.replaceEndpoint1_with_tail hx q hendpoint_mem hendpoint_injective
          halternating hq_path hq_boundary hx_not_boundary hq_clean) P =
      endpointOffPathCount (X.replaceEndpoint1 a) P := by
  rfl

def CrossOffPathCountMaximal
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    Prop :=
  forall Y : H.Cross, crossOffPathEndpointCount Y P <=
    crossOffPathEndpointCount X P

theorem endpointOffPathCount_le_four
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (endpoint : Fin 4 -> V) :
    endpointOffPathCount endpoint P <= 4 := by
  classical
  have hsubset :
      endpointOffPathFinset endpoint P ⊆ (Finset.univ : Finset (Fin 4)) := by
    intro i hi
    simp
  have hcard :=
    Finset.card_le_card hsubset
  simpa [endpointOffPathCount] using hcard

theorem endpointOffPathCount_eq_four_of_all_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V}
    (hall_off : forall i : Fin 4, endpoint i ∉ P.pathSet) :
    endpointOffPathCount endpoint P = 4 := by
  classical
  have hfinset : endpointOffPathFinset endpoint P = Finset.univ := by
    ext i
    simp [endpointOffPathFinset, hall_off i]
  simp [endpointOffPathCount, hfinset]

theorem endpointOffPathCount_eq_four_iff_all_off_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} :
    endpointOffPathCount endpoint P = 4 ↔
      forall i : Fin 4, endpoint i ∉ P.pathSet := by
  classical
  constructor
  · intro h i hi_path
    have hsubset :
        endpointOffPathFinset endpoint P ⊆
          (Finset.univ : Finset (Fin 4)) := by
      intro j hj
      simp
    have hne :
        endpointOffPathFinset endpoint P ≠
          (Finset.univ : Finset (Fin 4)) := by
      intro hEq
      have hi_mem : i ∈ endpointOffPathFinset endpoint P := by
        rw [hEq]
        simp
      exact (mem_endpointOffPathFinset_iff P).mp hi_mem hi_path
    have hlt :
        (endpointOffPathFinset endpoint P).card <
          (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hne⟩)
    have huniv : (Finset.univ : Finset (Fin 4)).card = 4 := by
      simp
    have hle4 : (endpointOffPathFinset endpoint P).card < 4 := by
      simpa [huniv] using hlt
    have hcard_eq : (endpointOffPathFinset endpoint P).card = 4 := by
      simpa [endpointOffPathCount] using h
    omega
  · intro hall
    exact endpointOffPathCount_eq_four_of_all_off_path P hall

theorem crossOffPathEndpointCount_eq_four_iff_all_off_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    crossOffPathEndpointCount X P = 4 ↔
      forall i : Fin 4, X.endpoints.endpoint i ∉ P.pathSet := by
  simpa [crossOffPathEndpointCount_eq_endpointOffPathCount P X] using
    endpointOffPathCount_eq_four_iff_all_off_path
      (P := P) (endpoint := X.endpoints.endpoint)

theorem endpointOffPathCount_eq_three_of_single_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} {l : Fin 4}
    (hl_path : endpoint l ∈ P.pathSet)
    (hothers_off : forall i : Fin 4, i ≠ l -> endpoint i ∉ P.pathSet) :
    endpointOffPathCount endpoint P = 3 := by
  classical
  have hfinset :
      endpointOffPathFinset endpoint P = Finset.univ.erase l := by
    ext i
    by_cases hil : i = l
    · subst i
      simp [endpointOffPathFinset, hl_path]
    · simp [endpointOffPathFinset, hil, hothers_off i hil]
  rw [endpointOffPathCount, hfinset]
  simp

theorem endpointOffPathCount_eq_three_iff_exists_single_on_path
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {endpoint : Fin 4 -> V} :
    endpointOffPathCount endpoint P = 3 ↔
      Exists fun l : Fin 4 =>
        endpoint l ∈ P.pathSet ∧
          forall i : Fin 4, i ≠ l -> endpoint i ∉ P.pathSet := by
  classical
  constructor
  · intro h
    by_cases h0 : endpoint 0 ∈ P.pathSet
    · by_cases h1 : endpoint 1 ∈ P.pathSet
      · have hcount_le : endpointOffPathCount endpoint P <= 2 := by
          have hsubset :
              endpointOffPathFinset endpoint P ⊆
                ({(2 : Fin 4), (3 : Fin 4)} : Finset (Fin 4)) := by
            intro i hi
            have hoff := (mem_endpointOffPathFinset_iff P).mp hi
            fin_cases i <;> simp_all
          have hcard := Finset.card_le_card hsubset
          simpa [endpointOffPathCount] using hcard
        omega
      · by_cases h2 : endpoint 2 ∈ P.pathSet
        · have hcount_le : endpointOffPathCount endpoint P <= 2 := by
            have hsubset :
                endpointOffPathFinset endpoint P ⊆
                  ({(1 : Fin 4), (3 : Fin 4)} : Finset (Fin 4)) := by
              intro i hi
              have hoff := (mem_endpointOffPathFinset_iff P).mp hi
              fin_cases i <;> simp_all
            have hcard := Finset.card_le_card hsubset
            simpa [endpointOffPathCount] using hcard
          omega
        · by_cases h3 : endpoint 3 ∈ P.pathSet
          · have hcount_le : endpointOffPathCount endpoint P <= 2 := by
              have hsubset :
                  endpointOffPathFinset endpoint P ⊆
                    ({(1 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) := by
                intro i hi
                have hoff := (mem_endpointOffPathFinset_iff P).mp hi
                fin_cases i <;> simp_all
              have hcard := Finset.card_le_card hsubset
              simpa [endpointOffPathCount] using hcard
            omega
          · refine ⟨0, h0, ?_⟩
            intro i hi
            fin_cases i <;> simp_all
    · by_cases h1 : endpoint 1 ∈ P.pathSet
      · by_cases h2 : endpoint 2 ∈ P.pathSet
        · have hcount_le : endpointOffPathCount endpoint P <= 2 := by
            have hsubset :
                endpointOffPathFinset endpoint P ⊆
                  ({(0 : Fin 4), (3 : Fin 4)} : Finset (Fin 4)) := by
              intro i hi
              have hoff := (mem_endpointOffPathFinset_iff P).mp hi
              fin_cases i <;> simp_all
            have hcard := Finset.card_le_card hsubset
            simpa [endpointOffPathCount] using hcard
          omega
        · by_cases h3 : endpoint 3 ∈ P.pathSet
          · have hcount_le : endpointOffPathCount endpoint P <= 2 := by
              have hsubset :
                  endpointOffPathFinset endpoint P ⊆
                    ({(0 : Fin 4), (2 : Fin 4)} : Finset (Fin 4)) := by
                intro i hi
                have hoff := (mem_endpointOffPathFinset_iff P).mp hi
                fin_cases i <;> simp_all
              have hcard := Finset.card_le_card hsubset
              simpa [endpointOffPathCount] using hcard
            omega
          · refine ⟨1, h1, ?_⟩
            intro i hi
            fin_cases i <;> simp_all
      · by_cases h2 : endpoint 2 ∈ P.pathSet
        · by_cases h3 : endpoint 3 ∈ P.pathSet
          · have hcount_le : endpointOffPathCount endpoint P <= 2 := by
              have hsubset :
                  endpointOffPathFinset endpoint P ⊆
                    ({(0 : Fin 4), (1 : Fin 4)} : Finset (Fin 4)) := by
                intro i hi
                have hoff := (mem_endpointOffPathFinset_iff P).mp hi
                fin_cases i <;> simp_all
              have hcard := Finset.card_le_card hsubset
              simpa [endpointOffPathCount] using hcard
            omega
          · refine ⟨2, h2, ?_⟩
            intro i hi
            fin_cases i <;> simp_all
        · by_cases h3 : endpoint 3 ∈ P.pathSet
          · refine ⟨3, h3, ?_⟩
            intro i hi
            fin_cases i <;> simp_all
          · have hcount_four :
                endpointOffPathCount endpoint P = 4 :=
              endpointOffPathCount_eq_four_of_all_off_path P (by
                intro i
                fin_cases i <;> simp_all)
            omega
  · rintro ⟨l, hl_path, hothers_off⟩
    exact endpointOffPathCount_eq_three_of_single_on_path
      P hl_path hothers_off

theorem crossOffPathEndpointCount_eq_three_iff_exists_single_on_path
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    crossOffPathEndpointCount X P = 3 ↔
      Exists fun l : Fin 4 =>
        X.endpoints.endpoint l ∈ P.pathSet ∧
          forall i : Fin 4, i ≠ l -> X.endpoints.endpoint i ∉ P.pathSet := by
  simpa [crossOffPathEndpointCount_eq_endpointOffPathCount P X] using
    endpointOffPathCount_eq_three_iff_exists_single_on_path
      (P := P) (endpoint := X.endpoints.endpoint)

theorem crossOffPathEndpointCount_le_four
    {S H : GeneralSociety V} (P : GMIX24CutPath S) (X : H.Cross) :
    crossOffPathEndpointCount X P <= 4 := by
  simpa [crossOffPathEndpointCount_eq_endpointOffPathCount P X] using
    endpointOffPathCount_le_four P X.endpoints.endpoint

theorem exists_crossOffPathCountMaximal_of_nonempty
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (hcross : Nonempty H.Cross) :
    Exists fun X : H.Cross => CrossOffPathCountMaximal P X := by
  classical
  by_cases h4 : Exists fun X : H.Cross => crossOffPathEndpointCount X P = 4
  · rcases h4 with ⟨X, hX⟩
    refine ⟨X, ?_⟩
    intro Y
    have hY := crossOffPathEndpointCount_le_four P Y
    omega
  · by_cases h3 :
        Exists fun X : H.Cross => crossOffPathEndpointCount X P = 3
    · rcases h3 with ⟨X, hX⟩
      refine ⟨X, ?_⟩
      intro Y
      have hYle := crossOffPathEndpointCount_le_four P Y
      have hYne4 : crossOffPathEndpointCount Y P ≠ 4 := by
        intro hY
        exact h4 ⟨Y, hY⟩
      omega
    · by_cases h2 :
        Exists fun X : H.Cross => crossOffPathEndpointCount X P = 2
      · rcases h2 with ⟨X, hX⟩
        refine ⟨X, ?_⟩
        intro Y
        have hYle := crossOffPathEndpointCount_le_four P Y
        have hYne4 : crossOffPathEndpointCount Y P ≠ 4 := by
          intro hY
          exact h4 ⟨Y, hY⟩
        have hYne3 : crossOffPathEndpointCount Y P ≠ 3 := by
          intro hY
          exact h3 ⟨Y, hY⟩
        omega
      · by_cases h1 :
          Exists fun X : H.Cross => crossOffPathEndpointCount X P = 1
        · rcases h1 with ⟨X, hX⟩
          refine ⟨X, ?_⟩
          intro Y
          have hYle := crossOffPathEndpointCount_le_four P Y
          have hYne4 : crossOffPathEndpointCount Y P ≠ 4 := by
            intro hY
            exact h4 ⟨Y, hY⟩
          have hYne3 : crossOffPathEndpointCount Y P ≠ 3 := by
            intro hY
            exact h3 ⟨Y, hY⟩
          have hYne2 : crossOffPathEndpointCount Y P ≠ 2 := by
            intro hY
            exact h2 ⟨Y, hY⟩
          omega
        · rcases hcross with ⟨X⟩
          refine ⟨X, ?_⟩
          intro Y
          have hXle := crossOffPathEndpointCount_le_four P X
          have hYle := crossOffPathEndpointCount_le_four P Y
          have hXne4 : crossOffPathEndpointCount X P ≠ 4 := by
            intro hX
            exact h4 ⟨X, hX⟩
          have hXne3 : crossOffPathEndpointCount X P ≠ 3 := by
            intro hX
            exact h3 ⟨X, hX⟩
          have hXne2 : crossOffPathEndpointCount X P ≠ 2 := by
            intro hX
            exact h2 ⟨X, hX⟩
          have hXne1 : crossOffPathEndpointCount X P ≠ 1 := by
            intro hX
            exact h1 ⟨X, hX⟩
          have hYne4 : crossOffPathEndpointCount Y P ≠ 4 := by
            intro hY
            exact h4 ⟨Y, hY⟩
          have hYne3 : crossOffPathEndpointCount Y P ≠ 3 := by
            intro hY
            exact h3 ⟨Y, hY⟩
          have hYne2 : crossOffPathEndpointCount Y P ≠ 2 := by
            intro hY
            exact h2 ⟨Y, hY⟩
          have hYne1 : crossOffPathEndpointCount Y P ≠ 1 := by
            intro hY
            exact h1 ⟨Y, hY⟩
          omega


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

