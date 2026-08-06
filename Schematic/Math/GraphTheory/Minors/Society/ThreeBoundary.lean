import Schematic.Math.GraphTheory.Minors.Society.General

/-!
Three-boundary society adapters.

This file is intentionally small.  Earlier versions carried a separate
three-boundary proof attempt for Graph Minors IX `(2.4)` using a long local
GM IX `(2.1)`/maximal-candidate development.  That route has been retired:
the live theorem is the source-aligned general cyclic-society theorem in
`Schematic.Math.GraphTheory.Minors.Society.General`, and this file only specializes that theorem
to the three named boundary vertices used by the RST layer.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

variable {V : Type u}
variable {G : SimpleGraph V}

def fin3Triple (i j k : Fin 3) : Fin 3 -> Fin 3
  | 0 => i
  | 1 => j
  | 2 => k

theorem fin3Triple_injective
    {i j k : Fin 3}
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    Function.Injective (fin3Triple i j k) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [fin3Triple] at hab ⊢
  · exact False.elim (hij hab)
  · exact False.elim (hik hab)
  · exact False.elim (hij hab.symm)
  · exact False.elim (hjk hab)
  · exact False.elim (hik hab.symm)
  · exact False.elim (hjk hab.symm)

/-- A local society whose boundary is indexed by a fixed type. -/
structure BoundarySociety (G : SimpleGraph V) (ι : Type*) where
  boundary : ι -> V

abbrev ThreeBoundarySociety (G : SimpleGraph V) :=
  BoundarySociety G (Fin 3)

/-- The endpoint part of a GM IX cross, abstracted away from the two paths. -/
structure FourBoundaryEndpoints (boundary : Fin 3 -> V) where
  endpoint : Fin 4 -> V
  endpoint_mem_boundary : forall i : Fin 4, endpoint i ∈ Set.range boundary
  endpoint_injective : Function.Injective endpoint

theorem no_fourBoundaryEndpoints_on_three_boundary
    {boundary : Fin 3 -> V} :
    Not (Nonempty (FourBoundaryEndpoints boundary)) := by
  rintro ⟨X⟩
  exact
    not_injective_of_maps_fin4_into_injective_fin3_range
      X.endpoint X.endpoint_mem_boundary X.endpoint_injective

/-- The three-boundary specialization of the GM IX tripod. -/
structure ThreeBoundaryTripod
    (G : SimpleGraph V)
    (boundary : Fin 3 -> V) where
  left : V
  right : V
  left_ne_right : left ≠ right
  left_not_boundary : forall i : Fin 3, left ≠ boundary i
  right_not_boundary : forall i : Fin 3, right ≠ boundary i
  rim : Fin 3 -> G.Walk left right
  rim_isPath : forall i : Fin 3, (rim i).IsPath
  attach : Fin 3 -> V
  attach_mem_rim : forall i : Fin 3, attach i ∈ Walk.InternalVertices (rim i)
  rim_internals_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint (Walk.InternalVertices (rim i)) (Walk.InternalVertices (rim j))
  leg : forall i : Fin 3, G.Walk (attach i) (boundary i)
  leg_isPath : forall i : Fin 3, (leg i).IsPath
  legs_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint {v : V | v ∈ (leg i).support} {v : V | v ∈ (leg j).support}
  leg_meets_rims_only_at_attach :
    forall i j : Fin 3, forall v : V,
      v ∈ (leg i).support ->
      v ∈ (rim j).support ->
        v = attach i

def ThreeBoundaryTripod.reindex
    {boundary : Fin 3 -> V}
    (H : ThreeBoundaryTripod G boundary)
    (e : Fin 3 -> Fin 3)
    (he : Function.Injective e) :
    ThreeBoundaryTripod G (fun i : Fin 3 => boundary (e i)) where
  left := H.left
  right := H.right
  left_ne_right := H.left_ne_right
  left_not_boundary := fun i => H.left_not_boundary (e i)
  right_not_boundary := fun i => H.right_not_boundary (e i)
  rim := fun i => H.rim (e i)
  rim_isPath := fun i => H.rim_isPath (e i)
  attach := fun i => H.attach (e i)
  attach_mem_rim := fun i => H.attach_mem_rim (e i)
  rim_internals_disjoint := by
    intro i j hij
    exact H.rim_internals_disjoint (e i) (e j) (fun h => hij (he h))
  leg := fun i => H.leg (e i)
  leg_isPath := fun i => H.leg_isPath (e i)
  legs_disjoint := by
    intro i j hij
    exact H.legs_disjoint (e i) (e j) (fun h => hij (he h))
  leg_meets_rims_only_at_attach := by
    intro i j v hvleg hvrim
    exact H.leg_meets_rims_only_at_attach (e i) (e j) v hvleg hvrim

def ThreeBoundaryTripod.changeBoundary
    {boundary boundary' : Fin 3 -> V}
    (H : ThreeBoundaryTripod G boundary)
    (hboundary : boundary = boundary') :
    ThreeBoundaryTripod G boundary' := by
  cases hboundary
  exact H

/-- The three-boundary rural conclusion used by RST. -/
structure ThreeBoundaryRural
    (G : SimpleGraph V)
    (_boundary : Fin 3 -> V) : Prop where
  planar : IsPlanar G

theorem ThreeBoundaryRural.isPlanar
    {boundary : Fin 3 -> V}
    (R : ThreeBoundaryRural G boundary) :
    IsPlanar G :=
  R.planar

theorem ThreeBoundaryRural.of_isPlanar
    {boundary : Fin 3 -> V}
    (hG : IsPlanar G) :
    ThreeBoundaryRural G boundary where
  planar := hG

/-- The cyclic-boundary society associated to three named boundary vertices. -/
def threeBoundaryCyclicBoundary
    (boundary : Fin 3 -> V)
    (hinj : Function.Injective boundary) :
    CyclicBoundary V where
  vertices := [boundary 0, boundary 1, boundary 2]
  nodup := by
    simp [hinj.eq_iff]

/-- View a three-boundary society as a general cyclic-boundary society. -/
def generalSocietyOfThreeBoundary
    (G : SimpleGraph V)
    (boundary : Fin 3 -> V)
    (hinj : Function.Injective boundary) :
    GeneralSociety V where
  graph := G
  boundary := threeBoundaryCyclicBoundary boundary hinj

@[simp]
theorem generalSocietyOfThreeBoundary_boundarySet
    (G : SimpleGraph V)
    (boundary : Fin 3 -> V)
    (hinj : Function.Injective boundary) :
    (generalSocietyOfThreeBoundary G boundary hinj).boundarySet =
      Set.range boundary := by
  ext v
  constructor
  · intro hv
    simp [generalSocietyOfThreeBoundary, threeBoundaryCyclicBoundary,
      GeneralSociety.boundarySet, CyclicBoundary.vertexSet] at hv
    rcases hv with hv | hv | hv
    · exact ⟨0, hv.symm⟩
    · exact ⟨1, hv.symm⟩
    · exact ⟨2, hv.symm⟩
  · intro hv
    rcases hv with ⟨i, rfl⟩
    fin_cases i <;> simp [generalSocietyOfThreeBoundary,
      threeBoundaryCyclicBoundary, GeneralSociety.boundarySet,
      CyclicBoundary.vertexSet]

theorem generalSocietyOfThreeBoundary_no_cross
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary) :
    Not (Nonempty (generalSocietyOfThreeBoundary G boundary hinj).Cross) := by
  rintro ⟨X⟩
  let Y : FourBoundaryEndpoints boundary := {
    endpoint := X.endpoints.endpoint
    endpoint_mem_boundary := by
      intro i
      have hmem :
          X.endpoints.endpoint i ∈
            (generalSocietyOfThreeBoundary G boundary hinj).boundarySet :=
        X.endpoints.endpoint_mem i
      simpa [generalSocietyOfThreeBoundary_boundarySet] using hmem
    endpoint_injective := X.endpoints.endpoint_injective
  }
  exact no_fourBoundaryEndpoints_on_three_boundary ⟨Y⟩

/-- A general-society tripod whose boundary feet are already indexed by
`T.boundary` is a three-boundary tripod for that boundary. -/
def GeneralSociety.Tripod.toThreeBoundaryTripodSameBoundary
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary)
    (T : (generalSocietyOfThreeBoundary G boundary hinj).Tripod) :
    ThreeBoundaryTripod G T.boundary where
  left := T.left
  right := T.right
  left_ne_right := T.left_ne_right
  left_not_boundary := by
    intro i hleft
    have hleg : T.left ∈ (T.leg i).support := by
      simp [hleft]
    have hrim : T.left ∈ (T.rim i).support :=
      (T.rim i).start_mem_support
    have hattach :=
      T.legs_meet_rims_only_at_attach i i T.left hleg hrim
    exact (T.attach_mem_rim i).2.1 hattach.symm
  right_not_boundary := by
    intro i hright
    have hleg : T.right ∈ (T.leg i).support := by
      simp [hright]
    have hrim : T.right ∈ (T.rim i).support :=
      (T.rim i).end_mem_support
    have hattach :=
      T.legs_meet_rims_only_at_attach i i T.right hleg hrim
    exact (T.attach_mem_rim i).2.2 hattach.symm
  rim := T.rim
  rim_isPath := T.rim_isPath
  attach := T.attach
  attach_mem_rim := T.attach_mem_rim
  rim_internals_disjoint := T.rim_internals_disjoint
  leg := T.leg
  leg_isPath := T.leg_isPath
  legs_disjoint := T.legs_pairwise_disjoint
  leg_meets_rims_only_at_attach := T.legs_meet_rims_only_at_attach

/-- Convert a general-society tripod in the three-boundary adapter back to
the paper-facing three-boundary tripod. -/
noncomputable def GeneralSociety.Tripod.toThreeBoundaryTripod
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary)
    (T : (generalSocietyOfThreeBoundary G boundary hinj).Tripod) :
    ThreeBoundaryTripod G boundary := by
  classical
  let S : GeneralSociety V := generalSocietyOfThreeBoundary G boundary hinj
  have hT_subset : Set.range T.boundary ⊆ Set.range boundary := by
    intro v hv
    rcases hv with ⟨i, rfl⟩
    have hmem : T.boundary i ∈ S.boundarySet := T.boundary_mem i
    simpa [S, generalSocietyOfThreeBoundary_boundarySet] using hmem
  have hcardT : (Set.range T.boundary).ncard = 3 := by
    rw [Set.ncard_range_of_injective T.boundary_injective]
    simp
  have hcardB : (Set.range boundary).ncard = 3 := by
    rw [Set.ncard_range_of_injective hinj]
    simp
  have hB_le_T :
      (Set.range boundary).ncard <= (Set.range T.boundary).ncard := by
    omega
  have hRangeEq : Set.range T.boundary = Set.range boundary :=
    Set.eq_of_subset_of_ncard_le hT_subset hB_le_T
  have hboundary_mem_T :
      forall i : Fin 3, boundary i ∈ Set.range T.boundary := by
    intro i
    rw [hRangeEq]
    exact ⟨i, rfl⟩
  let e : Fin 3 -> Fin 3 := fun i =>
    Classical.choose (hboundary_mem_T i)
  have he : forall i : Fin 3, T.boundary (e i) = boundary i := by
    intro i
    exact Classical.choose_spec (hboundary_mem_T i)
  have he_inj : Function.Injective e := by
    intro i j hij
    apply hinj
    rw [← he i, ← he j, hij]
  exact ((T.toThreeBoundaryTripodSameBoundary hinj).reindex e he_inj).changeBoundary
    (funext he)

theorem generalSocietyOfThreeBoundary_no_tripod_of_no_threeBoundaryTripod
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary)
    (hno : Not (Nonempty (ThreeBoundaryTripod G boundary))) :
    Not (Nonempty (generalSocietyOfThreeBoundary G boundary hinj).Tripod) := by
  rintro ⟨T⟩
  exact hno ⟨T.toThreeBoundaryTripod hinj⟩

theorem ThreeBoundaryRural.of_generalSociety
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary)
    (R : (generalSocietyOfThreeBoundary G boundary hinj).Rural) :
    ThreeBoundaryRural G boundary where
  planar := R.planar

/-- A completed general GM IX `(2.4)` theorem gives the three-boundary
rural/tripod alternative once the three-boundary society has been shown
`ThreeConnected` in the general-society sense. -/
theorem generalSocietyOfThreeBoundary_rural_or_tripod_of_GMIX24Statement
    [DecidableEq V]
    (hGM : GeneralSociety.GMIX24Statement (V := V))
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary)
    (hthree :
      (generalSocietyOfThreeBoundary G boundary hinj).ThreeConnected) :
    Nonempty (ThreeBoundaryTripod G boundary) ∨
      Nonempty (ThreeBoundaryRural G boundary) := by
  classical
  by_cases htripod : Nonempty (ThreeBoundaryTripod G boundary)
  · exact Or.inl htripod
  · have hno_cross :
        Not
          (Nonempty
            (generalSocietyOfThreeBoundary G boundary hinj).Cross) :=
      generalSocietyOfThreeBoundary_no_cross (G := G) hinj
    have hno_tripod :
        Not
          (Nonempty
            (generalSocietyOfThreeBoundary G boundary hinj).Tripod) :=
      generalSocietyOfThreeBoundary_no_tripod_of_no_threeBoundaryTripod
        (G := G) hinj htripod
    obtain ⟨R⟩ :=
      hGM (generalSocietyOfThreeBoundary G boundary hinj)
        hthree hno_cross hno_tripod
    exact Or.inr ⟨ThreeBoundaryRural.of_generalSociety (G := G) hinj R⟩

/-- Direct four-connected upgrade to the general-society 3-connectedness
hypothesis.  This is the preferred route in the paper formalization. -/
theorem generalSocietyOfThreeBoundary_threeConnected_of_fourConnected
    [Fintype V]
    {boundary : Fin 3 -> V}
    (hinj : Function.Injective boundary)
    (hG : IsFourConnected G) :
    (generalSocietyOfThreeBoundary G boundary hinj).ThreeConnected := by
  classical
  intro S hboundary hright horder
  rcases hright with ⟨v, hv, _hvActive⟩
  by_cases hleft_only : (S.left \ S.right).Nonempty
  · exact isFourConnected_no_proper_separation_orderAtMost_three
      hG S ⟨hleft_only, ⟨v, hv⟩⟩
      (S.orderAtMost_mono horder (by decide))
  · have hleft_subset_right : S.left ⊆ S.right := by
      intro x hxleft
      by_contra hxright
      exact hleft_only ⟨x, hxleft, hxright⟩
    have hrange_subset_separator : Set.range boundary ⊆ S.separator := by
      rintro x ⟨i, rfl⟩
      have hleft : boundary i ∈ S.left := by
        exact hboundary (by
          rw [generalSocietyOfThreeBoundary_boundarySet]
          exact ⟨i, rfl⟩)
      exact ⟨hleft, hleft_subset_right hleft⟩
    have hrange_card : (Set.range boundary).ncard = 3 := by
      rw [Set.ncard_range_of_injective hinj]
      simp
    have hseparator_le_two : S.separator.ncard <= 2 :=
      S.separator_ncard_le_of_orderAtMost horder
    have hrange_le_separator :
        (Set.range boundary).ncard <= S.separator.ncard :=
      Set.ncard_le_ncard hrange_subset_separator
    omega

end Schematic.Math.GraphTheory
