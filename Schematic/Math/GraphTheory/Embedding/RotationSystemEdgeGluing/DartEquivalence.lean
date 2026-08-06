import Schematic.Math.GraphTheory.Embedding.RotationSystemEdgeGluing.CollapsedPlanarity

/-! Transport from surviving sum darts to the simple graph union. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemEdgeGluing

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
variable {x y : V}

/-- Send every surviving summand dart to the same ordered edge in the simple
graph union.  The right marker darts are absent from the source. -/
noncomputable def collapsedDartMap
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y) :
    (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart ->
      OrientedEdge (G₁ ⊔ G₂) := by
  intro d
  rcases d with ⟨⟨e, hez⟩, heu⟩
  cases e with
  | inl e =>
      exact ⟨(e.tail, e.head),
        (sup_adj G₁ G₂ e.tail e.head).mpr (Or.inl e.adj)⟩
  | inr e =>
      exact ⟨(e.tail, e.head),
        (sup_adj G₁ G₂ e.tail e.head).mpr (Or.inr e.adj)⟩

@[simp]
theorem collapsedDartMap_val
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (d : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart) :
    (collapsedDartMap R₁ R₂ hxy₁ hxy₂ d).1 =
      d.1.1.elim (fun e => (e.tail, e.head))
        (fun e => (e.tail, e.head)) := by
  rcases d with ⟨⟨e, hez⟩, heu⟩
  cases e <;> rfl

@[simp]
theorem collapsedDartMap_tail
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (d : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart) :
    (collapsedDartMap R₁ R₂ hxy₁ hxy₂ d).tail =
      RotationSystemGluing.sumTail d.1.1 := by
  rcases d with ⟨⟨e, hez⟩, heu⟩
  cases e <;> rfl

omit [Fintype V] [DecidableEq V]
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] in
private theorem right_dart_ne_markers_of_not_left
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (e : OrientedEdge G₂)
    (hnot : ¬ G₁.Adj e.tail e.head) :
    e ≠ markerForward hxy₂ ∧ e ≠ markerBackward hxy₂ := by
  constructor
  · intro he
    apply hnot
    simpa [he, markerForward] using hxy₁
  · intro he
    apply hnot
    simpa [he, markerBackward, markerForward] using hxy₁.symm

/-- The surviving disjoint-sum darts are exactly the oriented edges of the
simple union when the marker is the only common edge. -/
theorem collapsedDartMap_bijective
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x)) :
    Function.Bijective (collapsedDartMap R₁ R₂ hxy₁ hxy₂) := by
  constructor
  · intro d f hdf
    rcases d with ⟨⟨d, hdz⟩, hdu⟩
    rcases f with ⟨⟨f, hfz⟩, hfu⟩
    have hp := congrArg Subtype.val hdf
    cases d with
    | inl d =>
        cases f with
        | inl f =>
            apply Subtype.ext
            apply Subtype.ext
            apply congrArg Sum.inl
            apply Subtype.ext
            exact hp
        | inr f =>
            have hp' : (d.tail, d.head) = (f.tail, f.head) := hp
            have hpTail : d.tail = f.tail := by
              simpa using congrArg Prod.fst hp'
            have hpHead : d.head = f.head := by
              simpa using congrArg Prod.snd hp'
            have hfAdj : G₂.Adj d.tail d.head := by
              rw [hpTail, hpHead]
              exact f.adj
            rcases hcommon d.adj hfAdj with hxy | hyx
            · have hf : f = markerForward hxy₂ := by
                apply Subtype.ext
                exact hp'.symm.trans (Prod.ext hxy.1 hxy.2)
              apply False.elim
              apply hfz
              simp [hf, duplicateMarker]
            · have hf : f = markerBackward hxy₂ := by
                apply Subtype.ext
                exact hp'.symm.trans (Prod.ext hyx.1 hyx.2)
              apply False.elim
              apply hfu
              apply Subtype.ext
              exact (congrArg Sum.inr hf).trans
                (duplicateOpposite_val R₁ R₂ hxy₁ hxy₂).symm
    | inr d =>
        cases f with
        | inl f =>
            have hp' : (d.tail, d.head) = (f.tail, f.head) := hp
            have hpTail : d.tail = f.tail := by
              simpa using congrArg Prod.fst hp'
            have hpHead : d.head = f.head := by
              simpa using congrArg Prod.snd hp'
            have hdAdj : G₂.Adj f.tail f.head := by
              rw [← hpTail, ← hpHead]
              exact d.adj
            rcases hcommon f.adj hdAdj with hxy | hyx
            · have hd : d = markerForward hxy₂ := by
                apply Subtype.ext
                exact hp'.trans (Prod.ext hxy.1 hxy.2)
              apply False.elim
              apply hdz
              simp [hd, duplicateMarker]
            · have hd : d = markerBackward hxy₂ := by
                apply Subtype.ext
                exact hp'.trans (Prod.ext hyx.1 hyx.2)
              apply False.elim
              apply hdu
              apply Subtype.ext
              exact (congrArg Sum.inr hd).trans
                (duplicateOpposite_val R₁ R₂ hxy₁ hxy₂).symm
        | inr f =>
            apply Subtype.ext
            apply Subtype.ext
            apply congrArg Sum.inr
            apply Subtype.ext
            exact hp
  · intro d
    by_cases h₁ : G₁.Adj d.tail d.head
    · let e : OrientedEdge G₁ := ⟨(d.tail, d.head), h₁⟩
      have hez :
          (Sum.inl e :
            (twoPointSum R₁ R₂ hxy₁ hxy₂).Dart) ≠
            duplicateMarker R₁ R₂ hxy₁ hxy₂ :=
        Sum.inl_ne_inr
      let e' :
          ((twoPointSum R₁ R₂ hxy₁ hxy₂).walkupF
            (duplicateMarker R₁ R₂ hxy₁ hxy₂)).Dart :=
        ⟨Sum.inl e, hez⟩
      have heu : e' ≠ duplicateOpposite R₁ R₂ hxy₁ hxy₂ := by
        intro heu
        have hv := congrArg Subtype.val heu
        simp [e'] at hv
      refine ⟨⟨e', heu⟩, ?_⟩
      apply Subtype.ext
      rfl
    · have h₂ : G₂.Adj d.tail d.head :=
        ((sup_adj G₁ G₂ d.tail d.head).mp d.adj).resolve_left h₁
      let e : OrientedEdge G₂ := ⟨(d.tail, d.head), h₂⟩
      have hmarkers :=
        right_dart_ne_markers_of_not_left hxy₁ hxy₂ e h₁
      have hez :
          (Sum.inr e :
            (twoPointSum R₁ R₂ hxy₁ hxy₂).Dart) ≠
            duplicateMarker R₁ R₂ hxy₁ hxy₂ := by
        intro he
        apply hmarkers.1
        exact Sum.inr.inj he
      let e' :
          ((twoPointSum R₁ R₂ hxy₁ hxy₂).walkupF
            (duplicateMarker R₁ R₂ hxy₁ hxy₂)).Dart :=
        ⟨Sum.inr e, hez⟩
      have heu : e' ≠ duplicateOpposite R₁ R₂ hxy₁ hxy₂ := by
        intro heu
        apply hmarkers.2
        have hv := congrArg Subtype.val heu
        have hv' :
            (Sum.inr e :
              (twoPointSum R₁ R₂ hxy₁ hxy₂).Dart) =
              Sum.inr (markerBackward hxy₂) := by
          simpa [e'] using hv.trans
            (duplicateOpposite_val R₁ R₂ hxy₁ hxy₂)
        exact Sum.inr.inj hv'
      refine ⟨⟨e', heu⟩, ?_⟩
      apply Subtype.ext
      rfl

noncomputable def collapsedDartEquiv
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (hcommon : forall ⦃a b : V⦄,
      G₁.Adj a b -> G₂.Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x)) :
    (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart ≃
      OrientedEdge (G₁ ⊔ G₂) :=
  Equiv.ofBijective (collapsedDartMap R₁ R₂ hxy₁ hxy₂)
    (collapsedDartMap_bijective R₁ R₂ hxy₁ hxy₂ hcommon)

theorem collapsedHypermap_edge_source
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (d : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart) :
    ((collapsedHypermap R₁ R₂ hxy₁ hxy₂).edge d).1.1 =
      (twoPointSum R₁ R₂ hxy₁ hxy₂).edge d.1.1 := by
  let K := twoPointSum R₁ R₂ hxy₁ hxy₂
  let z := duplicateMarker R₁ R₂ hxy₁ hxy₂
  let hplain := twoPointSum_plain R₁ R₂ hxy₁ hxy₂
  let u := duplicateOpposite R₁ R₂ hxy₁ hxy₂
  change (((K.walkupF z).walkupE u).edge d).1.1 = K.edge d.1.1
  have hu : u =
      (⟨K.edge z, Hypermap.Plain.edge_ne (G := K) hplain z⟩ :
        (K.walkupF z).Dart) := by
    apply Subtype.ext
    rfl
  subst u
  exact K.walkupF_walkupE_opposite_edge_apply_coe hplain z d

theorem collapsedDartMap_edge
    (R₁ : RotationSystem G₁) (R₂ : RotationSystem G₂)
    (hxy₁ : G₁.Adj x y) (hxy₂ : G₂.Adj x y)
    (d : (collapsedHypermap R₁ R₂ hxy₁ hxy₂).Dart) :
    collapsedDartMap R₁ R₂ hxy₁ hxy₂
        ((collapsedHypermap R₁ R₂ hxy₁ hxy₂).edge d) =
      (collapsedDartMap R₁ R₂ hxy₁ hxy₂ d).symm := by
  apply Subtype.ext
  let code : Sum (OrientedEdge G₁) (OrientedEdge G₂) -> V × V :=
    fun e => e.elim (fun f => (f.tail, f.head))
      (fun f => (f.tail, f.head))
  calc
    (collapsedDartMap R₁ R₂ hxy₁ hxy₂
        ((collapsedHypermap R₁ R₂ hxy₁ hxy₂).edge d)).1 =
        code ((collapsedHypermap R₁ R₂ hxy₁ hxy₂).edge d).1.1 :=
      collapsedDartMap_val R₁ R₂ hxy₁ hxy₂ _
    _ = code ((twoPointSum R₁ R₂ hxy₁ hxy₂).edge d.1.1) := by
      rw [collapsedHypermap_edge_source]
    _ = ((collapsedDartMap R₁ R₂ hxy₁ hxy₂ d).symm).1 := by
      rcases d with ⟨⟨d, hdz⟩, hdu⟩
      cases d <;> rfl


end RotationSystemEdgeGluing
end FourColor
end Schematic.Math.GraphTheory
