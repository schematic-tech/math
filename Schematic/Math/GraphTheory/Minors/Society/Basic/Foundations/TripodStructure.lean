import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.CrossPairedReplacements

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The structural core of a GM IX tripod: three internally disjoint
`u`--`v` rim paths, one internal attachment on each rim, and a disjoint
linkage from those attachments to three boundary vertices.

The printed GM IX definition phrases the linkage as
`{s_1,s_2,s_3} -> {t_1,t_2,t_3}` with respect to the rim union and the society
boundary.  The "with respect to the boundary" part is recorded below as
`Tripod.LegBoundaryClean`; the older raw structure is kept because much of the
existing constructor library builds and transforms this structural core before
proving the relevant source-cleanliness facts. -/
structure Tripod (S : GeneralSociety V) where
  left : V
  right : V
  left_ne_right : left ≠ right
  rim : Fin 3 -> S.graph.Walk left right
  rim_isPath : forall i : Fin 3, (rim i).IsPath
  attach : Fin 3 -> V
  attach_mem_rim : forall i : Fin 3, attach i ∈ Walk.InternalVertices (rim i)
  boundary : Fin 3 -> V
  boundary_mem : forall i : Fin 3, boundary i ∈ S.boundarySet
  boundary_injective : Function.Injective boundary
  leg : forall i : Fin 3, S.graph.Walk (attach i) (boundary i)
  leg_isPath : forall i : Fin 3, (leg i).IsPath
  rim_internals_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint (Walk.InternalVertices (rim i)) (Walk.InternalVertices (rim j))
  legs_pairwise_disjoint :
    forall i j : Fin 3, i ≠ j ->
      Disjoint {v : V | v ∈ (leg i).support}
        {v : V | v ∈ (leg j).support}
  legs_meet_rims_only_at_attach :
    forall i j : Fin 3, forall v : V,
      v ∈ (leg i).support ->
        v ∈ (rim j).support ->
          v = attach i

@[simp]
theorem Tripod.cast_left {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) :
    (h ▸ X : T.Tripod).left = X.left := by
  cases h
  rfl

@[simp]
theorem Tripod.cast_right {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) :
    (h ▸ X : T.Tripod).right = X.right := by
  cases h
  rfl

@[simp]
theorem Tripod.cast_rim_support {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (i : Fin 3) :
    ((h ▸ X : T.Tripod).rim i).support = (X.rim i).support := by
  cases h
  rfl

@[simp]
theorem Tripod.cast_leg_support {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (i : Fin 3) :
    ((h ▸ X : T.Tripod).leg i).support = (X.leg i).support := by
  cases h
  rfl

@[simp]
theorem Tripod.cast_leg_nil {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (i : Fin 3) :
    ((h ▸ X : T.Tripod).leg i).Nil ↔ (X.leg i).Nil := by
  cases h
  rfl

@[simp]
theorem Tripod.cast_boundary {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (i : Fin 3) :
    (h ▸ X : T.Tripod).boundary i = X.boundary i := by
  cases h
  rfl

namespace Tripod

/-- The boundary-clean part of the paper's `X -> Ω` condition for the three
tripod linkage paths: no internal vertex of a leg is a society-boundary vertex.

This is weaker than `LegBoundaryContactClean`: it does not rule out the start
of a leg being a society-boundary vertex different from the terminal foot.
It is also weaker than `BoundaryClean`, which rules out boundary contacts on
the rim endpoints and rim interiors. -/
def LegBoundaryClean {S : GeneralSociety V} (T : S.Tripod) : Prop :=
  forall i : Fin 3, Disjoint (Walk.InternalVertices (T.leg i)) S.boundarySet

/-- Exact boundary-clean condition for the paper's `X -> Ω` linkage legs:
the terminal foot is the only society-boundary vertex on each leg. -/
def LegBoundaryContactClean {S : GeneralSociety V} (T : S.Tripod) : Prop :=
  forall i : Fin 3, forall z : V,
    z ∈ (T.leg i).support -> z ∈ S.boundarySet -> z = T.boundary i

theorem legBoundaryContactClean_legBoundaryClean
    {S : GeneralSociety V} {T : S.Tripod}
    (hclean : T.LegBoundaryContactClean) :
    T.LegBoundaryClean := by
  intro i
  rw [Set.disjoint_left]
  intro z hzInternal hzBoundary
  exact hzInternal.2.2 (hclean i z hzInternal.1 hzBoundary)

/-- First-boundary normalization for one raw tripod leg.

The paper's tripod linkage paths are `X -> Ω` paths, so after leaving the
rim union they have no intermediate boundary contact.  The structural `Tripod`
object only records the final selected boundary foot.  This lemma isolates
the canonical source-clean prefix: stop the leg at its first society-boundary
vertex. -/
theorem exists_leg_prefix_first_boundary
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    Exists fun b : V =>
      Exists fun hb : b ∈ (T.leg i).support =>
        b ∈ S.boundarySet ∧
          forall z : V,
            z ∈ ((T.leg i).takeUntil b hb).support ->
              z ∈ S.boundarySet -> z = b := by
  exact
    Walk.IsPath.exists_takeUntil_first_mem
      (G := S.graph) (T.leg_isPath i) S.boundarySet (T.boundary_mem i)

/-- The prefix supplied by `exists_leg_prefix_first_boundary` has the
boundary-clean internal-vertex property required by a GM IX `X -> Ω` path. -/
theorem leg_prefix_first_boundary_internal_disjoint
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod) {i : Fin 3}
    {b : V} (hb : b ∈ (T.leg i).support)
    (hfirst :
      forall z : V,
        z ∈ ((T.leg i).takeUntil b hb).support ->
          z ∈ S.boundarySet -> z = b) :
    Disjoint
      (Walk.InternalVertices ((T.leg i).takeUntil b hb))
      S.boundarySet := by
  rw [Set.disjoint_left]
  intro z hzInternal hzBoundary
  exact hzInternal.2.2 (hfirst z hzInternal.1 hzBoundary)

/-- Simultaneous first-boundary choices for the three raw legs of a tripod. -/
structure FirstBoundaryLegData [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod) where
  boundary : Fin 3 -> V
  boundary_mem_leg : forall i : Fin 3, boundary i ∈ (T.leg i).support
  boundary_mem : forall i : Fin 3, boundary i ∈ S.boundarySet
  first :
    forall i : Fin 3, forall z : V,
      z ∈ ((T.leg i).takeUntil (boundary i) (boundary_mem_leg i)).support ->
        z ∈ S.boundarySet -> z = boundary i

/-- Choose the first society-boundary vertex on each raw leg. -/
noncomputable def firstBoundaryLegData
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod) :
    FirstBoundaryLegData T := by
  classical
  refine
    { boundary := fun i =>
        Classical.choose (T.exists_leg_prefix_first_boundary i)
      boundary_mem_leg := ?_
      boundary_mem := ?_
      first := ?_ }
  · intro i
    exact
      Classical.choose
        (Classical.choose_spec (T.exists_leg_prefix_first_boundary i))
  · intro i
    exact
      (Classical.choose_spec
        (Classical.choose_spec (T.exists_leg_prefix_first_boundary i))).1
  · intro i z hz hzBoundary
    exact
      (Classical.choose_spec
        (Classical.choose_spec (T.exists_leg_prefix_first_boundary i))).2
        z hz hzBoundary

theorem FirstBoundaryLegData.prefix_internal_disjoint
    [DecidableEq V]
    {S : GeneralSociety V} {T : S.Tripod}
    (D : FirstBoundaryLegData T) (i : Fin 3) :
    Disjoint
      (Walk.InternalVertices
        ((T.leg i).takeUntil (D.boundary i) (D.boundary_mem_leg i)))
      S.boundarySet :=
  T.leg_prefix_first_boundary_internal_disjoint
    (D.boundary_mem_leg i) (D.first i)

theorem FirstBoundaryLegData.boundary_injective
    [DecidableEq V]
    {S : GeneralSociety V} {T : S.Tripod}
    (D : FirstBoundaryLegData T) :
    Function.Injective D.boundary := by
  intro i j hij
  by_contra hne
  exact
    Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hne)
      (D.boundary_mem_leg i)
      (by simpa [hij] using D.boundary_mem_leg j)

theorem FirstBoundaryLegData.boundary_eq_attach_of_attach_boundary
    [DecidableEq V]
    {S : GeneralSociety V} {T : S.Tripod}
    (D : FirstBoundaryLegData T) {i : Fin 3}
    (hattach : T.attach i ∈ S.boundarySet) :
    D.boundary i = T.attach i := by
  have hstart :
      T.attach i ∈
        ((T.leg i).takeUntil (D.boundary i) (D.boundary_mem_leg i)).support :=
    ((T.leg i).takeUntil (D.boundary i) (D.boundary_mem_leg i)).start_mem_support
  exact (D.first i (T.attach i) hstart hattach).symm

theorem FirstBoundaryLegData.leg_prefix_boundary_contact_eq
    [DecidableEq V]
    {S : GeneralSociety V} {T : S.Tripod}
    (D : FirstBoundaryLegData T) {i : Fin 3} {z : V}
    (hz :
      z ∈
        ((T.leg i).takeUntil (D.boundary i) (D.boundary_mem_leg i)).support)
    (hzBoundary : z ∈ S.boundarySet) :
    z = D.boundary i :=
  D.first i z hz hzBoundary

/-- Trim every raw tripod leg at its first society-boundary vertex.

The rims and attachment vertices are unchanged.  The new boundary feet are the
first boundary contacts along the old legs, so the resulting tripod satisfies
the source `X -> Ω` internal cleanliness for its legs. -/
def trimLegsToFirstBoundary
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod)
    (D : FirstBoundaryLegData T) :
    S.Tripod where
  left := T.left
  right := T.right
  left_ne_right := T.left_ne_right
  rim := T.rim
  rim_isPath := T.rim_isPath
  attach := T.attach
  attach_mem_rim := T.attach_mem_rim
  boundary := D.boundary
  boundary_mem := D.boundary_mem
  boundary_injective := D.boundary_injective
  leg i := (T.leg i).takeUntil (D.boundary i) (D.boundary_mem_leg i)
  leg_isPath i := (T.leg_isPath i).takeUntil (D.boundary_mem_leg i)
  rim_internals_disjoint := T.rim_internals_disjoint
  legs_pairwise_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro v hv_i hv_j
    exact
      Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
        (SimpleGraph.Walk.support_takeUntil_subset (T.leg i)
          (D.boundary_mem_leg i) hv_i)
        (SimpleGraph.Walk.support_takeUntil_subset (T.leg j)
          (D.boundary_mem_leg j) hv_j)
  legs_meet_rims_only_at_attach := by
    intro i j v hv_leg hv_rim
    exact T.legs_meet_rims_only_at_attach i j v
      (SimpleGraph.Walk.support_takeUntil_subset (T.leg i)
        (D.boundary_mem_leg i) hv_leg)
      hv_rim

theorem trimLegsToFirstBoundary_legBoundaryClean
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod)
    (D : FirstBoundaryLegData T) :
    (T.trimLegsToFirstBoundary D).LegBoundaryClean := by
  intro i
  simpa [trimLegsToFirstBoundary] using D.prefix_internal_disjoint i

theorem trimLegsToFirstBoundary_leg_boundary_contact_eq
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod)
    (D : FirstBoundaryLegData T) {i : Fin 3} {z : V}
    (hz : z ∈ ((T.trimLegsToFirstBoundary D).leg i).support)
    (hzBoundary : z ∈ S.boundarySet) :
    z = (T.trimLegsToFirstBoundary D).boundary i := by
  simpa [trimLegsToFirstBoundary] using
    D.leg_prefix_boundary_contact_eq (i := i) hz hzBoundary

theorem trimLegsToFirstBoundary_legBoundaryContactClean
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod)
    (D : FirstBoundaryLegData T) :
    (T.trimLegsToFirstBoundary D).LegBoundaryContactClean := by
  intro i z hz hzBoundary
  exact T.trimLegsToFirstBoundary_leg_boundary_contact_eq D hz hzBoundary

theorem exists_legBoundaryClean_tripod_of_exists_tripod
    [DecidableEq V]
    {S : GeneralSociety V}
    (hT : Nonempty S.Tripod) :
    Exists fun T : S.Tripod => T.LegBoundaryClean := by
  rcases hT with ⟨T⟩
  let D := T.firstBoundaryLegData
  exact ⟨T.trimLegsToFirstBoundary D,
    T.trimLegsToFirstBoundary_legBoundaryClean D⟩

theorem exists_legBoundaryContactClean_tripod_of_exists_tripod
    [DecidableEq V]
    {S : GeneralSociety V}
    (hT : Nonempty S.Tripod) :
    Exists fun T : S.Tripod => T.LegBoundaryContactClean := by
  rcases hT with ⟨T⟩
  let D := T.firstBoundaryLegData
  exact ⟨T.trimLegsToFirstBoundary D,
    T.trimLegsToFirstBoundary_legBoundaryContactClean D⟩

theorem no_tripod_of_no_legBoundaryClean_tripod
    [DecidableEq V]
    {S : GeneralSociety V}
    (hclean :
      forall T : S.Tripod, T.LegBoundaryClean -> False) :
    Not (Nonempty S.Tripod) := by
  intro hT
  rcases exists_legBoundaryClean_tripod_of_exists_tripod hT with
    ⟨T, hTclean⟩
  exact hclean T hTclean

theorem no_tripod_of_no_legBoundaryContactClean_tripod
    [DecidableEq V]
    {S : GeneralSociety V}
    (hclean :
      forall T : S.Tripod, T.LegBoundaryContactClean -> False) :
    Not (Nonempty S.Tripod) := by
  intro hT
  rcases exists_legBoundaryContactClean_tripod_of_exists_tripod hT with
    ⟨T, hTclean⟩
  exact hclean T hTclean

def vertexSet {S : GeneralSociety V} (T : S.Tripod) : Set V :=
  {v | (Exists fun i : Fin 3 => v ∈ (T.rim i).support) ∨
    Exists fun i : Fin 3 => v ∈ (T.leg i).support}

@[simp]
theorem cast_vertexSet {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) :
    (h ▸ X : T.Tripod).vertexSet = X.vertexSet := by
  cases h
  rfl

@[simp]
theorem cast_rim_internalVertices {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (i : Fin 3) :
    Walk.InternalVertices ((h ▸ X : T.Tripod).rim i) =
      Walk.InternalVertices (X.rim i) := by
  cases h
  rfl

theorem rim_mem_vertexSet {S : GeneralSociety V} (T : S.Tripod)
    {i : Fin 3} {v : V} (hv : v ∈ (T.rim i).support) :
    v ∈ T.vertexSet := by
  exact Or.inl ⟨i, hv⟩

theorem leg_mem_vertexSet {S : GeneralSociety V} (T : S.Tripod)
    {i : Fin 3} {v : V} (hv : v ∈ (T.leg i).support) :
    v ∈ T.vertexSet := by
  exact Or.inr ⟨i, hv⟩

theorem left_mem_vertexSet {S : GeneralSociety V} (T : S.Tripod) :
    T.left ∈ T.vertexSet :=
  T.rim_mem_vertexSet (i := 0) (T.rim 0).start_mem_support

theorem right_mem_vertexSet {S : GeneralSociety V} (T : S.Tripod) :
    T.right ∈ T.vertexSet :=
  T.rim_mem_vertexSet (i := 0) (T.rim 0).end_mem_support

theorem attach_mem_vertexSet {S : GeneralSociety V} (T : S.Tripod)
    (i : Fin 3) :
    T.attach i ∈ T.vertexSet :=
  T.rim_mem_vertexSet (i := i) (T.attach_mem_rim i).1

theorem boundary_mem_vertexSet {S : GeneralSociety V} (T : S.Tripod)
    (i : Fin 3) :
    T.boundary i ∈ T.vertexSet :=
  T.leg_mem_vertexSet (i := i) (T.leg i).end_mem_support


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
