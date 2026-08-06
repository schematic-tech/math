import Schematic.Math.GraphTheory.Minors.Society.Basic.TripodOptimization

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Reverse the common rim endpoints of a tripod, leaving the three boundary
feet and legs fixed. -/
def flip {S : GeneralSociety V} (T : S.Tripod) : S.Tripod where
  left := T.right
  right := T.left
  left_ne_right := T.left_ne_right.symm
  rim i := (T.rim i).reverse
  rim_isPath i := (T.rim_isPath i).reverse
  attach i := T.attach i
  attach_mem_rim i := by
    rw [Walk.internalVertices_reverse]
    exact T.attach_mem_rim i
  boundary i := T.boundary i
  boundary_mem i := T.boundary_mem i
  boundary_injective := T.boundary_injective
  leg i := T.leg i
  leg_isPath i := T.leg_isPath i
  rim_internals_disjoint := by
    intro i j hij
    rw [Walk.internalVertices_reverse, Walk.internalVertices_reverse]
    exact T.rim_internals_disjoint i j hij
  legs_pairwise_disjoint := T.legs_pairwise_disjoint
  legs_meet_rims_only_at_attach := by
    intro i j v hvLeg hvRim
    have hvRim' : v ∈ (T.rim j).support := by
      simpa [SimpleGraph.Walk.support_reverse] using hvRim
    exact T.legs_meet_rims_only_at_attach i j v hvLeg hvRim'

@[simp]
theorem flip_left {S : GeneralSociety V} (T : S.Tripod) :
    T.flip.left = T.right := rfl

@[simp]
theorem flip_right {S : GeneralSociety V} (T : S.Tripod) :
    T.flip.right = T.left := rfl

@[simp]
theorem flip_rim {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    T.flip.rim i = (T.rim i).reverse := rfl

@[simp]
theorem flip_attach {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    T.flip.attach i = T.attach i := rfl

@[simp]
theorem flip_boundary {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    T.flip.boundary i = T.boundary i := rfl

@[simp]
theorem flip_leg {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    T.flip.leg i = T.leg i := rfl

@[simp]
theorem flip_vertexSet {S : GeneralSociety V} (T : S.Tripod) :
    T.flip.vertexSet = T.vertexSet := by
  ext v
  constructor
  · intro hv
    rcases hv with hvRim | hvLeg
    · rcases hvRim with ⟨i, hi⟩
      exact Or.inl ⟨i, by
        simpa [SimpleGraph.Walk.support_reverse] using hi⟩
    · exact Or.inr hvLeg
  · intro hv
    rcases hv with hvRim | hvLeg
    · rcases hvRim with ⟨i, hi⟩
      exact Or.inl ⟨i, by
        simpa [SimpleGraph.Walk.support_reverse] using hi⟩
    · exact Or.inr hvLeg

theorem boundaryClean_flip {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.BoundaryClean) :
    T.flip.BoundaryClean := by
  refine ⟨hclean.2.1, hclean.1, ?_, ?_⟩
  · intro i
    simpa [Tripod.flip, Walk.internalVertices_reverse] using hclean.2.2.1 i
  · intro i
    simpa [Tripod.flip] using hclean.2.2.2 i

theorem boundaryClean_leg_not_nil {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.BoundaryClean) (i : Fin 3) :
    Not (T.leg i).Nil := by
  intro hnil
  have hboundary_attach : T.boundary i = T.attach i :=
    (T.leg_nil_iff_boundary_eq_attach i).mp hnil
  have hattach_boundary : T.attach i ∈ S.boundarySet := by
    simpa [hboundary_attach] using T.boundary_mem i
  exact
    Set.disjoint_left.mp (hclean.2.2.1 i)
      (T.attach_mem_rim i) hattach_boundary

theorem boundaryClean_attach_not_boundary {S : GeneralSociety V}
    (T : S.Tripod) (hclean : T.BoundaryClean) (i : Fin 3) :
    T.attach i ∉ S.boundarySet := by
  intro hboundary
  exact
    Set.disjoint_left.mp (hclean.2.2.1 i)
      (T.attach_mem_rim i) hboundary

theorem boundaryClean_boundary_ne_attach {S : GeneralSociety V}
    (T : S.Tripod) (hclean : T.BoundaryClean) (i : Fin 3) :
    T.boundary i ≠ T.attach i := by
  intro h
  exact T.boundaryClean_attach_not_boundary hclean i
    (by simpa [← h] using T.boundary_mem i)

theorem boundaryClean_boundary_not_mem_rim {S : GeneralSociety V}
    (T : S.Tripod) (hclean : T.BoundaryClean)
    (i j : Fin 3) :
    T.boundary i ∉ (T.rim j).support := by
  intro hmem
  exact T.boundaryClean_boundary_ne_attach hclean i
    (T.boundary_mem_rim_eq_attach hmem)

theorem attach_ne_of_ne {S : GeneralSociety V}
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j) :
    T.attach i ≠ T.attach j := by
  intro h
  have hj :
      T.attach i ∈ Walk.InternalVertices (T.rim j) := by
    simpa [h] using T.attach_mem_rim j
  exact
    Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
      (T.attach_mem_rim i) hj

theorem attach_not_mem_rim_of_ne {S : GeneralSociety V}
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j) :
    T.attach i ∉ (T.rim j).support := by
  intro hmem
  rcases T.rim_support_internal_or_endpoint hmem with hjInternal | hjEndpoint
  · exact
      Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
        (T.attach_mem_rim i) hjInternal
  · rcases hjEndpoint with hleft | hright
    · exact (T.attach_mem_rim i).2.1 hleft
    · exact (T.attach_mem_rim i).2.2 hright

/-- The old rim segment from the left common end to the attachment. -/
def leftToAttach {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    S.graph.Walk T.left (T.attach i) :=
  (T.rim i).takeUntil (T.attach i) (T.attach_mem_rim i).1

/-- The old rim segment from the attachment back to the left common end. -/
def attachToLeft {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    S.graph.Walk (T.attach i) T.left :=
  (T.leftToAttach i).reverse

/-- The old rim segment from the attachment to the right common end. -/
def attachToRight {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    S.graph.Walk (T.attach i) T.right :=
  (T.rim i).dropUntil (T.attach i) (T.attach_mem_rim i).1

/-- The old rim segment from the right common end back to the attachment. -/
def rightToAttach {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    S.graph.Walk T.right (T.attach i) :=
  (T.attachToRight i).reverse

theorem leftToAttach_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    (T.leftToAttach i).IsPath := by
  simpa [Tripod.leftToAttach] using
    (T.rim_isPath i).takeUntil (T.attach_mem_rim i).1

theorem attachToLeft_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    (T.attachToLeft i).IsPath := by
  simpa [Tripod.attachToLeft] using (T.leftToAttach_isPath i).reverse

theorem attachToRight_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    (T.attachToRight i).IsPath := by
  simpa [Tripod.attachToRight] using
    (T.rim_isPath i).dropUntil (T.attach_mem_rim i).1

theorem rightToAttach_isPath {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    (T.rightToAttach i).IsPath := by
  simpa [Tripod.rightToAttach] using (T.attachToRight_isPath i).reverse

theorem leftToAttach_support_subset_rim {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) {z : V}
    (hz : z ∈ (T.leftToAttach i).support) :
    z ∈ (T.rim i).support := by
  exact
    SimpleGraph.Walk.support_takeUntil_subset (T.rim i)
      (T.attach_mem_rim i).1 (by simpa [Tripod.leftToAttach] using hz)

theorem mem_leftToAttach_of_rim_supportIndex_le_attach
    {S : GeneralSociety V} [DecidableEq V]
    (T : S.Tripod) {i : Fin 3} {z : V}
    (hz : z ∈ (T.rim i).support)
    (hle :
      Walk.supportIndex (T.rim i) z <=
        Walk.supportIndex (T.rim i) (T.attach i)) :
    z ∈ (T.leftToAttach i).support := by
  simpa [Tripod.leftToAttach, Walk.supportIndex] using
    Walk.mem_support_takeUntil_of_idxOf_le
      (p := T.rim i) (x := T.attach i) (y := z)
      (T.attach_mem_rim i).1 hz hle

theorem attach_mem_leftToAttach {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    T.attach i ∈ (T.leftToAttach i).support := by
  simp [Tripod.leftToAttach]

theorem attachToLeft_support_subset_rim {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) {z : V}
    (hz : z ∈ (T.attachToLeft i).support) :
    z ∈ (T.rim i).support := by
  have hzLeft :
      z ∈ (T.leftToAttach i).support := by
    simpa [Tripod.attachToLeft, SimpleGraph.Walk.support_reverse] using hz
  exact T.leftToAttach_support_subset_rim i hzLeft

theorem attachToRight_support_subset_rim {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) {z : V}
    (hz : z ∈ (T.attachToRight i).support) :
    z ∈ (T.rim i).support := by
  exact
    SimpleGraph.Walk.support_dropUntil_subset (T.rim i)
      (T.attach_mem_rim i).1 (by simpa [Tripod.attachToRight] using hz)

theorem mem_attachToRight_of_attach_supportIndex_le_rim
    {S : GeneralSociety V} [DecidableEq V]
    (T : S.Tripod) {i : Fin 3} {z : V}
    (hz : z ∈ (T.rim i).support)
    (hle :
      Walk.supportIndex (T.rim i) (T.attach i) <=
        Walk.supportIndex (T.rim i) z) :
    z ∈ (T.attachToRight i).support := by
  simpa [Tripod.attachToRight, Walk.supportIndex] using
    Walk.mem_support_dropUntil_of_idxOf_le
      (p := T.rim i) (x := T.attach i) (y := z)
      (T.attach_mem_rim i).1 hz hle

theorem attach_mem_attachToRight {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    T.attach i ∈ (T.attachToRight i).support := by
  simp [Tripod.attachToRight]

theorem rightToAttach_support_subset_rim {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) {z : V}
    (hz : z ∈ (T.rightToAttach i).support) :
    z ∈ (T.rim i).support := by
  have hzRight :
    z ∈ (T.attachToRight i).support := by
    simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse] using hz
  exact T.attachToRight_support_subset_rim i hzRight

theorem right_not_mem_leftToAttach {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    T.right ∉ (T.leftToAttach i).support := by
  exact
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.rim_isPath i) (T.attach_mem_rim i).1
      (fun h => (T.attach_mem_rim i).2.2 h.symm)

theorem right_not_mem_attachToLeft {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    T.right ∉ (T.attachToLeft i).support := by
  intro hright
  exact T.right_not_mem_leftToAttach i
    (by
      simpa [Tripod.attachToLeft, SimpleGraph.Walk.support_reverse]
        using hright)

theorem left_not_mem_attachToRight {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    T.left ∉ (T.attachToRight i).support := by
  exact
    Walk.IsPath.start_not_mem_dropUntil_support_of_ne
      (T.rim_isPath i)
      (T.attach_mem_rim i).1
      (fun h => (T.attach_mem_rim i).2.1 h)

theorem left_not_mem_rightToAttach {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) :
    T.left ∉ (T.rightToAttach i).support := by
  intro hleft
  exact T.left_not_mem_attachToRight i
    (by
      simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse]
        using hleft)

theorem rightToAttach_support_inter_rim_eq_right {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j)
    {z : V}
    (hzi : z ∈ (T.rightToAttach i).support)
    (hzj : z ∈ (T.rim j).support) :
    z = T.right := by
  have hziRim : z ∈ (T.rim i).support :=
    T.rightToAttach_support_subset_rim i hzi
  rcases T.rim_support_internal_or_endpoint hziRim with hziInternal | hziEnd
  · rcases T.rim_support_internal_or_endpoint hzj with hzjInternal | hzjEnd
    · exact False.elim
        (Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hziInternal hzjInternal)
    · rcases hzjEnd with hzLeft | hzRight
      · exact False.elim (hziInternal.2.1 hzLeft)
      · exact hzRight
  · rcases hziEnd with hzLeft | hzRight
    · exact False.elim
        (T.left_not_mem_rightToAttach i (by simpa [hzLeft] using hzi))
    · exact hzRight

theorem leftToAttach_support_inter_rim_eq_left {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j)
    {z : V}
    (hzi : z ∈ (T.leftToAttach i).support)
    (hzj : z ∈ (T.rim j).support) :
    z = T.left := by
  have hziRim : z ∈ (T.rim i).support :=
    T.leftToAttach_support_subset_rim i hzi
  rcases T.rim_support_internal_or_endpoint hziRim with hziInternal | hziEnd
  · rcases T.rim_support_internal_or_endpoint hzj with hzjInternal | hzjEnd
    · exact False.elim
        (Set.disjoint_left.mp (T.rim_internals_disjoint i j hij)
          hziInternal hzjInternal)
    · rcases hzjEnd with hzLeft | hzRight
      · exact hzLeft
      · exact False.elim (hziInternal.2.2 hzRight)
  · rcases hziEnd with hzLeft | hzRight
    · exact hzLeft
    · exact False.elim
        (T.right_not_mem_leftToAttach i (by simpa [hzRight] using hzi))

theorem attachToLeft_support_inter_attachToRight_eq_attach
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) {z : V}
    (hzLeft : z ∈ (T.attachToLeft i).support)
    (hzRight : z ∈ (T.attachToRight i).support) :
    z = T.attach i := by
  have hzTake :
      z ∈ (T.leftToAttach i).support := by
    simpa [Tripod.attachToLeft, SimpleGraph.Walk.support_reverse] using hzLeft
  exact
    Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      (T.rim_isPath i) (T.attach_mem_rim i).1
      (by simpa [Tripod.leftToAttach] using hzTake)
      (by simpa [Tripod.attachToRight] using hzRight)

theorem leftToAttach_support_inter_rightToAttach_eq_attach
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) (i : Fin 3) {z : V}
    (hzLeft : z ∈ (T.leftToAttach i).support)
    (hzRight : z ∈ (T.rightToAttach i).support) :
    z = T.attach i := by
  have hzDrop :
      z ∈ (T.attachToRight i).support := by
    simpa [Tripod.rightToAttach, SimpleGraph.Walk.support_reverse] using hzRight
  exact
    Walk.IsPath.eq_split_vertex_of_mem_takeUntil_and_dropUntil
      (T.rim_isPath i) (T.attach_mem_rim i).1
      (by simpa [Tripod.leftToAttach] using hzLeft)
      (by simpa [Tripod.attachToRight] using hzDrop)

/-- A strict prefix of the left arm before a hit `x` does not meet the opposite
right arm. -/
theorem leftToAttach_takeUntil_support_disjoint_rightToAttach
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i : Fin 3} {x : V}
    (hx : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i) :
    Disjoint
      {z : V | z ∈ ((T.leftToAttach i).takeUntil x hx).support}
      {z : V | z ∈ (T.rightToAttach i).support} := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzRight
  have hzLeft : z ∈ (T.leftToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hx
      hzPrefix
  have hzAttach : z = T.attach i :=
    T.leftToAttach_support_inter_rightToAttach_eq_attach i hzLeft hzRight
  have hattach_not_prefix :
      T.attach i ∉ ((T.leftToAttach i).takeUntil x hx).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.leftToAttach_isPath i) hx
      (by simpa [ne_eq] using hx_ne_attach.symm)
  exact hattach_not_prefix (by simpa [hzAttach] using hzPrefix)

/-- A strict prefix of a left arm can meet another old rim only at the old
left common endpoint. -/
theorem leftToAttach_takeUntil_support_inter_rim_eq_left
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j) {x z : V}
    (hx : x ∈ (T.leftToAttach i).support)
    (hzPrefix : z ∈ ((T.leftToAttach i).takeUntil x hx).support)
    (hzRim : z ∈ (T.rim j).support) :
    z = T.left := by
  have hzLeft : z ∈ (T.leftToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hx
      hzPrefix
  exact T.leftToAttach_support_inter_rim_eq_left hij hzLeft hzRim

/-- A strict prefix of a left arm before a non-attachment hit is disjoint from
the corresponding old leg. -/
theorem leftToAttach_takeUntil_support_disjoint_leg
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i : Fin 3} {x : V}
    (hx : x ∈ (T.leftToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i) :
    Disjoint
      {z : V | z ∈ ((T.leftToAttach i).takeUntil x hx).support}
      {z : V | z ∈ (T.leg i).support} := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzLeg
  have hzLeft : z ∈ (T.leftToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach i) hx
      hzPrefix
  have hzRim : z ∈ (T.rim i).support :=
    T.leftToAttach_support_subset_rim i hzLeft
  have hzAttach : z = T.attach i :=
    T.legs_meet_rims_only_at_attach i i z hzLeg hzRim
  have hattach_not_prefix :
      T.attach i ∉ ((T.leftToAttach i).takeUntil x hx).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.leftToAttach_isPath i) hx
      (by simpa [ne_eq] using hx_ne_attach.symm)
  exact hattach_not_prefix (by simpa [hzAttach] using hzPrefix)

/-- A strict prefix of the right arm before a hit `x` does not meet the opposite
left arm. -/
theorem rightToAttach_takeUntil_support_disjoint_leftToAttach
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i : Fin 3} {x : V}
    (hx : x ∈ (T.rightToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i) :
    Disjoint
      {z : V | z ∈ ((T.rightToAttach i).takeUntil x hx).support}
      {z : V | z ∈ (T.leftToAttach i).support} := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzLeft
  have hzRight : z ∈ (T.rightToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach i) hx
      hzPrefix
  have hzAttach : z = T.attach i :=
    T.leftToAttach_support_inter_rightToAttach_eq_attach i hzLeft hzRight
  have hattach_not_prefix :
      T.attach i ∉ ((T.rightToAttach i).takeUntil x hx).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.rightToAttach_isPath i) hx
      (by simpa [ne_eq] using hx_ne_attach.symm)
  exact hattach_not_prefix (by simpa [hzAttach] using hzPrefix)

/-- A strict prefix of a right arm can meet another old rim only at the old
right common endpoint. -/
theorem rightToAttach_takeUntil_support_inter_rim_eq_right
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i j : Fin 3} (hij : i ≠ j) {x z : V}
    (hx : x ∈ (T.rightToAttach i).support)
    (hzPrefix : z ∈ ((T.rightToAttach i).takeUntil x hx).support)
    (hzRim : z ∈ (T.rim j).support) :
    z = T.right := by
  have hzRight : z ∈ (T.rightToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach i) hx
      hzPrefix
  exact T.rightToAttach_support_inter_rim_eq_right hij hzRight hzRim

/-- A strict prefix of a right arm before a non-attachment hit is disjoint from
the corresponding old leg. -/
theorem rightToAttach_takeUntil_support_disjoint_leg
    {S : GeneralSociety V}
    [DecidableEq V]
    (T : S.Tripod) {i : Fin 3} {x : V}
    (hx : x ∈ (T.rightToAttach i).support)
    (hx_ne_attach : x ≠ T.attach i) :
    Disjoint
      {z : V | z ∈ ((T.rightToAttach i).takeUntil x hx).support}
      {z : V | z ∈ (T.leg i).support} := by
  rw [Set.disjoint_left]
  intro z hzPrefix hzLeg
  have hzRight : z ∈ (T.rightToAttach i).support :=
    SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach i) hx
      hzPrefix
  have hzRim : z ∈ (T.rim i).support :=
    T.rightToAttach_support_subset_rim i hzRight
  have hzAttach : z = T.attach i :=
    T.legs_meet_rims_only_at_attach i i z hzLeg hzRim
  have hattach_not_prefix :
      T.attach i ∉ ((T.rightToAttach i).takeUntil x hx).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil
      (T.rightToAttach_isPath i) hx
      (by simpa [ne_eq] using hx_ne_attach.symm)
  exact hattach_not_prefix (by simpa [hzAttach] using hzPrefix)


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
