import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.TripodContacts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod
/-- If a tripod's three feet exhaust the ambient society boundary and no leg is
trivial, then the tripod is boundary-clean.

This packages the common cleanup used when a general-society tripod is being
specialized back to a three-boundary society: hidden boundary contacts on rims
would force a nil leg, and hidden boundary contacts on legs are excluded by
leg disjointness or by being the endpoint rather than an internal vertex. -/
theorem boundaryClean_of_boundarySet_subset_range_boundary_of_no_leg_nil
    {S : GeneralSociety V}
    (T : S.Tripod)
    (hboundary_subset : S.boundarySet ⊆ Set.range T.boundary)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    T.BoundaryClean := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft_boundary
    rcases hboundary_subset hleft_boundary with ⟨i, hi⟩
    exact T.left_not_mem_leg i (by
      rw [← hi]
      exact (T.leg i).end_mem_support)
  · intro hright_boundary
    rcases hboundary_subset hright_boundary with ⟨i, hi⟩
    exact T.right_not_mem_leg i (by
      rw [← hi]
      exact (T.leg i).end_mem_support)
  · intro r
    rw [Set.disjoint_left]
    intro v hvInternal hvBoundary
    rcases hboundary_subset hvBoundary with ⟨i, hi⟩
    have hboundary_rim : T.boundary i ∈ (T.rim r).support := by
      simpa [hi] using hvInternal.1
    have hboundary_attach : T.boundary i = T.attach i :=
      T.boundary_mem_rim_eq_attach hboundary_rim
    exact hleg_not_nil i ((T.boundary_eq_attach_iff_leg_nil i).mp hboundary_attach)
  · intro r
    rw [Set.disjoint_left]
    intro v hvInternal hvBoundary
    rcases hboundary_subset hvBoundary with ⟨i, hi⟩
    have hboundary_leg : T.boundary i ∈ (T.leg r).support := by
      simpa [hi] using hvInternal.1
    by_cases hir : i = r
    · subst i
      exact hvInternal.2.2 hi.symm
    · exact
        T.boundary_not_mem_leg_of_ne (i := r) (j := i)
          (fun hri => hir hri.symm) hboundary_leg

/-- Boundary-contact normalization implies boundary cleanliness.

This is the form needed for the source GM IX `(2.4)` tripod paragraph.  The
paper's linkage language says that the three legs are paths from the rim
union to the society boundary, hence no other society-boundary vertex is met.
Once that fact is formalized as `hcontacts`, and zero-length legs are ruled
out, the Lean `BoundaryClean` predicate follows. -/
theorem boundaryClean_of_boundary_contacts_of_no_leg_nil
    {S : GeneralSociety V}
    (T : S.Tripod)
    (hcontacts :
      forall z : V, z ∈ S.boundarySet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    T.BoundaryClean := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hleft_boundary
    rcases hcontacts T.left hleft_boundary T.left_mem_vertexSet with ⟨i, hi⟩
    exact T.left_not_mem_leg i (by
      rw [hi]
      exact (T.leg i).end_mem_support)
  · intro hright_boundary
    rcases hcontacts T.right hright_boundary T.right_mem_vertexSet with ⟨i, hi⟩
    exact T.right_not_mem_leg i (by
      rw [hi]
      exact (T.leg i).end_mem_support)
  · intro r
    rw [Set.disjoint_left]
    intro v hvInternal hvBoundary
    have hvVertex : v ∈ T.vertexSet :=
      T.rim_mem_vertexSet (i := r) hvInternal.1
    rcases hcontacts v hvBoundary hvVertex with ⟨i, hi⟩
    have hboundary_rim : T.boundary i ∈ (T.rim r).support := by
      simpa [hi] using hvInternal.1
    have hboundary_attach : T.boundary i = T.attach i :=
      T.boundary_mem_rim_eq_attach hboundary_rim
    exact hleg_not_nil i ((T.boundary_eq_attach_iff_leg_nil i).mp hboundary_attach)
  · intro r
    rw [Set.disjoint_left]
    intro v hvInternal hvBoundary
    have hvVertex : v ∈ T.vertexSet :=
      T.leg_mem_vertexSet (i := r) hvInternal.1
    rcases hcontacts v hvBoundary hvVertex with ⟨i, hi⟩
    have hboundary_leg : T.boundary i ∈ (T.leg r).support := by
      simpa [hi] using hvInternal.1
    by_cases hir : i = r
    · subst i
      exact hvInternal.2.2 hi
    · exact
        T.boundary_not_mem_leg_of_ne (i := r) (j := i)
          (fun hri => hir hri.symm) hboundary_leg

theorem vertexSet_leg_or_rim_internal_or_endpoint {S : GeneralSociety V}
    (T : S.Tripod) {v : V}
    (hv : v ∈ T.vertexSet) :
    (Exists fun i : Fin 3 => v ∈ (T.leg i).support) ∨
      (Exists fun i : Fin 3 => v ∈ Walk.InternalVertices (T.rim i)) ∨
        v = T.left ∨ v = T.right := by
  rcases hv with hrim | hleg
  · rcases hrim with ⟨i, hvi⟩
    rcases T.rim_support_internal_or_endpoint hvi with hvint | hvend
    · exact Or.inr (Or.inl ⟨i, hvint⟩)
    · exact Or.inr (Or.inr hvend)
  · exact Or.inl hleg

theorem contact_not_same_branch_escape {S : GeneralSociety V}
    (T : S.Tripod) {i : Fin 3} {x : V}
    (hxT :
      Exists fun k : Fin 3 =>
        x ∈ (T.rim k).support ∨ x ∈ (T.leg k).support)
    (hnot_same :
      Not
        (x ∈ (T.leg i).support ∨
          (x ∈ Walk.InternalVertices (T.rim i) ∧
            forall j : Fin 3, x ≠ T.attach j))) :
    x = T.left ∨ x = T.right ∨
      Exists fun k : Fin 3 =>
        k ≠ i ∧
          (x ∈ (T.leg k).support ∨
            x ∈ Walk.InternalVertices (T.rim k)) := by
  have hxVertex : x ∈ T.vertexSet := by
    rcases hxT with ⟨k, hxk⟩
    rcases hxk with hxrim | hxleg
    · exact T.rim_mem_vertexSet (i := k) hxrim
    · exact T.leg_mem_vertexSet (i := k) hxleg
  rcases T.vertexSet_leg_or_rim_internal_or_endpoint hxVertex with hleg | hrest
  · rcases hleg with ⟨k, hxleg⟩
    by_cases hki : k = i
    · subst k
      exact False.elim (hnot_same (Or.inl hxleg))
    · exact Or.inr (Or.inr ⟨k, hki, Or.inl hxleg⟩)
  · rcases hrest with hrim | hend
    · rcases hrim with ⟨k, hxrim⟩
      by_cases hki : k = i
      · subst k
        by_cases hattach : Exists fun j : Fin 3 => x = T.attach j
        · rcases hattach with ⟨j, hxj⟩
          by_cases hji : j = i
          · subst j
            have hxleg_i : x ∈ (T.leg i).support := by
              simp [hxj]
            exact False.elim (hnot_same (Or.inl hxleg_i))
          · have hxleg_j : x ∈ (T.leg j).support := by
              simp [hxj]
            exact Or.inr (Or.inr ⟨j, hji, Or.inl hxleg_j⟩)
        · have hnot_attach : forall j : Fin 3, x ≠ T.attach j := by
            intro j hxj
            exact hattach ⟨j, hxj⟩
          exact False.elim (hnot_same (Or.inr ⟨hxrim, hnot_attach⟩))
      · exact Or.inr (Or.inr ⟨k, hki, Or.inr hxrim⟩)
    · rcases hend with hleft | hright
      · exact Or.inl hleft
      · exact Or.inr (Or.inl hright)

theorem clean_tail_from_rim_hit_not_boundary_of_ne_attach
    {S : GeneralSociety V}
    {G : SimpleGraph V}
    (T : S.Tripod) {i : Fin 3} {x y : V}
    (hx : x ∈ (T.rim i).support)
    (q : G.Walk x y)
    (hx_ne_attach : forall j : Fin 3, x ≠ T.attach j)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    forall j : Fin 3, y ≠ T.boundary j := by
  intro j hy
  have hyT : y ∈ T.vertexSet := by
    rw [hy]
    exact T.boundary_mem_vertexSet j
  have hy_eq_x : y = x :=
    hq_clean y q.end_mem_support hyT
  have hx_boundary : x = T.boundary j := hy_eq_x.symm.trans hy
  have hxLeg : x ∈ (T.leg j).support := by
    rw [hx_boundary]
    exact (T.leg j).end_mem_support
  have hx_attach :
      x = T.attach j :=
    T.legs_meet_rims_only_at_attach j i x hxLeg hx
  exact hx_ne_attach j hx_attach

theorem clean_tail_from_rim_hit_endpoint_mem_vertexSet_eq
    {S : GeneralSociety V} (T : S.Tripod) {x y : V}
    (q : S.graph.Walk x y)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x)
    (hyT : y ∈ T.vertexSet) :
    y = x :=
  hq_clean y q.end_mem_support hyT

def reindex {S : GeneralSociety V} (T : S.Tripod)
    (e : Fin 3 -> Fin 3) (he : Function.Injective e) :
    S.Tripod where
  left := T.left
  right := T.right
  left_ne_right := T.left_ne_right
  rim i := T.rim (e i)
  rim_isPath i := T.rim_isPath (e i)
  attach i := T.attach (e i)
  attach_mem_rim i := T.attach_mem_rim (e i)
  boundary i := T.boundary (e i)
  boundary_mem i := T.boundary_mem (e i)
  boundary_injective := fun i j hij => he (T.boundary_injective hij)
  leg i := T.leg (e i)
  leg_isPath i := T.leg_isPath (e i)
  rim_internals_disjoint := by
    intro i j hij
    exact T.rim_internals_disjoint (e i) (e j) (fun h => hij (he h))
  legs_pairwise_disjoint := by
    intro i j hij
    exact T.legs_pairwise_disjoint (e i) (e j) (fun h => hij (he h))
  legs_meet_rims_only_at_attach := by
    intro i j v hvLeg hvRim
    exact T.legs_meet_rims_only_at_attach (e i) (e j) v hvLeg hvRim

theorem reindex_vertexSet_subset {S : GeneralSociety V} (T : S.Tripod)
    (e : Fin 3 -> Fin 3) (he : Function.Injective e) :
    (T.reindex e he).vertexSet ⊆ T.vertexSet := by
  intro v hv
  rcases hv with hrim | hleg
  · rcases hrim with ⟨i, hi⟩
    exact T.rim_mem_vertexSet (i := e i) hi
  · rcases hleg with ⟨i, hi⟩
    exact T.leg_mem_vertexSet (i := e i) hi

theorem legBoundaryContactClean_reindex
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (e : Fin 3 -> Fin 3) (he : Function.Injective e) :
    (T.reindex e he).LegBoundaryContactClean := by
  intro i z hzLeg hzBoundary
  simpa [Tripod.reindex] using
    hclean (e i) z (by simpa [Tripod.reindex] using hzLeg) hzBoundary

/-- A hidden boundary contact on a branch with a nontrivial linkage leg gives
a strictly shorter source-clean tripod.

The branch is first moved to index zero, where
`replaceLegZeroByNilAtInternalBoundary` performs the normalization.  This is
the well-founded descent needed by the direct GM IX `(2.4)` side-tripod proof:
minimal source-clean tripods can have hidden internal boundary contacts only
on branches whose linkage leg is already nil. -/
theorem exists_sourceClean_tripod_shorter_of_internal_boundary_contact
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (i : Fin 3) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim i))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j)
    (hleg : Not (T.leg i).Nil) :
    Exists fun U : S.Tripod =>
      U.LegBoundaryContactClean ∧ U.linkageLength < T.linkageLength := by
  classical
  fin_cases i
  · let U :=
      T.replaceLegZeroByNilAtInternalBoundary z hzInternal hzBoundary
        hzNotBoundary
    exact
      ⟨U,
        T.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          hclean z hzInternal hzBoundary hzNotBoundary,
        T.replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
          z hzInternal hzBoundary hzNotBoundary hleg⟩
  · let e : Fin 3 -> Fin 3 := fin3Order 1 0 2
    have he : Function.Injective e :=
      fin3Order_injective (by decide) (by decide) (by decide)
    let Tre := T.reindex e he
    have hzInternal' : z ∈ Walk.InternalVertices (Tre.rim 0) := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hzInternal
    have hzNotBoundary' :
        forall j : Fin 3, z ≠ Tre.boundary j := by
      intro j hz
      exact hzNotBoundary (e j) (by
        simpa [Tre, Tripod.reindex] using hz)
    have hleg' : Not (Tre.leg 0).Nil := by
      intro hnil
      exact hleg (by
        simpa [Tre, Tripod.reindex, e, fin3Order] using hnil)
    let U :=
      Tre.replaceLegZeroByNilAtInternalBoundary z hzInternal' hzBoundary
        hzNotBoundary'
    refine
      ⟨U,
        Tre.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          (T.legBoundaryContactClean_reindex hclean e he)
          z hzInternal' hzBoundary hzNotBoundary',
        ?_⟩
    calc
      U.linkageLength < Tre.linkageLength :=
        Tre.replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
          z hzInternal' hzBoundary hzNotBoundary' hleg'
      _ = T.linkageLength := by
        simp [Tre, linkageLength, Tripod.reindex, e, fin3Order,
          Nat.add_comm, Nat.add_assoc]
  · let e : Fin 3 -> Fin 3 := fin3Order 2 0 1
    have he : Function.Injective e :=
      fin3Order_injective (by decide) (by decide) (by decide)
    let Tre := T.reindex e he
    have hzInternal' : z ∈ Walk.InternalVertices (Tre.rim 0) := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hzInternal
    have hzNotBoundary' :
        forall j : Fin 3, z ≠ Tre.boundary j := by
      intro j hz
      exact hzNotBoundary (e j) (by
        simpa [Tre, Tripod.reindex] using hz)
    have hleg' : Not (Tre.leg 0).Nil := by
      intro hnil
      exact hleg (by
        simpa [Tre, Tripod.reindex, e, fin3Order] using hnil)
    let U :=
      Tre.replaceLegZeroByNilAtInternalBoundary z hzInternal' hzBoundary
        hzNotBoundary'
    refine
      ⟨U,
        Tre.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          (T.legBoundaryContactClean_reindex hclean e he)
          z hzInternal' hzBoundary hzNotBoundary',
        ?_⟩
    calc
      U.linkageLength < Tre.linkageLength :=
        Tre.replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
          z hzInternal' hzBoundary hzNotBoundary' hleg'
      _ = T.linkageLength := by
        simp [Tre, linkageLength, Tripod.reindex, e, fin3Order,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Every nonempty tripod family contains a source-clean member whose three
linkage legs have minimum total length.

The family of tripod structures itself need not be presented as a finite type.
Only the natural-valued linkage length is minimized, using well-ordering of
`Nat`; first-boundary trimming supplies the initial source-clean member. -/
theorem exists_linkageLength_minimal_sourceClean_tripod
    [DecidableEq V]
    {S : GeneralSociety V}
    (hT : Nonempty S.Tripod) :
    Exists fun T : S.Tripod =>
      T.LegBoundaryContactClean ∧
        forall U : S.Tripod,
          U.LegBoundaryContactClean ->
            T.linkageLength <= U.linkageLength := by
  classical
  rcases
      exists_legBoundaryContactClean_tripod_of_exists_tripod hT with
    ⟨T₀, hT₀clean⟩
  let HasCleanLength : Nat -> Prop :=
    fun n =>
      Exists fun T : S.Tripod =>
        T.LegBoundaryContactClean ∧ T.linkageLength = n
  have hexists : Exists HasCleanLength :=
    ⟨T₀.linkageLength, T₀, hT₀clean, rfl⟩
  let n := Nat.find hexists
  rcases Nat.find_spec hexists with ⟨T, hTclean, hTlength⟩
  refine ⟨T, hTclean, ?_⟩
  intro U hUclean
  rw [hTlength]
  exact Nat.find_min' hexists ⟨U, hUclean, rfl⟩

/-- Number of selected tripod feet lying in a prescribed vertex set.

For the GM IX `(2.4)` application, `A` is the vertex set of the induced cut
path.  Keeping this definition independent of the cut package makes the
normalization below a reusable tripod lemma. -/
noncomputable def footCountIn
    {S : GeneralSociety V} (T : S.Tripod) (A : Set V) : Nat := by
  classical
  exact (Finset.univ.filter fun i : Fin 3 => T.boundary i ∈ A).card

theorem footCountIn_le_three
    {S : GeneralSociety V} (T : S.Tripod) (A : Set V) :
    T.footCountIn A <= 3 := by
  classical
  calc
    T.footCountIn A <= (Finset.univ : Finset (Fin 3)).card := by
      exact Finset.card_filter_le _ _
    _ = 3 := by simp

theorem footCountIn_eq_three_indicators
    {S : GeneralSociety V} (T : S.Tripod) (A : Set V)
    [DecidablePred (fun v : V => v ∈ A)] :
    T.footCountIn A =
      (if T.boundary 0 ∈ A then 1 else 0) +
        (if T.boundary 1 ∈ A then 1 else 0) +
          (if T.boundary 2 ∈ A then 1 else 0) := by
  classical
  rw [footCountIn, show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} from rfl]
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  by_cases h0 : T.boundary 0 ∈ A <;>
    by_cases h1 : T.boundary 1 ∈ A <;>
      by_cases h2 : T.boundary 2 ∈ A <;>
        simp [h0, h1, h2]

/-- A source-clean tripod chosen lexicographically: first maximize the number
of feet in `A`, then minimize the total linkage length among those maximizers.

The family of tripod structures need not be finite.  Both coordinates are
natural numbers, so two applications of well-ordering suffice. -/
theorem exists_footCount_maximal_linkageLength_minimal_sourceClean_tripod
    [DecidableEq V]
    {S : GeneralSociety V}
    (A : Set V)
    (hT : Nonempty S.Tripod) :
    Exists fun T : S.Tripod =>
      T.LegBoundaryContactClean ∧
        (forall U : S.Tripod,
          U.LegBoundaryContactClean ->
            U.footCountIn A <= T.footCountIn A) ∧
          forall U : S.Tripod,
            U.LegBoundaryContactClean ->
              U.footCountIn A = T.footCountIn A ->
                T.linkageLength <= U.linkageLength := by
  classical
  rcases
      exists_legBoundaryContactClean_tripod_of_exists_tripod hT with
    ⟨T₀, hT₀clean⟩
  let HasCleanDeficit : Nat -> Prop :=
    fun d =>
      Exists fun T : S.Tripod =>
        T.LegBoundaryContactClean ∧ d = 3 - T.footCountIn A
  have hdeficit_exists : Exists HasCleanDeficit :=
    ⟨3 - T₀.footCountIn A, T₀, hT₀clean, rfl⟩
  let d := Nat.find hdeficit_exists
  rcases Nat.find_spec hdeficit_exists with
    ⟨T₁, hT₁clean, hdT₁⟩
  let HasMaximalCleanLength : Nat -> Prop :=
    fun n =>
      Exists fun T : S.Tripod =>
        T.LegBoundaryContactClean ∧
          T.footCountIn A = T₁.footCountIn A ∧
            T.linkageLength = n
  have hlength_exists : Exists HasMaximalCleanLength :=
    ⟨T₁.linkageLength, T₁, hT₁clean, rfl, rfl⟩
  let n := Nat.find hlength_exists
  rcases Nat.find_spec hlength_exists with
    ⟨T, hTclean, hTcount, hTlength⟩
  refine ⟨T, hTclean, ?_, ?_⟩
  · intro U hUclean
    have hdeficit_min :
        3 - T₁.footCountIn A <= 3 - U.footCountIn A := by
      rw [← hdT₁]
      exact Nat.find_min' hdeficit_exists
        ⟨U, hUclean, rfl⟩
    have hUle : U.footCountIn A <= T₁.footCountIn A := by
      have hT₁le := T₁.footCountIn_le_three A
      have hUle3 := U.footCountIn_le_three A
      omega
    simpa [hTcount] using hUle
  · intro U hUclean hUcount
    rw [hTlength]
    exact Nat.find_min' hlength_exists
      ⟨U, hUclean, hUcount.trans hTcount, rfl⟩

/-- Replacing a branch whose old foot is outside `A` by a hidden internal
contact in `A` produces a source-clean tripod with strictly more feet in
`A`.  The output may be reindexed; `footCountIn` is invariant under that
permutation. -/
theorem exists_sourceClean_tripod_more_feet_of_internal_boundary_contact
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (A : Set V)
    (i : Fin 3) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim i))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j)
    (hzA : z ∈ A)
    (hiA : T.boundary i ∉ A) :
    Exists fun U : S.Tripod =>
      U.LegBoundaryContactClean ∧
        T.footCountIn A < U.footCountIn A := by
  classical
  fin_cases i
  · let U :=
      T.replaceLegZeroByNilAtInternalBoundary z hzInternal hzBoundary
        hzNotBoundary
    have hiA0 : T.boundary 0 ∉ A := by simpa using hiA
    refine
      ⟨U,
        T.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          hclean z hzInternal hzBoundary hzNotBoundary,
        ?_⟩
    rw [T.footCountIn_eq_three_indicators,
      U.footCountIn_eq_three_indicators]
    simp [U, replaceLegZeroByNilAtInternalBoundary, hzA, hiA0]
    by_cases h1 : T.boundary 1 ∈ A <;>
      by_cases h2 : T.boundary 2 ∈ A <;>
        simp [h1, h2]
  · let e : Fin 3 -> Fin 3 := fin3Order 1 0 2
    have he : Function.Injective e :=
      fin3Order_injective (by decide) (by decide) (by decide)
    let Tre := T.reindex e he
    have hzInternal' : z ∈ Walk.InternalVertices (Tre.rim 0) := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hzInternal
    have hzNotBoundary' :
        forall j : Fin 3, z ≠ Tre.boundary j := by
      intro j hz
      exact hzNotBoundary (e j) (by
        simpa [Tre, Tripod.reindex] using hz)
    let U :=
      Tre.replaceLegZeroByNilAtInternalBoundary z hzInternal' hzBoundary
        hzNotBoundary'
    have hiA1 : T.boundary 1 ∉ A := by simpa using hiA
    refine
      ⟨U,
        Tre.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          (T.legBoundaryContactClean_reindex hclean e he)
          z hzInternal' hzBoundary hzNotBoundary',
        ?_⟩
    rw [T.footCountIn_eq_three_indicators,
      U.footCountIn_eq_three_indicators]
    simp [U, Tre, Tripod.reindex, e, fin3Order,
      replaceLegZeroByNilAtInternalBoundary, hzA, hiA1]
    by_cases h0 : T.boundary 0 ∈ A <;>
      by_cases h2 : T.boundary 2 ∈ A <;>
        simp [h0, h2]
  · let e : Fin 3 -> Fin 3 := fin3Order 2 0 1
    have he : Function.Injective e :=
      fin3Order_injective (by decide) (by decide) (by decide)
    let Tre := T.reindex e he
    have hzInternal' : z ∈ Walk.InternalVertices (Tre.rim 0) := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hzInternal
    have hzNotBoundary' :
        forall j : Fin 3, z ≠ Tre.boundary j := by
      intro j hz
      exact hzNotBoundary (e j) (by
        simpa [Tre, Tripod.reindex] using hz)
    let U :=
      Tre.replaceLegZeroByNilAtInternalBoundary z hzInternal' hzBoundary
        hzNotBoundary'
    have hiA2 : T.boundary 2 ∉ A := by simpa using hiA
    refine
      ⟨U,
        Tre.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          (T.legBoundaryContactClean_reindex hclean e he)
          z hzInternal' hzBoundary hzNotBoundary',
        ?_⟩
    rw [T.footCountIn_eq_three_indicators,
      U.footCountIn_eq_three_indicators]
    simp [U, Tre, Tripod.reindex, e, fin3Order,
      replaceLegZeroByNilAtInternalBoundary, hzA, hiA2]
    by_cases h0 : T.boundary 0 ∈ A <;>
      by_cases h1 : T.boundary 1 ∈ A <;>
        simp [h0, h1]

/-- If both the old foot and the replacement contact lie in `A`, the same
normalization preserves `footCountIn`; a nontrivial old leg still makes the
linkage strictly shorter. -/
theorem exists_sourceClean_tripod_same_feet_shorter_of_internal_boundary_contact
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (A : Set V)
    (i : Fin 3) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim i))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j)
    (hzA : z ∈ A)
    (hiA : T.boundary i ∈ A)
    (hleg : Not (T.leg i).Nil) :
    Exists fun U : S.Tripod =>
      U.LegBoundaryContactClean ∧
        U.footCountIn A = T.footCountIn A ∧
          U.linkageLength < T.linkageLength := by
  classical
  fin_cases i
  · let U :=
      T.replaceLegZeroByNilAtInternalBoundary z hzInternal hzBoundary
        hzNotBoundary
    have hiA0 : T.boundary 0 ∈ A := by simpa using hiA
    refine
      ⟨U,
        T.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          hclean z hzInternal hzBoundary hzNotBoundary,
        ?_, ?_⟩
    · rw [T.footCountIn_eq_three_indicators,
        U.footCountIn_eq_three_indicators]
      simp [U, replaceLegZeroByNilAtInternalBoundary, hzA, hiA0]
      rfl
    · exact
        T.replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
          z hzInternal hzBoundary hzNotBoundary hleg
  · let e : Fin 3 -> Fin 3 := fin3Order 1 0 2
    have he : Function.Injective e :=
      fin3Order_injective (by decide) (by decide) (by decide)
    let Tre := T.reindex e he
    have hzInternal' : z ∈ Walk.InternalVertices (Tre.rim 0) := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hzInternal
    have hzNotBoundary' :
        forall j : Fin 3, z ≠ Tre.boundary j := by
      intro j hz
      exact hzNotBoundary (e j) (by
        simpa [Tre, Tripod.reindex] using hz)
    have hleg' : Not (Tre.leg 0).Nil := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hleg
    let U :=
      Tre.replaceLegZeroByNilAtInternalBoundary z hzInternal' hzBoundary
        hzNotBoundary'
    have hiA1 : T.boundary 1 ∈ A := by simpa using hiA
    refine
      ⟨U,
        Tre.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          (T.legBoundaryContactClean_reindex hclean e he)
          z hzInternal' hzBoundary hzNotBoundary',
        ?_, ?_⟩
    · rw [T.footCountIn_eq_three_indicators,
        U.footCountIn_eq_three_indicators]
      simp [U, Tre, Tripod.reindex, e, fin3Order,
        replaceLegZeroByNilAtInternalBoundary, hzA, hiA1,
        Nat.add_comm, Nat.add_assoc]
      rfl
    · calc
        U.linkageLength < Tre.linkageLength :=
          Tre.replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
            z hzInternal' hzBoundary hzNotBoundary' hleg'
        _ = T.linkageLength := by
          simp [Tre, linkageLength, Tripod.reindex, e, fin3Order,
            Nat.add_comm, Nat.add_assoc]
  · let e : Fin 3 -> Fin 3 := fin3Order 2 0 1
    have he : Function.Injective e :=
      fin3Order_injective (by decide) (by decide) (by decide)
    let Tre := T.reindex e he
    have hzInternal' : z ∈ Walk.InternalVertices (Tre.rim 0) := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hzInternal
    have hzNotBoundary' :
        forall j : Fin 3, z ≠ Tre.boundary j := by
      intro j hz
      exact hzNotBoundary (e j) (by
        simpa [Tre, Tripod.reindex] using hz)
    have hleg' : Not (Tre.leg 0).Nil := by
      simpa [Tre, Tripod.reindex, e, fin3Order] using hleg
    let U :=
      Tre.replaceLegZeroByNilAtInternalBoundary z hzInternal' hzBoundary
        hzNotBoundary'
    have hiA2 : T.boundary 2 ∈ A := by simpa using hiA
    refine
      ⟨U,
        Tre.replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
          (T.legBoundaryContactClean_reindex hclean e he)
          z hzInternal' hzBoundary hzNotBoundary',
        ?_, ?_⟩
    · rw [T.footCountIn_eq_three_indicators,
        U.footCountIn_eq_three_indicators]
      simp [U, Tre, Tripod.reindex, e, fin3Order,
        replaceLegZeroByNilAtInternalBoundary, hzA, hiA2,
        Nat.add_comm, Nat.add_assoc]
      rfl
    · calc
        U.linkageLength < Tre.linkageLength :=
          Tre.replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
            z hzInternal' hzBoundary hzNotBoundary' hleg'
        _ = T.linkageLength := by
          simp [Tre, linkageLength, Tripod.reindex, e, fin3Order,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Lexicographic normalization of hidden internal contacts.

In a source-clean tripod maximizing feet in `A` and minimizing linkage length
among maximizers, every hidden internal contact in `A` lies on a branch whose
selected foot is already in `A` and whose linkage leg is nil. -/
theorem internal_boundary_contact_foot_mem_and_leg_nil_of_lexicographic
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (A : Set V)
    (hmax :
      forall U : S.Tripod,
        U.LegBoundaryContactClean ->
          U.footCountIn A <= T.footCountIn A)
    (hminimal :
      forall U : S.Tripod,
        U.LegBoundaryContactClean ->
          U.footCountIn A = T.footCountIn A ->
            T.linkageLength <= U.linkageLength)
    (i : Fin 3) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim i))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j)
    (hzA : z ∈ A) :
    T.boundary i ∈ A ∧ (T.leg i).Nil := by
  have hiA : T.boundary i ∈ A := by
    by_contra hiA
    rcases
        T.exists_sourceClean_tripod_more_feet_of_internal_boundary_contact
          hclean A i z hzInternal hzBoundary hzNotBoundary hzA hiA with
      ⟨U, hUclean, hmore⟩
    exact (Nat.not_lt_of_ge (hmax U hUclean)) hmore
  refine ⟨hiA, ?_⟩
  by_contra hleg
  rcases
      T.exists_sourceClean_tripod_same_feet_shorter_of_internal_boundary_contact
        hclean A i z hzInternal hzBoundary hzNotBoundary hzA hiA hleg with
    ⟨U, hUclean, hUcount, hshorter⟩
  exact (Nat.not_lt_of_ge (hminimal U hUclean hUcount)) hshorter

/-- In a minimum-length source-clean tripod, every hidden internal
society-boundary contact belongs to a branch whose linkage leg is nil.

This is the well-founded normalization used in the literal GM IX `(2.4)`
side-tripod paragraph.  A non-nil leg would permit the strictly shorter
replacement constructed above, contradicting minimality. -/
theorem leg_nil_of_minimal_sourceClean_internal_boundary_contact
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (hminimal :
      forall U : S.Tripod,
        U.LegBoundaryContactClean ->
          T.linkageLength <= U.linkageLength)
    (i : Fin 3) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim i))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j) :
    (T.leg i).Nil := by
  by_contra hleg
  rcases
      T.exists_sourceClean_tripod_shorter_of_internal_boundary_contact
        hclean i z hzInternal hzBoundary hzNotBoundary hleg with
    ⟨U, hUclean, hshorter⟩
  exact (Nat.not_lt_of_ge (hminimal U hUclean)) hshorter

theorem boundaryClean_reindex {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.BoundaryClean)
    (e : Fin 3 -> Fin 3) (he : Function.Injective e) :
    (T.reindex e he).BoundaryClean := by
  exact ⟨hclean.1, hclean.2.1,
    (by
      intro i
      simpa [Tripod.reindex] using hclean.2.2.1 (e i)),
    (by
      intro i
      simpa [Tripod.reindex] using hclean.2.2.2 (e i))⟩


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
