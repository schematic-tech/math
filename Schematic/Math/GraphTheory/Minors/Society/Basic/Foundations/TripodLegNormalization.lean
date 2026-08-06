import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.TripodStructure

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Replace one tripod linkage leg by the nil path at an internal rim vertex
which is already on the society boundary.

This is the elementary normalization move implicit in the definition of a
GM IX tripod.  A boundary vertex in the interior of the `i`-th rim is itself
a valid `X -> Ω` path endpoint: use that vertex as the new attachment and
boundary foot, and use the nil path as the new linkage leg.  The hypothesis
that it is not one of the old three feet preserves injectivity of the feet.

The operation is important for the literal `(2.4)` descent.  A hidden rim
contact does not need to be declared impossible for the original tripod.
When the old `i`-th leg is nontrivial, this operation produces a tripod with
a strictly shorter linkage package; a minimal tripod therefore has no such
contact on a nontrivial branch. -/
noncomputable def replaceLegZeroByNilAtInternalBoundary
    {S : GeneralSociety V} (T : S.Tripod) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim 0))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j) :
    S.Tripod := by
  classical
  let attach' : Fin 3 -> V
    | 0 => z
    | 1 => T.attach 1
    | 2 => T.attach 2
  let boundary' : Fin 3 -> V
    | 0 => z
    | 1 => T.boundary 1
    | 2 => T.boundary 2
  let leg' : forall j : Fin 3, S.graph.Walk (attach' j) (boundary' j) :=
    fun
      | 0 => SimpleGraph.Walk.nil
      | 1 => T.leg 1
      | 2 => T.leg 2
  refine {
    left := T.left
    right := T.right
    left_ne_right := T.left_ne_right
    rim := T.rim
    rim_isPath := T.rim_isPath
    attach := attach'
    attach_mem_rim := ?_
    boundary := boundary'
    boundary_mem := ?_
    boundary_injective := ?_
    leg := leg'
    leg_isPath := ?_
    rim_internals_disjoint := T.rim_internals_disjoint
    legs_pairwise_disjoint := ?_
    legs_meet_rims_only_at_attach := ?_
  }
  · intro j
    by_cases hji : j = 0
    · subst j
      simpa [attach'] using hzInternal
    · fin_cases j
      · exact False.elim (hji rfl)
      · exact T.attach_mem_rim 1
      · exact T.attach_mem_rim 2
  · intro j
    by_cases hji : j = 0
    · subst j
      simpa [boundary'] using hzBoundary
    · fin_cases j
      · exact False.elim (hji rfl)
      · exact T.boundary_mem 1
      · exact T.boundary_mem 2
  · intro j k hjk
    by_cases hji : j = 0
    · subst j
      by_cases hki : k = 0
      · exact hki.symm
      · have hzk : z = T.boundary k := by
          fin_cases k <;> simp_all [boundary']
        exact False.elim (hzNotBoundary k hzk)
    · by_cases hki : k = 0
      · subst k
        have hjz : T.boundary j = z := by
          fin_cases j <;> simp_all [boundary']
        exact False.elim (hzNotBoundary j hjz.symm)
      · exact T.boundary_injective (by
          fin_cases j <;> fin_cases k <;> simp_all [boundary'])
  · intro j
    fin_cases j
    · exact SimpleGraph.Walk.IsPath.nil
    · exact T.leg_isPath 1
    · exact T.leg_isPath 2
  · intro j k hjk
    by_cases hji : j = 0
    · subst j
      have hki : k ≠ 0 := by
        intro hki
        exact hjk hki.symm
      rw [Set.disjoint_left]
      intro v hvj hvk
      have hvz : v = z := by
        simpa [leg'] using hvj
      subst v
      have hzLeg : z ∈ (T.leg k).support := by
        fin_cases k <;> simp_all [leg']
      have hzAttach : z = T.attach k :=
        T.legs_meet_rims_only_at_attach k 0 z hzLeg
          (Walk.internalVertices_subset_support (T.rim 0) hzInternal)
      have hzInternalK : z ∈ Walk.InternalVertices (T.rim k) := by
        simpa [hzAttach] using T.attach_mem_rim k
      exact
        Set.disjoint_left.mp
          (T.rim_internals_disjoint 0 k (fun hik => hki hik.symm))
          hzInternal hzInternalK
    · by_cases hki : k = 0
      · subst k
        rw [Set.disjoint_left]
        intro v hvj hvk
        have hvz : v = z := by
          simpa [leg'] using hvk
        subst v
        have hzLeg : z ∈ (T.leg j).support := by
          fin_cases j <;> simp_all [leg']
        have hzAttach : z = T.attach j :=
          T.legs_meet_rims_only_at_attach j 0 z hzLeg
            (Walk.internalVertices_subset_support (T.rim 0) hzInternal)
        have hzInternalJ : z ∈ Walk.InternalVertices (T.rim j) := by
          simpa [hzAttach] using T.attach_mem_rim j
        exact
          Set.disjoint_left.mp
            (T.rim_internals_disjoint j 0 hji)
            hzInternalJ hzInternal
      · fin_cases j <;> fin_cases k <;>
          simp_all [leg', T.legs_pairwise_disjoint]
  · intro j k v hvLeg hvRim
    by_cases hji : j = 0
    · subst j
      have hvz : v = z := by
        simpa [leg'] using hvLeg
      simp [attach', hvz]
    · fin_cases j
      · exact False.elim (hji rfl)
      · exact
          T.legs_meet_rims_only_at_attach 1 k v
            (by simpa [leg'] using hvLeg) hvRim
      · exact
          T.legs_meet_rims_only_at_attach 2 k v
            (by simpa [leg'] using hvLeg) hvRim

@[simp]
theorem replaceLegZeroByNilAtInternalBoundary_leg_zero_nil
    {S : GeneralSociety V} (T : S.Tripod) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim 0))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j) :
    ((T.replaceLegZeroByNilAtInternalBoundary z hzInternal hzBoundary
      hzNotBoundary).leg 0).Nil := by
  classical
  simp [replaceLegZeroByNilAtInternalBoundary]

theorem replaceLegZeroByNilAtInternalBoundary_legBoundaryContactClean
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim 0))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j) :
    (T.replaceLegZeroByNilAtInternalBoundary z hzInternal hzBoundary
      hzNotBoundary).LegBoundaryContactClean := by
  classical
  intro j w hwLeg hwBoundary
  fin_cases j
  · simpa [replaceLegZeroByNilAtInternalBoundary] using hwLeg
  · simpa [replaceLegZeroByNilAtInternalBoundary] using
      hclean 1 w hwLeg hwBoundary
  · simpa [replaceLegZeroByNilAtInternalBoundary] using
      hclean 2 w hwLeg hwBoundary

/-- Total length of the three linkage legs of a tripod. -/
def linkageLength {S : GeneralSociety V} (T : S.Tripod) : Nat :=
  (T.leg 0).length + (T.leg 1).length + (T.leg 2).length

theorem replaceLegZeroByNilAtInternalBoundary_linkageLength_lt
    {S : GeneralSociety V} (T : S.Tripod) (z : V)
    (hzInternal : z ∈ Walk.InternalVertices (T.rim 0))
    (hzBoundary : z ∈ S.boundarySet)
    (hzNotBoundary : forall j : Fin 3, z ≠ T.boundary j)
    (hleg : Not (T.leg 0).Nil) :
    (T.replaceLegZeroByNilAtInternalBoundary z hzInternal hzBoundary
      hzNotBoundary).linkageLength < T.linkageLength := by
  have hzero : (T.leg 0).length ≠ 0 := by
    intro h
    exact hleg ((SimpleGraph.Walk.nil_iff_length_eq).mpr h)
  have hpos : 0 < (T.leg 0).length := Nat.pos_of_ne_zero hzero
  simp [linkageLength, replaceLegZeroByNilAtInternalBoundary]
  omega

theorem trimLegsToFirstBoundary_vertexSet_subset
    [DecidableEq V]
    {S : GeneralSociety V} (T : S.Tripod)
    (D : FirstBoundaryLegData T) :
    (T.trimLegsToFirstBoundary D).vertexSet ⊆ T.vertexSet := by
  intro z hz
  rcases hz with hzRim | hzLeg
  · rcases hzRim with ⟨i, hzi⟩
    exact T.rim_mem_vertexSet (i := i) (by
      simpa [trimLegsToFirstBoundary] using hzi)
  · rcases hzLeg with ⟨i, hzi⟩
    exact T.leg_mem_vertexSet (i := i)
      (SimpleGraph.Walk.support_takeUntil_subset (T.leg i)
        (D.boundary_mem_leg i)
        (by simpa [trimLegsToFirstBoundary] using hzi))

theorem boundary_contact_boundary_or_rim_of_legBoundaryContactClean
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    {z : V}
    (hzBoundary : z ∈ S.boundarySet)
    (hzT : z ∈ T.vertexSet) :
    (Exists fun m : Fin 3 => z = T.boundary m) ∨
      Exists fun i : Fin 3 => z ∈ (T.rim i).support := by
  rcases hzT with hzRim | hzLeg
  · exact Or.inr hzRim
  · rcases hzLeg with ⟨i, hzLeg⟩
    exact Or.inl ⟨i, hclean i z hzLeg hzBoundary⟩

theorem rim_contact_of_legBoundaryContactClean_of_not_boundary
    {S : GeneralSociety V} (T : S.Tripod)
    (hclean : T.LegBoundaryContactClean)
    {z : V}
    (hzBoundary : z ∈ S.boundarySet)
    (hzT : z ∈ T.vertexSet)
    (hnot_boundary : forall m : Fin 3, z ≠ T.boundary m) :
    Exists fun i : Fin 3 => z ∈ (T.rim i).support := by
  rcases
      T.boundary_contact_boundary_or_rim_of_legBoundaryContactClean
        hclean hzBoundary hzT with
    hboundary | hrim
  · rcases hboundary with ⟨m, hm⟩
    exact False.elim (hnot_boundary m hm)
  · exact hrim

/-- A raw tripod leg has no internal contact with any of the three selected
boundary feet of the tripod.

This is weaker than the full GM IX `X -> Ω` cleanliness, which rules out all
internal society-boundary vertices, but it is already forced by the current
tripod fields: the own boundary foot is the end of the leg, and the other two
feet lie on pairwise-disjoint legs. -/
theorem leg_internal_disjoint_boundary_range
    {S : GeneralSociety V} (T : S.Tripod) (i : Fin 3) :
    Disjoint (Walk.InternalVertices (T.leg i)) (Set.range T.boundary) := by
  rw [Set.disjoint_left]
  intro z hzInternal hzBoundary
  rcases hzBoundary with ⟨j, rfl⟩
  by_cases hji : j = i
  · subst j
    exact hzInternal.2.2 rfl
  · exact
      Set.disjoint_left.mp (T.legs_pairwise_disjoint i j (by
        intro hij
        exact hji hij.symm))
        hzInternal.1 (T.leg j).end_mem_support


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
