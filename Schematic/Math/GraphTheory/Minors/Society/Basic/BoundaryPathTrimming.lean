import Schematic.Math.GraphTheory.Minors.Society.Basic.SupportAndBoundaryPaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Boundary-clean trimming across a prescribed change of side.

If the two boundary ends of a simple path lie on opposite sides of a set
`A`, then some subpath still has its initial boundary vertex in `A` and its
terminal boundary vertex outside `A`, and has no boundary vertex internally.
The support-containment conclusion is essential when this lemma is applied to
two vertex-disjoint paths: trimming preserves their disjointness.

This is the one-path induction used in the standard normalization of the GM IX
definition of an `Omega`-path, whose interior is allowed to meet `Omega`. -/
theorem exists_boundary_clean_transition_subpath_of_path [DecidableEq V]
    (S : GeneralSociety V)
    (A : Set V)
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t)
    (hsA : s ∈ A)
    (htA : t ∉ A)
    {q : S.graph.Walk s t}
    (hq_path : q.IsPath) :
    Exists fun s' : V =>
      Exists fun t' : V =>
        s' ∈ S.boundarySet ∧ t' ∈ S.boundarySet ∧ s' ≠ t' ∧
          s' ∈ A ∧ t' ∉ A ∧
            Exists fun r : S.graph.Walk s' t' =>
              r.IsPath ∧
                Walk.InternalVertices r ∩ S.boundarySet = ∅ ∧
                  forall z : V, z ∈ r.support -> z ∈ q.support := by
  classical
  let Q : Nat -> Prop := fun n =>
    forall {s t : V},
      s ∈ S.boundarySet ->
        t ∈ S.boundarySet ->
          s ≠ t ->
            s ∈ A ->
              t ∉ A ->
                forall {q : S.graph.Walk s t},
                  q.IsPath ->
                    q.length = n ->
                      Exists fun s' : V =>
                        Exists fun t' : V =>
                          s' ∈ S.boundarySet ∧
                            t' ∈ S.boundarySet ∧ s' ≠ t' ∧
                              s' ∈ A ∧ t' ∉ A ∧
                                Exists fun r : S.graph.Walk s' t' =>
                                  r.IsPath ∧
                                    Walk.InternalVertices r ∩
                                        S.boundarySet = ∅ ∧
                                      forall z : V,
                                        z ∈ r.support -> z ∈ q.support
  have hQ : forall n : Nat, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s t hs ht hst hsA htA q hq_path hlen
      by_cases hclean :
          Walk.InternalVertices q ∩ S.boundarySet = ∅
      · exact
          ⟨s, t, hs, ht, hst, hsA, htA, q, hq_path, hclean,
            fun _z hz => hz⟩
      · have hnonempty :
            (Walk.InternalVertices q ∩ S.boundarySet).Nonempty := by
          rw [Set.nonempty_iff_ne_empty]
          exact hclean
        rcases hnonempty with ⟨x, hxInternal, hxBoundary⟩
        have hxSupport : x ∈ q.support := hxInternal.1
        have hxs : x ≠ s := hxInternal.2.1
        have hxt : x ≠ t := hxInternal.2.2
        by_cases hxA : x ∈ A
        · let q' : S.graph.Walk x t := q.dropUntil x hxSupport
          have hq'_path : q'.IsPath := by
            simpa [q'] using hq_path.dropUntil hxSupport
          have hlt : q'.length < n := by
            have hdrop : q'.length < q.length := by
              simpa [q'] using
                Walk.length_dropUntil_lt_of_mem_support_ne_start
                  hxSupport hxs
            omega
          rcases
              ih q'.length hlt hxBoundary ht hxt hxA htA
                hq'_path rfl with
            ⟨s', t', hs', ht', hs't', hs'A, ht'A, r,
              hrPath, hrClean, hrSubset⟩
          refine
            ⟨s', t', hs', ht', hs't', hs'A, ht'A, r,
              hrPath, hrClean, ?_⟩
          intro z hzr
          exact SimpleGraph.Walk.support_dropUntil_subset q hxSupport
            (hrSubset z hzr)
        · let q' : S.graph.Walk s x := q.takeUntil x hxSupport
          have hq'_path : q'.IsPath := by
            simpa [q'] using hq_path.takeUntil hxSupport
          have hlt : q'.length < n := by
            have htake : q'.length < q.length := by
              simpa [q'] using
                SimpleGraph.Walk.length_takeUntil_lt hxSupport hxt
            omega
          rcases
              ih q'.length hlt hs hxBoundary hxs.symm hsA hxA
                hq'_path rfl with
            ⟨s', t', hs', ht', hs't', hs'A, ht'A, r,
              hrPath, hrClean, hrSubset⟩
          refine
            ⟨s', t', hs', ht', hs't', hs'A, ht'A, r,
              hrPath, hrClean, ?_⟩
          intro z hzr
          exact SimpleGraph.Walk.support_takeUntil_subset q hxSupport
            (hrSubset z hzr)
  exact hQ q.length hs ht hst hsA htA hq_path rfl

/-- Two vertex-disjoint paths with alternating boundary ends contain a cross
in the boundary-clean normal form used by `GeneralSociety.Cross`.

The GM IX definition of an `Omega`-path allows internal boundary contacts.
The first trim crosses the complementary arc between the ends of the second
path.  After cyclically rotating the resulting four boundary points, the
second trim crosses the arc between the new ends of the first path.  Thus the
two trims must still alternate; trimming independently without these chosen
arcs would not preserve that conclusion. -/
theorem Cross.of_disjoint_alternating_paths
    {S : GeneralSociety V}
    (E : CrossEndpoints S.boundary)
    {p : S.graph.Walk (E.endpoint 0) (E.endpoint 2)}
    {q : S.graph.Walk (E.endpoint 1) (E.endpoint 3)}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hpq :
      Disjoint {z : V | z ∈ p.support} {z : V | z ∈ q.support}) :
    Nonempty S.Cross := by
  classical
  have h31 : E.endpoint 3 ≠ E.endpoint 1 := by
    intro h
    exact (by decide : (3 : Fin 4) ≠ 1) (E.endpoint_injective h)
  have h13 : E.endpoint 1 ≠ E.endpoint 3 := h31.symm
  have hrot :
      CrossEndpointAlternating S.boundary (fun i =>
        if i = 0 then E.endpoint 1
        else if i = 1 then E.endpoint 2
        else if i = 2 then E.endpoint 3
        else E.endpoint 0) :=
    CrossEndpointAlternating.rotate1 E.endpoint_mem
      E.endpoint_injective E.cyclic_alternating
  let A : Set V :=
    S.boundary.clockwiseArcSet (E.endpoint 3) (E.endpoint 1)
  have he0A : E.endpoint 0 ∈ A := by
    change S.boundary.ClockwiseOpenBetween
      (E.endpoint 3) (E.endpoint 1) (E.endpoint 0)
    simpa [CrossEndpointAlternating] using hrot.2
  have he2_reverse :
      E.endpoint 2 ∈
        S.boundary.clockwiseArcSet (E.endpoint 1) (E.endpoint 3) := by
    change S.boundary.ClockwiseOpenBetween
      (E.endpoint 1) (E.endpoint 3) (E.endpoint 2)
    simpa [CrossEndpointAlternating] using hrot.1
  have he2_not_A : E.endpoint 2 ∉ A := by
    intro he2A
    exact Set.disjoint_left.mp
      (S.boundary.clockwiseArcSet_disjoint_reverse
        (E.endpoint_mem 3) h31) he2A he2_reverse
  obtain ⟨a0, a2, ha0_boundary, ha2_boundary, ha02, ha0A, ha2_not_A,
      p', hp'_path, hp'_clean, hp'_subset⟩ :=
    exists_boundary_clean_transition_subpath_of_path S A
      (E.endpoint_mem 0) (E.endpoint_mem 2)
      (by
        intro h
        exact (by decide : (0 : Fin 4) ≠ 2) (E.endpoint_injective h))
      he0A he2_not_A hp
  have ha0_ne_e1 : a0 ≠ E.endpoint 1 := by
    intro h
    subst a0
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.start_mem_support) q.start_mem_support
  have ha0_ne_e3 : a0 ≠ E.endpoint 3 := by
    intro h
    subst a0
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.start_mem_support) q.end_mem_support
  have ha2_ne_e1 : a2 ≠ E.endpoint 1 := by
    intro h
    subst a2
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.end_mem_support) q.start_mem_support
  have ha2_ne_e3 : a2 ≠ E.endpoint 3 := by
    intro h
    subst a2
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.end_mem_support) q.end_mem_support
  have ha2_reverse :
      a2 ∈ S.boundary.clockwiseArcSet (E.endpoint 1) (E.endpoint 3) := by
    rcases S.boundary.clockwiseOpen_or_reverse_of_mem_ne
        (E.endpoint_mem 3) ha2_boundary
        ha2_ne_e3 ha2_ne_e1 h31 with hA | hreverse
    · exact False.elim (ha2_not_A (by simpa [A] using hA))
    · exact hreverse
  let base : Fin 4 -> V
    | 0 => E.endpoint 3
    | 1 => a0
    | 2 => E.endpoint 1
    | 3 => a2
  have hbase_mem : forall i : Fin 4, base i ∈ S.boundarySet := by
    intro i
    fin_cases i
    · exact E.endpoint_mem 3
    · exact ha0_boundary
    · exact E.endpoint_mem 1
    · exact ha2_boundary
  have hbase_injective : Function.Injective base := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [base] at hij ⊢ <;>
      first
      | rfl
      | exact False.elim (ha0_ne_e3 hij.symm)
      | exact False.elim (ha0_ne_e3 hij)
      | exact False.elim (h31 hij)
      | exact False.elim (h31 hij.symm)
      | exact False.elim (ha2_ne_e3 hij.symm)
      | exact False.elim (ha2_ne_e3 hij)
      | exact False.elim (ha0_ne_e1 hij)
      | exact False.elim (ha0_ne_e1 hij.symm)
      | exact False.elim (ha02 hij)
      | exact False.elim (ha02 hij.symm)
      | exact False.elim (ha2_ne_e1 hij.symm)
      | exact False.elim (ha2_ne_e1 hij)
  have hbase_alternating :
      CrossEndpointAlternating S.boundary base := by
    dsimp [CrossEndpointAlternating, base]
    change S.boundary.ClockwiseOpenBetween
        (E.endpoint 3) (E.endpoint 1) a0 ∧
      S.boundary.ClockwiseOpenBetween
        (E.endpoint 1) (E.endpoint 3) a2
    exact ⟨ha0A, ha2_reverse⟩
  let middle : Fin 4 -> V
    | 0 => a0
    | 1 => E.endpoint 1
    | 2 => a2
    | 3 => E.endpoint 3
  have hmiddle_alternating :
      CrossEndpointAlternating S.boundary middle := by
    have h := CrossEndpointAlternating.rotate1 hbase_mem hbase_injective
      hbase_alternating
    simpa [middle, base] using h
  let B : Set V := S.boundary.clockwiseArcSet a0 a2
  have he1B : E.endpoint 1 ∈ B := by
    change S.boundary.ClockwiseOpenBetween a0 a2 (E.endpoint 1)
    simpa [middle, CrossEndpointAlternating] using hmiddle_alternating.1
  have he3_reverse :
      E.endpoint 3 ∈ S.boundary.clockwiseArcSet a2 a0 := by
    change S.boundary.ClockwiseOpenBetween a2 a0 (E.endpoint 3)
    simpa [middle, CrossEndpointAlternating] using hmiddle_alternating.2
  have he3_not_B : E.endpoint 3 ∉ B := by
    intro he3B
    exact Set.disjoint_left.mp
      (S.boundary.clockwiseArcSet_disjoint_reverse ha0_boundary ha02)
      he3B he3_reverse
  obtain ⟨b1, b3, hb1_boundary, hb3_boundary, hb13, hb1B, hb3_not_B,
      q', hq'_path, hq'_clean, hq'_subset⟩ :=
    exists_boundary_clean_transition_subpath_of_path S B
      (E.endpoint_mem 1) (E.endpoint_mem 3) h13 he1B he3_not_B hq
  have hb1_ne_a0 : b1 ≠ a0 := by
    intro h
    subst b1
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.start_mem_support)
      (hq'_subset _ q'.start_mem_support)
  have hb1_ne_a2 : b1 ≠ a2 := by
    intro h
    subst b1
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.end_mem_support)
      (hq'_subset _ q'.start_mem_support)
  have hb3_ne_a0 : b3 ≠ a0 := by
    intro h
    subst b3
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.start_mem_support)
      (hq'_subset _ q'.end_mem_support)
  have hb3_ne_a2 : b3 ≠ a2 := by
    intro h
    subst b3
    exact Set.disjoint_left.mp hpq
      (hp'_subset _ p'.end_mem_support)
      (hq'_subset _ q'.end_mem_support)
  have hb3_reverse : b3 ∈ S.boundary.clockwiseArcSet a2 a0 := by
    rcases S.boundary.clockwiseOpen_or_reverse_of_mem_ne
        ha0_boundary hb3_boundary
        hb3_ne_a0 hb3_ne_a2 ha02 with hB | hreverse
    · exact False.elim (hb3_not_B (by simpa [B] using hB))
    · exact hreverse
  let endpoint : Fin 4 -> V
    | 0 => a0
    | 1 => b1
    | 2 => a2
    | 3 => b3
  have endpoint_mem : forall i : Fin 4, endpoint i ∈ S.boundarySet := by
    intro i
    fin_cases i <;>
      simp [endpoint, ha0_boundary, hb1_boundary, ha2_boundary, hb3_boundary]
  have endpoint_injective : Function.Injective endpoint := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [endpoint] at hij ⊢ <;>
      first
      | rfl
      | exact False.elim (hb1_ne_a0 hij.symm)
      | exact False.elim (hb1_ne_a0 hij)
      | exact False.elim (ha02 hij)
      | exact False.elim (ha02 hij.symm)
      | exact False.elim (hb3_ne_a0 hij.symm)
      | exact False.elim (hb3_ne_a0 hij)
      | exact False.elim (hb1_ne_a2 hij)
      | exact False.elim (hb1_ne_a2 hij.symm)
      | exact False.elim (hb13 hij)
      | exact False.elim (hb13 hij.symm)
      | exact False.elim (hb3_ne_a2 hij.symm)
      | exact False.elim (hb3_ne_a2 hij)
  refine ⟨{
    endpoints := {
      endpoint := endpoint
      endpoint_mem := endpoint_mem
      endpoint_injective := endpoint_injective
      cyclic_alternating := by
        dsimp [CrossEndpointAlternating, endpoint]
        change S.boundary.ClockwiseOpenBetween a0 a2 b1 ∧
          S.boundary.ClockwiseOpenBetween a2 a0 b3
        exact ⟨hb1B, hb3_reverse⟩
    }
    firstPath := p'
    secondPath := q'
    firstPath_isPath := hp'_path
    secondPath_isPath := hq'_path
    firstPath_nontrivial := ?_
    secondPath_nontrivial := ?_
    paths_disjoint := ?_
    first_internal_boundary := hp'_clean
    second_internal_boundary := hq'_clean
  }⟩
  · intro hlen
    exact ha02 (SimpleGraph.Walk.eq_of_length_eq_zero hlen)
  · intro hlen
    exact hb13 (SimpleGraph.Walk.eq_of_length_eq_zero hlen)
  · rw [Set.disjoint_left]
    intro z hzp' hzq'
    exact Set.disjoint_left.mp hpq (hp'_subset z hzp') (hq'_subset z hzq')

/-- A path between two distinct boundary vertices contains a clean
boundary-to-boundary subpath, and therefore no third boundary vertex occurs on
the resulting subpath support. -/
theorem exists_boundary_clean_subpath_avoiding_remainder_of_path [DecidableEq V]
    (S : GeneralSociety V)
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t)
    {q : S.graph.Walk s t}
    (hq_path : q.IsPath) :
    Exists fun s' : V =>
      Exists fun t' : V =>
        s' ∈ S.boundarySet ∧ t' ∈ S.boundarySet ∧ s' ≠ t' ∧
          Exists fun r : S.graph.Walk s' t' =>
            r.IsPath ∧
              Walk.InternalVertices r ∩ S.boundarySet = ∅ ∧
                forall z : V,
                  z ∈ r.support ->
                    z ∈ S.boundarySet \ ({s', t'} : Set V) ->
                      False := by
  classical
  obtain ⟨s', t', hs', ht', hs't', r, hr_path, hr_clean⟩ :=
    S.exists_boundary_clean_subpath_of_path hs ht hst hq_path
  refine ⟨s', t', hs', ht', hs't', r, hr_path, hr_clean, ?_⟩
  intro z hzr hzboundary
  have hzs : z ≠ s' := by
    intro h
    exact hzboundary.2 (by simp [h])
  have hzt : z ≠ t' := by
    intro h
    exact hzboundary.2 (by simp [h])
  have hz_internal : z ∈ Walk.InternalVertices r :=
    ⟨hzr, hzs, hzt⟩
  have hz_bad : z ∈ Walk.InternalVertices r ∩ S.boundarySet :=
    ⟨hz_internal, hzboundary.1⟩
  have hz_not : z ∉ Walk.InternalVertices r ∩ S.boundarySet := by
    rw [hr_clean]
    simp
  exact hz_not hz_bad


end GeneralSociety

end Schematic.Math.GraphTheory
