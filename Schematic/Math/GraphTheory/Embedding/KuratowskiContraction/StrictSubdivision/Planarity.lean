import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.InternalPath

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem strictSubdivisionModel_collapseEdge_collapsed_branch_of_internal_impossible
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    (huses :
      (∃ x, M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target)) ∨
      ∃ x y, ∃ hxy : K.Adj x y,
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          (M.edgePath hxy).support)
    (hinternal_impossible :
      ∀ {x y : W} (hxy : K.Adj x y),
        (none : (GraphContraction.collapseEdge G hab).Target) ∈
          Walk.InternalVertices (M.edgePath hxy) → False) :
    ∃ x, M.branchVertex x =
      (none : (GraphContraction.collapseEdge G hab).Target) := by
  rcases huses with hbranch | ⟨x, y, hxy, hsupport⟩
  · exact hbranch
  · by_cases hx : M.branchVertex x = none
    · exact ⟨x, hx⟩
    · by_cases hy : M.branchVertex y = none
      · exact ⟨y, hy⟩
      · exact False.elim (hinternal_impossible hxy
          ⟨hsupport, fun h => hx h.symm, fun h => hy h.symm⟩)

/-- In a planar source graph, a strict `K_5` model in an edge contraction
cannot use the collapsed vertex only internally on an edge path; otherwise the
internal-edge uncontraction constructor gives a strict `K_5` model in the
source graph. -/
theorem strictSubdivisionModel_K5_collapseEdge_collapsed_branch_of_planar
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph) :
    Exists fun x : Fin 5 =>
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target) := by
  apply strictSubdivisionModel_collapseEdge_collapsed_branch_of_internal_impossible
    hab M (strictSubdivisionModel_K5_collapseEdge_uses_collapsed_of_planar h_planar hab M)
  intro x y hxy hinternal
  exact h_planar.no_K5_subdivision
    (containsStrictSubdivision_of_collapseEdge_internal_edgePath
      hab M hxy hinternal)

/-- The analogous branch-use conclusion for quotient `K_{3,3}` models. -/
theorem strictSubdivisionModel_K33_collapseEdge_collapsed_branch_of_planar
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K33Graph
        (GraphContraction.collapseEdge G hab).graph) :
    Exists fun x : K33Vertex =>
      M.branchVertex x =
        (none : (GraphContraction.collapseEdge G hab).Target) := by
  apply strictSubdivisionModel_collapseEdge_collapsed_branch_of_internal_impossible
    hab M (strictSubdivisionModel_K33_collapseEdge_uses_collapsed_of_planar h_planar hab M)
  intro x y hxy hinternal
  exact h_planar.no_K33_subdivision
    (containsStrictSubdivision_of_collapseEdge_internal_edgePath
      hab M hxy hinternal)

theorem not_containsStrictSubdivision_K33_collapseEdge_of_planar
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b) :
    Not (ContainsStrictSubdivision K33Graph
      (GraphContraction.collapseEdge G hab).graph) := by
  intro hK33
  rcases hK33 with ⟨M⟩
  rcases
      strictSubdivisionModel_K33_collapseEdge_collapsed_branch_of_planar
        h_planar hab M with
    ⟨c, hc⟩
  exact h_planar.no_K33_subdivision
    (containsStrictSubdivision_K33_of_collapseEdge_collapsed_branch
      hab M hc)

theorem containsStrictSubdivision_K5_of_collapseEdge_collapsed_branch_pair_direct
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c : Fin 5}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (hpair_direct :
      forall {y z : Fin 5} (hcy : K5Graph.Adj c y) (hcz : K5Graph.Adj c z),
        y ≠ z ->
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) ∨
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcz hc).v)) :
    ContainsStrictSubdivision K5Graph G :=
  containsStrictSubdivision_of_collapseEdge_branch_root_pair_direct
    hab M hc hroot_pair hother_pair hroot_other hpair_direct

theorem containsStrictSubdivision_K5_or_K33_of_collapseEdge_K5_four_neighbours
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c p q r s : Fin 5}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hpc : p ≠ c) (hqc : q ≠ c) (hrc : r ≠ c) (hsc : s ≠ c)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hcover : forall y : Fin 5, y ≠ c ->
      y = p ∨ y = q ∨ y = r ∨ y = s) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  classical
  let src : Fin 4 -> Fin 5
    | 0 => p
    | 1 => q
    | 2 => r
    | 3 => s
  have hsrc_ne_c : forall i : Fin 4, src i ≠ c := by
    intro i
    fin_cases i
    · simpa [src] using hpc
    · simpa [src] using hqc
    · simpa [src] using hrc
    · simpa [src] using hsc
  have hsrc_inj : Function.Injective src := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [src] at hij ⊢
    all_goals
      first
      | exact False.elim (hpq hij)
      | exact False.elim (hpq hij.symm)
      | exact False.elim (hpr hij)
      | exact False.elim (hpr hij.symm)
      | exact False.elim (hps hij)
      | exact False.elim (hps hij.symm)
      | exact False.elim (hqr hij)
      | exact False.elim (hqr hij.symm)
      | exact False.elim (hqs hij)
      | exact False.elim (hqs hij.symm)
      | exact False.elim (hrs hij)
      | exact False.elim (hrs hij.symm)
  have hsrc_adj : forall i : Fin 4, K5Graph.Adj c (src i) := by
    intro i
    exact K5Graph.adj_of_ne (hsrc_ne_c i).symm
  let Tail (i : Fin 4) : CollapseEdgeBranchIncidentTail hab M
      (hsrc_adj i) hc :=
    CollapseEdgeBranchIncidentTail.ofModel hab M (hsrc_adj i) hc
  let side : Fin 4 -> Bool := fun i =>
    if G.Adj a ((Tail i).v) then true else false
  have exists_index_of_adj :
      forall {y : Fin 5}, K5Graph.Adj c y ->
        Exists fun i : Fin 4 => y = src i := by
    intro y hcy
    rcases hcover y hcy.ne.symm with hy | hy | hy | hy
    · exact ⟨0, by simp [src, hy]⟩
    · exact ⟨1, by simp [src, hy]⟩
    · exact ⟨2, by simp [src, hy]⟩
    · exact ⟨3, by simp [src, hy]⟩
  have ha_of_side_true :
      forall {y : Fin 5} (hcy : K5Graph.Adj c y) {i : Fin 4},
        y = src i -> side i = true ->
          G.Adj a
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) := by
    intro y hcy i hy htrue
    subst y
    have hproof : hcy = hsrc_adj i := Subsingleton.elim _ _
    cases hproof
    by_cases ha : G.Adj a ((Tail i).v)
    · simpa [Tail] using ha
    · have hfalse : side i = false := by
        simp [side, Tail, ha]
      simp [hfalse] at htrue
  have hb_of_side_false :
      forall {y : Fin 5} (hcy : K5Graph.Adj c y) {i : Fin 4},
        y = src i -> side i = false ->
          G.Adj b
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) := by
    intro y hcy i hy hfalse
    subst y
    have hproof : hcy = hsrc_adj i := Subsingleton.elim _ _
    cases hproof
    have hnot_a : ¬ G.Adj a ((Tail i).v) := by
      intro ha
      have htrue : side i = true := by
        simp [side, Tail, ha]
      simp [htrue] at hfalse
    exact (Tail i).hside.resolve_left (by simpa [Tail] using hnot_a)
  have hidx_ne_of_vertices_ne :
      forall {y z : Fin 5} {iy iz : Fin 4},
        y = src iy -> z = src iz -> y ≠ z -> iy ≠ iz := by
    intro y z iy iz hy hz hyz hidx
    apply hyz
    calc
      y = src iy := hy
      _ = src iz := by rw [hidx]
      _ = z := hz.symm
  rcases fin4_bool_pair_majority_or_two_two side with hmajor | htwo_two
  · rcases hmajor with ⟨rootSide, hmajor⟩
    cases rootSide
    · left
      refine
        containsStrictSubdivision_K5_of_collapseEdge_collapsed_branch_pair_direct
          hab M hc (root := b) (other := a) ?_ ?_ hab.symm ?_
      · simp
      · simp
      · intro y z hcy hcz hyz
        rcases exists_index_of_adj hcy with ⟨iy, hy⟩
        rcases exists_index_of_adj hcz with ⟨iz, hz⟩
        have hiyz : iy ≠ iz :=
          hidx_ne_of_vertices_ne hy hz hyz
        rcases hmajor iy iz hiyz with hyfalse | hzfalse
        · left
          exact hb_of_side_false hcy hy hyfalse
        · right
          exact hb_of_side_false hcz hz hzfalse
    · left
      refine
        containsStrictSubdivision_K5_of_collapseEdge_collapsed_branch_pair_direct
          hab M hc (root := a) (other := b) ?_ ?_ hab ?_
      · simp
      · simp
      · intro y z hcy hcz hyz
        rcases exists_index_of_adj hcy with ⟨iy, hy⟩
        rcases exists_index_of_adj hcz with ⟨iz, hz⟩
        have hiyz : iy ≠ iz :=
          hidx_ne_of_vertices_ne hy hz hyz
        rcases hmajor iy iz hiyz with hytrue | hztrue
        · left
          exact ha_of_side_true hcy hy hytrue
        · right
          exact ha_of_side_true hcz hz hztrue
  · rcases htwo_two with
      ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl,
        hi, hj, hk, hl⟩
    right
    have hpq' : src i ≠ src j := by
      intro h
      exact hij (hsrc_inj h)
    have hpr' : src i ≠ src k := by
      intro h
      exact hik (hsrc_inj h)
    have hps' : src i ≠ src l := by
      intro h
      exact hil (hsrc_inj h)
    have hqr' : src j ≠ src k := by
      intro h
      exact hjk (hsrc_inj h)
    have hqs' : src j ≠ src l := by
      intro h
      exact hjl (hsrc_inj h)
    have hrs' : src k ≠ src l := by
      intro h
      exact hkl (hsrc_inj h)
    exact
      containsStrictSubdivision_K33_of_collapseEdge_K5_two_two
        hab M (Tail i) (Tail j) (Tail k) (Tail l)
        hpq' hpr' hps' hqr' hqs' hrs'
        (ha_of_side_true (hsrc_adj i) rfl hi)
        (ha_of_side_true (hsrc_adj j) rfl hj)
        (hb_of_side_false (hsrc_adj k) rfl hk)
        (hb_of_side_false (hsrc_adj l) rfl hl)

theorem containsStrictSubdivision_K5_or_K33_of_collapseEdge_collapsed_branch
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c : Fin 5}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    ContainsStrictSubdivision K5Graph G ∨
      ContainsStrictSubdivision K33Graph G := by
  fin_cases c
  · exact
      containsStrictSubdivision_K5_or_K33_of_collapseEdge_K5_four_neighbours
        hab M hc (c := 0) (p := 1) (q := 2) (r := 3) (s := 4)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by
          intro y hy
          fin_cases y <;> simp at hy ⊢)
  · exact
      containsStrictSubdivision_K5_or_K33_of_collapseEdge_K5_four_neighbours
        hab M hc (c := 1) (p := 0) (q := 2) (r := 3) (s := 4)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by
          intro y hy
          fin_cases y <;> simp at hy ⊢)
  · exact
      containsStrictSubdivision_K5_or_K33_of_collapseEdge_K5_four_neighbours
        hab M hc (c := 2) (p := 0) (q := 1) (r := 3) (s := 4)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by
          intro y hy
          fin_cases y <;> simp at hy ⊢)
  · exact
      containsStrictSubdivision_K5_or_K33_of_collapseEdge_K5_four_neighbours
        hab M hc (c := 3) (p := 0) (q := 1) (r := 2) (s := 4)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by
          intro y hy
          fin_cases y <;> simp at hy ⊢)
  · exact
      containsStrictSubdivision_K5_or_K33_of_collapseEdge_K5_four_neighbours
        hab M hc (c := 4) (p := 0) (q := 1) (r := 2) (s := 3)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by
          intro y hy
          fin_cases y <;> simp at hy ⊢)

theorem not_containsStrictSubdivision_K5_collapseEdge_of_planar_of_pair_direct
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b root other : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c : Fin 5}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (hpair_direct :
      forall {y z : Fin 5} (hcy : K5Graph.Adj c y) (hcz : K5Graph.Adj c z),
        y ≠ z ->
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) ∨
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcz hc).v)) :
    False :=
  h_planar.no_K5_subdivision
    (containsStrictSubdivision_K5_of_collapseEdge_collapsed_branch_pair_direct
      hab M hc hroot_pair hother_pair hroot_other hpair_direct)

theorem not_containsStrictSubdivision_K5_collapseEdge_of_planar
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b) :
    Not (ContainsStrictSubdivision K5Graph
      (GraphContraction.collapseEdge G hab).graph) := by
  intro hK5
  rcases hK5 with ⟨M⟩
  rcases
      strictSubdivisionModel_K5_collapseEdge_collapsed_branch_of_planar
        h_planar hab M with
    ⟨c, hc⟩
  rcases
      containsStrictSubdivision_K5_or_K33_of_collapseEdge_collapsed_branch
        hab M hc with
    hK5_source | hK33_source
  · exact h_planar.no_K5_subdivision hK5_source
  · exact h_planar.no_K33_subdivision hK33_source
end FourColor

end Schematic.Math.GraphTheory
