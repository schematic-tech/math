import Schematic.Math.GraphTheory.Minors.Society.RuralGluing

/-!
Terminal-linkage normalization for the GM IX (2.4) source proof.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

omit [DecidableEq V] in
/-- Boundary-cleanliness of an off-path side leg in the ambient society.

This is useful bookkeeping for reroutings, but it is not the proof of the
first sentence of the side-tripod paragraph: the printed proof handles that
sentence directly by following the induced cut path and taking last contacts
with the original tripod. -/
theorem left_tripod_off_path_leg_ambient_target_clean
    [DecidableEq V]
    {S : GeneralSociety V}
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (i : Fin 3)
    (hi : T.boundary i ∉ P.pathSet) :
    T.boundary i ∈ S.boundarySet ∧
      (forall z : V,
        z ∈ (T.leg i).support ->
          z ∈ S.boundarySet -> z = T.boundary i) := by
  have hiArc : T.boundary i ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T i).mp hi
  refine ⟨P.leftBoundaryArc_subset hiArc, ?_⟩
  intro z hzLeg hzBoundary
  have hzSideOrPath : z ∈ P.leftSide ∪ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_leg_support_subset_side_or_path
      P hno_cross T i hzLeg
  have hzCut : z ∈ P.leftCutBoundarySet := by
    rcases hzSideOrPath with hzLeft | hzPath
    · exact Or.inl
        (P.boundary_mem_leftSide_of_no_cross hno_cross hzBoundary hzLeft)
    · exact Or.inr hzPath
  apply hsource_clean i z hzLeg
  rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
  exact hzCut

omit [DecidableEq V] in
/-- An endpoint-preserving GM IX `(2.2)` consequence available for later
rerouting arguments.  GM IX `(2.4)` does not need this detour for its
side-tripod paragraph; the live proof below follows the induced cut path
directly, as in the source. -/
theorem exists_left_tripod_ambient_linkage_preserving_off_path_foot
    [Fintype V] [DecidableEq V]
    (S : GeneralSociety V)
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S)
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hsource_clean : T.LegBoundaryContactClean)
    (i : Fin 3)
    (hi : T.boundary i ∉ P.pathSet) :
    let carrier : Set V :=
      {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
    Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
      T.attach i ∈ Set.range M.source ∧
        T.boundary i ∈ Set.range M.target := by
  rcases
      left_tripod_off_path_leg_ambient_target_clean
        (S := S) hno_cross P T hsource_clean i hi with
    ⟨hiBoundary, hiTargetClean⟩
  exact
    hthree.hasMappedTripodAttachmentLinkageToBoundary_preserving_foot
      T
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
      i hiBoundary hiTargetClean

/-- A clean set-linkage whose three sources occupy three distinct interiors of
a theta is already a tripod. -/
def ThreeSetLinkage.toTripodOfDistinctRimSources
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (M : ThreeSetLinkage S.graph
      {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
      S.boundarySet)
    (e : Fin 3 -> Fin 3)
    (he : Function.Injective e)
    (hsource : forall i : Fin 3,
      M.source i ∈ Walk.InternalVertices (T.rim (e i))) :
    S.Tripod := by
  let rim : Fin 3 -> S.graph.Walk T.left T.right :=
    fun i => (T.rim (e i)).mapLe hgraph
  let L : ThreeVertexLinkage S.graph M.source M.target := {
    targetEquiv := Equiv.refl (Fin 3)
    path := M.path
    isPath := M.isPath
    pairwise_vertex_disjoint := M.pairwise_vertex_disjoint
  }
  apply
    Tripod.ofThreeVertexLinkage
      T.left T.right T.left_ne_right rim
      (fun i => by
        simpa [rim] using
          (SimpleGraph.Walk.mapLe_isPath hgraph).mpr (T.rim_isPath (e i)))
      M.source
      (fun i => by
        simpa [rim, Walk.InternalVertices,
          SimpleGraph.Walk.support_mapLe_eq_support] using hsource i)
      M.target M.target_mem M.target_injective L
  · intro i j hij
    simpa [rim, Walk.InternalVertices,
      SimpleGraph.Walk.support_mapLe_eq_support] using
      T.rim_internals_disjoint (e i) (e j) (fun h => hij (he h))
  · intro i j z hzPath hzRim
    apply M.source_clean i z hzPath
    exact ⟨e j, by
      simpa [rim, SimpleGraph.Walk.support_mapLe_eq_support] using hzRim⟩

/-- Exact residual after the distinct-rim source branch of a clean linkage has
been excluded: one source is a common theta endpoint, or two distinct sources
lie internally on the same old rim. -/
theorem ThreeSetLinkage.endpoint_or_same_rim_sources_of_no_tripod
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (M : ThreeSetLinkage S.graph
      {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
      S.boundarySet)
    (hno_tripod : Not (Nonempty S.Tripod)) :
    (Exists fun i : Fin 3 =>
      M.source i = T.left ∨ M.source i = T.right) ∨
      Exists fun i : Fin 3 =>
        Exists fun j : Fin 3 =>
          Exists fun r : Fin 3 =>
            i ≠ j ∧
              M.source i ∈ Walk.InternalVertices (T.rim r) ∧
                M.source j ∈ Walk.InternalVertices (T.rim r) := by
  classical
  have hclassify : forall i : Fin 3,
      (M.source i = T.left ∨ M.source i = T.right) ∨
        Exists fun r : Fin 3 =>
          M.source i ∈ Walk.InternalVertices (T.rim r) := by
    intro i
    have hiCarrier :
        M.source i ∈
          {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support} := by
      exact M.source_mem i
    rcases hiCarrier with ⟨r, hir⟩
    rcases T.rim_support_internal_or_endpoint hir with hi | hi
    · exact Or.inr ⟨r, hi⟩
    · exact Or.inl hi
  by_cases hend : Exists fun i : Fin 3 =>
      M.source i = T.left ∨ M.source i = T.right
  · exact Or.inl hend
  · right
    have hinternal : forall i : Fin 3,
        Exists fun r : Fin 3 =>
          M.source i ∈ Walk.InternalVertices (T.rim r) := by
      intro i
      rcases hclassify i with hi | hi
      · exact False.elim (hend ⟨i, hi⟩)
      · exact hi
    choose rimIndex hrimIndex using hinternal
    by_cases hinjective : Function.Injective rimIndex
    · exact False.elim
        (hno_tripod
          ⟨Schematic.Math.GraphTheory.GeneralSociety.GMIX24SourceProof.ThreeSetLinkage.toTripodOfDistinctRimSources
            T hgraph M rimIndex hinjective hrimIndex⟩)
    · rcases Function.not_injective_iff.mp hinjective with
        ⟨i, j, hijRim, hij⟩
      exact
        ⟨i, j, rimIndex i, hij, hrimIndex i,
          by simpa [hijRim] using hrimIndex j⟩

/-- Exact third-source residual after preserving sources on two distinct rims.

If a clean carrier-to-boundary linkage retains one source in the `i`-rim and
one in the distinct `k`-rim, then ambient tripod-freeness leaves an
unselected source only at a common theta endpoint or internally on one of
those two outer rims.  An internal source on the remaining `j`-rim would put
the three linkage sources on three distinct rims and directly instantiate an
ambient tripod. -/
theorem ThreeSetLinkage.exists_unselected_endpoint_or_outer_rim_source_of_no_tripod
    {S H : GeneralSociety V}
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    (M : ThreeSetLinkage S.graph
      {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
      S.boundarySet)
    (hno_tripod : Not (Nonempty S.Tripod))
    {i k : Fin 3} (hik : i ≠ k)
    (hi_internal : T.boundary i ∈ Walk.InternalVertices (T.rim i))
    (hk_internal : T.boundary k ∈ Walk.InternalVertices (T.rim k))
    (hi_source : T.boundary i ∈ Set.range M.source)
    (hk_source : T.boundary k ∈ Set.range M.source) :
    Exists fun m : Fin 3 =>
      M.source m ≠ T.boundary i ∧
        M.source m ≠ T.boundary k ∧
          ((M.source m = T.left ∨ M.source m = T.right) ∨
            M.source m ∈ Walk.InternalVertices (T.rim i) ∨
              M.source m ∈ Walk.InternalVertices (T.rim k)) := by
  classical
  rcases hi_source with ⟨a, ha⟩
  rcases hk_source with ⟨b, hb⟩
  have hab : a ≠ b := by
    intro hab
    have hikBoundary : T.boundary i = T.boundary k := by
      rw [← ha, ← hb, hab]
    exact hik (T.boundary_injective hikBoundary)
  rcases
      Schematic.Math.GraphTheory.GeneralSociety.GMIX24SourceProof.ThreeSetLinkage.endpoint_or_same_rim_sources_of_no_tripod
        T hgraph M hno_tripod with
    hend | hsame
  · rcases hend with ⟨m, hm⟩
    refine ⟨m, ?_, ?_, Or.inl hm⟩
    · intro hmi
      rcases hm with hm | hm
      · exact T.left_ne_boundary i (hm.symm.trans hmi)
      · exact T.right_ne_boundary i (hm.symm.trans hmi)
    · intro hmk
      rcases hm with hm | hm
      · exact T.left_ne_boundary k (hm.symm.trans hmk)
      · exact T.right_ne_boundary k (hm.symm.trans hmk)
  · rcases hsame with ⟨r, s, q, hrs, hrq, hsq⟩
    have hpairs : r = a ∨ s = a ∨ r = b ∨ s = b := by
      fin_cases a <;> fin_cases b <;> fin_cases r <;> fin_cases s <;>
        simp_all
    rcases hpairs with hra | hsa | hrb | hsb
    · subst r
      have hqi : q = i := by
        by_contra hqi
        exact Set.disjoint_left.mp (T.rim_internals_disjoint q i hqi)
          hrq (by simpa [ha] using hi_internal)
      have hs_ne_a : s ≠ a := fun h => hrs h.symm
      have hs_ne_b : s ≠ b := by
        intro hsb
        subst s
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          (by simpa [hqi, hb] using hsq) hk_internal
      refine ⟨s, ?_, ?_, Or.inr (Or.inl ?_)⟩
      · intro h
        exact hs_ne_a (M.source_injective (by simpa [ha] using h))
      · intro h
        exact hs_ne_b (M.source_injective (by simpa [hb] using h))
      · simpa [hqi] using hsq
    · subst s
      have hqi : q = i := by
        by_contra hqi
        exact Set.disjoint_left.mp (T.rim_internals_disjoint q i hqi)
          hsq (by simpa [ha] using hi_internal)
      have hr_ne_a : r ≠ a := hrs
      have hr_ne_b : r ≠ b := by
        intro hrb
        subst r
        exact Set.disjoint_left.mp (T.rim_internals_disjoint i k hik)
          (by simpa [hqi, hb] using hrq) hk_internal
      refine ⟨r, ?_, ?_, Or.inr (Or.inl ?_)⟩
      · intro h
        exact hr_ne_a (M.source_injective (by simpa [ha] using h))
      · intro h
        exact hr_ne_b (M.source_injective (by simpa [hb] using h))
      · simpa [hqi] using hrq
    · subst r
      have hqk : q = k := by
        by_contra hqk
        exact Set.disjoint_left.mp (T.rim_internals_disjoint q k hqk)
          hrq (by simpa [hb] using hk_internal)
      have hs_ne_b : s ≠ b := fun h => hrs h.symm
      have hs_ne_a : s ≠ a := by
        intro hsa
        subst s
        exact Set.disjoint_left.mp (T.rim_internals_disjoint k i (fun h => hik h.symm))
          (by simpa [hqk, ha] using hsq) hi_internal
      refine ⟨s, ?_, ?_, Or.inr (Or.inr ?_)⟩
      · intro h
        exact hs_ne_a (M.source_injective (by simpa [ha] using h))
      · intro h
        exact hs_ne_b (M.source_injective (by simpa [hb] using h))
      · simpa [hqk] using hsq
    · subst s
      have hqk : q = k := by
        by_contra hqk
        exact Set.disjoint_left.mp (T.rim_internals_disjoint q k hqk)
          hsq (by simpa [hb] using hk_internal)
      have hr_ne_b : r ≠ b := hrs
      have hr_ne_a : r ≠ a := by
        intro hra
        subst r
        exact Set.disjoint_left.mp (T.rim_internals_disjoint k i (fun h => hik h.symm))
          (by simpa [hqk, ha] using hrq) hi_internal
      refine ⟨r, ?_, ?_, Or.inr (Or.inr ?_)⟩
      · intro h
        exact hr_ne_a (M.source_injective (by simpa [ha] using h))
      · intro h
        exact hr_ne_b (M.source_injective (by simpa [hb] using h))
      · simpa [hqk] using hrq

omit [DecidableEq V] in
/-- In an order-three set-linkage retaining two distinct sources and two
distinct targets, there is a source path outside the selected source pair and
a target path outside the selected target pair.  They are either the same
path, or they are two of the linkage's pairwise disjoint paths.

This is the finite matching split used in the terminal GM IX `(2.4)`
rerouting.  The augmenting-path theorem preserves endpoint sets, so the
unselected source and target need not remain paired. -/
theorem ThreeSetLinkage.exists_unselected_source_target_paired_or_disjoint
    {G : SimpleGraph V} {X Y : Set V}
    (M : ThreeSetLinkage G X Y)
    {x0 x1 y0 y1 : V}
    (hx01 : x0 ≠ x1)
    (hy01 : y0 ≠ y1)
    (hx0 : x0 ∈ Set.range M.source)
    (hx1 : x1 ∈ Set.range M.source)
    (hy0 : y0 ∈ Set.range M.target)
    (hy1 : y1 ∈ Set.range M.target) :
    Exists fun m : Fin 3 =>
      Exists fun n : Fin 3 =>
        M.source m ≠ x0 ∧ M.source m ≠ x1 ∧
          M.target n ≠ y0 ∧ M.target n ≠ y1 ∧
            (m = n ∨
              (m ≠ n ∧
                Disjoint {z : V | z ∈ (M.path m).support}
                  {z : V | z ∈ (M.path n).support})) := by
  rcases hx0 with ⟨a, ha⟩
  rcases hx1 with ⟨b, hb⟩
  rcases hy0 with ⟨c, hc⟩
  rcases hy1 with ⟨d, hd⟩
  have hab : a ≠ b := by
    intro hab
    exact hx01 (ha.symm.trans ((congrArg M.source hab).trans hb))
  have hcd : c ≠ d := by
    intro hcd
    exact hy01 (hc.symm.trans ((congrArg M.target hcd).trans hd))
  obtain ⟨m, hma, hmb⟩ :
      Exists fun m : Fin 3 => m ≠ a ∧ m ≠ b := by
    fin_cases a <;> fin_cases b <;> simp_all
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  obtain ⟨n, hnc, hnd⟩ :
      Exists fun n : Fin 3 => n ≠ c ∧ n ≠ d := by
    fin_cases c <;> fin_cases d <;> simp_all
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  have hmx0 : M.source m ≠ x0 := by
    intro hm
    exact hma (M.source_injective (hm.trans ha.symm))
  have hmx1 : M.source m ≠ x1 := by
    intro hm
    exact hmb (M.source_injective (hm.trans hb.symm))
  have hny0 : M.target n ≠ y0 := by
    intro hn
    exact hnc (M.target_injective (hn.trans hc.symm))
  have hny1 : M.target n ≠ y1 := by
    intro hn
    exact hnd (M.target_injective (hn.trans hd.symm))
  refine ⟨m, n, hmx0, hmx1, hny0, hny1, ?_⟩
  by_cases hmn : m = n
  · exact Or.inl hmn
  · exact Or.inr ⟨hmn, M.pairwise_vertex_disjoint m n hmn⟩

omit [DecidableEq V] in
/-- Choose the path carrying the unique target outside a retained target
pair, and compare it with any specified linkage path. -/
theorem ThreeSetLinkage.exists_unselected_target_paired_or_disjoint
    {G : SimpleGraph V} {X Y : Set V}
    (M : ThreeSetLinkage G X Y)
    {y0 y1 : V}
    (hy01 : y0 ≠ y1)
    (hy0 : y0 ∈ Set.range M.target)
    (hy1 : y1 ∈ Set.range M.target)
    (m : Fin 3) :
    Exists fun n : Fin 3 =>
      M.target n ≠ y0 ∧ M.target n ≠ y1 ∧
        (m = n ∨
          (m ≠ n ∧
            Disjoint {z : V | z ∈ (M.path m).support}
              {z : V | z ∈ (M.path n).support})) := by
  rcases hy0 with ⟨c, hc⟩
  rcases hy1 with ⟨d, hd⟩
  have hcd : c ≠ d := by
    intro hcd
    exact hy01 (hc.symm.trans ((congrArg M.target hcd).trans hd))
  obtain ⟨n, hnc, hnd⟩ :
      Exists fun n : Fin 3 => n ≠ c ∧ n ≠ d := by
    fin_cases c <;> fin_cases d <;> simp_all
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  have hny0 : M.target n ≠ y0 := by
    intro hn
    exact hnc (M.target_injective (hn.trans hc.symm))
  have hny1 : M.target n ≠ y1 := by
    intro hn
    exact hnd (M.target_injective (hn.trans hd.symm))
  refine ⟨n, hny0, hny1, ?_⟩
  by_cases hmn : m = n
  · exact Or.inl hmn
  · exact Or.inr ⟨hmn, M.pairwise_vertex_disjoint m n hmn⟩

/-- Source-correct normal form of the order-two outer-tail exchange.

The two cut-path tails retain the first and last ordered collapsed feet and
the boundary targets `P.s` and `P.t`.  Ambient tripod-freeness forces the
remaining source to be an old theta end or an interior point of one of the
two outer old rims.  The remaining target lies on one of the two open
boundary arcs.  Because GM IX `(2.2)` preserves endpoint sets rather than a
matching, the two remaining endpoints are either paired or carried by two
disjoint linkage paths. -/
theorem ThreeConnected.exists_outerTailLinkage_terminal_normal_form
    [Fintype V] [Fintype (Sym2 V)]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    let carrier : Set V :=
      {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
    Exists fun M : ThreeSetLinkage S.graph carrier S.boundarySet =>
      Exists fun m : Fin 3 =>
        M.source m ≠ T.boundary i ∧
          M.source m ≠ T.boundary k ∧
            ((M.source m = T.left ∨ M.source m = T.right) ∨
              M.source m ∈ Walk.InternalVertices (T.rim i) ∨
                M.source m ∈ Walk.InternalVertices (T.rim k)) ∧
              Exists fun n : Fin 3 =>
                (M.target n ∈ P.leftBoundaryArc ∨
                  M.target n ∈ P.rightBoundaryArc) ∧
                  (m = n ∨
                    (m ≠ n ∧
                      Disjoint {z : V | z ∈ (M.path m).support}
                        {z : V | z ∈ (M.path n).support})) := by
  classical
  let carrier : Set V :=
    {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
  rcases
      Schematic.Math.GraphTheory.GeneralSociety.GMIX24CutPath.ThreeConnected.exists_carrierLinkage_preserving_ordered_outer_tails
        hthree
        P T hgraph hij hik hjk hi hk hleg_i_nil hleg_k_nil
        hij_order hjk_order hpath_contacts with
    ⟨M, hi_source, hk_source, hs_target, ht_target⟩
  have hi_internal :
      T.boundary i ∈ Walk.InternalVertices (T.rim i) := by
    simpa [(T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using
      T.attach_mem_rim i
  have hk_internal :
      T.boundary k ∈ Walk.InternalVertices (T.rim k) := by
    simpa [(T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using
      T.attach_mem_rim k
  rcases
      Schematic.Math.GraphTheory.GeneralSociety.GMIX24SourceProof.ThreeSetLinkage.exists_unselected_endpoint_or_outer_rim_source_of_no_tripod
        T hgraph M hno_tripod hik hi_internal hk_internal
        hi_source hk_source with
    ⟨m, hmi, hmk, hm_source⟩
  rcases
      Schematic.Math.GraphTheory.GeneralSociety.GMIX24SourceProof.ThreeSetLinkage.exists_unselected_target_paired_or_disjoint
        M P.s_ne_t hs_target ht_target m with
    ⟨n, hns, hnt, hmn⟩
  have hn_arc :
      M.target n ∈ P.leftBoundaryArc ∨
        M.target n ∈ P.rightBoundaryArc := by
    rcases P.boundary_mem_endpoint_or_arc (M.target_mem n) with
      hns' | hnt' | hnleft | hnright
    · exact False.elim (hns hns')
    · exact False.elim (hnt hnt')
    · exact Or.inl hnleft
    · exact Or.inr hnright
  exact ⟨M, m, hmi, hmk, hm_source, n, hn_arc, hmn⟩


end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
