import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.PathIntervals.Disjointness

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

theorem pathTailToStart_clean_first_foot_of_path_contacts
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {z : V}
    (hz : z ∈ (P.pathTailToStart hi).support)
    (hzT : z ∈ T.vertexSet) :
    z = T.boundary i := by
  have hzPath : z ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet hi z hz
  rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
  rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
  · simpa [hmi] using hm
  · rcases hmjk with hmj | hmk
    · exact False.elim
        ((P.pathTailToStart_not_mem_of_supportIndex_lt hi hij_order)
          (by simpa [hmj, hm] using hz))
    · exact False.elim
        ((P.pathTailToStart_not_mem_of_supportIndex_lt hi
          (lt_trans hij_order hjk_order))
          (by simpa [hmk, hm] using hz))

theorem pathSegmentBetween_clean_two_feet_of_path_contacts
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {z : V}
    (hz :
      z ∈
        (P.pathSegmentBetween hi hj
          (Nat.le_of_lt hij_order)).support)
    (hzT : z ∈ T.vertexSet) :
    z = T.boundary i ∨ z = T.boundary j := by
  have hzPath : z ∈ P.pathSet :=
    P.pathSegmentBetween_support_subset_pathSet hi hj
      (Nat.le_of_lt hij_order) z hz
  rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
  rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
  · exact Or.inl (by simpa [hmi] using hm)
  · rcases hmjk with hmj | hmk
    · exact Or.inr (by simpa [hmj] using hm)
    · exact False.elim
        ((P.not_mem_segmentBetween_of_right_lt_supportIndex hi hj
          (Nat.le_of_lt hij_order) hjk_order)
          (by simpa [hmk, hm, GMIX24CutPath.pathSegmentBetween] using hz))

/-- Clean the full first-to-last cut-path segment in the ordered three-foot
configuration.

This is the path-contact normalization used in the remaining source
side-tripod case of GM IX `(2.4)`: when the two outer ordered side legs have
collapsed, the new cut-path rim is the segment from the first foot to the last
foot, and it may meet the old side tripod only at the three named feet. -/
theorem pathSegmentBetween_clean_three_feet_of_path_contacts
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {z : V}
    (hz :
      z ∈
        (P.pathSegmentBetween hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order))).support)
    (hzT : z ∈ T.vertexSet) :
    z = T.boundary i ∨ z = T.boundary j ∨ z = T.boundary k := by
  have hzPath : z ∈ P.pathSet :=
    P.pathSegmentBetween_support_subset_pathSet hi hk
      (Nat.le_of_lt (lt_trans hij_order hjk_order)) z hz
  rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
  rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
  · exact Or.inl (by simpa [hmi] using hm)
  · rcases hmjk with hmj | hmk
    · exact Or.inr (Or.inl (by simpa [hmj] using hm))
    · exact Or.inr (Or.inr (by simpa [hmk] using hm))

/-- The median ordered foot is an internal vertex of the full first-to-last
cut-path segment.

This is the formal local version of the source phrase that the three side feet
lie on the induced path in order.  It supplies the attachment point for the
full cut-path rim in the collapsed-outer-leg side-tripod construction. -/
theorem pathSegmentBetween_middle_boundary_mem_internal
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    T.boundary j ∈
      Walk.InternalVertices
        (P.pathSegmentBetween hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order))) :=
  P.pathSegmentBetween_middle_mem_internal hi hj hk hij_order hjk_order

/-- Clean a middle-to-last cut-path segment when the remaining foot lies before
the segment.

The earlier `pathSegmentBetween_clean_two_feet_of_path_contacts` excludes a
third foot after the segment.  The first-collapsed-branch residual in the GM
IX `(2.4)` source proof needs the dual local fact: the omitted foot is the
first ordered foot, hence before the `j`--`k` segment. -/
theorem pathSegmentBetween_clean_two_feet_of_path_contacts_left_third
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : T.boundary j ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {z : V}
    (hz :
      z ∈
        (P.pathSegmentBetween hj hk
          (Nat.le_of_lt hjk_order)).support)
    (hzT : z ∈ T.vertexSet) :
    z = T.boundary j ∨ z = T.boundary k := by
  have hzPath : z ∈ P.pathSet :=
    P.pathSegmentBetween_support_subset_pathSet hj hk
      (Nat.le_of_lt hjk_order) z hz
  rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
  rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
  · exact False.elim
      ((P.not_mem_segmentBetween_of_supportIndex_lt_left hj hk
        (Nat.le_of_lt hjk_order) hij_order)
        (by simpa [hmi, hm, GMIX24CutPath.pathSegmentBetween] using hz))
  · rcases hmjk with hmj | hmk
    · exact Or.inl (by simpa [hmj] using hm)
    · exact Or.inr (by simpa [hmk] using hm)

theorem pathTailToEnd_clean_last_foot_of_path_contacts
    [DecidableEq V]
    {S H : GeneralSociety V} (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {z : V}
    (hz : z ∈ (P.pathTailToEnd hk).support)
    (hzT : z ∈ T.vertexSet) :
    z = T.boundary k := by
  have hzPath : z ∈ P.pathSet :=
    P.pathTailToEnd_support_subset_pathSet hk z hz
  rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
  rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
  · exact False.elim
      ((P.pathTailToEnd_not_mem_of_supportIndex_lt hk
        (lt_trans hij_order hjk_order))
        (by simpa [hmi, hm] using hz))
  · rcases hmjk with hmj | hmk
    · exact False.elim
        ((P.pathTailToEnd_not_mem_of_supportIndex_lt hk hjk_order)
          (by simpa [hmj, hm] using hz))
    · simpa [hmk] using hm

/-- GM IX `(2.2)` completion retaining the two ordered outer cut-path tails.

When the first and last ordered side-tripod legs are nil, their feet are
already points of the old theta carrier.  The two disjoint tails of the
induced path from those feet to `s` and `t` are clean carrier-to-boundary
paths.  Completing this selected order-two linkage against the order-three
linkage supplied by society three-connectivity retains both sources and both
targets.  This is the ambient augmentation required in the collapsed source
case; it does not impose the obsolete fixed rim-deleted-subgraph linkage. -/
theorem ThreeConnected.exists_carrierLinkage_preserving_ordered_outer_tails
    [Fintype V] [DecidableEq V]
    {S H : GeneralSociety V}
    (hthree : S.ThreeConnected)
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
      T.boundary i ∈ Set.range M.source ∧
        T.boundary k ∈ Set.range M.source ∧
          P.s ∈ Set.range M.target ∧ P.t ∈ Set.range M.target := by
  classical
  let carrier : Set V :=
    {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
  let p0 : S.graph.Walk (T.boundary i) P.s := P.pathTailToStart hi
  let p1 : S.graph.Walk (T.boundary k) P.t := P.pathTailToEnd hk
  have hsource0 : T.boundary i ∈ carrier := by
    exact ⟨i, by
      simpa [(T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil] using
        Walk.internalVertices_subset_support (T.rim i) (T.attach_mem_rim i)⟩
  have hsource1 : T.boundary k ∈ carrier := by
    exact ⟨k, by
      simpa [(T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil] using
        Walk.internalVertices_subset_support (T.rim k) (T.attach_mem_rim k)⟩
  have hp0_source_clean :
      forall z : V, z ∈ p0.support -> z ∈ carrier -> z = T.boundary i := by
    intro z hz ⟨r, hzr⟩
    exact P.pathTailToStart_clean_first_foot_of_path_contacts
      T hij hik hjk hi hij_order hjk_order hpath_contacts hz
      (T.rim_mem_vertexSet (i := r) hzr)
  have hp1_source_clean :
      forall z : V, z ∈ p1.support -> z ∈ carrier -> z = T.boundary k := by
    intro z hz ⟨r, hzr⟩
    exact P.pathTailToEnd_clean_last_foot_of_path_contacts
      T hij hik hjk hk hij_order hjk_order hpath_contacts hz
      (T.rim_mem_vertexSet (i := r) hzr)
  have hp0_target_clean :
      forall z : V, z ∈ p0.support -> z ∈ S.boundarySet -> z = P.s := by
    intro z hz hzBoundary
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet hi z hz
    rcases P.boundary_mem_pathSet_eq_s_or_t hzBoundary hzPath with hzs | hzt
    · exact hzs
    · subst z
      have ht_le_i := P.pathTailToStart_supportIndex_le hi hz
      have hi_lt_k := lt_trans hij_order hjk_order
      have hk_le_t := Walk.IsPath.supportIndex_le_end P.path_isPath
        (by simpa [GMIX24CutPath.pathSet] using hk)
      omega
  have hp1_target_clean :
      forall z : V, z ∈ p1.support -> z ∈ S.boundarySet -> z = P.t := by
    intro z hz hzBoundary
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet hk z hz
    rcases P.boundary_mem_pathSet_eq_s_or_t hzBoundary hzPath with hzs | hzt
    · subst z
      have hk_le_s := P.pathTailToEnd_supportIndex_le hk hz
      have hs_le_i := Walk.supportIndex_start_le
        (p := P.path) (x := T.boundary i)
      have hi_lt_k := lt_trans hij_order hjk_order
      omega
    · exact hzt
  let Lselected : PartialSetLinkage S.graph carrier S.boundarySet 2 :=
    PartialSetLinkage.ofTwoPaths p0 p1
      (P.pathTailToStart_isPath hi) (P.pathTailToEnd_isPath hk)
      hsource0 hsource1 P.s_mem_boundary P.t_mem_boundary
      (by
        intro h
        exact hik (T.boundary_injective h))
      P.s_ne_t
      (P.pathTailToStart_support_disjoint_pathTailToEnd
        hi hk (lt_trans hij_order hjk_order))
      hp0_source_clean hp1_source_clean hp0_target_clean hp1_target_clean
  rcases hthree.hasMappedTripodAttachmentLinkageToBoundary T hgraph with
    ⟨right, hrightBoundary, ⟨Lfull⟩⟩
  let F : ThreeSetLinkage S.graph carrier S.boundarySet :=
    Lfull.toThreeSetLinkage carrier S.boundarySet
      (by
        intro r
        exact ⟨r, Walk.internalVertices_subset_support
          (T.rim r) (T.attach_mem_rim r)⟩)
      hrightBoundary
  rcases Lselected.exists_threeSetLinkage_extending (by omega) F with
    ⟨M, hsource, htarget⟩
  refine ⟨M, hsource ?_, hsource ?_, htarget ?_, htarget ?_⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem pathTailToStart_internal_boundary_empty
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    Walk.InternalVertices (P.pathTailToStart hx) ∩ S.boundarySet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hz_internal :
      z ∈ Walk.InternalVertices (P.pathTailToStart hx) := hz.1
  have hz_boundary : z ∈ S.boundarySet := hz.2
  have hz_path : z ∈ P.pathSet :=
    P.pathTailToStart_support_subset_pathSet hx z hz_internal.1
  rcases P.boundary_mem_pathSet_eq_s_or_t hz_boundary hz_path with hzs | hzt
  · have hs_internal :
        P.s ∈ Walk.InternalVertices (P.pathTailToStart hx) := by
      exact hzs ▸ hz_internal
    exact hs_internal.2.2 rfl
  · have ht_internal :
        P.t ∈ Walk.InternalVertices (P.pathTailToStart hx) := by
      exact hzt ▸ hz_internal
    by_cases hxt : x = P.t
    · subst x
      exact ht_internal.2.1 rfl
    · have hx_support : x ∈ P.path.support := by
        simpa [pathSet] using hx
      have ht_not_support :
          P.t ∉ (P.pathTailToStart hx).support := by
        intro ht_support
        have ht_take :
            P.t ∈ (P.path.takeUntil x hx_support).support := by
          have ht_rev :
              P.t ∈ (P.path.takeUntil x hx_support).support.reverse := by
            simpa [pathTailToStart, SimpleGraph.Walk.support_reverse] using
              ht_support
          exact List.mem_reverse.mp ht_rev
        exact
          (SimpleGraph.Walk.endpoint_notMem_support_takeUntil
            P.path_isPath hx_support (by exact fun h => hxt h.symm)) ht_take
      exact ht_not_support ht_internal.1

theorem pathTailToEnd_internal_boundary_empty
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    Walk.InternalVertices (P.pathTailToEnd hx) ∩ S.boundarySet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  have hz_internal :
      z ∈ Walk.InternalVertices (P.pathTailToEnd hx) := hz.1
  have hz_boundary : z ∈ S.boundarySet := hz.2
  have hz_path : z ∈ P.pathSet :=
    P.pathTailToEnd_support_subset_pathSet hx z hz_internal.1
  rcases P.boundary_mem_pathSet_eq_s_or_t hz_boundary hz_path with hzs | hzt
  · have hs_internal :
        P.s ∈ Walk.InternalVertices (P.pathTailToEnd hx) := by
      exact hzs ▸ hz_internal
    by_cases hxs : x = P.s
    · subst x
      exact hs_internal.2.1 rfl
    · have hx_support : x ∈ P.path.support := by
        simpa [pathSet] using hx
      have hs_not_support :
          P.s ∉ (P.pathTailToEnd hx).support := by
        simpa [pathTailToEnd] using
          (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
            P.path_isPath hx_support hxs)
      exact hs_not_support hs_internal.1
  · have ht_internal :
        P.t ∈ Walk.InternalVertices (P.pathTailToEnd hx) := by
      exact hzt ▸ hz_internal
    exact ht_internal.2.2 rfl

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
