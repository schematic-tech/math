import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.BoundaryTailLifts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Left-side ordered all-path-foot constructor when the clean tail starts at
an internal contact on the median leg rather than at the old median foot.

This is the side-tripod branch used in the literal GM IX `(2.4)` proof after
the three old feet have been ordered along the cut path.  The two outer feet
are routed along the cut path to `s` and `t`; the supplied clean outside tail
from `x` supplies the new middle foot `a`. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_leg_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg j).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order i j k
  have he : Function.Injective e :=
    fin3Order_injective hij hik hjk
  let Tre := T.reindex e he
  have h0P : Tre.boundary 0 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 0
  have h2P : Tre.boundary 2 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 2
  have hxTre : x ∈ (Tre.leg 1).support := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx
  have hnot_j_zero :
      T.boundary j ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0) hij_order
  have hnot_k_zero :
      T.boundary k ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0)
        (lt_trans hij_order hjk_order)
  have hnot_i_two :
      T.boundary i ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2)
        (lt_trans hij_order hjk_order)
  have hnot_j_two :
      T.boundary j ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2) hjk_order
  refine ⟨Tre.liftAppendOuterTailsReplaceMiddleLegWithTail
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToStart h0P)
    hxTre
    q
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToEnd h2P)
    ?_ hq_path ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToStart_isPath h0P
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToEnd_isPath h2P
  · intro z hz hzTre
    have hz0 : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz0))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro z hz hzTre
    exact hq_clean z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    have hz2 : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz2))
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm
  · rw [Set.disjoint_left]
    intro z hz0 hzq
    have hz0' : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz0
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using
        P.pathTailToStart_support_disjoint_pathTailToEnd h0P h2P
          (by simpa [Tre, Tripod.reindex, e, fin3Order] using
            lt_trans hij_order hjk_order)
  · rw [Set.disjoint_left]
    intro z hzq hz2
    have hz2' : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz2
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)

/-- Left-side ordered all-path-foot constructor when the clean tail starts at
an internal contact on the median rim. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_rim_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ Walk.InternalVertices (T.rim j))
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order i j k
  have he : Function.Injective e :=
    fin3Order_injective hij hik hjk
  let Tre := T.reindex e he
  have h0P : Tre.boundary 0 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 0
  have h2P : Tre.boundary 2 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 2
  have hxTre : x ∈ Walk.InternalVertices (Tre.rim 1) := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx
  have hnot_j_zero :
      T.boundary j ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0) hij_order
  have hnot_k_zero :
      T.boundary k ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0)
        (lt_trans hij_order hjk_order)
  have hnot_i_two :
      T.boundary i ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2)
        (lt_trans hij_order hjk_order)
  have hnot_j_two :
      T.boundary j ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2) hjk_order
  refine ⟨Tre.liftAppendOuterTailsReplaceMiddleRimWithTail
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToStart h0P)
    hxTre
    q
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToEnd h2P)
    ?_ hq_path ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToStart_isPath h0P
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToEnd_isPath h2P
  · intro z hz hzTre
    have hz0 : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz0))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro z hz hzTre
    exact hq_clean z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    have hz2 : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz2))
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm
  · rw [Set.disjoint_left]
    intro z hz0 hzq
    have hz0' : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz0
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using
        P.pathTailToStart_support_disjoint_pathTailToEnd h0P h2P
          (by simpa [Tre, Tripod.reindex, e, fin3Order] using
            lt_trans hij_order hjk_order)
  · rw [Set.disjoint_left]
    intro z hzq hz2
    have hz2' : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz2
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)

/-- Left-side ordered all-path-foot constructor when the clean tail starts on
the first branch rather than on the median branch.

The median foot is routed back to `s`; this tail may pass through the old
first foot, which has become the deleted middle boundary of the reindexed
tripod.  The relaxed low-level constructor and the boundary/rim exclusion
lemma discharge exactly that bookkeeping. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_first_leg_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg i).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order j i k
  have he : Function.Injective e :=
    fin3Order_injective hij.symm hjk hik
  let Tre := T.reindex e he
  have h0P : Tre.boundary 0 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 1
  have h2P : Tre.boundary 2 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 2
  have hxTre : x ∈ (Tre.leg 1).support := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx
  have hx_ne_i : x ≠ T.boundary i := by
    intro hxi
    exact (hq_outside x q.start_mem_support).2 (by
      simpa [hxi, fin3Order] using hold 0)
  have hx_neTre : x ≠ Tre.boundary 1 := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx_ne_i
  have hmiddle_not_rim :
      forall r : Fin 3, Tre.boundary 1 ∉ (Tre.rim r).support := by
    intro r
    exact Tre.boundary_not_mem_rim_of_leg_hit_ne_boundary hxTre hx_neTre
  have hnot_k_zero :
      T.boundary k ∉ (P.pathTailToStart (hold 1)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 1) hjk_order
  have hnot_i_two :
      T.boundary i ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2)
        (lt_trans hij_order hjk_order)
  have hnot_j_two :
      T.boundary j ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2) hjk_order
  refine ⟨Tre.liftAppendOuterTailsReplaceMiddleLegWithTailAllowMiddleBoundary
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToStart h0P)
    hxTre hx_neTre
    q
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToEnd h2P)
    ?_ hq_path ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToStart_isPath h0P
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToEnd_isPath h2P
  · intro z hz hzTre
    have hz0 : z ∈ (P.pathTailToStart (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 1) z hz0
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact Or.inr (by
        simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm)
    · rcases hmjk with hmj | hmk
      · exact Or.inl (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm)
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro z hz hzTre
    exact hq_clean z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    have hz2 : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz2))
      · exact Or.inl (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm)
  · intro r z hz hzr
    have hz0 : z ∈ (P.pathTailToStart (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 1) z hz0
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · have hzi_rim : T.boundary i ∈ (Tre.rim r).support := by
        simpa [hmi, hm] using hzr
      exact False.elim
        ((hmiddle_not_rim r) (by
          simpa [Tre, Tripod.reindex, e, fin3Order] using hzi_rim))
    · rcases hmjk with hmj | hmk
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro r z hz hzr
    have hz2 : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz2))
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm
  · rw [Set.disjoint_left]
    intro z hz0 hzq
    have hz0' : z ∈ (P.pathTailToStart (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz0
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 1) z hz0'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using
        P.pathTailToStart_support_disjoint_pathTailToEnd h0P h2P
          (by simpa [Tre, Tripod.reindex, e, fin3Order] using hjk_order)
  · rw [Set.disjoint_left]
    intro z hzq hz2
    have hz2' : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz2
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)

/-- Left-side ordered all-path-foot constructor when the clean tail starts on
the first rim rather than on the median branch, in the nondegenerate case
where the deleted old first foot is not itself on a rim.

The source proof uses this as one of the `r = 1` side-tripod alternatives:
the median foot is routed back to `s`, the last foot to `t`, and the clean
tail from the first rim contact supplies the new middle leg. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_first_rim_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ Walk.InternalVertices (T.rim i))
    (hboundary_not_rim :
      forall r : Fin 3, T.boundary i ∉ (T.rim r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order j i k
  have he : Function.Injective e :=
    fin3Order_injective hij.symm hjk hik
  let Tre := T.reindex e he
  have h0P : Tre.boundary 0 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 1
  have h2P : Tre.boundary 2 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 2
  have hxTre : x ∈ Walk.InternalVertices (Tre.rim 1) := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx
  have hmiddle_not_rim :
      forall r : Fin 3, Tre.boundary 1 ∉ (Tre.rim r).support := by
    intro r hr
    exact hboundary_not_rim (fin3Order j i k r)
      (by simpa [Tre, Tripod.reindex, e, fin3Order] using hr)
  have hnot_k_zero :
      T.boundary k ∉ (P.pathTailToStart (hold 1)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 1) hjk_order
  have hnot_i_two :
      T.boundary i ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2)
        (lt_trans hij_order hjk_order)
  have hnot_j_two :
      T.boundary j ∉ (P.pathTailToEnd (hold 2)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 2) hjk_order
  refine ⟨Tre.liftAppendOuterTailsReplaceMiddleRimWithTailAllowMiddleBoundary
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToStart h0P)
    hxTre
    q
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToEnd h2P)
    ?_ hq_path ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToStart_isPath h0P
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToEnd_isPath h2P
  · intro z hz hzTre
    have hz0 : z ∈ (P.pathTailToStart (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 1) z hz0
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact Or.inr (by
        simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm)
    · rcases hmjk with hmj | hmk
      · exact Or.inl (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm)
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro z hz hzTre
    exact hq_clean z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    have hz2 : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz2))
      · exact Or.inl (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm)
  · intro r z hz hzr
    have hz0 : z ∈ (P.pathTailToStart (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 1) z hz0
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · have hzi_rim : T.boundary i ∈ (Tre.rim r).support := by
        simpa [hmi, hm] using hzr
      exact False.elim
        ((hmiddle_not_rim r) (by
          simpa [Tre, Tripod.reindex, e, fin3Order] using hzi_rim))
    · rcases hmjk with hmj | hmk
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro r z hz hzr
    have hz2 : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz2))
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm
  · rw [Set.disjoint_left]
    intro z hz0 hzq
    have hz0' : z ∈ (P.pathTailToStart (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz0
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 1) z hz0'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using
        P.pathTailToStart_support_disjoint_pathTailToEnd h0P h2P
          (by simpa [Tre, Tripod.reindex, e, fin3Order] using hjk_order)
  · rw [Set.disjoint_left]
    intro z hzq hz2
    have hz2' : z ∈ (P.pathTailToEnd (hold 2)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz2
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 2) z hz2'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)

/-- Left-side ordered all-path-foot constructor when the clean tail starts on
the last branch rather than on the median branch.

This is the mirror of
`..._replace_first_leg_of_ordered_indices_path_contacts`: the first foot is
routed to `s`, while the median foot is routed to `t` and may pass through
the old last foot after that last branch has become the reindexed middle leg. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_last_leg_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ (T.leg k).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order i k j
  have he : Function.Injective e :=
    fin3Order_injective hik hij hjk.symm
  let Tre := T.reindex e he
  have h0P : Tre.boundary 0 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 0
  have h2P : Tre.boundary 2 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 1
  have hxTre : x ∈ (Tre.leg 1).support := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx
  have hx_ne_k : x ≠ T.boundary k := by
    intro hxk
    exact (hq_outside x q.start_mem_support).2 (by
      simpa [hxk, fin3Order] using hold 2)
  have hx_neTre : x ≠ Tre.boundary 1 := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx_ne_k
  have hmiddle_not_rim :
      forall r : Fin 3, Tre.boundary 1 ∉ (Tre.rim r).support := by
    intro r
    exact Tre.boundary_not_mem_rim_of_leg_hit_ne_boundary hxTre hx_neTre
  have hnot_j_zero :
      T.boundary j ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0) hij_order
  have hnot_k_zero :
      T.boundary k ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0)
        (lt_trans hij_order hjk_order)
  have hnot_i_two :
      T.boundary i ∉ (P.pathTailToEnd (hold 1)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 1) hij_order
  refine ⟨Tre.liftAppendOuterTailsReplaceMiddleLegWithTailAllowMiddleBoundary
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToStart h0P)
    hxTre hx_neTre
    q
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToEnd h2P)
    ?_ hq_path ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToStart_isPath h0P
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToEnd_isPath h2P
  · intro z hz hzTre
    have hz0 : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact Or.inl (by
        simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm)
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz0))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro z hz hzTre
    exact hq_clean z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    have hz2 : z ∈ (P.pathTailToEnd (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 1) z hz2
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact Or.inl (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm)
      · exact Or.inr (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm)
  · intro r z hz hzr
    have hz0 : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz0))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro r z hz hzr
    have hz2 : z ∈ (P.pathTailToEnd (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 1) z hz2
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm
      · have hzk_rim : T.boundary k ∈ (Tre.rim r).support := by
          simpa [hmk, hm] using hzr
        exact False.elim
          ((hmiddle_not_rim r) (by
            simpa [Tre, Tripod.reindex, e, fin3Order] using hzk_rim))
  · rw [Set.disjoint_left]
    intro z hz0 hzq
    have hz0' : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz0
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using
        P.pathTailToStart_support_disjoint_pathTailToEnd h0P h2P
          (by simpa [Tre, Tripod.reindex, e, fin3Order] using hij_order)
  · rw [Set.disjoint_left]
    intro z hzq hz2
    have hz2' : z ∈ (P.pathTailToEnd (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz2
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 1) z hz2'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)

/-- Left-side ordered all-path-foot constructor when the clean tail starts on
the last rim rather than on the median branch, in the nondegenerate case
where the deleted old last foot is not itself on a rim.

This is the mirror of the first-rim constructor: the first foot is routed to
`s`, the median foot to `t`, and the clean outside tail starts from the old
last rim. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_last_rim_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx : x ∈ Walk.InternalVertices (T.rim k))
    (hboundary_not_rim :
      forall r : Fin 3, T.boundary k ∉ (T.rim r).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order i k j
  have he : Function.Injective e :=
    fin3Order_injective hik hij hjk.symm
  let Tre := T.reindex e he
  have h0P : Tre.boundary 0 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 0
  have h2P : Tre.boundary 2 ∈ P.pathSet := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold 1
  have hxTre : x ∈ Walk.InternalVertices (Tre.rim 1) := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using hx
  have hmiddle_not_rim :
      forall r : Fin 3, Tre.boundary 1 ∉ (Tre.rim r).support := by
    intro r hr
    exact hboundary_not_rim (fin3Order i k j r)
      (by simpa [Tre, Tripod.reindex, e, fin3Order] using hr)
  have hnot_j_zero :
      T.boundary j ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0) hij_order
  have hnot_k_zero :
      T.boundary k ∉ (P.pathTailToStart (hold 0)).support := by
    simpa [fin3Order] using
      P.pathTailToStart_not_mem_of_supportIndex_lt (hold 0)
        (lt_trans hij_order hjk_order)
  have hnot_i_two :
      T.boundary i ∉ (P.pathTailToEnd (hold 1)).support := by
    simpa [fin3Order] using
      P.pathTailToEnd_not_mem_of_supportIndex_lt (hold 1) hij_order
  refine ⟨Tre.liftAppendOuterTailsReplaceMiddleRimWithTailAllowMiddleBoundary
    (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety_graph_le
    (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToStart h0P)
    hxTre
    q
    (by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using P.pathTailToEnd h2P)
    ?_ hq_path ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToStart_isPath h0P
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using P.pathTailToEnd_isPath h2P
  · intro z hz hzTre
    have hz0 : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact Or.inl (by
        simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm)
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz0))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro z hz hzTre
    exact hq_clean z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    have hz2 : z ∈ (P.pathTailToEnd (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 1) z hz2
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · exact Or.inl (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm)
      · exact Or.inr (by
          simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm)
  · intro r z hz hzr
    have hz0 : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz0))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz0))
  · intro r z hz hzr
    have hz2 : z ∈ (P.pathTailToEnd (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 1) z hz2
    have hzTre : z ∈ Tre.vertexSet :=
      Or.inl ⟨r, hzr⟩
    have hzT : z ∈ T.vertexSet :=
      T.reindex_vertexSet_subset e he hzTre
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz2))
    · rcases hmjk with hmj | hmk
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmj] using hm
      · have hzk_rim : T.boundary k ∈ (Tre.rim r).support := by
          simpa [hmk, hm] using hzr
        exact False.elim
          ((hmiddle_not_rim r) (by
            simpa [Tre, Tripod.reindex, e, fin3Order] using hzk_rim))
  · rw [Set.disjoint_left]
    intro z hz0 hzq
    have hz0' : z ∈ (P.pathTailToStart (hold 0)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz0
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToStart_support_subset_pathSet (hold 0) z hz0'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)
  · simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
      using
        P.pathTailToStart_support_disjoint_pathTailToEnd h0P h2P
          (by simpa [Tre, Tripod.reindex, e, fin3Order] using hij_order)
  · rw [Set.disjoint_left]
    intro z hzq hz2
    have hz2' : z ∈ (P.pathTailToEnd (hold 1)).support := by
      simpa [Tre, Tripod.reindex, e, fin3Order, GMIX24CutPath.boundaryTriple]
        using hz2
    have hzPath : z ∈ P.pathSet :=
      P.pathTailToEnd_support_subset_pathSet (hold 1) z hz2'
    exact (hq_outside z hzq).2 (by
      simpa [GMIX24CutPath.pathSet] using hzPath)

/-- Ordered side-tripod constructor covering all leg contacts and the median
rim contact.

The source proof's median-branch conclusion is later used to remove the
first/last alternatives under ambient tripod-freeness.  This theorem exposes
the three constructors in one place: first leg, median leg/rim, or last leg
all produce an ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_ordered_leg_or_median_branch_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      x ∈ (T.leg i).support ∨
        (x ∈ (T.leg j).support ∨
          x ∈ Walk.InternalVertices (T.rim j)) ∨
        x ∈ (T.leg k).support)
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  rcases hx with hfirst | hrest
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_first_leg_of_ordered_indices_path_contacts
        P hno_cross T hij hik hjk q hfirst ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean
  rcases hrest with hmiddle | hlast
  · rcases hmiddle with hmidleg | hmidrim
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_leg_of_ordered_indices_path_contacts
          P hno_cross T hij hik hjk q hmidleg ha hold hq_path
          hij_order hjk_order hq_outside hpath_contacts hq_clean
    · exact
        GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_rim_of_ordered_indices_path_contacts
          P hno_cross T hij hik hjk q hmidrim ha hold hq_path
          hij_order hjk_order hq_outside hpath_contacts hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_last_leg_of_ordered_indices_path_contacts
        P hno_cross T hij hik hjk q hlast ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean

/-- Median-branch side-tripod constructor for the all-path-foot case.

This combines the leg-contact and rim-contact constructors: if the clean
outside tail starts on the branch whose old foot is median along the cut path,
then routing the two outer old feet to `s` and `t` and using the tail to the
arc vertex `a` gives an ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {x a : V} (q : S.graph.Walk x a)
    (hx :
      x ∈ (T.leg j).support ∨ x ∈ Walk.InternalVertices (T.rim j))
    (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (hq_path : q.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  rcases hx with hxleg | hxrim
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_leg_of_ordered_indices_path_contacts
        P hno_cross T hij hik hjk q hxleg ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean
  · exact
      GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_rim_of_ordered_indices_path_contacts
        P hno_cross T hij hik hjk q hxrim ha hold hq_path
        hij_order hjk_order hq_outside hpath_contacts hq_clean

/-- Left-side all-path-foot constructor from the source-shaped median-branch
contact condition.

The wrapper sorts the three old feet along the cut path.  The caller supplies
the remaining mathematical assertion from the GM IX side-tripod paragraph:
after that sorting, the clean outside tail starts on the median branch. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_all_path_feet_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmedian :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j))
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  obtain ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩ :=
    P.exists_ordered_tripod_boundary_indices T holdAll
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk q
      (hmedian hij hik hjk hij_order hjk_order) ha
      (fun r : Fin 3 => holdAll (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts hq_clean

/-- Right-side all-path-foot median-branch constructor.

This is obtained by reversing the cut path and applying the completed
left-side constructor.  The median condition is intentionally stated in the
`P.reverse` order: that is the literal source order for the right canonical
society after the two sides are swapped. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_all_path_feet_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.rightBoundaryArc)
    (hq_path : q.IsPath)
    (hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmedian :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.reverse.path (T.boundary i) <
            Walk.supportIndex P.reverse.path (T.boundary j) ->
          Walk.supportIndex P.reverse.path (T.boundary j) <
            Walk.supportIndex P.reverse.path (T.boundary k) ->
          x ∈ (T.leg j).support ∨
            x ∈ Walk.InternalVertices (T.rim j))
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ T.vertexSet -> z = x) :
    Nonempty S.Tripod := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_middle_branch_of_all_path_feet_path_contacts
      P.reverse hno_cross Trev
      (by
        intro i
        simpa [Trev] using holdAll i)
      q
      (by simpa [Trev] using ha)
      hq_path
      (by
        intro w hw
        simpa using hq_outside w hw)
      (by
        intro z hzPath hzT
        have hzPathP : z ∈ P.pathSet := by
          simpa using hzPath
        have hzTorig : z ∈ T.vertexSet := by
          simpa [Trev] using hzT
        simpa [Trev] using hpath_contacts z hzPathP hzTorig)
      (by
        intro i j k hij hik hjk hij_order hjk_order
        exact
          (by
            simpa [Trev] using
              hmedian hij hik hjk
                (by simpa [Trev] using hij_order)
                (by simpa [Trev] using hjk_order)))
      (by
        intro z hz hzT
        exact hq_clean z hz (by simpa [Trev] using hzT))


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
