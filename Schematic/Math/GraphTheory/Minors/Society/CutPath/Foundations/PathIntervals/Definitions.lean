import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.CutPathData

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

def pathSet {S : GeneralSociety V} (P : GMIX24CutPath S) : Set V :=
  {v : V | v ∈ P.path.support}

def outside {S : GeneralSociety V} (P : GMIX24CutPath S) : Set V :=
  {v : V | v ∈ S.activeSet ∧ v ∉ P.path.support}

theorem pathSet_finite {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.pathSet.Finite := by
  classical
  simp [pathSet]

theorem s_mem_pathSet {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.s ∈ P.pathSet := by
  exact P.path.start_mem_support

theorem t_mem_pathSet {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.t ∈ P.pathSet := by
  exact P.path.end_mem_support

theorem s_not_mem_outside {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.s ∉ P.outside := by
  intro hs
  exact hs.2 P.path.start_mem_support

theorem t_not_mem_outside {S : GeneralSociety V} (P : GMIX24CutPath S) :
    P.t ∉ P.outside := by
  intro ht
  exact ht.2 P.path.end_mem_support

theorem boundary_mem_pathSet_eq_s_or_t {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hvBoundary : v ∈ S.boundarySet)
    (hvPath : v ∈ P.pathSet) :
    v = P.s ∨ v = P.t := by
  classical
  by_cases hvs : v = P.s
  · exact Or.inl hvs
  · by_cases hvt : v = P.t
    · exact Or.inr hvt
    · have hvInternal : v ∈ Walk.InternalVertices P.path :=
        ⟨by simpa [pathSet] using hvPath, hvs, hvt⟩
      have hvBad : v ∈ Walk.InternalVertices P.path ∩ S.boundarySet :=
        ⟨hvInternal, hvBoundary⟩
      have hvNot : v ∉ Walk.InternalVertices P.path ∩ S.boundarySet := by
        rw [P.internal_disjoint_boundary]
        simp
      exact False.elim (hvNot hvBad)

theorem pathSet_inter_boundary_subset_endpoints {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.pathSet ∩ S.boundarySet ⊆ ({P.s, P.t} : Set V) := by
  intro v hv
  rcases P.boundary_mem_pathSet_eq_s_or_t hv.2 hv.1 with hvs | hvt
  · exact Or.inl hvs
  · exact Or.inr hvt

theorem pathSet_boundary_iff_eq_s_or_t {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V} :
    v ∈ P.pathSet ∧ v ∈ S.boundarySet ↔ v = P.s ∨ v = P.t := by
  constructor
  · intro hv
    exact P.boundary_mem_pathSet_eq_s_or_t hv.2 hv.1
  · intro hv
    rcases hv with hvs | hvt
    · subst v
      exact ⟨P.s_mem_pathSet, P.s_mem_boundary⟩
    · subst v
      exact ⟨P.t_mem_pathSet, P.t_mem_boundary⟩

theorem walk_internal_boundary_subset_endpoints_of_support_subset_pathSet
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V} {q : S.graph.Walk u v}
    (hsupport : forall z : V, z ∈ q.support -> z ∈ P.pathSet) :
    Walk.InternalVertices q ∩ S.boundarySet ⊆ ({P.s, P.t} : Set V) := by
  intro z hz
  exact P.boundary_mem_pathSet_eq_s_or_t hz.2 (hsupport z hz.1.1)

theorem walk_internal_boundary_empty_of_support_subset_pathSet_avoids_endpoints
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {u v : V} {q : S.graph.Walk u v}
    (hsupport : forall z : V, z ∈ q.support -> z ∈ P.pathSet)
    (hs_endpoint : P.s = u ∨ P.s = v)
    (ht_endpoint : P.t = u ∨ P.t = v) :
    Walk.InternalVertices q ∩ S.boundarySet = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rcases
      P.walk_internal_boundary_subset_endpoints_of_support_subset_pathSet
        hsupport hz with hzs | hzt
  · have hs_internal : P.s ∈ Walk.InternalVertices q := by
      exact hzs ▸ hz.1
    rcases hs_endpoint with hs_eq_u | hs_eq_v
    · exact hs_internal.2.1 hs_eq_u
    · exact hs_internal.2.2 hs_eq_v
  · have hzt_eq : z = P.t := by simpa using hzt
    have ht_internal : P.t ∈ Walk.InternalVertices q := by
      exact hzt_eq ▸ hz.1
    rcases ht_endpoint with ht_eq_u | ht_eq_v
    · exact ht_internal.2.1 ht_eq_u
    · exact ht_internal.2.2 ht_eq_v

def pathTailToStart [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    S.graph.Walk x P.s :=
  (P.path.takeUntil x (by simpa [pathSet] using hx)).reverse

def pathTailToEnd [DecidableEq V] {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    S.graph.Walk x P.t :=
  P.path.dropUntil x (by simpa [pathSet] using hx)

def pathSegmentBetween [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y) :
    S.graph.Walk x y :=
  Walk.segmentBetween P.path
    (by simpa [pathSet] using hx)
    (by simpa [pathSet] using hy)
    hxy

theorem pathTailToStart_isPath [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    (P.pathTailToStart hx).IsPath := by
  simpa [pathTailToStart] using
    (P.path_isPath.takeUntil (by simpa [pathSet] using hx)).reverse

theorem pathTailToEnd_isPath [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    (P.pathTailToEnd hx).IsPath := by
  simpa [pathTailToEnd] using
    P.path_isPath.dropUntil (by simpa [pathSet] using hx)

theorem pathSegmentBetween_isPath [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y) :
    (P.pathSegmentBetween hx hy hxy).IsPath := by
  simpa [pathSegmentBetween] using
    Walk.segmentBetween_isPath P.path_isPath
      (by simpa [pathSet] using hx)
      (by simpa [pathSet] using hy)
      hxy

theorem pathTailToStart_support_subset_pathSet
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    forall z : V, z ∈ (P.pathTailToStart hx).support -> z ∈ P.pathSet := by
  intro z hz
  have hz_take :
      z ∈ (P.path.takeUntil x (by simpa [pathSet] using hx)).support := by
    have hzrev :
        z ∈ (P.path.takeUntil x (by simpa [pathSet] using hx)).support.reverse := by
      simpa [pathTailToStart, SimpleGraph.Walk.support_reverse] using hz
    exact List.mem_reverse.mp hzrev
  exact by
    simpa [pathSet] using
      SimpleGraph.Walk.support_takeUntil_subset P.path
        (by simpa [pathSet] using hx) hz_take

theorem pathTailToEnd_support_subset_pathSet
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x : V} (hx : x ∈ P.pathSet) :
    forall z : V, z ∈ (P.pathTailToEnd hx).support -> z ∈ P.pathSet := by
  intro z hz
  exact by
    simpa [pathSet, pathTailToEnd] using
      SimpleGraph.Walk.support_dropUntil_subset P.path
        (by simpa [pathSet] using hx) hz

theorem pathSegmentBetween_support_subset_pathSet
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y) :
    forall z : V, z ∈ (P.pathSegmentBetween hx hy hxy).support ->
      z ∈ P.pathSet := by
  intro z hz
  exact by
    simpa [pathSet, pathSegmentBetween] using
      Walk.segmentBetween_support_subset
        (p := P.path)
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy)
        hxy hz

/-- If the start of the cut path lies on an ordered subsegment, then it is the
left endpoint of that subsegment. -/
theorem pathSegmentBetween_start_mem_eq_left
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (hs :
      P.s ∈ (P.pathSegmentBetween hx hy hxy).support) :
    x = P.s := by
  have hs_support : P.s ∈ P.path.support := P.path.start_mem_support
  have hx_support : x ∈ P.path.support := by
    simpa [pathSet] using hx
  have hx_le_s :
      Walk.supportIndex P.path x <= Walk.supportIndex P.path P.s := by
    simpa [pathSegmentBetween] using
      Walk.segmentBetween_supportIndex_left_le P.path_isPath
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy)
        hxy hs
  have hs_le_x :
      Walk.supportIndex P.path P.s <= Walk.supportIndex P.path x :=
    Walk.supportIndex_start_le (p := P.path)
  exact
    Walk.supportIndex_injective_of_mem hx_support
      (le_antisymm hx_le_s hs_le_x)

/-- If the end of the cut path lies on an ordered subsegment, then it is the
right endpoint of that subsegment. -/
theorem pathSegmentBetween_end_mem_eq_right
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y : V} (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet)
    (hxy : Walk.supportIndex P.path x <= Walk.supportIndex P.path y)
    (ht :
      P.t ∈ (P.pathSegmentBetween hx hy hxy).support) :
    y = P.t := by
  have ht_support : P.t ∈ P.path.support := P.path.end_mem_support
  have hy_support : y ∈ P.path.support := by
    simpa [pathSet] using hy
  have ht_le_y :
      Walk.supportIndex P.path P.t <= Walk.supportIndex P.path y := by
    simpa [pathSegmentBetween] using
      Walk.segmentBetween_supportIndex_right_le
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy)
        hxy ht
  have hy_le_t :
      Walk.supportIndex P.path y <= Walk.supportIndex P.path P.t :=
    Walk.IsPath.supportIndex_le_end P.path_isPath hy_support
  exact
    Walk.supportIndex_injective_of_mem hy_support
      (le_antisymm hy_le_t ht_le_y)

/-- If `y` lies strictly between `x` and `z` on the cut path, then it is an
internal vertex of the cut-path segment from `x` to `z`.

This is the local path-order fact needed in the source GM IX `(2.4)`
side-tripod paragraph when the two outer ordered feet have collapsed and the
middle foot supplies the attachment on the new cut-path rim. -/
theorem pathSegmentBetween_middle_mem_internal
    [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {x y z : V}
    (hx : x ∈ P.pathSet) (hy : y ∈ P.pathSet) (hz : z ∈ P.pathSet)
    (hxy :
      Walk.supportIndex P.path x < Walk.supportIndex P.path y)
    (hyz :
      Walk.supportIndex P.path y < Walk.supportIndex P.path z) :
    y ∈
      Walk.InternalVertices
        (P.pathSegmentBetween hx hz (le_of_lt (lt_trans hxy hyz))) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [pathSegmentBetween, pathSet] using
      Walk.mem_support_segmentBetween_of_supportIndex_between
        (p := P.path)
        (by simpa [pathSet] using hx)
        (by simpa [pathSet] using hy)
        (by simpa [pathSet] using hz)
        (le_of_lt hxy) (le_of_lt hyz)
  · intro hyx
    subst y
    exact (Nat.lt_irrefl _) hxy
  · intro hyz_eq
    subst z
    exact (Nat.lt_irrefl _) hyz

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
