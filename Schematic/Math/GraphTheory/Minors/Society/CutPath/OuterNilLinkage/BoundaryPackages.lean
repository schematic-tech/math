import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.CleanTailBoundary
import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.EndpointClassification
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- Concrete boundary-allowed data for the double-outer-collapsed linkage
graph once the two cut-path endpoints are known not to be the collapsed outer
feet.

The side-boundary target is handled by the left-arc contact lemma.  The
previous endpoint-classification lemmas handle `P.s` and `P.t`: any rim
incidence is either already one of the three allowed new attachments, or it
would identify that cut-path endpoint with one of the two collapsed outer feet,
which is excluded here. -/
theorem outerNilCommonLeftEndpointBoundary_allowed_of_no_endpoint_outer_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hall : forall m : Fin 3, T.boundary m ∈ P.pathSet)
    (harc_contacts :
      forall z : V, z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hs_ne_i : P.s ≠ T.boundary i)
    (hs_ne_k : P.s ≠ T.boundary k)
    (ht_ne_i : P.t ≠ T.boundary i)
    (ht_ne_k : P.t ≠ T.boundary k) :
    forall r s : Fin 3,
      outerNilCommonLeftEndpointBoundary P a r ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
      Exists fun m : Fin 3 =>
        outerNilCommonLeftEndpointBoundary P a r =
          T.outerNilCommonLeftEndpointAttach j m := by
  classical
  refine
    T.outerNilCommonLeftEndpointBoundary_allowed_of_endpoint_allowed
      P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      hall harc_contacts ha ?_ ?_
  · intro s hs
    rcases
        T.outerNilCommonLeftEndpoint_start_mem_rim_allowed_or_outer_boundary
          P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
          hjk_order hpath_contacts s hs with
      hallowed | houter
    · exact hallowed
    · rcases houter with hsi | hsk
      · exact False.elim (hs_ne_i hsi)
      · exact False.elim (hs_ne_k hsk)
  · intro s ht
    rcases
        T.outerNilCommonLeftEndpoint_end_mem_rim_allowed_or_outer_boundary
          P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
          hjk_order hpath_contacts s ht with
      hallowed | houter
    · exact hallowed
    · rcases houter with hti | htk
      · exact False.elim (ht_ne_i hti)
      · exact False.elim (ht_ne_k htk)

/-- Concrete boundary-allowed data for the double-outer-collapsed linkage
graph from the two genuine endpoint exclusions.

After the three side-tripod feet have been ordered on the induced cut path,
the cut-path start cannot be the last ordered outer foot, and the cut-path end
cannot be the first ordered outer foot.  Thus only the two extreme coincidences
`P.s = T.boundary i` and `P.t = T.boundary k` remain as real residual cases. -/
theorem outerNilCommonLeftEndpointBoundary_allowed_of_extreme_endpoint_exclusions
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hall : forall m : Fin 3, T.boundary m ∈ P.pathSet)
    (harc_contacts :
      forall z : V, z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hs_ne_i : P.s ≠ T.boundary i)
    (ht_ne_k : P.t ≠ T.boundary k) :
    forall r s : Fin 3,
      outerNilCommonLeftEndpointBoundary P a r ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
      Exists fun m : Fin 3 =>
        outerNilCommonLeftEndpointBoundary P a r =
          T.outerNilCommonLeftEndpointAttach j m := by
  classical
  have hs_ne_k : P.s ≠ T.boundary k := by
    intro hsk
    have hk_idx0 :
        Walk.supportIndex P.path (T.boundary k) = 0 := by
      simpa [hsk.symm, Walk.supportIndex] using
        (Walk.idxOf_start_support P.path)
    omega
  have ht_ne_i : P.t ≠ T.boundary i := by
    intro hti
    have hk_le_t :
        Walk.supportIndex P.path (T.boundary k) <=
          Walk.supportIndex P.path P.t :=
      Walk.IsPath.supportIndex_le_end P.path_isPath hk
    have hi_eq_t :
        Walk.supportIndex P.path (T.boundary i) =
          Walk.supportIndex P.path P.t := by
      simp [hti.symm]
    omega
  exact
    T.outerNilCommonLeftEndpointBoundary_allowed_of_no_endpoint_outer_boundary
      P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
      hall harc_contacts hpath_contacts ha hs_ne_i hs_ne_k ht_ne_i ht_ne_k

/-- If the three side-tripod feet occur on the cut path in the source order
`i,j,k`, then the cut path cannot start at the last one. -/
theorem outerNilCommonLeftEndpoint_start_ne_last_ordered_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    P.s ≠ T.boundary k := by
  intro hsk
  have hk_idx0 :
      Walk.supportIndex P.path (T.boundary k) = 0 := by
    simpa [hsk.symm, Walk.supportIndex] using
      (Walk.idxOf_start_support P.path)
  omega

/-- If the three side-tripod feet occur on the cut path in the source order
`i,j,k`, then the cut path cannot end at the first one. -/
theorem outerNilCommonLeftEndpoint_end_ne_first_ordered_boundary
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k)) :
    P.t ≠ T.boundary i := by
  intro hti
  have hk_le_t :
      Walk.supportIndex P.path (T.boundary k) <=
        Walk.supportIndex P.path P.t :=
    Walk.IsPath.supportIndex_le_end P.path_isPath hk
  have hi_eq_t :
      Walk.supportIndex P.path (T.boundary i) =
        Walk.supportIndex P.path P.t := by
    simp [hti.symm]
  omega

/-- Boundary-allowed data from the actual clean-tail residual data.

This is the source-facing variant of
`outerNilCommonLeftEndpointBoundary_allowed_of_extreme_endpoint_exclusions`.
It does not require a global side-arc contact normalization theorem.  Instead,
the target `a` is handled by the concrete clean-tail classifier above, and the
only extra input is the local elimination of the nil non-median-rim residual
for that specific target.  The other two targets are `P.s` and `P.t`, handled
by path-contact normalization and the two genuine extreme endpoint exclusions. -/
theorem outerNilCommonLeftEndpointBoundary_allowed_of_clean_tail_extreme_endpoint_exclusions
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
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
    {x a : V} (q : S.graph.Walk x a)
    (ha : a ∈ P.leftBoundaryArc)
    (hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
        z = x)
    (hresidual :
      (x = T.left ∨ x = T.right) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil)
    (hzero_nil_residual :
      forall r : Fin 3,
        (r = i ∨ r = k) ->
          Tripod.outerNilCommonLeftEndpointBoundary P a 0 ∈
            Walk.InternalVertices (T.rim r) ->
          (T.leg r).Nil -> False)
    (hs_ne_i : P.s ≠ T.boundary i)
    (ht_ne_k : P.t ≠ T.boundary k) :
    forall r s : Fin 3,
      Tripod.outerNilCommonLeftEndpointBoundary P a r ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
      Exists fun m : Fin 3 =>
        Tripod.outerNilCommonLeftEndpointBoundary P a r =
          T.outerNilCommonLeftEndpointAttach j m := by
  classical
  have hs_ne_k : P.s ≠ T.boundary k :=
    T.outerNilCommonLeftEndpoint_start_ne_last_ordered_boundary
      P hij_order hjk_order
  have ht_ne_i : P.t ≠ T.boundary i :=
    T.outerNilCommonLeftEndpoint_end_ne_first_ordered_boundary
      P hk hij_order hjk_order
  intro r s hrs
  fin_cases r
  · rcases
      T.outerNilCommonLeftEndpointBoundary_zero_allowed_or_nil_residual_of_clean_tail
        P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order q ha
        hq_clean hresidual s
        (by
          simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hrs) with
    hallowed | hnil
    · exact hallowed
    · rcases hnil with ⟨r0, hr0, hzInternal, hleg_nil⟩
      exact False.elim
        (hzero_nil_residual r0 hr0 hzInternal hleg_nil)
  · rcases
      T.outerNilCommonLeftEndpoint_start_mem_rim_allowed_or_outer_boundary
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
        hjk_order hpath_contacts s
        (by
          simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hrs) with
    hallowed | houter
    · exact hallowed
    · rcases houter with hsi | hsk
      · exact False.elim (hs_ne_i hsi)
      · exact False.elim (hs_ne_k hsk)
  · rcases
      T.outerNilCommonLeftEndpoint_end_mem_rim_allowed_or_outer_boundary
        P hgraph hij hik hjk hleg_i_nil hleg_k_nil hi hk hij_order
        hjk_order hpath_contacts s
        (by
          simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hrs) with
    hallowed | houter
    · exact hallowed
    · rcases houter with hti | htk
      · exact False.elim (ht_ne_i hti)
      · exact False.elim (ht_ne_k htk)


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
