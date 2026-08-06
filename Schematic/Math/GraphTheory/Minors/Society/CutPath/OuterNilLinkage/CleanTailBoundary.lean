import Schematic.Math.GraphTheory.Minors.Society.CutPath.OuterNilLinkage.AllowedSubgraph
namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace Tripod

/-- In the double-outer-collapsed source construction, the new side-boundary
target `a` is not on any rebuilt rim.

This is one of the concrete boundary-allowed subcases needed before applying
the GM IX `(2.2)` linkage in the residual side-tripod branch.  If `a` lay on
the cut-path rim, then the induced cut path would contain a boundary vertex
from the open left boundary arc.  If `a` lay on one of the two old side-rim
routes, the arc-contact normalization would make it one of the three side
tripod feet, all of which have already been forced onto the cut path, giving
the same contradiction. -/
theorem outerNilCommonLeftEndpointBoundary_zero_not_mem_rims_of_leftArc_contacts
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
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
    {a : V}
    (ha : a ∈ P.leftBoundaryArc) :
    forall s : Fin 3,
      outerNilCommonLeftEndpointBoundary P a 0 ∉
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support := by
  classical
  intro s hs
  fin_cases s
  · have haPath :
        a ∈ P.pathSet := by
      exact
        P.pathSegmentBetween_support_subset_pathSet hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order)) a
          (by
            simpa [Tripod.outerNilCommonLeftEndpointBoundary,
              Tripod.outerNilCommonLeftEndpointRim] using hs)
    rcases P.boundary_mem_pathSet_eq_s_or_t
        (P.leftBoundaryArc_subset ha) haPath with has | hat
    · exact P.leftBoundaryArc_ne_s ha has
    · exact P.leftBoundaryArc_ne_t ha hat
  · have hsOld :
        a ∈ (T.attachToAttachViaLeft i k).support := by
      simpa [Tripod.outerNilCommonLeftEndpointBoundary,
        Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hs
    rcases T.attachToAttachViaLeft_support_cases hsOld with hai | hak
    · have haT : a ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := i) hai
      rcases harc_contacts a ha haT with ⟨m, hm⟩
      have haPath : a ∈ P.pathSet := by
        simpa [hm] using hall m
      rcases P.boundary_mem_pathSet_eq_s_or_t
          (P.leftBoundaryArc_subset ha) haPath with has | hat
      · exact P.leftBoundaryArc_ne_s ha has
      · exact P.leftBoundaryArc_ne_t ha hat
    · have haT : a ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := k) hak
      rcases harc_contacts a ha haT with ⟨m, hm⟩
      have haPath : a ∈ P.pathSet := by
        simpa [hm] using hall m
      rcases P.boundary_mem_pathSet_eq_s_or_t
          (P.leftBoundaryArc_subset ha) haPath with has | hat
      · exact P.leftBoundaryArc_ne_s ha has
      · exact P.leftBoundaryArc_ne_t ha hat
  · have hsOld :
        a ∈ (T.attachToAttachViaRight i k).support := by
      simpa [Tripod.outerNilCommonLeftEndpointBoundary,
        Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hs
    rcases T.attachToAttachViaRight_support_cases hsOld with hai | hak
    · have haT : a ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := i) hai
      rcases harc_contacts a ha haT with ⟨m, hm⟩
      have haPath : a ∈ P.pathSet := by
        simpa [hm] using hall m
      rcases P.boundary_mem_pathSet_eq_s_or_t
          (P.leftBoundaryArc_subset ha) haPath with has | hat
      · exact P.leftBoundaryArc_ne_s ha has
      · exact P.leftBoundaryArc_ne_t ha hat
    · have haT : a ∈ T.vertexSet :=
        T.rim_mem_vertexSet (i := k) hak
      rcases harc_contacts a ha haT with ⟨m, hm⟩
      have haPath : a ∈ P.pathSet := by
        simpa [hm] using hall m
      rcases P.boundary_mem_pathSet_eq_s_or_t
          (P.leftBoundaryArc_subset ha) haPath with has | hat
      · exact P.leftBoundaryArc_ne_s ha has
      · exact P.leftBoundaryArc_ne_t ha hat

/-- Clean-tail classification of the side-boundary target in the
double-outer-collapsed linkage graph.

For the first rebuilt boundary target `a`, the cut-path rim case is impossible
because `a` lies on the open side boundary arc.  On either old side rim, the
clean tail ending at `a` forces `a` to be the initial old-tripod contact `x`.
The residual classifier then says either `a` is one of the two common old
endpoints, hence an allowed new attachment, or it is exactly the nil
non-median-rim residual that still has to be eliminated by the source proof. -/
theorem outerNilCommonLeftEndpointBoundary_zero_allowed_or_nil_residual_of_clean_tail
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
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
            x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil) :
    forall s : Fin 3,
      Tripod.outerNilCommonLeftEndpointBoundary P a 0 ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
      (Exists fun m : Fin 3 =>
        Tripod.outerNilCommonLeftEndpointBoundary P a 0 =
          T.outerNilCommonLeftEndpointAttach j m) ∨
        Exists fun r : Fin 3 =>
          (r = i ∨ r = k) ∧
            Tripod.outerNilCommonLeftEndpointBoundary P a 0 ∈
              Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil := by
  classical
  intro s hs
  fin_cases s
  · have haPath :
        a ∈ P.pathSet := by
      exact
        P.pathSegmentBetween_support_subset_pathSet hi hk
          (Nat.le_of_lt (lt_trans hij_order hjk_order)) a
          (by
            simpa [Tripod.outerNilCommonLeftEndpointBoundary,
              Tripod.outerNilCommonLeftEndpointRim] using hs)
    exact False.elim
      (by
        rcases P.boundary_mem_pathSet_eq_s_or_t
            (P.leftBoundaryArc_subset ha) haPath with has | hat
        · exact P.leftBoundaryArc_ne_s ha has
        · exact P.leftBoundaryArc_ne_t ha hat)
  · have haOld :
        a ∈ (T.attachToAttachViaLeft i k).support := by
      simpa [Tripod.outerNilCommonLeftEndpointBoundary,
        Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hs
    have haT : a ∈ T.vertexSet := by
      rcases T.attachToAttachViaLeft_support_cases haOld with hai | hak
      · exact T.rim_mem_vertexSet (i := i) hai
      · exact T.rim_mem_vertexSet (i := k) hak
    have haPacked :
        Exists fun r : Fin 3 =>
          a ∈ (T.rim r).support ∨ a ∈ (T.leg r).support := by
      rcases haT with haRim | haLeg
      · rcases haRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases haLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩
    have hax : a = x :=
      hq_clean a q.end_mem_support haPacked
    rcases hresidual with hend | hnil
    · rcases hend with hx_left | hx_right
      · left
        exact ⟨1, by
          simp [Tripod.outerNilCommonLeftEndpointBoundary,
            Tripod.outerNilCommonLeftEndpointAttach, hax, hx_left]⟩
      · left
        exact ⟨2, by
          simp [Tripod.outerNilCommonLeftEndpointBoundary,
            Tripod.outerNilCommonLeftEndpointAttach, hax, hx_right]⟩
    · right
      rcases hnil with ⟨r, hr, hxrim, hleg_nil⟩
      exact ⟨r, hr, by
        simpa [Tripod.outerNilCommonLeftEndpointBoundary, hax] using hxrim,
        hleg_nil⟩
  · have haOld :
        a ∈ (T.attachToAttachViaRight i k).support := by
      simpa [Tripod.outerNilCommonLeftEndpointBoundary,
        Tripod.outerNilCommonLeftEndpointRim,
        SimpleGraph.Walk.support_mapLe_eq_support] using hs
    have haT : a ∈ T.vertexSet := by
      rcases T.attachToAttachViaRight_support_cases haOld with hai | hak
      · exact T.rim_mem_vertexSet (i := i) hai
      · exact T.rim_mem_vertexSet (i := k) hak
    have haPacked :
        Exists fun r : Fin 3 =>
          a ∈ (T.rim r).support ∨ a ∈ (T.leg r).support := by
      rcases haT with haRim | haLeg
      · rcases haRim with ⟨r, hr⟩
        exact ⟨r, Or.inl hr⟩
      · rcases haLeg with ⟨r, hr⟩
        exact ⟨r, Or.inr hr⟩
    have hax : a = x :=
      hq_clean a q.end_mem_support haPacked
    rcases hresidual with hend | hnil
    · rcases hend with hx_left | hx_right
      · left
        exact ⟨1, by
          simp [Tripod.outerNilCommonLeftEndpointBoundary,
            Tripod.outerNilCommonLeftEndpointAttach, hax, hx_left]⟩
      · left
        exact ⟨2, by
          simp [Tripod.outerNilCommonLeftEndpointBoundary,
            Tripod.outerNilCommonLeftEndpointAttach, hax, hx_right]⟩
    · right
      rcases hnil with ⟨r, hr, hxrim, hleg_nil⟩
      exact ⟨r, hr, by
        simpa [Tripod.outerNilCommonLeftEndpointBoundary, hax] using hxrim,
        hleg_nil⟩

/-- Boundary-allowed data for the double-outer-collapsed linkage reduces to
the two cut-path endpoints.

The preceding lemma proves that the side-boundary target `a` cannot lie on a
rebuilt rim.  Therefore the full `outerNilCommonLeftEndpointLinkageAllowed`
boundary condition is exactly the two remaining endpoint checks for `P.s` and
`P.t`.  This keeps the source proof focused on the genuine endpoint cases
instead of repeatedly reproving the vacuous `a` case. -/
theorem outerNilCommonLeftEndpointBoundary_allowed_of_endpoint_allowed
    {S H : GeneralSociety V}
    [DecidableEq V]
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hgraph : H.graph ≤ S.graph)
    {i j k : Fin 3}
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
    {a : V}
    (ha : a ∈ P.leftBoundaryArc)
    (hs_allowed :
      forall s : Fin 3,
        P.s ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            P.s = T.outerNilCommonLeftEndpointAttach j m)
    (ht_allowed :
      forall s : Fin 3,
        P.t ∈
          (T.outerNilCommonLeftEndpointRim P hgraph
            hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
          Exists fun m : Fin 3 =>
            P.t = T.outerNilCommonLeftEndpointAttach j m) :
    forall r s : Fin 3,
      outerNilCommonLeftEndpointBoundary P a r ∈
        (T.outerNilCommonLeftEndpointRim P hgraph
          hleg_i_nil hleg_k_nil hi hk hij_order hjk_order s).support ->
      Exists fun m : Fin 3 =>
        outerNilCommonLeftEndpointBoundary P a r =
          T.outerNilCommonLeftEndpointAttach j m := by
  classical
  intro r s hrs
  fin_cases r
  · exact False.elim
      (T.outerNilCommonLeftEndpointBoundary_zero_not_mem_rims_of_leftArc_contacts
        P hgraph hleg_i_nil hleg_k_nil hi hk hij_order hjk_order
        hall harc_contacts ha s (by
          simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hrs))
  · simpa [Tripod.outerNilCommonLeftEndpointBoundary] using
      hs_allowed s (by
        simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hrs)
  · simpa [Tripod.outerNilCommonLeftEndpointBoundary] using
      ht_allowed s (by
        simpa [Tripod.outerNilCommonLeftEndpointBoundary] using hrs)


end Tripod

end GeneralSociety

end Schematic.Math.GraphTheory
