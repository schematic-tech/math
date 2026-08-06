import Schematic.Math.GraphTheory.Minors.Society.Basic

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- Choose the three last contacts of a tripod-attachment linkage with the old
tripod carrier. -/
theorem Tripod.exists_attachmentLinkageLastContacts
    [DecidableEq V]
    {S H : GeneralSociety V}
    (T : H.Tripod)
    {right : Fin 3 -> V}
    (L : ThreeVertexLinkage S.graph T.attach right) :
    Nonempty (TripodAttachmentLinkageLastContacts T L) := by
  classical
  let X : Set V :=
    {z : V | Exists fun r : Fin 3 => z ∈ (T.rim r).support}
  have hstart :
      forall i : Fin 3, T.attach i ∈ X := by
    intro i
    exact
      ⟨i, Walk.internalVertices_subset_support
        (T.rim i) (T.attach_mem_rim i)⟩
  have hexists :
      forall i : Fin 3,
        Exists fun x : V =>
          Exists fun hx : x ∈ (L.path i).support =>
            x ∈ X ∧
              Exists fun q : S.graph.Walk x (right (L.targetEquiv i)) =>
                q.IsPath ∧
                  (forall z : V, z ∈ q.support ->
                    z ∈ (L.path i).support) ∧
                    (forall z : V, z ∈ q.support ->
                      Walk.supportIndex (L.path i) x <=
                        Walk.supportIndex (L.path i) z) ∧
                      forall z : V,
                        z ∈ q.support ->
                          z ∈ X -> z = x := by
    intro i
    obtain ⟨x, hx, hxT, htail_path, htail_clean, htail_subset,
        _htail_covers, htail_index⟩ :=
      Walk.IsPath.exists_dropUntil_last_mem_with_index_bound
        (G := S.graph) (L.isPath i) X (hstart i)
    exact
      ⟨x, hx, hxT,
        (L.path i).dropUntil x hx,
        htail_path, htail_subset, htail_index, htail_clean⟩
  choose contact hcontact_mem hcontact_carrier tail htail_path
    htail_subset htail_index htail_clean using hexists
  exact
    ⟨{
      contact := contact
      contact_mem_path := hcontact_mem
      contact_mem_carrier := hcontact_carrier
      tail := tail
      tail_isPath := htail_path
      tail_support_subset_path := htail_subset
      tail_index_bound := htail_index
      tail_clean := by
        intro i z hz hzr
        exact htail_clean i z hz (by simpa [X] using hzr)
    }⟩

/-- A deletion set of size `< 3` in an induced-subgraph vertex subtype deletes
at most two ambient vertices.

This is the cardinal bridge used by the GM IX `(2.2)` no-separator argument:
subgraph-deletion separators are stated over subtype vertices, while
`ThreeConnected` is a statement about ambient society separations. -/
theorem subtype_val_image_ncard_le_two_of_ncard_lt_three
    [Fintype V]
    {p : V -> Prop}
    (D : Set {v : V // p v})
    (hD : D.ncard < 3) :
    (Subtype.val '' D).ncard <= 2 := by
  have himage : (Subtype.val '' D).ncard <= D.ncard :=
    Set.ncard_image_le
  omega

/-- Subtype-deletion version of the 3-connected-society separator principle.

After lifting a small deletion set from an induced linkage graph to the ambient
vertex set, no remaining active component of the ambient deletion graph can be
boundary-free. -/
theorem ThreeConnected.no_active_boundary_free_component_after_subtype_deletion
    [Fintype V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    {p : V -> Prop}
    {D : Set {v : V // p v}}
    (hD : D.ncard < 3)
    (C : (S.graph.induce (Subtype.val '' D)ᶜ).ConnectedComponent)
    (hboundary :
      forall v : V,
        (Exists fun hv : v ∈ (Subtype.val '' D)ᶜ =>
          (⟨v, hv⟩ : {x : V // x ∈ (Subtype.val '' D)ᶜ}) ∈ C.supp) ->
          v ∉ S.boundarySet)
    (hactive :
      Exists fun v : V =>
        (Exists fun hv : v ∈ (Subtype.val '' D)ᶜ =>
          (⟨v, hv⟩ : {x : V // x ∈ (Subtype.val '' D)ᶜ}) ∈ C.supp) ∧
          v ∈ S.activeSet) :
    False :=
  hthree.no_active_boundary_free_induced_component_after_small_deletion
    (subtype_val_image_ncard_le_two_of_ncard_lt_three D hD) C hboundary
    hactive

/-- A graph component containing at least two society boundary vertices supplies
the clean boundary path needed by the boundary-path version of the GM IX `(2.4)`
source wrapper. -/
theorem SimpleGraph.ConnectedComponent.exists_boundary_clean_path_avoiding_remainder
    [DecidableEq V]
    {S : GeneralSociety V}
    (C : S.graph.ConnectedComponent)
    (hboundary_two : 2 <= (C.supp ∩ S.boundarySet).ncard) :
    Exists fun s : V =>
      Exists fun t : V =>
        s ∈ S.boundarySet ∧ t ∈ S.boundarySet ∧ s ≠ t ∧
          Exists fun q : S.graph.Walk s t =>
            q.IsPath ∧
              forall z : V,
                z ∈ q.support ->
                  z ∈ S.boundarySet \ ({s, t} : Set V) ->
                    False := by
  classical
  have hfinite :
      (C.supp ∩ S.boundarySet).Finite :=
    S.boundarySet_finite.subset (by
      intro v hv
      exact hv.2)
  have htwo : 1 < (C.supp ∩ S.boundarySet).ncard := by omega
  obtain ⟨s, t, hs, ht, hst⟩ :=
    (Set.one_lt_ncard_iff hfinite).mp htwo
  have hreach : S.graph.Reachable s t :=
    C.reachable_of_mem_supp hs.1 ht.1
  obtain ⟨q0, hq0_path⟩ := hreach.exists_isPath
  obtain ⟨s', t', hs', ht', hs't', q, hq_path, _hq_clean,
      hq_avoid⟩ :=
    S.exists_boundary_clean_subpath_avoiding_remainder_of_path
      hs.2 ht.2 hst hq0_path
  exact ⟨s', t', hs', ht', hs't', q, hq_path, hq_avoid⟩

/-- Source-boundary path extracted from any large graph component in a
three-connected society. -/
theorem ThreeConnected.exists_boundary_clean_path_avoiding_remainder_of_large_component
    [Fintype V]
    [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (C : S.graph.ConnectedComponent)
    (hC_large : 3 <= C.supp.ncard) :
    Exists fun s : V =>
      Exists fun t : V =>
        s ∈ S.boundarySet ∧ t ∈ S.boundarySet ∧ s ≠ t ∧
          Exists fun q : S.graph.Walk s t =>
            q.IsPath ∧
              forall z : V,
                z ∈ q.support ->
                  z ∈ S.boundarySet \ ({s, t} : Set V) ->
                    False := by
  have hboundary_three :
      3 <= (C.supp ∩ S.boundarySet).ncard :=
    hthree.connectedComponent_boundarySet_ncard_ge_three C hC_large
  exact Schematic.Math.GraphTheory.GeneralSociety.SimpleGraph.ConnectedComponent.exists_boundary_clean_path_avoiding_remainder
    C (by omega)

/-- A three-connected non-rural society contains a clean path between two
distinct boundary vertices.

Non-rurality first rules out the edgeless graph.  In the component of any
chosen edge, a component with at least three vertices meets the boundary at
least three times.  If the component has at most two vertices, society
three-connectivity forces both endpoints of the chosen edge onto the boundary:
otherwise the component itself, separated from the rest along its boundary
vertices, is a forbidden separation of order at most two. -/
theorem ThreeConnected.exists_boundary_clean_path_avoiding_remainder_of_nonrural
    [Fintype V]
    [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (hnot_rural : Not (Nonempty S.Rural)) :
    Exists fun s : V =>
      Exists fun t : V =>
        s ∈ S.boundarySet ∧ t ∈ S.boundarySet ∧ s ≠ t ∧
          Exists fun q : S.graph.Walk s t =>
            q.IsPath ∧
              forall z : V,
                z ∈ q.support ->
                  z ∈ S.boundarySet \ ({s, t} : Set V) ->
                    False := by
  classical
  have hgraph_ne : S.graph ≠ ⊥ := by
    intro hgraph
    exact hnot_rural (Rural.of_graph_eq_bot hgraph)
  obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hgraph_ne
  let C : S.graph.ConnectedComponent := S.graph.connectedComponentMk u
  have huC : u ∈ C.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hvC : v ∈ C.supp := (C.mem_supp_congr_adj huv).mp huC
  by_cases hC_large : 3 <= C.supp.ncard
  · exact
      hthree.exists_boundary_clean_path_avoiding_remainder_of_large_component
        C hC_large
  · have hC_small : C.supp.ncard <= 2 := by omega
    have hinter_le :
        (C.supp ∩ S.boundarySet).ncard <= C.supp.ncard :=
      Set.ncard_le_ncard Set.inter_subset_left
    have huBoundary : u ∈ S.boundarySet := by
      by_contra huNot
      have hboundary_three :=
        hthree.connectedComponent_boundarySet_ncard_ge_three_of_nonboundary
          C huC huNot huv.left_mem_support
      omega
    have hvBoundary : v ∈ S.boundarySet := by
      by_contra hvNot
      have hboundary_three :=
        hthree.connectedComponent_boundarySet_ncard_ge_three_of_nonboundary
          C hvC hvNot huv.right_mem_support
      omega
    have hfinite : (C.supp ∩ S.boundarySet).Finite :=
      S.boundarySet_finite.subset Set.inter_subset_right
    have hboundary_two : 2 <= (C.supp ∩ S.boundarySet).ncard := by
      have hone : 1 < (C.supp ∩ S.boundarySet).ncard :=
        (Set.one_lt_ncard_iff hfinite).mpr
          ⟨u, v, ⟨huC, huBoundary⟩, ⟨hvC, hvBoundary⟩, huv.ne⟩
      omega
    exact
      SimpleGraph.ConnectedComponent.exists_boundary_clean_path_avoiding_remainder
        C hboundary_two

theorem exists_boundary_clean_path_of_preconnected [DecidableEq V]
    (S : GeneralSociety V)
    (hpre : S.graph.Preconnected)
    {s t : V}
    (hs : s ∈ S.boundarySet)
    (ht : t ∈ S.boundarySet)
    (hst : s ≠ t) :
    Exists fun s' : V =>
      Exists fun t' : V =>
        s' ∈ S.boundarySet ∧ t' ∈ S.boundarySet ∧ s' ≠ t' ∧
          Exists fun q : S.graph.Walk s' t' =>
            q.IsPath ∧ Walk.InternalVertices q ∩ S.boundarySet = ∅ := by
  classical
  obtain ⟨q0⟩ := hpre s t
  exact S.exists_boundary_clean_subpath_of_path hs ht hst q0.toPath.property

theorem exists_boundary_clean_path_avoiding_remainder [DecidableEq V]
    (S : GeneralSociety V)
    (hpre : S.graph.Preconnected)
    (hboundary_card : 2 <= S.boundarySet.ncard) :
    Exists fun s : V =>
      Exists fun t : V =>
        s ∈ S.boundarySet ∧ t ∈ S.boundarySet ∧ s ≠ t ∧
          Exists fun q : S.graph.Walk s t =>
            q.IsPath ∧
              Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                forall z : V,
                  z ∈ q.support ->
                    z ∈ S.boundarySet \ ({s, t} : Set V) ->
                      False := by
  classical
  have htwo : 1 < S.boundarySet.ncard := by omega
  obtain ⟨s, t, hs, ht, hst⟩ :=
    (Set.one_lt_ncard_iff S.boundarySet_finite).mp htwo
  obtain ⟨s', t', hs', ht', hs't', q, hq_path, hq_clean⟩ :=
    S.exists_boundary_clean_path_of_preconnected hpre hs ht hst
  exact ⟨s', t', hs', ht', hs't', q, hq_path, hq_clean, by
    intro z hzq hzboundary
    have hzs : z ≠ s' := by
      intro h
      exact hzboundary.2 (by simp [h])
    have hzt : z ≠ t' := by
      intro h
      exact hzboundary.2 (by simp [h])
    have hz_internal : z ∈ Walk.InternalVertices q :=
      ⟨hzq, hzs, hzt⟩
    have hz_bad : z ∈ Walk.InternalVertices q ∩ S.boundarySet :=
      ⟨hz_internal, hzboundary.1⟩
    have hz_not : z ∉ Walk.InternalVertices q ∩ S.boundarySet := by
      rw [hq_clean]
      simp
    exact hz_not hz_bad⟩

theorem exists_chordless_boundary_path_avoiding_remainder [DecidableEq V]
    (S : GeneralSociety V)
    (hpre : S.graph.Preconnected)
    (hboundary_card : 2 <= S.boundarySet.ncard) :
    Exists fun s : V =>
      Exists fun t : V =>
        s ∈ S.boundarySet ∧ t ∈ S.boundarySet ∧ s ≠ t ∧
          Exists fun q : S.graph.Walk s t =>
            q.IsPath ∧ q.IsChordless ∧
              Walk.InternalVertices q ∩ S.boundarySet = ∅ ∧
                forall z : V,
                  z ∈ q.support ->
                    z ∈ S.boundarySet \ ({s, t} : Set V) ->
                      False := by
  classical
  obtain ⟨s, t, hs, ht, hst, q, _hq_path, _hq_clean, hq_avoid⟩ :=
    S.exists_boundary_clean_path_avoiding_remainder hpre hboundary_card
  let A : Set V := (S.boundarySet \ ({s, t} : Set V))ᶜ
  have hsA : s ∈ A := by
    intro hs_bad
    exact hs_bad.2 (by simp)
  have htA : t ∈ A := by
    intro ht_bad
    exact ht_bad.2 (by simp)
  have hq_support_A : forall z : V, z ∈ q.support -> z ∈ A := by
    intro z hz hzA
    exact hq_avoid z hz hzA
  have hreach :
      (S.graph.induce A).Reachable
        (⟨s, hsA⟩ : A) (⟨t, htA⟩ : A) :=
    Walk.reachable_induce_of_support_subset q hq_support_A
  obtain ⟨r, hr_path, hr_chordless, hr_support_A⟩ :=
    reachable_induce_exists_chordless_path_support_subset
      (G := S.graph) hsA htA hreach
  have hr_avoid :
      forall z : V,
        z ∈ r.support ->
          z ∈ S.boundarySet \ ({s, t} : Set V) ->
            False := by
    intro z hzr hzboundary
    exact hr_support_A z hzr hzboundary
  have hr_clean :
      Walk.InternalVertices r ∩ S.boundarySet = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hz_internal : z ∈ Walk.InternalVertices r := hz.1
    have hz_boundary : z ∈ S.boundarySet := hz.2
    exact hr_avoid z hz_internal.1
      ⟨hz_boundary, by
        intro hzst
        rcases hzst with hzs | hzt
        · exact hz_internal.2.1 hzs
        · exact hz_internal.2.2 hzt⟩
  exact ⟨s, t, hs, ht, hst, r, hr_path, hr_chordless, hr_clean,
    hr_avoid⟩

end GeneralSociety

end Schematic.Math.GraphTheory
