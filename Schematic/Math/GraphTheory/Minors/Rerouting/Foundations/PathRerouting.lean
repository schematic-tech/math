import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.NoncoreBoundaries

/-! Rerouting the folded path through a noncore component. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def FoldedDuplicateLinkageDataInSet.reroutePathYZWalk
    [DecidableEq V]
    {A : Set V} {root v1 x y z b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    (p : G.Walk nb nd)
    (hndd : G.Adj nd d) :
    G.Walk y z :=
  ((((F.toLinkage.pathYZ.takeUntil b hb_path).append hbn.toWalk).append p).append
      hndd.toWalk).append
    (F.toLinkage.pathYZ.dropUntil d hd_path)

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZWalk_support_subset_path_or_component
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    forall w : V,
      w ∈ (F.reroutePathYZWalk hb_path hd_path hbn p hndd).support ->
        w ∈ F.toLinkage.pathYZ.support ∨
          w ∈ F.noncoreComponent hc := by
  intro w hw
  let pref : G.Walk y b := F.toLinkage.pathYZ.takeUntil b hb_path
  let edgeIn : G.Walk b nb := hbn.toWalk
  let edgeOut : G.Walk nd d := hndd.toWalk
  let suffix : G.Walk d z := F.toLinkage.pathYZ.dropUntil d hd_path
  have hw_outer :
      w ∈ (((pref.append edgeIn).append p).append edgeOut).support ∨
        w ∈ suffix.support := by
    exact (SimpleGraph.Walk.mem_support_append_iff
      (((pref.append edgeIn).append p).append edgeOut) suffix).mp
      (by simpa [FoldedDuplicateLinkageDataInSet.reroutePathYZWalk,
          pref, edgeIn, edgeOut, suffix] using hw)
  rcases hw_outer with hw_left | hw_suffix
  · have hw_left' :
        w ∈ ((pref.append edgeIn).append p).support ∨
          w ∈ edgeOut.support := by
      exact (SimpleGraph.Walk.mem_support_append_iff
        ((pref.append edgeIn).append p) edgeOut).mp hw_left
    rcases hw_left' with hw_left'' | hw_edge_out
    · have hw_left'' :
          w ∈ (pref.append edgeIn).support ∨ w ∈ p.support := by
        exact (SimpleGraph.Walk.mem_support_append_iff
          (pref.append edgeIn) p).mp hw_left''
      rcases hw_left'' with hw_prefix_edge | hw_component
      · have hw_prefix_edge' : w ∈ pref.support ∨ w ∈ edgeIn.support := by
          exact (SimpleGraph.Walk.mem_support_append_iff pref edgeIn).mp
            hw_prefix_edge
        rcases hw_prefix_edge' with hw_prefix | hw_edge_in
        · exact Or.inl
            (SimpleGraph.Walk.support_takeUntil_subset
              F.toLinkage.pathYZ hb_path (by simpa [pref] using hw_prefix))
        · simp [edgeIn] at hw_edge_in
          rcases hw_edge_in with rfl | rfl
          · exact Or.inl hb_path
          · exact Or.inr (hp_component _ p.start_mem_support)
      · exact Or.inr (hp_component w hw_component)
    · simp [edgeOut] at hw_edge_out
      rcases hw_edge_out with rfl | rfl
      · exact Or.inr (hp_component _ p.end_mem_support)
      · exact Or.inl hd_path
  · exact Or.inl
      (SimpleGraph.Walk.support_dropUntil_subset
        F.toLinkage.pathYZ hd_path (by simpa [suffix] using hw_suffix))

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZWalk_support_subset_set
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    forall w : V,
      w ∈ (F.reroutePathYZWalk hb_path hd_path hbn p hndd).support ->
        w ∈ A := by
  intro w hw
  rcases F.reroutePathYZWalk_support_subset_path_or_component
      hc hb_path hd_path hbn hndd hp_component w hw with hpath | hcomponent
  · exact F.pathYZ_support_subset_set w hpath
  · exact F.deletedPathSet_subset_set
      (F.noncoreComponent_subset_deletedPathSet hc hcomponent)

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZWalk_support_disjoint_core
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    forall w : V,
      w ∈ (F.reroutePathYZWalk hb_path hd_path hbn p hndd).support ->
        w ∉ F.pathXComponentCore.verts := by
  intro w hw hw_core
  rcases F.reroutePathYZWalk_support_subset_path_or_component
      hc hb_path hd_path hbn hndd hp_component w hw with hpath | hcomponent
  · exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
      hpath hw_core
  · exact Set.disjoint_left.mp (F.noncoreComponent_disjoint_core hc)
      hcomponent hw_core

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZWalk_avoids_openInterval_vertex
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (ha_open : a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ b d)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    a ∉ (F.reroutePathYZWalk hb_path hd_path hbn p hndd).support := by
  intro ha_reroute
  let pref : G.Walk y b := F.toLinkage.pathYZ.takeUntil b hb_path
  let edgeIn : G.Walk b nb := hbn.toWalk
  let edgeOut : G.Walk nd d := hndd.toWalk
  let suffix : G.Walk d z := F.toLinkage.pathYZ.dropUntil d hd_path
  have ha_path : a ∈ F.toLinkage.pathYZ.support := ha_open.1
  have hcomponent_not_path :
      forall w : V, w ∈ F.noncoreComponent hc ->
        w ∉ F.toLinkage.pathYZ.support := by
    intro w hw_component hw_path
    exact Set.disjoint_left.mp (F.noncoreComponent_disjoint_pathYZ hc)
      hw_component hw_path
  have ha_outer :
      a ∈ (((pref.append edgeIn).append p).append edgeOut).support ∨
        a ∈ suffix.support := by
    exact (SimpleGraph.Walk.mem_support_append_iff
      (((pref.append edgeIn).append p).append edgeOut) suffix).mp
      (by simpa [FoldedDuplicateLinkageDataInSet.reroutePathYZWalk,
          pref, edgeIn, edgeOut, suffix] using ha_reroute)
  rcases ha_outer with ha_left | ha_suffix
  · have ha_left' :
        a ∈ ((pref.append edgeIn).append p).support ∨
          a ∈ edgeOut.support := by
      exact (SimpleGraph.Walk.mem_support_append_iff
        ((pref.append edgeIn).append p) edgeOut).mp ha_left
    rcases ha_left' with ha_left'' | ha_edge_out
    · have ha_left'' :
          a ∈ (pref.append edgeIn).support ∨ a ∈ p.support := by
        exact (SimpleGraph.Walk.mem_support_append_iff
          (pref.append edgeIn) p).mp ha_left''
      rcases ha_left'' with ha_prefix_edge | ha_component
      · have ha_prefix_edge' : a ∈ pref.support ∨ a ∈ edgeIn.support := by
          exact (SimpleGraph.Walk.mem_support_append_iff pref edgeIn).mp
            ha_prefix_edge
        rcases ha_prefix_edge' with ha_prefix | ha_edge_in
        · exact
            (Walk.not_mem_takeUntil_of_idxOf_lt hb_path
              ha_open.2.1) (by simpa [pref] using ha_prefix)
        · simp [edgeIn] at ha_edge_in
          rcases ha_edge_in with ha_eq_b | ha_eq_nb
          · exact Walk.left_not_mem_openSupportInterval
              F.toLinkage.pathYZ (by simpa [ha_eq_b] using ha_open)
          · exact
              hcomponent_not_path a
                (by simpa [ha_eq_nb] using
                  hp_component nb p.start_mem_support)
                ha_path
      · exact
          hcomponent_not_path a (hp_component a ha_component) ha_path
    · simp [edgeOut] at ha_edge_out
      rcases ha_edge_out with ha_eq_nd | ha_eq_d
      · exact
          hcomponent_not_path a
            (by simpa [ha_eq_nd] using hp_component nd p.end_mem_support)
            ha_path
      · exact Walk.right_not_mem_openSupportInterval
          F.toLinkage.pathYZ (by simpa [ha_eq_d] using ha_open)
  · exact
      (Walk.IsPath.not_mem_dropUntil_of_idxOf_lt
        F.toLinkage.pathYZ_isPath hd_path ha_path ha_open.2.2)
        (by simpa [suffix] using ha_suffix)

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZPath_support_subset_set
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    forall w : V,
      w ∈ ((F.reroutePathYZWalk hb_path hd_path hbn p hndd).toPath :
          G.Walk y z).support ->
        w ∈ A := by
  intro w hw
  exact F.reroutePathYZWalk_support_subset_set
    hc hb_path hd_path hbn hndd hp_component w
      (SimpleGraph.Walk.support_toPath_subset
        (F.reroutePathYZWalk hb_path hd_path hbn p hndd) hw)

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZPath_disjoint_pathX
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    Disjoint {w : V | w ∈ F.toLinkage.pathX.support}
      {w : V |
        w ∈ ((F.reroutePathYZWalk hb_path hd_path hbn p hndd).toPath :
          G.Walk y z).support} := by
  rw [Set.disjoint_left]
  intro w hwX hwReroute
  have hw_walk :
      w ∈ (F.reroutePathYZWalk hb_path hd_path hbn p hndd).support :=
    SimpleGraph.Walk.support_toPath_subset
      (F.reroutePathYZWalk hb_path hd_path hbn p hndd) hwReroute
  rcases F.reroutePathYZWalk_support_subset_path_or_component
      hc hb_path hd_path hbn hndd hp_component w hw_walk with hpath | hcomponent
  · exact Set.disjoint_left.mp F.toLinkage.pathX_pathYZ_disjoint hwX hpath
  · have hw_core : w ∈ F.pathXComponentCore.verts :=
      F.pathX_support_subset_pathXComponentCore w hwX
    exact Set.disjoint_left.mp (F.noncoreComponent_disjoint_core hc)
      hcomponent hw_core

theorem FoldedDuplicateLinkageDataInSet.reroutePathYZPath_support_disjoint_core
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    forall w : V,
      w ∈ ((F.reroutePathYZWalk hb_path hd_path hbn p hndd).toPath :
          G.Walk y z).support ->
        w ∉ F.pathXComponentCore.verts := by
  intro w hw hw_core
  exact F.reroutePathYZWalk_support_disjoint_core
    hc hb_path hd_path hbn hndd hp_component w
      (SimpleGraph.Walk.support_toPath_subset
        (F.reroutePathYZWalk hb_path hd_path hbn p hndd) hw)
      hw_core

noncomputable def FoldedDuplicateLinkageDataInSet.reroutePathYZReplacement
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    (p : G.Walk nb nd)
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc) :
    FoldedDuplicateLinkageDataInSet G A root v1 x y z := by
  let q : G.Walk y z := F.reroutePathYZWalk hb_path hd_path hbn p hndd
  exact
    F.replacePathYZAny (q.toPath : G.Walk y z) q.toPath.property
      (by
        intro w hw
        simpa [q] using
          F.reroutePathYZPath_support_subset_set
            hc hb_path hd_path hbn hndd hp_component w hw)
      (by
        simpa [q] using
          F.reroutePathYZPath_disjoint_pathX
            hc hb_path hd_path hbn hndd hp_component)

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_ncard_lt_reroutePathYZReplacement_of_new_adjacent_vertex
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z c b d nb nd a h : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hd_path : d ∈ F.toLinkage.pathYZ.support)
    (hbn : G.Adj b nb)
    {p : G.Walk nb nd}
    (hndd : G.Adj nd d)
    (hp_component :
      forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc)
    (hh_core : h ∈ F.pathXComponentCore.verts)
    (ha_set : a ∈ A)
    (ha_not_reroute :
      a ∉ ((F.reroutePathYZWalk hb_path hd_path hbn p hndd).toPath :
          G.Walk y z).support)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hha : G.Adj h a) :
    F.pathXComponentCore.verts.ncard <
      (F.reroutePathYZReplacement hc hb_path hd_path hbn p hndd
        hp_component).pathXComponentCore.verts.ncard := by
  let q : G.Walk y z := F.reroutePathYZWalk hb_path hd_path hbn p hndd
  have hq_set :
      forall w : V, w ∈ (q.toPath : G.Walk y z).support -> w ∈ A := by
    intro w hw
    simpa [q] using
      F.reroutePathYZPath_support_subset_set
        hc hb_path hd_path hbn hndd hp_component w hw
  have hq_disj :
      Disjoint {w : V | w ∈ F.toLinkage.pathX.support}
        {w : V | w ∈ (q.toPath : G.Walk y z).support} := by
    simpa [q] using
      F.reroutePathYZPath_disjoint_pathX
        hc hb_path hd_path hbn hndd hp_component
  have hcore_avoids :
      forall w : V, w ∈ F.pathXComponentCore.verts ->
        w ∉ (q.toPath : G.Walk y z).support := by
    intro w hw_core hw_q
    exact F.reroutePathYZPath_support_disjoint_core
      hc hb_path hd_path hbn hndd hp_component w
      (by simpa [q] using hw_q) hw_core
  have hlt :=
    F.pathXComponentCore_ncard_lt_replacePathYZAny_of_new_adjacent_vertex
      (q.toPath : G.Walk y z) q.toPath.property hq_set hq_disj
      hcore_avoids hh_core ha_set
      (by simpa [q] using ha_not_reroute) ha_not_core hha
  simpa [FoldedDuplicateLinkageDataInSet.reroutePathYZReplacement, q]
    using hlt

theorem FoldedDuplicateLinkageDataInSet.no_noncoreComponent_with_small_boundary
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hc : c ∈ F.noncoreDeletedSet)
    (hboundary_small :
      (F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).ncard < 3) :
    False :=
  F.no_nonempty_noncore_closed_subset_with_small_boundary
    hG hseparator
    (C := F.noncoreComponent hc)
    (F.noncoreComponent_subset_noncoreDeletedSet hc)
    (F.noncoreComponent_nonempty hc)
    (by
      intro a b ha hb_noncore hab
      exact F.noncoreComponent_closed_under_noncore_neighbor
        hc ha hb_noncore hab)
    hboundary_small

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_all_component_boundaries_small
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hboundary_small :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        (F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).ncard < 3) :
    F.noncoreDeletedSet = ∅ := by
  classical
  by_contra hnonempty_empty
  obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.mpr hnonempty_empty
  exact F.no_noncoreComponent_with_small_boundary
    hG hseparator hc (hboundary_small c hc)

theorem FoldedDuplicateLinkageDataInSet.three_le_noncoreComponent_boundary_ncard
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hc : c ∈ F.noncoreDeletedSet) :
    3 <= (F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).ncard := by
  by_contra hlt
  have hsmall :
      (F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).ncard < 3 := by
    omega
  exact F.no_noncoreComponent_with_small_boundary
    hG hseparator hc hsmall


end Schematic.Math.GraphTheory
