import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.AttachedComponents

/-! Core attachment points and stable consecutive intervals. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def FoldedDuplicateLinkageDataInSet.pathYZCoreAttachmentSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) : Set V :=
  {a : V | a ∈ F.toLinkage.pathYZ.support ∧
    (a = y ∨ a = z ∨
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h a)}

theorem FoldedDuplicateLinkageDataInSet.pathYZCoreAttachmentSet_subset_pathYZ
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.pathYZCoreAttachmentSet ⊆ {a : V | a ∈ F.toLinkage.pathYZ.support} := by
  intro a ha
  exact ha.1

theorem FoldedDuplicateLinkageDataInSet.y_mem_pathYZCoreAttachmentSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    y ∈ F.pathYZCoreAttachmentSet := by
  exact ⟨F.toLinkage.pathYZ.start_mem_support, Or.inl rfl⟩

theorem FoldedDuplicateLinkageDataInSet.z_mem_pathYZCoreAttachmentSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    z ∈ F.pathYZCoreAttachmentSet := by
  exact ⟨F.toLinkage.pathYZ.end_mem_support, Or.inr (Or.inl rfl)⟩

theorem FoldedDuplicateLinkageDataInSet.mem_pathYZCoreAttachmentSet_of_adjacent_core
    {A : Set V} {root v1 x y z a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_path : a ∈ F.toLinkage.pathYZ.support)
    (hadj_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h a) :
    a ∈ F.pathYZCoreAttachmentSet := by
  exact ⟨ha_path, Or.inr (Or.inr hadj_core)⟩

theorem FoldedDuplicateLinkageDataInSet.pathYZCoreAttachmentSet_disjoint_core
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    Disjoint F.pathYZCoreAttachmentSet F.pathXComponentCore.verts := by
  rw [Set.disjoint_left]
  intro a ha hcore
  exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore ha.1 hcore

theorem FoldedDuplicateLinkageDataInSet.not_coreAttachment_in_openInterval_between_noncoreComponent_boundaries_of_max_core
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z c b d a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hmax :
      forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x y z,
        F'.pathXComponentCore.verts.ncard <=
          F.pathXComponentCore.verts.ncard)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb : b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc))
    (hd : d ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc))
    (ha_attach : a ∈ F.pathYZCoreAttachmentSet)
    (ha_open : a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ b d) :
    False := by
  classical
  obtain ⟨nb, nd, p, _hnb_component, _hnd_component, hbn, hndd,
      _hp_path, hp_component⟩ :=
    F.exists_path_between_noncoreComponent_boundary_witnesses hc hb hd
  have ha_path : a ∈ F.toLinkage.pathYZ.support := ha_open.1
  have ha_set : a ∈ A := F.pathYZ_support_subset_set a ha_path
  have ha_not_core : a ∉ F.pathXComponentCore.verts := by
    intro ha_core
    exact Set.disjoint_left.mp F.pathYZCoreAttachmentSet_disjoint_core
      ha_attach ha_core
  have ha_not_y : a ≠ y := by
    intro hay
    exact Walk.not_start_mem_openSupportInterval F.toLinkage.pathYZ
      (by simpa [hay] using ha_open)
  have ha_not_z : a ≠ z := by
    intro haz
    exact
      (Walk.IsPath.not_end_mem_openSupportInterval_of_right_mem
        F.toLinkage.pathYZ_isPath hd.1)
        (by simpa [haz] using ha_open)
  rcases ha_attach.2 with hay | haz | hcore_adj
  · exact ha_not_y hay
  · exact ha_not_z haz
  rcases hcore_adj with ⟨h, hh_core, hha⟩
  have ha_not_reroute :
      a ∉ ((F.reroutePathYZWalk hb.1 hd.1 hbn p hndd).toPath :
          G.Walk y z).support := by
    intro ha_toPath
    exact
      F.reroutePathYZWalk_avoids_openInterval_vertex
        hc hb.1 hd.1 ha_open hbn hndd hp_component
        (SimpleGraph.Walk.support_toPath_subset
          (F.reroutePathYZWalk hb.1 hd.1 hbn p hndd) ha_toPath)
  have hlt :=
    F.pathXComponentCore_ncard_lt_reroutePathYZReplacement_of_new_adjacent_vertex
      hc hb.1 hd.1 hbn hndd hp_component hh_core ha_set
      ha_not_reroute ha_not_core hha
  have hle :=
    hmax (F.reroutePathYZReplacement hc hb.1 hd.1 hbn p hndd
      hp_component)
  omega

theorem FoldedDuplicateLinkageDataInSet.exists_noncoreComponent_boundary_not_coreAttachment_of_max_core
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hcore_max :
      forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z,
        F'.pathXComponentCore.verts.ncard <=
          F.pathXComponentCore.verts.ncard)
    (hc : c ∈ F.noncoreDeletedSet) :
    Exists fun b : V =>
      b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ∧
        b ∉ F.pathYZCoreAttachmentSet := by
  classical
  let B : Set V := F.noncorePathBoundaryOfSet (F.noncoreComponent hc)
  have hnot_small : ¬ B.ncard < 3 := by
    intro hsmall
    exact F.no_noncoreComponent_with_small_boundary
      hG hseparator hc (by simpa [B] using hsmall)
  by_contra hno
  have hall_attach :
      forall b : V, b ∈ B -> b ∈ F.pathYZCoreAttachmentSet := by
    intro b hb
    by_contra hb_not_attach
    exact hno ⟨b, by simpa [B] using hb, hb_not_attach⟩
  have hB_nonempty : B.Nonempty := by
    by_contra hB_empty
    have hB_eq_empty : B = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro b hb
      exact hB_empty ⟨b, hb⟩
    have hsmall : B.ncard < 3 := by
      simp [hB_eq_empty]
    exact hnot_small hsmall
  obtain ⟨l, hlB, hmin⟩ :=
    Walk.exists_min_idx_mem_of_set_nonempty F.toLinkage.pathYZ hB_nonempty
  obtain ⟨r, hrB, hmax⟩ :=
    Walk.exists_max_idx_mem_of_set_nonempty_of_subset_support
      F.toLinkage.pathYZ hB_nonempty
      (by
        intro b hb
        exact (by simpa [B] using hb : b ∈
          F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).1)
  have hsub : B ⊆ ({l, r} : Set V) := by
    intro d hdB
    have hd_path : d ∈ F.toLinkage.pathYZ.support :=
      (by simpa [B] using hdB : d ∈
        F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).1
    have hl_path : l ∈ F.toLinkage.pathYZ.support :=
      (by simpa [B] using hlB : l ∈
        F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).1
    have hr_path : r ∈ F.toLinkage.pathYZ.support :=
      (by simpa [B] using hrB : r ∈
        F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).1
    have hld : F.toLinkage.pathYZ.support.idxOf l <=
        F.toLinkage.pathYZ.support.idxOf d := hmin d hdB
    have hdr : F.toLinkage.pathYZ.support.idxOf d <=
        F.toLinkage.pathYZ.support.idxOf r := hmax d hdB
    by_cases hdl_idx :
        F.toLinkage.pathYZ.support.idxOf d =
          F.toLinkage.pathYZ.support.idxOf l
    · have hdl : d = l := (List.idxOf_inj hd_path).mp hdl_idx
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, hdl]
    · by_cases hdr_idx :
          F.toLinkage.pathYZ.support.idxOf d =
            F.toLinkage.pathYZ.support.idxOf r
      · have hdr_eq : d = r := (List.idxOf_inj hd_path).mp hdr_idx
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, hdr_eq]
      · have hlt_l :
            F.toLinkage.pathYZ.support.idxOf l <
              F.toLinkage.pathYZ.support.idxOf d := by
          omega
        have hlt_r :
            F.toLinkage.pathYZ.support.idxOf d <
              F.toLinkage.pathYZ.support.idxOf r := by
          omega
        have hd_open :
            d ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ l r :=
          ⟨hd_path, hlt_l, hlt_r⟩
        have hd_attach : d ∈ F.pathYZCoreAttachmentSet :=
          hall_attach d hdB
        exact False.elim
          (F.not_coreAttachment_in_openInterval_between_noncoreComponent_boundaries_of_max_core
            hcore_max hc
            (by simpa [B] using hlB)
            (by simpa [B] using hrB)
            hd_attach hd_open)
  have hsmall : B.ncard < 3 := by
    simpa [B] using
      F.noncorePathBoundaryOfSet_ncard_lt_three_of_subset_pair
        (C := F.noncoreComponent hc) hsub
  exact hnot_small hsmall

theorem FoldedDuplicateLinkageDataInSet.noncorePathBoundary_attachedToOpenInterval_subset_supportInterval_of_max_core
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hcore_max :
      forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x y z,
        F'.pathXComponentCore.verts.ncard <=
          F.pathXComponentCore.verts.ncard)
    (hu_attach : u ∈ F.pathYZCoreAttachmentSet)
    (hv_attach : v ∈ F.pathYZCoreAttachmentSet) :
    F.noncorePathBoundaryOfSet
        (F.noncoreComponentsAttachedToOpenInterval u v) ⊆
      Walk.SupportInterval F.toLinkage.pathYZ u v := by
  classical
  intro d hd_boundary
  by_contra hd_not_interval
  have hd_path : d ∈ F.toLinkage.pathYZ.support := hd_boundary.1
  rcases hd_boundary.2 with ⟨a, ha_attached, hadj⟩
  rcases ha_attached with
    ⟨c, hc, ha_component, b, hb_open, hb_boundary⟩
  have hd_component_boundary :
      d ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) :=
    ⟨hd_path, a, ha_component, hadj⟩
  have hu_path : u ∈ F.toLinkage.pathYZ.support :=
    F.pathYZCoreAttachmentSet_subset_pathYZ hu_attach
  have hv_path : v ∈ F.toLinkage.pathYZ.support :=
    F.pathYZCoreAttachmentSet_subset_pathYZ hv_attach
  have hb_path : b ∈ F.toLinkage.pathYZ.support := hb_open.1
  have hnot_between :
      ¬ (F.toLinkage.pathYZ.support.idxOf u <=
            F.toLinkage.pathYZ.support.idxOf d ∧
          F.toLinkage.pathYZ.support.idxOf d <=
            F.toLinkage.pathYZ.support.idxOf v) := by
    intro hbetween
    exact hd_not_interval ⟨hd_path, hbetween.1, hbetween.2⟩
  have houtside :
      F.toLinkage.pathYZ.support.idxOf d <
          F.toLinkage.pathYZ.support.idxOf u ∨
        F.toLinkage.pathYZ.support.idxOf v <
          F.toLinkage.pathYZ.support.idxOf d := by
    by_cases hud :
        F.toLinkage.pathYZ.support.idxOf u <=
          F.toLinkage.pathYZ.support.idxOf d
    · right
      by_contra hvd_not
      have hdv :
          F.toLinkage.pathYZ.support.idxOf d <=
            F.toLinkage.pathYZ.support.idxOf v := by
        omega
      exact hnot_between ⟨hud, hdv⟩
    · left
      omega
  rcases houtside with hd_lt_u | hv_lt_d
  · have hu_open :
        u ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ d b := by
      exact ⟨hu_path, hd_lt_u, hb_open.2.1⟩
    exact
      F.not_coreAttachment_in_openInterval_between_noncoreComponent_boundaries_of_max_core
        hcore_max hc hd_component_boundary hb_boundary hu_attach hu_open
  · have hv_open :
        v ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ b d := by
      exact ⟨hv_path, hb_open.2.2, hv_lt_d⟩
    exact
      F.not_coreAttachment_in_openInterval_between_noncoreComponent_boundaries_of_max_core
        hcore_max hc hb_boundary hd_component_boundary hv_attach hv_open

theorem FoldedDuplicateLinkageDataInSet.optimized_nonattachment_boundary_stable
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hcore_max :
      forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z,
        F'.pathXComponentCore.verts.ncard <=
          F.pathXComponentCore.verts.ncard) :
    forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
      Exists fun b : V =>
        b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ∧
          b ∉ F.pathYZCoreAttachmentSet ∧
            forall u v : V,
              u ∈ F.pathYZCoreAttachmentSet ->
                v ∈ F.pathYZCoreAttachmentSet ->
                  b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                    (forall a : V,
                      a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                        a ∉ F.pathYZCoreAttachmentSet) ->
                      F.noncorePathBoundaryOfSet
                          (F.noncoreComponentsAttachedToOpenInterval u v) ⊆
                        Walk.SupportInterval F.toLinkage.pathYZ u v := by
  intro c hc
  rcases F.exists_noncoreComponent_boundary_not_coreAttachment_of_max_core
      hG hseparator hcore_max hc with
    ⟨b, hb_boundary, hb_not_attach⟩
  exact ⟨b, hb_boundary, hb_not_attach, by
    intro u v hu_attach hv_attach _hb_open _hno_open_attach
    exact
      F.noncorePathBoundary_attachedToOpenInterval_subset_supportInterval_of_max_core
        hcore_max hu_attach hv_attach⟩

theorem FoldedDuplicateLinkageDataInSet.exists_consecutive_coreAttachment_interval_of_not_attachment
    [DecidableEq V]
    {A : Set V} {root v1 x y z b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hb_path : b ∈ F.toLinkage.pathYZ.support)
    (hb_not_attachment : b ∉ F.pathYZCoreAttachmentSet) :
    Exists fun u : V =>
      Exists fun v : V =>
        u ∈ F.pathYZCoreAttachmentSet ∧
          v ∈ F.pathYZCoreAttachmentSet ∧
            b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
              forall a : V,
                a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                  a ∉ F.pathYZCoreAttachmentSet := by
  rcases Walk.IsPath.exists_consecutive_attachment_interval
      F.toLinkage.pathYZ_isPath F.pathYZCoreAttachmentSet
      F.y_mem_pathYZCoreAttachmentSet F.z_mem_pathYZCoreAttachmentSet
      hb_path hb_not_attachment with
    ⟨u, v, _hu_path, hu_attach, _hv_path, hv_attach,
      hb_open, hno_open_attach⟩
  exact ⟨u, v, hu_attach, hv_attach, hb_open, hno_open_attach⟩

theorem FoldedDuplicateLinkageDataInSet.exists_consecutive_coreAttachment_interval_of_boundary_not_attachment
    [DecidableEq V]
    {A : Set V} {root v1 x y z b : V} {C : Set V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hb_boundary : b ∈ F.noncorePathBoundaryOfSet C)
    (hb_not_attachment : b ∉ F.pathYZCoreAttachmentSet) :
    Exists fun u : V =>
      Exists fun v : V =>
        u ∈ F.pathYZCoreAttachmentSet ∧
          v ∈ F.pathYZCoreAttachmentSet ∧
            b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
              forall a : V,
                a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                  a ∉ F.pathYZCoreAttachmentSet := by
  exact
    F.exists_consecutive_coreAttachment_interval_of_not_attachment
      hb_boundary.1 hb_not_attachment

theorem FoldedDuplicateLinkageDataInSet.attached_openInterval_boundary_pair_of_stable_interval
    [DecidableEq V]
    {S : Separation G} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hopen_no_core_attachment :
      forall a : V, a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
        a ∉ F.pathYZCoreAttachmentSet)
    (hattached_path_boundary :
      forall {a b : V},
        a ∈ F.noncoreComponentsAttachedToOpenInterval u v ->
          b ∈ F.toLinkage.pathYZ.support ->
            G.Adj a b ->
              b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∨
                b = u ∨ b = v) :
    forall {a b : V},
      a ∈ F.noncoreComponentsAttachedToOpenInterval u v ∪
          Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
        b ∉ F.noncoreComponentsAttachedToOpenInterval u v ∪
          Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
          G.Adj a b -> b = u ∨ b = v := by
  classical
  intro a b ha hb_not hab
  let C : Set V := F.noncoreComponentsAttachedToOpenInterval u v
  let I : Set V := Walk.OpenSupportInterval F.toLinkage.pathYZ u v
  have hC_sub : C ⊆ F.noncoreDeletedSet := by
    simpa [C] using
      F.noncoreComponentsAttachedToOpenInterval_subset_noncoreDeletedSet
        (u := u) (v := v)
  have hb_not_C : b ∉ C := by
    intro hbC
    exact hb_not (Or.inl (by simpa [C] using hbC))
  have hb_not_I : b ∉ I := by
    intro hbI
    exact hb_not (Or.inr (by simpa [I] using hbI))
  rcases ha with haC | haI
  · have haC' : a ∈ C := by simpa [C] using haC
    have ha_noncore : a ∈ F.noncoreDeletedSet := hC_sub haC'
    rcases F.neighbor_of_mem_noncoreDeletedSet_mem_pathYZ_or_noncoreDeletedSet
        hseparator ha_noncore hab with hb_path | hb_noncore
    · rcases hattached_path_boundary haC hb_path hab with hbI | hb_endpoint
      · exact False.elim (hb_not_I (by simpa [I] using hbI))
      · exact hb_endpoint
    · have hbC : b ∈ C := by
        simpa [C] using
          F.noncoreComponentsAttachedToOpenInterval_closed_under_noncore_neighbor
            haC hb_noncore hab
      exact False.elim (hb_not_C hbC)
  · have haI' : a ∈ I := by simpa [I] using haI
    have ha_path : a ∈ F.toLinkage.pathYZ.support :=
      Walk.openSupportInterval_subset_support F.toLinkage.pathYZ haI
    have ha_left : a ∈ S.left :=
      F.pathYZ_support_subset_set a ha_path
    have ha_not_core_attachment : a ∉ F.pathYZCoreAttachmentSet :=
      hopen_no_core_attachment a haI
    have hx_not_path : x ∉ F.toLinkage.pathYZ.support := by
      intro hx_path
      exact Set.disjoint_left.mp F.toLinkage.pathX_pathYZ_disjoint
        F.toLinkage.pathX.end_mem_support hx_path
    have ha_not_right : a ∉ S.right := by
      intro ha_right
      have ha_sep : a ∈ S.separator := ⟨ha_left, ha_right⟩
      have ha_xyz : a = x ∨ a = y ∨ a = z := by
        have : a ∈ ({x, y, z} : Set V) := by
          simpa [hseparator] using ha_sep
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
      rcases ha_xyz with hax | hay | haz
      · exact hx_not_path (by simpa [hax] using ha_path)
      · exact ha_not_core_attachment
          (by simpa [hay] using F.y_mem_pathYZCoreAttachmentSet)
      · exact ha_not_core_attachment
          (by simpa [haz] using F.z_mem_pathYZCoreAttachmentSet)
    have h_of_left : b ∈ S.left -> b = u ∨ b = v := by
      intro hb_left
      by_cases hb_path : b ∈ F.toLinkage.pathYZ.support
      · exact
          Walk.IsPath.IsChordless.adj_openSupportInterval_path_outside_eq_endpoint
            F.toLinkage.pathYZ_isPath hpathYZ_chordless haI hb_path
            (by simpa [I] using hb_not_I) hab
      · have hb_deleted : b ∈ F.deletedPathSet := ⟨hb_left, hb_path⟩
        by_cases hb_core : b ∈ F.pathXComponentCore.verts
        · have ha_core_attachment : a ∈ F.pathYZCoreAttachmentSet :=
            F.mem_pathYZCoreAttachmentSet_of_adjacent_core
              ha_path ⟨b, hb_core, hab.symm⟩
          exact False.elim (ha_not_core_attachment ha_core_attachment)
        · have hb_noncore : b ∈ F.noncoreDeletedSet :=
            ⟨hb_deleted, hb_core⟩
          have hb_component :
              b ∈ F.noncoreComponent hb_noncore := by
            exact ⟨hb_noncore, SimpleGraph.Reachable.rfl⟩
          have ha_boundary :
              a ∈ F.noncorePathBoundaryOfSet
                    (F.noncoreComponent hb_noncore) := by
            exact ⟨ha_path, b, hb_component, hab.symm⟩
          have hbC : b ∈ C := by
            simpa [C] using
              F.noncoreComponent_subset_attachedToOpenInterval_of_boundary_mem
                hb_noncore haI ha_boundary hb_component
          exact False.elim (hb_not_C hbC)
    rcases S.mem_left_or_right b with hb_left | hb_right
    · exact h_of_left hb_left
    · by_cases hb_left : b ∈ S.left
      · exact h_of_left hb_left
      · exact False.elim
          (S.no_cross ha_left ha_not_right hb_right hb_left hab)


end Schematic.Math.GraphTheory
