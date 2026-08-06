import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.CoreAttachments

/-! Interval boundary separations and noncore elimination. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem FoldedDuplicateLinkageDataInSet.noncorePathBoundaryOfSet_eq_endpoint_or_mem_openInterval
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V} {C : Set V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hboundary_interval :
      F.noncorePathBoundaryOfSet C ⊆
        Walk.SupportInterval F.toLinkage.pathYZ u v)
    {b : V}
    (hb : b ∈ F.noncorePathBoundaryOfSet C) :
    b = u ∨ b = v ∨
      b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v := by
  exact Walk.mem_supportInterval_eq_endpoint_or_mem_open
    F.toLinkage.pathYZ (hboundary_interval hb)

theorem FoldedDuplicateLinkageDataInSet.noncorePathBoundaryOfSet_endpoint_pair_of_subset_interval_not_open
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V} {C : Set V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hboundary_interval :
      F.noncorePathBoundaryOfSet C ⊆
        Walk.SupportInterval F.toLinkage.pathYZ u v)
    {b : V}
    (hb : b ∈ F.noncorePathBoundaryOfSet C)
    (hb_not_open :
      b ∉ Walk.OpenSupportInterval F.toLinkage.pathYZ u v) :
    b = u ∨ b = v := by
  rcases F.noncorePathBoundaryOfSet_eq_endpoint_or_mem_openInterval
      hboundary_interval hb with hb_u | hb_v | hb_open
  · exact Or.inl hb_u
  · exact Or.inr hb_v
  · exact False.elim (hb_not_open hb_open)

theorem FoldedDuplicateLinkageDataInSet.attached_path_boundary_of_boundary_subset_interval
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hboundary_interval :
      F.noncorePathBoundaryOfSet
          (F.noncoreComponentsAttachedToOpenInterval u v) ⊆
        Walk.SupportInterval F.toLinkage.pathYZ u v) :
    forall {a d : V},
      a ∈ F.noncoreComponentsAttachedToOpenInterval u v ->
        d ∈ F.toLinkage.pathYZ.support ->
          G.Adj a d ->
            d ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∨
              d = u ∨ d = v := by
  intro a d ha hd_path hadj
  have hd_boundary :
      d ∈ F.noncorePathBoundaryOfSet
            (F.noncoreComponentsAttachedToOpenInterval u v) := by
    exact ⟨hd_path, a, ha, hadj⟩
  rcases F.noncorePathBoundaryOfSet_eq_endpoint_or_mem_openInterval
      hboundary_interval hd_boundary with hd_u | hd_v | hd_open
  · exact Or.inr (Or.inl hd_u)
  · exact Or.inr (Or.inr hd_v)
  · exact Or.inl hd_open

theorem FoldedDuplicateLinkageDataInSet.no_nonempty_noncore_path_interval_with_boundary_pair
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    {C I : Set V}
    (hC_sub : C ⊆ F.noncoreDeletedSet)
    (hC_nonempty : C.Nonempty)
    (hI_sub_path : I ⊆ {a : V | a ∈ F.toLinkage.pathYZ.support})
    (hu_path : u ∈ F.toLinkage.pathYZ.support)
    (hv_path : v ∈ F.toLinkage.pathYZ.support)
    (hboundary_pair :
      forall {a b : V}, a ∈ C ∪ I -> b ∉ C ∪ I ->
        G.Adj a b -> b = u ∨ b = v)
    (hdisj_endpoints : Disjoint (C ∪ I) ({u, v} : Set V)) :
    False := by
  classical
  have hCI_nonempty : (C ∪ I).Nonempty := by
    rcases hC_nonempty with ⟨c, hc⟩
    exact ⟨c, Or.inl hc⟩
  have hv1_not_C : v1 ∉ C := by
    intro hv1C
    exact (hC_sub hv1C).2 F.v1_mem_pathXComponentCore
  have hv1_not_I : v1 ∉ I := by
    intro hv1I
    exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
      (hI_sub_path hv1I) F.v1_mem_pathXComponentCore
  have hv1_ne_u : v1 ≠ u := by
    intro hv1u
    exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
      (by simpa [hv1u] using hu_path) F.v1_mem_pathXComponentCore
  have hv1_ne_v : v1 ≠ v := by
    intro hv1v
    exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
      (by simpa [hv1v] using hv_path) F.v1_mem_pathXComponentCore
  have houtside : ((C ∪ I) ∪ ({u, v} : Set V))ᶜ.Nonempty := by
    refine ⟨v1, ?_⟩
    intro hv1mem
    rcases hv1mem with hv1CI | hv1uv
    · rcases hv1CI with hv1C | hv1I
      · exact hv1_not_C hv1C
      · exact hv1_not_I hv1I
    · simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hv1uv
      exact hv1uv.elim hv1_ne_u hv1_ne_v
  exact hG.no_nonempty_set_with_boundary_pair
    (C := C ∪ I) (u := u) (v := v)
    hboundary_pair hdisj_endpoints hCI_nonempty houtside

theorem FoldedDuplicateLinkageDataInSet.noncore_union_openInterval_disjoint_endpoints
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    {C : Set V}
    (hC_sub : C ⊆ F.noncoreDeletedSet)
    (hu_path : u ∈ F.toLinkage.pathYZ.support)
    (hv_path : v ∈ F.toLinkage.pathYZ.support) :
    Disjoint
      (C ∪ Walk.OpenSupportInterval F.toLinkage.pathYZ u v)
      ({u, v} : Set V) := by
  rw [Set.disjoint_left]
  intro a ha ha_end
  rcases ha_end with hau | hav
  · rcases ha with haC | haI
    · exact Set.disjoint_left.mp F.noncoreDeletedSet_disjoint_pathYZ
        (hC_sub haC) (by simpa [hau] using hu_path)
    · exact Walk.left_not_mem_openSupportInterval F.toLinkage.pathYZ
        (by simpa [hau] using haI)
  · have hav_eq : a = v := by
      simpa [Set.mem_singleton_iff] using hav
    rcases ha with haC | haI
    · exact Set.disjoint_left.mp F.noncoreDeletedSet_disjoint_pathYZ
        (hC_sub haC) (by simpa [hav_eq] using hv_path)
    · exact Walk.right_not_mem_openSupportInterval F.toLinkage.pathYZ
        (by simpa [hav_eq] using haI)

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_component_interval_separators
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hinterval_separator :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun C : Set V =>
          Exists fun I : Set V =>
            Exists fun u : V =>
              Exists fun v : V =>
                F.noncoreComponent hc ⊆ C ∧
                  C ⊆ F.noncoreDeletedSet ∧
                    C.Nonempty ∧
                      I ⊆ {a : V | a ∈ F.toLinkage.pathYZ.support} ∧
                        u ∈ F.toLinkage.pathYZ.support ∧
                          v ∈ F.toLinkage.pathYZ.support ∧
                            (forall {a b : V}, a ∈ C ∪ I ->
                              b ∉ C ∪ I -> G.Adj a b -> b = u ∨ b = v) ∧
                              Disjoint (C ∪ I) ({u, v} : Set V)) :
    F.noncoreDeletedSet = ∅ := by
  classical
  by_contra hnonempty_empty
  obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.mpr hnonempty_empty
  rcases hinterval_separator c hc with
    ⟨C, I, u, v, _hcomponent_sub, hC_sub, hC_nonempty, hI_sub,
      hu_path, hv_path, hboundary_pair, hdisj⟩
  exact F.no_nonempty_noncore_path_interval_with_boundary_pair
    hG hC_sub hC_nonempty hI_sub hu_path hv_path hboundary_pair hdisj

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_component_interval_separators
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hinterval_separator :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun C : Set V =>
          Exists fun I : Set V =>
            Exists fun u : V =>
              Exists fun v : V =>
                F.noncoreComponent hc ⊆ C ∧
                  C ⊆ F.noncoreDeletedSet ∧
                    C.Nonempty ∧
                      I ⊆ {a : V | a ∈ F.toLinkage.pathYZ.support} ∧
                        u ∈ F.toLinkage.pathYZ.support ∧
                          v ∈ F.toLinkage.pathYZ.support ∧
                            (forall {a b : V}, a ∈ C ∪ I ->
                              b ∉ C ∪ I -> G.Adj a b -> b = u ∨ b = v) ∧
                              Disjoint (C ∪ I) ({u, v} : Set V)) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_component_interval_separators
      hG hinterval_separator)

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_component_openInterval_separators
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hopen_interval_separator :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun C : Set V =>
          Exists fun u : V =>
            Exists fun v : V =>
              F.noncoreComponent hc ⊆ C ∧
                C ⊆ F.noncoreDeletedSet ∧
                  C.Nonempty ∧
                    u ∈ F.toLinkage.pathYZ.support ∧
                      v ∈ F.toLinkage.pathYZ.support ∧
                        (forall {a b : V},
                          a ∈ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            b ∉ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            G.Adj a b -> b = u ∨ b = v) ∧
                          Disjoint
                            (C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v)
                            ({u, v} : Set V)) :
    F.noncoreDeletedSet = ∅ := by
  classical
  exact F.noncoreDeletedSet_eq_empty_of_component_interval_separators
    hG (by
      intro c hc
      rcases hopen_interval_separator c hc with
        ⟨C, u, v, hcomponent_sub, hC_sub, hC_nonempty, hu_path,
          hv_path, hboundary_pair, hdisj⟩
      refine ⟨C, Walk.OpenSupportInterval F.toLinkage.pathYZ u v, u, v,
        hcomponent_sub, hC_sub, hC_nonempty, ?_, hu_path, hv_path,
        hboundary_pair, hdisj⟩
      exact Walk.openSupportInterval_subset_support F.toLinkage.pathYZ)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_component_openInterval_separators
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hopen_interval_separator :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun C : Set V =>
          Exists fun u : V =>
            Exists fun v : V =>
              F.noncoreComponent hc ⊆ C ∧
                C ⊆ F.noncoreDeletedSet ∧
                  C.Nonempty ∧
                    u ∈ F.toLinkage.pathYZ.support ∧
                      v ∈ F.toLinkage.pathYZ.support ∧
                        (forall {a b : V},
                          a ∈ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            b ∉ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            G.Adj a b -> b = u ∨ b = v) ∧
                          Disjoint
                            (C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v)
                            ({u, v} : Set V)) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_component_openInterval_separators
      hG hopen_interval_separator)

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_component_openInterval_boundaries
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hopen_interval_boundary :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun C : Set V =>
          Exists fun u : V =>
            Exists fun v : V =>
              F.noncoreComponent hc ⊆ C ∧
                C ⊆ F.noncoreDeletedSet ∧
                  C.Nonempty ∧
                    u ∈ F.toLinkage.pathYZ.support ∧
                      v ∈ F.toLinkage.pathYZ.support ∧
                        (forall {a b : V},
                          a ∈ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            b ∉ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            G.Adj a b -> b = u ∨ b = v)) :
    F.noncoreDeletedSet = ∅ := by
  exact F.noncoreDeletedSet_eq_empty_of_component_openInterval_separators
    hG (by
      intro c hc
      rcases hopen_interval_boundary c hc with
        ⟨C, u, v, hcomponent_sub, hC_sub, hC_nonempty, hu_path,
          hv_path, hboundary_pair⟩
      exact ⟨C, u, v, hcomponent_sub, hC_sub, hC_nonempty,
        hu_path, hv_path, hboundary_pair,
        F.noncore_union_openInterval_disjoint_endpoints
          hC_sub hu_path hv_path⟩)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_component_openInterval_boundaries
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hopen_interval_boundary :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun C : Set V =>
          Exists fun u : V =>
            Exists fun v : V =>
              F.noncoreComponent hc ⊆ C ∧
                C ⊆ F.noncoreDeletedSet ∧
                  C.Nonempty ∧
                    u ∈ F.toLinkage.pathYZ.support ∧
                      v ∈ F.toLinkage.pathYZ.support ∧
                        (forall {a b : V},
                          a ∈ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            b ∉ C ∪
                              Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                            G.Adj a b -> b = u ∨ b = v)) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_component_openInterval_boundaries
      hG hopen_interval_boundary)

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_attached_openInterval_boundaries
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hattached_boundary :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun u : V =>
          Exists fun v : V =>
            Exists fun b : V =>
              u ∈ F.toLinkage.pathYZ.support ∧
                v ∈ F.toLinkage.pathYZ.support ∧
                  b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
                    b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ∧
                      (forall {a d : V},
                        a ∈ F.noncoreComponentsAttachedToOpenInterval u v ∪
                            Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                          d ∉ F.noncoreComponentsAttachedToOpenInterval u v ∪
                            Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                          G.Adj a d -> d = u ∨ d = v)) :
    F.noncoreDeletedSet = ∅ := by
  exact F.noncoreDeletedSet_eq_empty_of_component_openInterval_boundaries
    hG (by
      intro c hc
      rcases hattached_boundary c hc with
        ⟨u, v, b, hu_path, hv_path, hb_open, hb_boundary,
          hboundary_pair⟩
      refine
        ⟨F.noncoreComponentsAttachedToOpenInterval u v, u, v, ?_,
          F.noncoreComponentsAttachedToOpenInterval_subset_noncoreDeletedSet,
          ?_, hu_path, hv_path, hboundary_pair⟩
      · exact
          F.noncoreComponent_subset_attachedToOpenInterval_of_boundary_mem
            hc hb_open hb_boundary
      · exact
          F.noncoreComponentsAttachedToOpenInterval_nonempty_of_boundary_mem
            hc hb_open hb_boundary)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_attached_openInterval_boundaries
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hattached_boundary :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun u : V =>
          Exists fun v : V =>
            Exists fun b : V =>
              u ∈ F.toLinkage.pathYZ.support ∧
                v ∈ F.toLinkage.pathYZ.support ∧
                  b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
                    b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ∧
                      (forall {a d : V},
                        a ∈ F.noncoreComponentsAttachedToOpenInterval u v ∪
                            Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                          d ∉ F.noncoreComponentsAttachedToOpenInterval u v ∪
                            Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                          G.Adj a d -> d = u ∨ d = v)) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_attached_openInterval_boundaries
      hG hattached_boundary)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_attached_stable_openIntervals
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hstable_intervals :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun u : V =>
          Exists fun v : V =>
            Exists fun b : V =>
              u ∈ F.pathYZCoreAttachmentSet ∧
                v ∈ F.pathYZCoreAttachmentSet ∧
                  b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
                    b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ∧
                      (forall a : V,
                        a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                          a ∉ F.pathYZCoreAttachmentSet) ∧
                        (forall {a d : V},
                          a ∈ F.noncoreComponentsAttachedToOpenInterval u v ->
                            d ∈ F.toLinkage.pathYZ.support ->
                              G.Adj a d ->
                                d ∈ Walk.OpenSupportInterval
                                    F.toLinkage.pathYZ u v ∨
                                  d = u ∨ d = v)) :
    (G.induce F.deletedPathSet).Connected := by
  exact F.deletedPathSet_connected_of_attached_openInterval_boundaries
    hG (by
      intro c hc
      rcases hstable_intervals c hc with
        ⟨u, v, b, hu_attach, hv_attach, hb_open, hb_boundary,
          hno_core_open, hattached_boundary⟩
      exact ⟨u, v, b,
        F.pathYZCoreAttachmentSet_subset_pathYZ hu_attach,
        F.pathYZCoreAttachmentSet_subset_pathYZ hv_attach,
        hb_open, hb_boundary,
        F.attached_openInterval_boundary_pair_of_stable_interval
          hseparator hpathYZ_chordless hno_core_open
          hattached_boundary⟩)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_attached_stable_openIntervals_boundary_subset
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hstable_intervals :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun u : V =>
          Exists fun v : V =>
            Exists fun b : V =>
              u ∈ F.pathYZCoreAttachmentSet ∧
                v ∈ F.pathYZCoreAttachmentSet ∧
                  b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
                    b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ∧
                      (forall a : V,
                        a ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ->
                          a ∉ F.pathYZCoreAttachmentSet) ∧
                        (F.noncorePathBoundaryOfSet
                            (F.noncoreComponentsAttachedToOpenInterval u v) ⊆
                          Walk.SupportInterval F.toLinkage.pathYZ u v)) :
    (G.induce F.deletedPathSet).Connected := by
  exact F.deletedPathSet_connected_of_attached_stable_openIntervals
    hG hseparator hpathYZ_chordless (by
      intro c hc
      rcases hstable_intervals c hc with
        ⟨u, v, b, hu_attach, hv_attach, hb_open, hb_boundary,
          hno_core_open, hboundary_interval⟩
      exact ⟨u, v, b, hu_attach, hv_attach, hb_open, hb_boundary,
        hno_core_open,
        F.attached_path_boundary_of_boundary_subset_interval
          hboundary_interval⟩)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_nonattachment_boundary_stable
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hstable :
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
                          Walk.SupportInterval F.toLinkage.pathYZ u v) :
    (G.induce F.deletedPathSet).Connected := by
  exact F.deletedPathSet_connected_of_attached_stable_openIntervals_boundary_subset
    hG hseparator hpathYZ_chordless (by
      intro c hc
      rcases hstable c hc with
        ⟨b, hb_boundary, hb_not_attachment, hboundary_subset⟩
      rcases F.exists_consecutive_coreAttachment_interval_of_boundary_not_attachment
          hb_boundary hb_not_attachment with
        ⟨u, v, hu_attach, hv_attach, hb_open, hno_open_attach⟩
      exact ⟨u, v, b, hu_attach, hv_attach, hb_open, hb_boundary,
        hno_open_attach,
        hboundary_subset u v hu_attach hv_attach hb_open
          hno_open_attach⟩)

theorem FoldedDuplicateLinkageDataInSet.no_nonempty_noncore_subset_with_boundary_pair
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hG : IsThreeConnected G)
    {C : Set V}
    (hC_sub : C ⊆ F.noncoreDeletedSet)
    (hC_nonempty : C.Nonempty)
    (hu_path : u ∈ F.toLinkage.pathYZ.support)
    (hv_path : v ∈ F.toLinkage.pathYZ.support)
    (hboundary_pair :
      forall {a b : V}, a ∈ C -> b ∉ C -> G.Adj a b -> b = u ∨ b = v) :
    False := by
  classical
  let T : Set V := ({u, v} : Set V)
  have hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b) := by
    intro a b ha hb_not hb_not_T hab
    rcases hboundary_pair ha hb_not hab with rfl | rfl
    · exact hb_not_T (by simp [T])
    · exact hb_not_T (by simp [T])
  have hdisj : Disjoint C T := by
    rw [Set.disjoint_left]
    intro a ha haT
    have ha_noncore : a ∈ F.noncoreDeletedSet := hC_sub ha
    have ha_path : a ∈ F.toLinkage.pathYZ.support := by
      rcases haT with hau | hav
      · simpa [T, Set.mem_insert_iff, Set.mem_singleton_iff, hau] using hu_path
      · have hav_eq : a = v := by
          simpa [T, Set.mem_singleton_iff] using hav
        simpa [hav_eq] using hv_path
    exact Set.disjoint_left.mp F.noncoreDeletedSet_disjoint_pathYZ
      ha_noncore ha_path
  have hv1_not_C : v1 ∉ C := by
    intro hv1C
    have hv1_noncore : v1 ∈ F.noncoreDeletedSet := hC_sub hv1C
    exact hv1_noncore.2 F.v1_mem_pathXComponentCore
  have hv1_not_T : v1 ∉ T := by
    intro hv1T
    have hv1_path : v1 ∈ F.toLinkage.pathYZ.support := by
      rcases hv1T with hv1u | hv1v
      · simpa [T, Set.mem_insert_iff, Set.mem_singleton_iff, hv1u] using hu_path
      · have hv1v_eq : v1 = v := by
          simpa [T, Set.mem_singleton_iff] using hv1v
        simpa [hv1v_eq] using hv_path
    exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
      hv1_path F.v1_mem_pathXComponentCore
  have houtside : (C ∪ T)ᶜ.Nonempty := by
    exact ⟨v1, by
      intro hv1
      rcases hv1 with hv1C | hv1T
      · exact hv1_not_C hv1C
      · exact hv1_not_T hv1T⟩
  have hTsmall : T.ncard < 3 := by
    have hTle : T.ncard <= 2 := by
      calc
        T.ncard = ({u, v} : Set V).ncard := rfl
        _ <= ({v} : Set V).ncard + 1 := by
          exact Set.ncard_insert_le u ({v} : Set V)
        _ = 2 := by simp
    omega
  exact hG.no_nonempty_set_with_small_boundary
    hboundary hdisj hC_nonempty houtside hTsmall

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_boundary_pair
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hG : IsThreeConnected G)
    (hu_path : u ∈ F.toLinkage.pathYZ.support)
    (hv_path : v ∈ F.toLinkage.pathYZ.support)
    (hboundary_pair :
      forall {a b : V}, a ∈ F.noncoreDeletedSet ->
        b ∉ F.noncoreDeletedSet -> G.Adj a b -> b = u ∨ b = v) :
    F.noncoreDeletedSet = ∅ := by
  classical
  by_contra hnonempty_empty
  have hnonempty : F.noncoreDeletedSet.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hnonempty_empty
  exact F.no_nonempty_noncore_subset_with_boundary_pair hG
    (C := F.noncoreDeletedSet) (by intro a ha; exact ha) hnonempty
    hu_path hv_path hboundary_pair


end Schematic.Math.GraphTheory
