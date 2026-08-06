import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.NoncoreNeighborhoods

/-! Path boundaries and connectivity inside the noncore region. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def FoldedDuplicateLinkageDataInSet.noncorePathBoundaryOfSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (C : Set V) : Set V :=
  {b : V | b ∈ F.toLinkage.pathYZ.support ∧
    Exists fun a : V => a ∈ C ∧ G.Adj a b}

theorem FoldedDuplicateLinkageDataInSet.mem_noncorePathBoundaryOfSet_iff
    {A : Set V} {root v1 x y z b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (C : Set V) :
    b ∈ F.noncorePathBoundaryOfSet C ↔
      b ∈ F.toLinkage.pathYZ.support ∧
        Exists fun a : V => a ∈ C ∧ G.Adj a b := by
  rfl

theorem FoldedDuplicateLinkageDataInSet.noncorePathBoundaryOfSet_subset_pathYZ
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (C : Set V) :
    F.noncorePathBoundaryOfSet C ⊆
      {b : V | b ∈ F.toLinkage.pathYZ.support} := by
  intro b hb
  exact hb.1

theorem FoldedDuplicateLinkageDataInSet.disjoint_noncore_subset_noncorePathBoundaryOfSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    {C : Set V}
    (hC_sub : C ⊆ F.noncoreDeletedSet) :
    Disjoint C (F.noncorePathBoundaryOfSet C) := by
  rw [Set.disjoint_left]
  intro a ha haBoundary
  exact Set.disjoint_left.mp F.noncoreDeletedSet_disjoint_pathYZ
    (hC_sub ha) haBoundary.1

theorem FoldedDuplicateLinkageDataInSet.no_nonempty_noncore_closed_subset_with_small_boundary
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    {C : Set V}
    (hC_sub : C ⊆ F.noncoreDeletedSet)
    (hC_nonempty : C.Nonempty)
    (hclosed_noncore :
      forall {a b : V}, a ∈ C -> b ∈ F.noncoreDeletedSet ->
        G.Adj a b -> b ∈ C)
    (hboundary_small : (F.noncorePathBoundaryOfSet C).ncard < 3) :
    False := by
  classical
  let T : Set V := F.noncorePathBoundaryOfSet C
  have hboundary :
      forall {a b : V}, a ∈ C -> b ∉ C -> b ∉ T -> Not (G.Adj a b) := by
    intro a b ha hb_not_C hb_not_T hab
    by_cases hb_noncore : b ∈ F.noncoreDeletedSet
    · exact hb_not_C (hclosed_noncore ha hb_noncore hab)
    · have hb_path : b ∈ F.toLinkage.pathYZ.support :=
        F.noncoreDeletedSet_boundary_subset_pathYZ
          hseparator (hC_sub ha) hb_noncore hab
      exact hb_not_T ⟨hb_path, a, ha, hab⟩
  have hdisj : Disjoint C T := by
    simpa [T] using
      F.disjoint_noncore_subset_noncorePathBoundaryOfSet hC_sub
  have hv1_not_C : v1 ∉ C := by
    intro hv1C
    have hv1_noncore : v1 ∈ F.noncoreDeletedSet := hC_sub hv1C
    exact hv1_noncore.2 F.v1_mem_pathXComponentCore
  have hv1_not_T : v1 ∉ T := by
    intro hv1T
    exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
      hv1T.1 F.v1_mem_pathXComponentCore
  have houtside : (C ∪ T)ᶜ.Nonempty := by
    exact ⟨v1, by
      intro hv1
      rcases hv1 with hv1C | hv1T
      · exact hv1_not_C hv1C
      · exact hv1_not_T hv1T⟩
  have hTsmall : T.ncard < 3 := by
    simpa [T] using hboundary_small
  exact hG.no_nonempty_set_with_small_boundary
    hboundary hdisj hC_nonempty houtside hTsmall

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_noncorePathBoundary_small
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hboundary_small :
      (F.noncorePathBoundaryOfSet F.noncoreDeletedSet).ncard < 3) :
    F.noncoreDeletedSet = ∅ := by
  classical
  by_contra hnonempty_empty
  have hnonempty : F.noncoreDeletedSet.Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hnonempty_empty
  exact F.no_nonempty_noncore_closed_subset_with_small_boundary
    hG hseparator
    (C := F.noncoreDeletedSet)
    (by intro a ha; exact ha)
    hnonempty
    (by
      intro a b _ha hb_noncore _hab
      exact hb_noncore)
    hboundary_small

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_noncorePathBoundary_small
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hboundary_small :
      (F.noncorePathBoundaryOfSet F.noncoreDeletedSet).ncard < 3) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_noncorePathBoundary_small
      hG hseparator hboundary_small)

def FoldedDuplicateLinkageDataInSet.noncoreComponent
    {A : Set V} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) : Set V :=
  {a : V | Exists fun ha : a ∈ F.noncoreDeletedSet =>
    (G.induce F.noncoreDeletedSet).Reachable ⟨c, hc⟩ ⟨a, ha⟩}

theorem FoldedDuplicateLinkageDataInSet.mem_noncoreComponent_iff
    {A : Set V} {root v1 x y z c a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) :
    a ∈ F.noncoreComponent hc ↔
      Exists fun ha : a ∈ F.noncoreDeletedSet =>
        (G.induce F.noncoreDeletedSet).Reachable ⟨c, hc⟩ ⟨a, ha⟩ := by
  rfl

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_subset_noncoreDeletedSet
    {A : Set V} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) :
    F.noncoreComponent hc ⊆ F.noncoreDeletedSet := by
  intro a ha
  rcases ha with ⟨ha_noncore, _hreach⟩
  exact ha_noncore

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_subset_deletedPathSet
    {A : Set V} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) :
    F.noncoreComponent hc ⊆ F.deletedPathSet := by
  intro a ha
  exact F.noncoreDeletedSet_subset_deletedPathSet
    (F.noncoreComponent_subset_noncoreDeletedSet hc ha)

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_disjoint_pathYZ
    {A : Set V} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) :
    Disjoint (F.noncoreComponent hc)
      {a : V | a ∈ F.toLinkage.pathYZ.support} := by
  rw [Set.disjoint_left]
  intro a ha hpath
  exact Set.disjoint_left.mp F.noncoreDeletedSet_disjoint_pathYZ
    (F.noncoreComponent_subset_noncoreDeletedSet hc ha) hpath

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_disjoint_core
    {A : Set V} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) :
    Disjoint (F.noncoreComponent hc) F.pathXComponentCore.verts := by
  rw [Set.disjoint_left]
  intro a ha hcore
  exact Set.disjoint_left.mp F.noncoreDeletedSet_disjoint_core
    (F.noncoreComponent_subset_noncoreDeletedSet hc ha) hcore

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_nonempty
    {A : Set V} {root v1 x y z c : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet) :
    (F.noncoreComponent hc).Nonempty := by
  exact ⟨c, hc, SimpleGraph.Reachable.rfl⟩

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_eq_of_mem
    {A : Set V} {root v1 x y z c d : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hd : d ∈ F.noncoreComponent hc) :
    F.noncoreComponent (F.noncoreComponent_subset_noncoreDeletedSet hc hd) =
      F.noncoreComponent hc := by
  ext a
  let hd_noncore : d ∈ F.noncoreDeletedSet :=
    F.noncoreComponent_subset_noncoreDeletedSet hc hd
  have hcd :
      (G.induce F.noncoreDeletedSet).Reachable
        ⟨c, hc⟩ ⟨d, hd_noncore⟩ := by
    rcases hd with ⟨hd_noncore', hreach⟩
    simpa [hd_noncore] using hreach
  constructor
  · rintro ⟨ha_noncore, hda⟩
    exact ⟨ha_noncore, hcd.trans hda⟩
  · rintro ⟨ha_noncore, hca⟩
    exact ⟨ha_noncore, hcd.symm.trans hca⟩

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_closed_under_noncore_neighbor
    {A : Set V} {root v1 x y z c a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (ha : a ∈ F.noncoreComponent hc)
    (hb_noncore : b ∈ F.noncoreDeletedSet)
    (hab : G.Adj a b) :
    b ∈ F.noncoreComponent hc := by
  rcases ha with ⟨ha_noncore, hreach⟩
  have hab_induce :
      (G.induce F.noncoreDeletedSet).Adj
        ⟨a, ha_noncore⟩ ⟨b, hb_noncore⟩ := by
    exact hab
  exact ⟨hb_noncore, hreach.trans (SimpleGraph.Adj.reachable hab_induce)⟩

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_exists_path_between
    [DecidableEq V]
    {A : Set V} {root v1 x y z c a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (ha : a ∈ F.noncoreComponent hc)
    (hb : b ∈ F.noncoreComponent hc) :
    Exists fun p : G.Walk a b =>
      p.IsPath ∧
        forall w : V, w ∈ p.support -> w ∈ F.noncoreComponent hc := by
  rcases ha with ⟨ha_noncore, hca⟩
  rcases hb with ⟨hb_noncore, hcb⟩
  have hab_reach :
      (G.induce F.noncoreDeletedSet).Reachable
        ⟨a, ha_noncore⟩ ⟨b, hb_noncore⟩ :=
    hca.symm.trans hcb
  obtain ⟨p, hp_path, hp_noncore⟩ :=
    reachable_induce_exists_path_support_subset
      (G := G) ha_noncore hb_noncore hab_reach
  refine ⟨p, hp_path, ?_⟩
  intro w hw
  let hw_noncore : w ∈ F.noncoreDeletedSet := hp_noncore w hw
  have haw :
      (G.induce F.noncoreDeletedSet).Reachable
        ⟨a, ha_noncore⟩ ⟨w, hw_noncore⟩ := by
    let q : G.Walk a w := p.takeUntil w hw
    have hq_support :
        forall t : V, t ∈ q.support -> t ∈ F.noncoreDeletedSet := by
      intro t ht
      exact hp_noncore t
        (SimpleGraph.Walk.support_takeUntil_subset p hw (by
          simpa [q] using ht))
    simpa [q, hw_noncore] using
      Walk.reachable_induce_of_support_subset q hq_support
  exact ⟨hw_noncore, hca.trans haw⟩

theorem FoldedDuplicateLinkageDataInSet.exists_path_between_noncoreComponent_boundary_witnesses
    [DecidableEq V]
    {A : Set V} {root v1 x y z c b d : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb : b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc))
    (hd : d ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc)) :
    Exists fun nb : V =>
      Exists fun nd : V =>
        Exists fun p : G.Walk nb nd =>
          nb ∈ F.noncoreComponent hc ∧
            nd ∈ F.noncoreComponent hc ∧
              G.Adj b nb ∧
                G.Adj nd d ∧
                  p.IsPath ∧
                    forall w : V, w ∈ p.support ->
                      w ∈ F.noncoreComponent hc := by
  rcases hb with ⟨_hb_path, nb, hnb_component, hnbb⟩
  rcases hd with ⟨_hd_path, nd, hnd_component, hndd⟩
  obtain ⟨p, hp_path, hp_component⟩ :=
    F.noncoreComponent_exists_path_between hc hnb_component hnd_component
  exact ⟨nb, nd, p, hnb_component, hnd_component,
    hnbb.symm, hndd, hp_path, hp_component⟩


end Schematic.Math.GraphTheory
