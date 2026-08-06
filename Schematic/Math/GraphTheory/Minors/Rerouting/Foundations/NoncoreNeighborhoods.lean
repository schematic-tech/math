import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.CoreMaximization

/-! Components and neighborhoods outside the maximized linkage core. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_component_eq_of_adj
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha : a ∈ F.deletedPathSet)
    (hb : b ∈ F.deletedPathSet)
    (hab : G.Adj a b) :
    (F.pathXDeletedInduce.coe.connectedComponentMk
        (⟨a, by
          change a ∈ F.deletedPathSet
          exact ha⟩ : F.pathXDeletedInduce.verts)) =
      (F.pathXDeletedInduce.coe.connectedComponentMk
        (⟨b, by
          change b ∈ F.deletedPathSet
          exact hb⟩ : F.pathXDeletedInduce.verts)) := by
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  change F.pathXDeletedInduce.Adj
    (⟨a, by
      change a ∈ F.deletedPathSet
      exact ha⟩ : F.pathXDeletedInduce.verts)
    (⟨b, by
      change b ∈ F.deletedPathSet
      exact hb⟩ : F.pathXDeletedInduce.verts)
  simpa [FoldedDuplicateLinkageDataInSet.pathXDeletedInduce] using
    (show a ∈ F.deletedPathSet ∧ b ∈ F.deletedPathSet ∧ G.Adj a b from
      ⟨ha, hb, hab⟩)

theorem FoldedDuplicateLinkageDataInSet.mem_core_of_adj_core_of_mem_deletedPathSet
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_core : a ∈ F.pathXComponentCore.verts)
    (hb : b ∈ F.deletedPathSet)
    (hab : G.Adj a b) :
    b ∈ F.pathXComponentCore.verts := by
  let H : G.Subgraph := F.pathXDeletedInduce
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact F.v1_mem_deletedPathSet⟩
  have ha_deleted : a ∈ F.deletedPathSet :=
    F.pathXComponentCore_subset_deletedPathSet ha_core
  let aH : H.verts := ⟨a, by
    change a ∈ F.deletedPathSet
    exact ha_deleted⟩
  let bH : H.verts := ⟨b, by
    change b ∈ F.deletedPathSet
    exact hb⟩
  have ha_mem :
      aH ∈ (H.coe.connectedComponentMk v1H).supp := by
    change a ∈
      (SimpleGraph.Subgraph.coeSubgraph
        ((H.coe.connectedComponentMk v1H).toSubgraph)).verts at ha_core
    rw [SimpleGraph.Subgraph.verts_coeSubgraph] at ha_core
    rcases ha_core with ⟨aH', haH', ha_eq⟩
    have haH_eq : aH' = aH := by
      apply Subtype.ext
      simpa using ha_eq
    simpa [haH_eq, SimpleGraph.ConnectedComponent.toSubgraph] using haH'
  have hb_same :
      H.coe.connectedComponentMk aH = H.coe.connectedComponentMk bH := by
    simpa [H, aH, bH] using
      F.deletedPathSet_component_eq_of_adj ha_deleted hb hab
  have hb_mem :
      bH ∈ (H.coe.connectedComponentMk v1H).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha_mem ⊢
    exact (hb_same ▸ ha_mem)
  change b ∈
    (SimpleGraph.Subgraph.coeSubgraph
      ((H.coe.connectedComponentMk v1H).toSubgraph)).verts
  rw [SimpleGraph.Subgraph.verts_coeSubgraph]
  exact ⟨bH, by
    simpa [SimpleGraph.ConnectedComponent.toSubgraph] using hb_mem, rfl⟩

theorem FoldedDuplicateLinkageDataInSet.mem_replacePathYZAny_core_of_adj_old_core
    {A : Set V} {root v1 x y z a h : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset : forall a : V, a ∈ q.support -> a ∈ A)
    (hdisj :
      Disjoint {a : V | a ∈ F.toLinkage.pathX.support}
        {a : V | a ∈ q.support})
    (hcore_avoids :
      forall b : V, b ∈ F.pathXComponentCore.verts -> b ∉ q.support)
    (hh_core : h ∈ F.pathXComponentCore.verts)
    (ha_set : a ∈ A)
    (ha_not_q : a ∉ q.support)
    (hha : G.Adj h a) :
    a ∈
      (F.replacePathYZAny q hq_path hq_support_subset hdisj).pathXComponentCore.verts := by
  let F' := F.replacePathYZAny q hq_path hq_support_subset hdisj
  have hsubset :
      F.pathXComponentCore.verts ⊆ F'.pathXComponentCore.verts := by
    simpa [F'] using
      F.pathXComponentCore_subset_replacePathYZAny_of_core_avoids
        q hq_path hq_support_subset hdisj hcore_avoids
  have hh_core' : h ∈ F'.pathXComponentCore.verts := hsubset hh_core
  have ha_deleted' : a ∈ F'.deletedPathSet := by
    exact ⟨ha_set, ha_not_q⟩
  simpa [F'] using
    F'.mem_core_of_adj_core_of_mem_deletedPathSet
      hh_core' ha_deleted' hha

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_ncard_lt_replacePathYZAny_of_new_adjacent_vertex
    [Fintype V]
    {A : Set V} {root v1 x y z a h : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset : forall a : V, a ∈ q.support -> a ∈ A)
    (hdisj :
      Disjoint {a : V | a ∈ F.toLinkage.pathX.support}
        {a : V | a ∈ q.support})
    (hcore_avoids :
      forall b : V, b ∈ F.pathXComponentCore.verts -> b ∉ q.support)
    (hh_core : h ∈ F.pathXComponentCore.verts)
    (ha_set : a ∈ A)
    (ha_not_q : a ∉ q.support)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hha : G.Adj h a) :
    F.pathXComponentCore.verts.ncard <
      (F.replacePathYZAny q hq_path hq_support_subset hdisj).pathXComponentCore.verts.ncard := by
  let F' := F.replacePathYZAny q hq_path hq_support_subset hdisj
  have hsubset :
      F.pathXComponentCore.verts ⊆ F'.pathXComponentCore.verts := by
    simpa [F'] using
      F.pathXComponentCore_subset_replacePathYZAny_of_core_avoids
        q hq_path hq_support_subset hdisj hcore_avoids
  have ha_new : a ∈ F'.pathXComponentCore.verts := by
    simpa [F'] using
      F.mem_replacePathYZAny_core_of_adj_old_core
        q hq_path hq_support_subset hdisj hcore_avoids
        hh_core ha_set ha_not_q hha
  have hssub : F.pathXComponentCore.verts ⊂ F'.pathXComponentCore.verts := by
    exact Set.ssubset_iff_subset_ne.mpr
      ⟨hsubset, by
        intro h_eq
        exact ha_not_core (by simpa [h_eq] using ha_new)⟩
  exact Set.ncard_lt_ncard hssub

theorem FoldedDuplicateLinkageDataInSet.adjacent_to_core_or_pathYZ_of_core_neighbor_in_set
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_core : a ∈ F.pathXComponentCore.verts)
    (hbA : b ∈ A)
    (hab : G.Adj a b) :
    b ∈ F.pathXComponentCore.verts ∨ b ∈ F.toLinkage.pathYZ.support := by
  by_cases hb_path : b ∈ F.toLinkage.pathYZ.support
  · exact Or.inr hb_path
  · exact Or.inl
      (F.mem_core_of_adj_core_of_mem_deletedPathSet
        ha_core ⟨hbA, hb_path⟩ hab)

theorem FoldedDuplicateLinkageDataInSet.not_adj_core_of_mem_deletedPathSet_not_core
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_core : a ∈ F.pathXComponentCore.verts)
    (hb_deleted : b ∈ F.deletedPathSet)
    (hb_not_core : b ∉ F.pathXComponentCore.verts) :
    Not (G.Adj a b) := by
  intro hab
  exact hb_not_core
    (F.mem_core_of_adj_core_of_mem_deletedPathSet
      ha_core hb_deleted hab)

theorem FoldedDuplicateLinkageDataInSet.not_adj_deleted_not_core_core
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hb_core : b ∈ F.pathXComponentCore.verts) :
    Not (G.Adj a b) := by
  intro hab
  exact F.not_adj_core_of_mem_deletedPathSet_not_core
    hb_core ha_deleted ha_not_core hab.symm

theorem FoldedDuplicateLinkageDataInSet.deleted_neighbor_in_set_not_path_not_core
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hbA : b ∈ A)
    (hb_not_path : b ∉ F.toLinkage.pathYZ.support)
    (hab : G.Adj a b) :
    b ∈ F.deletedPathSet ∧ b ∉ F.pathXComponentCore.verts := by
  have hb_deleted : b ∈ F.deletedPathSet := ⟨hbA, hb_not_path⟩
  refine ⟨hb_deleted, ?_⟩
  intro hb_core
  exact F.not_adj_deleted_not_core_core
    ha_deleted ha_not_core hb_core hab

theorem FoldedDuplicateLinkageDataInSet.mem_pathYZ_of_deleted_not_core_neighbor_core
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hb_core : b ∈ F.pathXComponentCore.verts)
    (hab : G.Adj a b) :
    b ∈ F.toLinkage.pathYZ.support := by
  by_contra hb_not_path
  exact F.not_adj_deleted_not_core_core
    ha_deleted ha_not_core hb_core hab

theorem FoldedDuplicateLinkageDataInSet.mem_pathYZ_of_core_neighbor_deleted_not_core
    {A : Set V} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha_core : a ∈ F.pathXComponentCore.verts)
    (hb_deleted : b ∈ F.deletedPathSet)
    (hb_not_core : b ∉ F.pathXComponentCore.verts)
    (hab : G.Adj a b) :
    a ∈ F.toLinkage.pathYZ.support := by
  by_contra ha_not_path
  exact F.not_adj_core_of_mem_deletedPathSet_not_core
    ha_core hb_deleted hb_not_core hab

theorem FoldedDuplicateLinkageDataInSet.deleted_not_core_not_mem_right_of_triple_separator
    [DecidableEq V]
    {S : Separation G} {root v1 x y z a : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts) :
    a ∉ S.right := by
  intro ha_right
  have ha_sep : a ∈ S.separator := ⟨ha_deleted.1, ha_right⟩
  have ha_xyz : a = x ∨ a = y ∨ a = z := by
    have : a ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using ha_sep
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  rcases ha_xyz with hax | hay | haz
  · exact ha_not_core (by simpa [hax] using F.x_mem_pathXComponentCore)
  · exact ha_deleted.2 (by simp [hay])
  · exact ha_deleted.2 (by simp [haz])

theorem FoldedDuplicateLinkageDataInSet.not_adj_right_only_of_deleted_not_core
    [DecidableEq V]
    {S : Separation G} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hb_right : b ∈ S.right)
    (hb_not_left : b ∉ S.left) :
    Not (G.Adj a b) := by
  exact S.no_cross ha_deleted.1
    (F.deleted_not_core_not_mem_right_of_triple_separator
      hseparator ha_deleted ha_not_core)
    hb_right hb_not_left

theorem FoldedDuplicateLinkageDataInSet.neighbor_in_left_of_deleted_not_core_mem_pathYZ_or_deleted_not_core
    {S : Separation G} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hb_left : b ∈ S.left)
    (hab : G.Adj a b) :
    b ∈ F.toLinkage.pathYZ.support ∨
      (b ∈ F.deletedPathSet ∧ b ∉ F.pathXComponentCore.verts) := by
  by_cases hb_path : b ∈ F.toLinkage.pathYZ.support
  · exact Or.inl hb_path
  · exact Or.inr
      (F.deleted_neighbor_in_set_not_path_not_core
        ha_deleted ha_not_core hb_left hb_path hab)

theorem FoldedDuplicateLinkageDataInSet.neighbor_of_deleted_not_core_mem_pathYZ_or_deleted_not_core
    [DecidableEq V]
    {S : Separation G} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (ha_deleted : a ∈ F.deletedPathSet)
    (ha_not_core : a ∉ F.pathXComponentCore.verts)
    (hab : G.Adj a b) :
    b ∈ F.toLinkage.pathYZ.support ∨
      (b ∈ F.deletedPathSet ∧ b ∉ F.pathXComponentCore.verts) := by
  rcases S.mem_left_or_right b with hb_left | hb_right
  · exact F.neighbor_in_left_of_deleted_not_core_mem_pathYZ_or_deleted_not_core
      ha_deleted ha_not_core hb_left hab
  · by_cases hb_left : b ∈ S.left
    · exact F.neighbor_in_left_of_deleted_not_core_mem_pathYZ_or_deleted_not_core
        ha_deleted ha_not_core hb_left hab
    · exact False.elim
        (F.not_adj_right_only_of_deleted_not_core
          hseparator ha_deleted ha_not_core hb_right hb_left hab)

def FoldedDuplicateLinkageDataInSet.noncoreDeletedSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) : Set V :=
  F.deletedPathSet \ F.pathXComponentCore.verts

theorem FoldedDuplicateLinkageDataInSet.mem_noncoreDeletedSet_iff
    {A : Set V} {root v1 x y z a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    a ∈ F.noncoreDeletedSet ↔
      a ∈ F.deletedPathSet ∧ a ∉ F.pathXComponentCore.verts := by
  rfl

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_subset_deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.noncoreDeletedSet ⊆ F.deletedPathSet := by
  intro a ha
  exact ha.1

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_disjoint_core
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    Disjoint F.noncoreDeletedSet F.pathXComponentCore.verts := by
  rw [Set.disjoint_left]
  intro a ha hcore
  exact ha.2 hcore

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_disjoint_pathYZ
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    Disjoint F.noncoreDeletedSet {a : V | a ∈ F.toLinkage.pathYZ.support} := by
  rw [Set.disjoint_left]
  intro a ha hpath
  exact ha.1.2 hpath

theorem FoldedDuplicateLinkageDataInSet.neighbor_of_mem_noncoreDeletedSet_mem_pathYZ_or_noncoreDeletedSet
    [DecidableEq V]
    {S : Separation G} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (ha : a ∈ F.noncoreDeletedSet)
    (hab : G.Adj a b) :
    b ∈ F.toLinkage.pathYZ.support ∨ b ∈ F.noncoreDeletedSet := by
  rcases F.neighbor_of_deleted_not_core_mem_pathYZ_or_deleted_not_core
      hseparator ha.1 ha.2 hab with hb_path | hb_noncore
  · exact Or.inl hb_path
  · exact Or.inr hb_noncore

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_boundary_subset_pathYZ
    [DecidableEq V]
    {S : Separation G} {root v1 x y z a b : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (ha : a ∈ F.noncoreDeletedSet)
    (hb_not : b ∉ F.noncoreDeletedSet)
    (hab : G.Adj a b) :
    b ∈ F.toLinkage.pathYZ.support := by
  rcases F.neighbor_of_mem_noncoreDeletedSet_mem_pathYZ_or_noncoreDeletedSet
      hseparator ha hab with hb_path | hb_noncore
  · exact hb_path
  · exact False.elim (hb_not hb_noncore)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    (G.induce F.deletedPathSet).Connected ↔ F.noncoreDeletedSet = ∅ := by
  constructor
  · intro hconnected
    have hsubset : F.deletedPathSet ⊆ F.pathXComponentCore.verts :=
      F.deletedPathSet_subset_core_of_connected hconnected
    ext a
    constructor
    · intro ha
      exact False.elim (ha.2 (hsubset ha.1))
    · intro ha
      exact False.elim ha
  · intro hempty
    apply F.deletedPathSet_connected_of_left_cover
    intro b hbA
    by_cases hb_path : b ∈ F.toLinkage.pathYZ.support
    · exact Or.inr hb_path
    · have hb_deleted : b ∈ F.deletedPathSet := ⟨hbA, hb_path⟩
      have hb_not_noncore : b ∉ F.noncoreDeletedSet := by
        intro hb_noncore
        rw [hempty] at hb_noncore
        exact hb_noncore
      have hb_core : b ∈ F.pathXComponentCore.verts := by
        by_contra hb_not_core
        exact hb_not_noncore ⟨hb_deleted, hb_not_core⟩
      exact Or.inl hb_core

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_pathYZ_support_small
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hsmall : {a : V | a ∈ F.toLinkage.pathYZ.support}.ncard < 3) :
    F.noncoreDeletedSet = ∅ := by
  classical
  by_contra hnonempty_empty
  have hnonempty : F.noncoreDeletedSet.Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hnonempty_empty
  let T : Set V := {a : V | a ∈ F.toLinkage.pathYZ.support}
  have hboundary :
      forall {a b : V}, a ∈ F.noncoreDeletedSet -> b ∉ F.noncoreDeletedSet ->
        b ∉ T -> Not (G.Adj a b) := by
    intro a b ha hb_not hb_not_T hab
    exact hb_not_T
      (F.noncoreDeletedSet_boundary_subset_pathYZ
        hseparator ha hb_not hab)
  have hdisj : Disjoint F.noncoreDeletedSet T := by
    simpa [T] using F.noncoreDeletedSet_disjoint_pathYZ
  have houtside : (F.noncoreDeletedSet ∪ T)ᶜ.Nonempty := by
    refine ⟨v1, ?_⟩
    intro hv
    rcases hv with hv_noncore | hv_path
    · exact hv_noncore.2 F.v1_mem_pathXComponentCore
    · exact Set.disjoint_left.mp F.pathYZ_disjoint_pathXComponentCore
        (by simpa [T] using hv_path) F.v1_mem_pathXComponentCore
  have hTsmall : T.ncard < 3 := by
    simpa [T] using hsmall
  exact hG.no_nonempty_set_with_small_boundary
    hboundary hdisj hnonempty houtside hTsmall


end Schematic.Math.GraphTheory
