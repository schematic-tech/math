import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.FoldedLinkage

/-! Linkages constrained to a set and maximization of their connected core. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

structure FoldedDuplicateLinkageDataInSet
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    (root v1 x y z : V) where
  toLinkage : FoldedDuplicateLinkageData G root v1 x y z
  pathX_support_subset_set :
    forall a : V, a ∈ toLinkage.pathX.support -> a ∈ A
  pathYZ_support_subset_set :
    forall a : V, a ∈ toLinkage.pathYZ.support -> a ∈ A

def FoldedDuplicateLinkageDataInSet.replacePathYZ
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset :
      forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support) :
    FoldedDuplicateLinkageDataInSet G A root v1 x y z where
  toLinkage :=
    F.toLinkage.replacePathYZ q hq_path hq_support_subset
  pathX_support_subset_set := F.pathX_support_subset_set
  pathYZ_support_subset_set := by
    intro a haq
    exact F.pathYZ_support_subset_set a (hq_support_subset a haq)

/--
Replace the `yz` path by an arbitrary path contained in the ambient set and
disjoint from the fixed `x` path.  Unlike `replacePathYZ`, this does not require
the new path to be a subpath of the old one.
-/
def FoldedDuplicateLinkageDataInSet.replacePathYZAny
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset : forall a : V, a ∈ q.support -> a ∈ A)
    (hdisj :
      Disjoint {a : V | a ∈ F.toLinkage.pathX.support}
        {a : V | a ∈ q.support}) :
    FoldedDuplicateLinkageDataInSet G A root v1 x y z where
  toLinkage :=
    F.toLinkage.replacePathYZAny q hq_path hdisj
  pathX_support_subset_set := F.pathX_support_subset_set
  pathYZ_support_subset_set := hq_support_subset

theorem FoldedDuplicateLinkageDataInSet.pathYZ_chordless_of_shortest_under_replacement
    [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hmin :
      forall (q : G.Walk y z), q.IsPath ->
        (forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support) ->
          F.toLinkage.pathYZ.length <= q.length) :
    F.toLinkage.pathYZ.IsChordless :=
  F.toLinkage.pathYZ_chordless_of_shortest_under_replacement hmin

def FoldedDuplicateLinkageDataInSet.deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) : Set V :=
  A \ {a : V | a ∈ F.toLinkage.pathYZ.support}

theorem FoldedDuplicateLinkageDataInSet.pathX_support_subset_deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    forall a : V, a ∈ F.toLinkage.pathX.support ->
      a ∈ F.deletedPathSet := by
  intro a ha
  refine ⟨F.pathX_support_subset_set a ha, ?_⟩
  intro haYZ
  exact Set.disjoint_left.mp F.toLinkage.pathX_pathYZ_disjoint ha haYZ

theorem FoldedDuplicateLinkageDataInSet.v1_mem_deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    v1 ∈ F.deletedPathSet :=
  F.pathX_support_subset_deletedPathSet v1 F.toLinkage.pathX.start_mem_support

theorem FoldedDuplicateLinkageDataInSet.x_mem_deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    x ∈ F.deletedPathSet :=
  F.pathX_support_subset_deletedPathSet x F.toLinkage.pathX.end_mem_support

theorem FoldedDuplicateLinkageDataInSet.pathYZ_disjoint_deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    Disjoint {a : V | a ∈ F.toLinkage.pathYZ.support} F.deletedPathSet := by
  rw [Set.disjoint_left]
  intro a haYZ haDel
  exact haDel.2 haYZ

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_subset_set
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.deletedPathSet ⊆ A := by
  intro a ha
  exact ha.1

noncomputable def FoldedDuplicateLinkageDataInSet.pathXDeletedInduce
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) : G.Subgraph :=
  (⊤ : G.Subgraph).induce F.deletedPathSet

noncomputable def FoldedDuplicateLinkageDataInSet.pathXComponentCore
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) : G.Subgraph :=
  let H : G.Subgraph := F.pathXDeletedInduce
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact F.v1_mem_deletedPathSet⟩
  SimpleGraph.Subgraph.coeSubgraph
    ((H.coe.connectedComponentMk v1H).toSubgraph)

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_connected
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.pathXComponentCore.coe.Connected := by
  let H : G.Subgraph := F.pathXDeletedInduce
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact F.v1_mem_deletedPathSet⟩
  have hconn :
      (SimpleGraph.Subgraph.coeSubgraph
        ((H.coe.connectedComponentMk v1H).toSubgraph)).coe.Connected :=
    (SimpleGraph.Subgraph.Connected.coeSubgraph
      ((H.coe.connectedComponentMk v1H).toSubgraph)
      (SimpleGraph.ConnectedComponent.connected_toSubgraph
        (H.coe.connectedComponentMk v1H))).coe
  simpa [FoldedDuplicateLinkageDataInSet.pathXComponentCore, H, v1H] using hconn

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_subset_deletedPathSet
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.pathXComponentCore.verts ⊆ F.deletedPathSet := by
  let H : G.Subgraph := F.pathXDeletedInduce
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact F.v1_mem_deletedPathSet⟩
  have hle :
      SimpleGraph.Subgraph.coeSubgraph
          ((H.coe.connectedComponentMk v1H).toSubgraph) ≤ H :=
    SimpleGraph.Subgraph.coeSubgraph_le
      ((H.coe.connectedComponentMk v1H).toSubgraph)
  intro a ha
  have haH : a ∈ H.verts := by
    exact hle.1 (by
      simpa [FoldedDuplicateLinkageDataInSet.pathXComponentCore, H, v1H] using ha)
  simpa [H, FoldedDuplicateLinkageDataInSet.pathXDeletedInduce] using haH

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_subset_set
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.pathXComponentCore.verts ⊆ A := by
  intro a ha
  exact F.deletedPathSet_subset_set
    (F.pathXComponentCore_subset_deletedPathSet ha)

theorem FoldedDuplicateLinkageDataInSet.v1_mem_pathXComponentCore
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    v1 ∈ F.pathXComponentCore.verts := by
  let H : G.Subgraph := F.pathXDeletedInduce
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact F.v1_mem_deletedPathSet⟩
  simpa [FoldedDuplicateLinkageDataInSet.pathXComponentCore, H, v1H] using v1H.2

theorem FoldedDuplicateLinkageDataInSet.pathX_support_subset_pathXComponentCore
    [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    forall a : V, a ∈ F.toLinkage.pathX.support ->
      a ∈ F.pathXComponentCore.verts := by
  intro a ha
  let H : G.Subgraph := F.pathXDeletedInduce
  let hv1Del : v1 ∈ F.deletedPathSet := F.v1_mem_deletedPathSet
  let haDel : a ∈ F.deletedPathSet :=
    F.pathX_support_subset_deletedPathSet a ha
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact hv1Del⟩
  let aH : H.verts := ⟨a, by
    change a ∈ F.deletedPathSet
    exact haDel⟩
  let q : G.Walk v1 a := F.toLinkage.pathX.takeUntil a ha
  have hq_support :
      forall b : V, b ∈ q.support -> b ∈ F.deletedPathSet := by
    intro b hb
    exact F.pathX_support_subset_deletedPathSet b
      (SimpleGraph.Walk.support_takeUntil_subset F.toLinkage.pathX ha (by
        simpa [q] using hb))
  have hreach_induce :
      (G.induce F.deletedPathSet).Reachable
        ⟨v1, hv1Del⟩ ⟨a, haDel⟩ :=
    Walk.reachable_induce_of_support_subset q hq_support
  have hreach : H.coe.Reachable v1H aH := by
    change ((⊤ : G.Subgraph).induce F.deletedPathSet).coe.Reachable
      ⟨v1, hv1Del⟩ ⟨a, haDel⟩
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hreach_induce
  have hmem :
      aH ∈ (H.coe.connectedComponentMk v1H).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  change a ∈
    (SimpleGraph.Subgraph.coeSubgraph
      ((H.coe.connectedComponentMk v1H).toSubgraph)).verts
  rw [SimpleGraph.Subgraph.verts_coeSubgraph]
  exact ⟨aH, by
    simpa [SimpleGraph.ConnectedComponent.toSubgraph] using hmem, rfl⟩

theorem FoldedDuplicateLinkageDataInSet.x_mem_pathXComponentCore
    [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    x ∈ F.pathXComponentCore.verts :=
  F.pathX_support_subset_pathXComponentCore x F.toLinkage.pathX.end_mem_support

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_subset_of_deletedPathSet_subset
    {A A' : Set V} {root root' v1 x y z x' y' z' : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (F' : FoldedDuplicateLinkageDataInSet G A' root' v1 x' y' z')
    (hdeleted : F.deletedPathSet ⊆ F'.deletedPathSet) :
    F.pathXComponentCore.verts ⊆ F'.pathXComponentCore.verts := by
  intro a ha_core
  have hv1_core : v1 ∈ F.pathXComponentCore.verts :=
    F.v1_mem_pathXComponentCore
  have hpre : F.pathXComponentCore.Preconnected :=
    ⟨F.pathXComponentCore_connected.preconnected⟩
  obtain ⟨p, hp_le_core⟩ :=
    (SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph
      F.pathXComponentCore).mp hpre hv1_core ha_core
  have hp_support_deleted' :
      forall b : V, b ∈ p.support -> b ∈ F'.deletedPathSet := by
    intro b hb
    exact hdeleted
      (F.pathXComponentCore_subset_deletedPathSet
        (hp_le_core.1 (p.mem_verts_toSubgraph.mpr hb)))
  let H' : G.Subgraph := F'.pathXDeletedInduce
  let hv1Del' : v1 ∈ F'.deletedPathSet := F'.v1_mem_deletedPathSet
  let haDel' : a ∈ F'.deletedPathSet := hp_support_deleted' a p.end_mem_support
  let v1H' : H'.verts := ⟨v1, by
    change v1 ∈ F'.deletedPathSet
    exact hv1Del'⟩
  let aH' : H'.verts := ⟨a, by
    change a ∈ F'.deletedPathSet
    exact haDel'⟩
  have hreach_induce :
      (G.induce F'.deletedPathSet).Reachable
        ⟨v1, hv1Del'⟩ ⟨a, haDel'⟩ :=
    Walk.reachable_induce_of_support_subset p hp_support_deleted'
  have hreach : H'.coe.Reachable v1H' aH' := by
    change ((⊤ : G.Subgraph).induce F'.deletedPathSet).coe.Reachable
      ⟨v1, hv1Del'⟩ ⟨a, haDel'⟩
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hreach_induce
  have hmem :
      aH' ∈ (H'.coe.connectedComponentMk v1H').supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  change a ∈
    (SimpleGraph.Subgraph.coeSubgraph
      ((H'.coe.connectedComponentMk v1H').toSubgraph)).verts
  rw [SimpleGraph.Subgraph.verts_coeSubgraph]
  exact ⟨aH', by
    simpa [SimpleGraph.ConnectedComponent.toSubgraph] using hmem, rfl⟩

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_subset_of_core_deletedPathSet
    {A A' : Set V} {root root' v1 x y z x' y' z' : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (F' : FoldedDuplicateLinkageDataInSet G A' root' v1 x' y' z')
    (hcore_deleted : F.pathXComponentCore.verts ⊆ F'.deletedPathSet) :
    F.pathXComponentCore.verts ⊆ F'.pathXComponentCore.verts := by
  intro a ha_core
  have hv1_core : v1 ∈ F.pathXComponentCore.verts :=
    F.v1_mem_pathXComponentCore
  have hpre : F.pathXComponentCore.Preconnected :=
    ⟨F.pathXComponentCore_connected.preconnected⟩
  obtain ⟨p, hp_le_core⟩ :=
    (SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph
      F.pathXComponentCore).mp hpre hv1_core ha_core
  have hp_support_deleted' :
      forall b : V, b ∈ p.support -> b ∈ F'.deletedPathSet := by
    intro b hb
    exact hcore_deleted
      (hp_le_core.1 (p.mem_verts_toSubgraph.mpr hb))
  let H' : G.Subgraph := F'.pathXDeletedInduce
  let hv1Del' : v1 ∈ F'.deletedPathSet :=
    hp_support_deleted' v1 p.start_mem_support
  let haDel' : a ∈ F'.deletedPathSet :=
    hp_support_deleted' a p.end_mem_support
  let v1H' : H'.verts := ⟨v1, by
    change v1 ∈ F'.deletedPathSet
    exact hv1Del'⟩
  let aH' : H'.verts := ⟨a, by
    change a ∈ F'.deletedPathSet
    exact haDel'⟩
  have hreach_induce :
      (G.induce F'.deletedPathSet).Reachable
        ⟨v1, hv1Del'⟩ ⟨a, haDel'⟩ :=
    Walk.reachable_induce_of_support_subset p hp_support_deleted'
  have hreach : H'.coe.Reachable v1H' aH' := by
    change ((⊤ : G.Subgraph).induce F'.deletedPathSet).coe.Reachable
      ⟨v1, hv1Del'⟩ ⟨a, haDel'⟩
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hreach_induce
  have hmem :
      aH' ∈ (H'.coe.connectedComponentMk v1H').supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  change a ∈
    (SimpleGraph.Subgraph.coeSubgraph
      ((H'.coe.connectedComponentMk v1H').toSubgraph)).verts
  rw [SimpleGraph.Subgraph.verts_coeSubgraph]
  exact ⟨aH', by
    simpa [SimpleGraph.ConnectedComponent.toSubgraph] using hmem, rfl⟩

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_subset_replacePathYZ
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset :
      forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support) :
    F.deletedPathSet ⊆
      (F.replacePathYZ q hq_path hq_support_subset).deletedPathSet := by
  intro a ha
  refine ⟨ha.1, ?_⟩
  intro haq
  exact ha.2 (hq_support_subset a haq)

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_subset_replacePathYZ
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset :
      forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support) :
    F.pathXComponentCore.verts ⊆
      (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts :=
  F.pathXComponentCore_subset_of_deletedPathSet_subset
    (F.replacePathYZ q hq_path hq_support_subset)
    (F.deletedPathSet_subset_replacePathYZ q hq_path hq_support_subset)

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_ncard_le_replacePathYZ
    [Fintype V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset :
      forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support) :
    F.pathXComponentCore.verts.ncard <=
      (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts.ncard :=
  Set.ncard_le_ncard
    (F.pathXComponentCore_subset_replacePathYZ q hq_path hq_support_subset)

theorem FoldedDuplicateLinkageDataInSet.pathXComponentCore_subset_replacePathYZAny_of_core_avoids
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset : forall a : V, a ∈ q.support -> a ∈ A)
    (hdisj :
      Disjoint {a : V | a ∈ F.toLinkage.pathX.support}
        {a : V | a ∈ q.support})
    (hcore_avoids :
      forall a : V, a ∈ F.pathXComponentCore.verts -> a ∉ q.support) :
    F.pathXComponentCore.verts ⊆
      (F.replacePathYZAny q hq_path hq_support_subset hdisj).pathXComponentCore.verts := by
  apply F.pathXComponentCore_subset_of_core_deletedPathSet
  intro a ha_core
  exact ⟨F.pathXComponentCore_subset_set ha_core, hcore_avoids a ha_core⟩

theorem FoldedDuplicateLinkageDataInSet.pathYZ_chordless_of_max_core_min_path
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hmax_replace :
      forall (q : G.Walk y z) (hq_path : q.IsPath)
        (hq_support_subset :
          forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support),
          (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts.ncard <=
            F.pathXComponentCore.verts.ncard)
    (hmin_replace :
      forall (q : G.Walk y z) (hq_path : q.IsPath)
        (hq_support_subset :
          forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support),
          (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts.ncard =
            F.pathXComponentCore.verts.ncard ->
            F.toLinkage.pathYZ.length <= q.length) :
    F.toLinkage.pathYZ.IsChordless := by
  by_contra hnot
  rcases Schematic.Math.GraphTheory.Walk.exists_shorter_path_of_not_chordless
      (G := G) (p := F.toLinkage.pathYZ) hnot with
    ⟨q, hq_path, hq_shorter, hq_support_subset⟩
  have hcore_le_new :=
    F.pathXComponentCore_ncard_le_replacePathYZ q hq_path hq_support_subset
  have hnew_le_core :=
    hmax_replace q hq_path hq_support_subset
  have hcore_eq :
      (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts.ncard =
        F.pathXComponentCore.verts.ncard :=
    le_antisymm hnew_le_core hcore_le_new
  have hlength_le :=
    hmin_replace q hq_path hq_support_subset hcore_eq
  omega

theorem exists_foldedDuplicateLinkageDataInSet_max_core_min_path
    [Fintype V]
    {A : Set V} {root v1 : V}
    (P :
      forall x y z : V,
        FoldedDuplicateLinkageDataInSet G A root v1 x y z -> Prop)
    (hP :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 x y z =>
              P x y z F) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 x y z =>
            P x y z F ∧
              (forall x' y' z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x' y' z',
                  P x' y' z' F' ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ∧
                (forall x' y' z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x' y' z',
                    P x' y' z' F' ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) := by
  classical
  let cardV : Nat := Fintype.card V
  let DeficitHit : Nat -> Prop := fun d =>
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 x y z =>
            P x y z F ∧ cardV - F.pathXComponentCore.verts.ncard = d
  have hDeficitHit : Exists DeficitHit := by
    rcases hP with ⟨x, y, z, F, hPF⟩
    exact ⟨cardV - F.pathXComponentCore.verts.ncard, x, y, z, F, hPF, rfl⟩
  let d0 : Nat := Nat.find hDeficitHit
  rcases Nat.find_spec hDeficitHit with
    ⟨x0, y0, z0, F0, hPF0, hdef0⟩
  have hcore0_max :
      forall x' y' z' : V,
        forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x' y' z',
          P x' y' z' F' ->
            F'.pathXComponentCore.verts.ncard <=
              F0.pathXComponentCore.verts.ncard := by
    intro x' y' z' F' hPF'
    have hfind_le :
        d0 <= cardV - F'.pathXComponentCore.verts.ncard := by
      exact Nat.find_min' hDeficitHit
        ⟨x', y', z', F', hPF', rfl⟩
    have hdef_le :
        cardV - F0.pathXComponentCore.verts.ncard <=
          cardV - F'.pathXComponentCore.verts.ncard := by
      simpa [d0, hdef0] using hfind_le
    have hF0_le_card :
        F0.pathXComponentCore.verts.ncard <= cardV := by
      simpa [cardV, Nat.card_eq_fintype_card] using
        Set.ncard_le_card F0.pathXComponentCore.verts
    have hF'_le_card :
        F'.pathXComponentCore.verts.ncard <= cardV := by
      simpa [cardV, Nat.card_eq_fintype_card] using
        Set.ncard_le_card F'.pathXComponentCore.verts
    omega
  let core0 : Nat := F0.pathXComponentCore.verts.ncard
  let LengthHit : Nat -> Prop := fun n =>
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 x y z =>
            P x y z F ∧ F.pathXComponentCore.verts.ncard = core0 ∧
              F.toLinkage.pathYZ.length = n
  have hLengthHit : Exists LengthHit := by
    exact ⟨F0.toLinkage.pathYZ.length, x0, y0, z0, F0, hPF0, rfl, rfl⟩
  let n0 : Nat := Nat.find hLengthHit
  rcases Nat.find_spec hLengthHit with
    ⟨x, y, z, F, hPF, hcoreF, hlenF⟩
  refine ⟨x, y, z, F, hPF, ?_, ?_⟩
  · intro x' y' z' F' hPF'
    have hle := hcore0_max x' y' z' F' hPF'
    simpa [core0, hcoreF] using hle
  · intro x' y' z' F' hPF' hcore_eq
    have hcore_eq_core0 : F'.pathXComponentCore.verts.ncard = core0 := by
      exact hcore_eq.trans hcoreF
    have hfind_le :
        n0 <= F'.toLinkage.pathYZ.length := by
      exact Nat.find_min' hLengthHit
        ⟨x', y', z', F', hPF', hcore_eq_core0, rfl⟩
    simpa [n0, hlenF] using hfind_le

theorem exists_foldedDuplicateLinkageDataInSet_max_core_min_path_chordless
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 : V}
    (P :
      forall x y z : V,
        FoldedDuplicateLinkageDataInSet G A root v1 x y z -> Prop)
    (hP :
      Exists fun x : V =>
        Exists fun y : V =>
          Exists fun z : V =>
            Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 x y z =>
              P x y z F)
    (hreplace :
      forall x y z : V,
        forall F : FoldedDuplicateLinkageDataInSet G A root v1 x y z,
          P x y z F ->
            forall (q : G.Walk y z) (hq_path : q.IsPath)
              (hq_support_subset :
                forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support),
                P x y z (F.replacePathYZ q hq_path hq_support_subset)) :
    Exists fun x : V =>
      Exists fun y : V =>
        Exists fun z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 x y z =>
            P x y z F ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (forall x' y' z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x' y' z',
                    P x' y' z' F' ->
                      F'.pathXComponentCore.verts.ncard <=
                        F.pathXComponentCore.verts.ncard) ∧
                  (forall x' y' z' : V,
                    forall F' : FoldedDuplicateLinkageDataInSet G A root v1 x' y' z',
                      P x' y' z' F' ->
                        F'.pathXComponentCore.verts.ncard =
                          F.pathXComponentCore.verts.ncard ->
                            F.toLinkage.pathYZ.length <=
                              F'.toLinkage.pathYZ.length) := by
  classical
  rcases exists_foldedDuplicateLinkageDataInSet_max_core_min_path
      (G := G) (A := A) (root := root) (v1 := v1) P hP with
    ⟨x, y, z, F, hPF, hcore_max, hlength_min⟩
  have hmax_replace :
      forall (q : G.Walk y z) (hq_path : q.IsPath)
        (hq_support_subset :
          forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support),
          (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts.ncard <=
            F.pathXComponentCore.verts.ncard := by
    intro q hq_path hq_support_subset
    exact hcore_max x y z (F.replacePathYZ q hq_path hq_support_subset)
      (hreplace x y z F hPF q hq_path hq_support_subset)
  have hmin_replace :
      forall (q : G.Walk y z) (hq_path : q.IsPath)
        (hq_support_subset :
          forall a : V, a ∈ q.support -> a ∈ F.toLinkage.pathYZ.support),
          (F.replacePathYZ q hq_path hq_support_subset).pathXComponentCore.verts.ncard =
            F.pathXComponentCore.verts.ncard ->
            F.toLinkage.pathYZ.length <= q.length := by
    intro q hq_path hq_support_subset hcore_eq
    exact hlength_min x y z (F.replacePathYZ q hq_path hq_support_subset)
      (hreplace x y z F hPF q hq_path hq_support_subset) hcore_eq
  have hchordless :
      F.toLinkage.pathYZ.IsChordless :=
    F.pathYZ_chordless_of_max_core_min_path hmax_replace hmin_replace
  exact ⟨x, y, z, F, hPF, hchordless, hcore_max, hlength_min⟩

theorem exists_foldedDuplicateLinkageDataInSet_tripleSet_max_core_min_path_chordless
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (h :
        Exists fun X : V =>
          Exists fun Y : V =>
            Exists fun Z : V =>
            Exists fun _F : FoldedDuplicateLinkageDataInSet G A root v1 X Y Z =>
              ({X, Y, Z} : Set V) = ({x, y, z} : Set V)) :
    Exists fun X : V =>
      Exists fun Y : V =>
        Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G A root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G A root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard <=
                        F.pathXComponentCore.verts.ncard) ∧
                  (forall X' Y' Z' : V,
                    forall F' : FoldedDuplicateLinkageDataInSet G A root v1 X' Y' Z',
                      ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                        F'.pathXComponentCore.verts.ncard =
                          F.pathXComponentCore.verts.ncard ->
                            F.toLinkage.pathYZ.length <=
                              F'.toLinkage.pathYZ.length) := by
  classical
  let P :
      forall X Y Z : V,
        FoldedDuplicateLinkageDataInSet G A root v1 X Y Z -> Prop :=
    fun X Y Z _F => ({X, Y, Z} : Set V) = ({x, y, z} : Set V)
  exact exists_foldedDuplicateLinkageDataInSet_max_core_min_path_chordless
    (G := G) (A := A) (root := root) (v1 := v1) P h (by
      intro X Y Z F hF q hq_path hq_support_subset
      exact hF)

theorem FoldedDuplicateLinkageDataInSet.pathYZ_disjoint_pathXComponentCore
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    Disjoint {a : V | a ∈ F.toLinkage.pathYZ.support}
      F.pathXComponentCore.verts := by
  rw [Set.disjoint_left]
  intro a haYZ haCore
  exact Set.disjoint_left.mp F.pathYZ_disjoint_deletedPathSet haYZ
    (F.pathXComponentCore_subset_deletedPathSet haCore)

theorem FoldedDuplicateLinkageDataInSet.mem_pathXComponentCore_or_pathYZ_of_left_cover
    {A : Set V} {root v1 x y z a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hcover :
      forall b : V, b ∈ A ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (ha : a ∈ A) :
    a ∈ F.pathXComponentCore.verts ∨
      a ∈ F.toLinkage.pathYZ.support :=
  hcover a ha

theorem FoldedDuplicateLinkageDataInSet.left_cover_iff_deletedPathSet_subset_core
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    (forall b : V, b ∈ A ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support) ↔
      F.deletedPathSet ⊆ F.pathXComponentCore.verts := by
  constructor
  · intro hcover b hb
    rcases hcover b hb.1 with hb_core | hb_path
    · exact hb_core
    · exact False.elim (hb.2 hb_path)
  · intro hsubset b hbA
    by_cases hb_path : b ∈ F.toLinkage.pathYZ.support
    · exact Or.inr hb_path
    · exact Or.inl (hsubset ⟨hbA, hb_path⟩)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_subset_core_of_connected
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hconnected : (G.induce F.deletedPathSet).Connected) :
    F.deletedPathSet ⊆ F.pathXComponentCore.verts := by
  intro a haDel
  let H : G.Subgraph := F.pathXDeletedInduce
  let hv1Del : v1 ∈ F.deletedPathSet := F.v1_mem_deletedPathSet
  let v1H : H.verts := ⟨v1, by
    change v1 ∈ F.deletedPathSet
    exact hv1Del⟩
  let aH : H.verts := ⟨a, by
    change a ∈ F.deletedPathSet
    exact haDel⟩
  have hreach_induce :
      (G.induce F.deletedPathSet).Reachable
        ⟨v1, hv1Del⟩ ⟨a, haDel⟩ :=
    hconnected ⟨v1, hv1Del⟩ ⟨a, haDel⟩
  have hreach : H.coe.Reachable v1H aH := by
    change ((⊤ : G.Subgraph).induce F.deletedPathSet).coe.Reachable
      ⟨v1, hv1Del⟩ ⟨a, haDel⟩
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hreach_induce
  have hmem :
      aH ∈ (H.coe.connectedComponentMk v1H).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  change a ∈
    (SimpleGraph.Subgraph.coeSubgraph
      ((H.coe.connectedComponentMk v1H).toSubgraph)).verts
  rw [SimpleGraph.Subgraph.verts_coeSubgraph]
  exact ⟨aH, by
    simpa [SimpleGraph.ConnectedComponent.toSubgraph] using hmem, rfl⟩

theorem FoldedDuplicateLinkageDataInSet.left_cover_of_deletedPathSet_connected
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hconnected : (G.induce F.deletedPathSet).Connected) :
    forall b : V, b ∈ A ->
      b ∈ F.pathXComponentCore.verts ∨
        b ∈ F.toLinkage.pathYZ.support :=
  (F.left_cover_iff_deletedPathSet_subset_core).mpr
    (F.deletedPathSet_subset_core_of_connected hconnected)

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_left_cover
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hcover :
      forall b : V, b ∈ A ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support) :
    (G.induce F.deletedPathSet).Connected := by
  have hdeleted_subset_core :
      F.deletedPathSet ⊆ F.pathXComponentCore.verts :=
    (F.left_cover_iff_deletedPathSet_subset_core).mp hcover
  have hcore_subset_deleted :
      F.pathXComponentCore.verts ⊆ F.deletedPathSet :=
    F.pathXComponentCore_subset_deletedPathSet
  have hverts :
      F.pathXComponentCore.verts = F.deletedPathSet :=
    Set.Subset.antisymm hcore_subset_deleted hdeleted_subset_core
  have hconn_core :
      (G.induce F.pathXComponentCore.verts).Connected :=
    SimpleGraph.Subgraph.Connected.induce_verts
      (show F.pathXComponentCore.Connected from
        ⟨F.pathXComponentCore_connected⟩)
  rw [hverts] at hconn_core
  exact hconn_core

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_iff_left_cover
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    (G.induce F.deletedPathSet).Connected ↔
      (forall b : V, b ∈ A ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support) := by
  exact ⟨F.left_cover_of_deletedPathSet_connected,
    F.deletedPathSet_connected_of_left_cover⟩


end Schematic.Math.GraphTheory
