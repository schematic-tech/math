import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.PathRerouting

/-! Noncore components attached to open path intervals. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def FoldedDuplicateLinkageDataInSet.noncoreComponentsAttachedToOpenInterval
    [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (u v : V) : Set V :=
  {a : V | Exists fun c : V =>
    Exists fun hc : c ∈ F.noncoreDeletedSet =>
      a ∈ F.noncoreComponent hc ∧
        Exists fun b : V =>
          b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v ∧
            b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc)}

theorem FoldedDuplicateLinkageDataInSet.noncoreComponentsAttachedToOpenInterval_subset_noncoreDeletedSet
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z) :
    F.noncoreComponentsAttachedToOpenInterval u v ⊆ F.noncoreDeletedSet := by
  intro a ha
  rcases ha with ⟨c, hc, ha_component, _hboundary⟩
  exact F.noncoreComponent_subset_noncoreDeletedSet hc ha_component

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_subset_attachedToOpenInterval_of_boundary_mem
    [DecidableEq V]
    {A : Set V} {root v1 x y z c u v b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_open : b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v)
    (hb_boundary :
      b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc)) :
    F.noncoreComponent hc ⊆
      F.noncoreComponentsAttachedToOpenInterval u v := by
  intro a ha
  exact ⟨c, hc, ha, b, hb_open, hb_boundary⟩

theorem FoldedDuplicateLinkageDataInSet.noncoreComponentsAttachedToOpenInterval_nonempty_of_boundary_mem
    [DecidableEq V]
    {A : Set V} {root v1 x y z c u v b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hc : c ∈ F.noncoreDeletedSet)
    (hb_open : b ∈ Walk.OpenSupportInterval F.toLinkage.pathYZ u v)
    (hb_boundary :
      b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc)) :
    (F.noncoreComponentsAttachedToOpenInterval u v).Nonempty := by
  rcases F.noncoreComponent_nonempty hc with ⟨a, ha⟩
  exact ⟨a,
    F.noncoreComponent_subset_attachedToOpenInterval_of_boundary_mem
      hc hb_open hb_boundary ha⟩

theorem FoldedDuplicateLinkageDataInSet.noncoreComponentsAttachedToOpenInterval_closed_under_noncore_neighbor
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v a b : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha : a ∈ F.noncoreComponentsAttachedToOpenInterval u v)
    (hb_noncore : b ∈ F.noncoreDeletedSet)
    (hab : G.Adj a b) :
    b ∈ F.noncoreComponentsAttachedToOpenInterval u v := by
  rcases ha with ⟨c, hc, ha_component, hboundary⟩
  exact ⟨c, hc,
    F.noncoreComponent_closed_under_noncore_neighbor
      hc ha_component hb_noncore hab,
    hboundary⟩

theorem FoldedDuplicateLinkageDataInSet.noncoreComponent_subset_attachedToOpenInterval_of_attached_mem
    [DecidableEq V]
    {A : Set V} {root v1 x y z u v a : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (ha : a ∈ F.noncoreComponentsAttachedToOpenInterval u v) :
    F.noncoreComponent
        (F.noncoreComponentsAttachedToOpenInterval_subset_noncoreDeletedSet
          (u := u) (v := v) ha) ⊆
      F.noncoreComponentsAttachedToOpenInterval u v := by
  rcases ha with ⟨c, hc, ha_component, b, hb_open, hb_boundary⟩
  let ha_noncore : a ∈ F.noncoreDeletedSet :=
    F.noncoreComponent_subset_noncoreDeletedSet hc ha_component
  have heq :
      F.noncoreComponent ha_noncore = F.noncoreComponent hc :=
    F.noncoreComponent_eq_of_mem hc ha_component
  intro d hd
  have hd_component : d ∈ F.noncoreComponent hc := by
    simpa [ha_noncore, heq] using hd
  exact ⟨c, hc, hd_component, b, hb_open, hb_boundary⟩

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_all_component_boundaries_small
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hboundary_small :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        (F.noncorePathBoundaryOfSet (F.noncoreComponent hc)).ncard < 3) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_all_component_boundaries_small
      hG hseparator hboundary_small)

theorem FoldedDuplicateLinkageDataInSet.noncorePathBoundaryOfSet_ncard_lt_three_of_subset_pair
    [Fintype V]
    {A : Set V} {root v1 x y z u v : V} {C : Set V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hsub : F.noncorePathBoundaryOfSet C ⊆ ({u, v} : Set V)) :
    (F.noncorePathBoundaryOfSet C).ncard < 3 := by
  classical
  have hpair_card : ({u, v} : Set V).ncard <= 2 := by
    calc
      ({u, v} : Set V).ncard <= ({v} : Set V).ncard + 1 := by
        exact Set.ncard_insert_le u ({v} : Set V)
      _ = 2 := by simp
  have hle :
      (F.noncorePathBoundaryOfSet C).ncard <= ({u, v} : Set V).ncard :=
    Set.ncard_le_ncard hsub
  omega

theorem FoldedDuplicateLinkageDataInSet.no_noncoreComponent_with_boundary_pair
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z c u v : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hc : c ∈ F.noncoreDeletedSet)
    (hboundary_pair :
      forall b : V,
        b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ->
          b = u ∨ b = v) :
    False := by
  have hsub :
      F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ⊆
        ({u, v} : Set V) := by
    intro b hb
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using
      hboundary_pair b hb
  exact F.no_noncoreComponent_with_small_boundary
    hG hseparator hc
    (F.noncorePathBoundaryOfSet_ncard_lt_three_of_subset_pair hsub)

theorem FoldedDuplicateLinkageDataInSet.noncoreDeletedSet_eq_empty_of_all_component_boundaries_pair
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hboundary_pair :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun u : V =>
          Exists fun v : V =>
            u ∈ F.toLinkage.pathYZ.support ∧
              v ∈ F.toLinkage.pathYZ.support ∧
                forall b : V,
                  b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ->
                    b = u ∨ b = v) :
    F.noncoreDeletedSet = ∅ := by
  classical
  apply F.noncoreDeletedSet_eq_empty_of_all_component_boundaries_small
    hG hseparator
  intro c hc
  rcases hboundary_pair c hc with
    ⟨u, v, _hu_path, _hv_path, hpair⟩
  have hsub :
      F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ⊆
        ({u, v} : Set V) := by
    intro b hb
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hpair b hb
  exact F.noncorePathBoundaryOfSet_ncard_lt_three_of_subset_pair hsub

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_all_component_boundaries_pair
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hG : IsThreeConnected G)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hboundary_pair :
      forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
        Exists fun u : V =>
          Exists fun v : V =>
            u ∈ F.toLinkage.pathYZ.support ∧
              v ∈ F.toLinkage.pathYZ.support ∧
                forall b : V,
                  b ∈ F.noncorePathBoundaryOfSet (F.noncoreComponent hc) ->
                    b = u ∨ b = v) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_all_component_boundaries_pair
      hG hseparator hboundary_pair)


end Schematic.Math.GraphTheory
