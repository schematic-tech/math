import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.IntervalSeparations

/-! Endpoint replacement separations for folded duplicate linkages. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem FoldedDuplicateLinkageDataInSet.deletedPathSet_connected_of_boundary_pair
    [Fintype V] [DecidableEq V]
    {A : Set V} {root v1 x y z u v : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hG : IsThreeConnected G)
    (hu_path : u ∈ F.toLinkage.pathYZ.support)
    (hv_path : v ∈ F.toLinkage.pathYZ.support)
    (hboundary_pair :
      forall {a b : V}, a ∈ F.noncoreDeletedSet ->
        b ∉ F.noncoreDeletedSet -> G.Adj a b -> b = u ∨ b = v) :
    (G.induce F.deletedPathSet).Connected := by
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (F.noncoreDeletedSet_eq_empty_of_boundary_pair
      hG hu_path hv_path hboundary_pair)

theorem FoldedDuplicateLinkageDataInSet.mem_pathXComponentCore_or_pathYZ_of_root_prefer
    [DecidableEq V]
    {S : Separation G} {root v1 v2 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hv2_left : v2 ∈ S.left)
    (hroot_prefer : v2 ∈ S.left \ S.right -> root = v2)
    (hroot_pathYZ : root ∈ F.toLinkage.pathYZ.support) :
    v2 ∈ F.pathXComponentCore.verts ∨
      v2 ∈ F.toLinkage.pathYZ.support := by
  by_cases hv2_right : v2 ∈ S.right
  · have hv2_sep : v2 ∈ S.separator := ⟨hv2_left, hv2_right⟩
    have hv2_xyz : v2 = x ∨ v2 = y ∨ v2 = z := by
      have : v2 ∈ ({x, y, z} : Set V) := by
        simpa [hseparator] using hv2_sep
      simpa [Set.mem_insert_iff] using this
    rcases hv2_xyz with rfl | rfl | rfl
    · exact Or.inl F.x_mem_pathXComponentCore
    · exact Or.inr F.toLinkage.pathYZ.start_mem_support
    · exact Or.inr F.toLinkage.pathYZ.end_mem_support
  · have hroot_eq : root = v2 := hroot_prefer ⟨hv2_left, hv2_right⟩
    exact Or.inr (by simpa [hroot_eq] using hroot_pathYZ)

theorem FoldedDuplicateLinkageDataInSet.internal_pathYZ_vertices_adjacent_pathXComponentCore
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {S : Separation G} {root v1 x y z a : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (ha : a ∈ Walk.InternalVertices F.toLinkage.pathYZ) :
    Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h a := by
  classical
  have ha_support : a ∈ F.toLinkage.pathYZ.support := ha.1
  have ha_left : a ∈ S.left :=
    F.pathYZ_support_subset_set a ha_support
  have hx_not_pathYZ : x ∉ F.toLinkage.pathYZ.support := by
    intro hx_path
    exact Set.disjoint_left.mp F.toLinkage.pathX_pathYZ_disjoint
      F.toLinkage.pathX.end_mem_support hx_path
  have ha_ne_x : a ≠ x := by
    intro h
    exact hx_not_pathYZ (by simpa [h] using ha_support)
  have ha_ne_y : a ≠ y := ha.2.1
  have ha_ne_z : a ≠ z := ha.2.2
  have ha_not_right : a ∉ S.right := by
    intro ha_right
    have ha_sep : a ∈ S.separator := ⟨ha_left, ha_right⟩
    have ha_xyz : a = x ∨ a = y ∨ a = z := by
      have : a ∈ ({x, y, z} : Set V) := by
        simpa [hseparator] using ha_sep
      simpa [Set.mem_insert_iff] using this
    rcases ha_xyz with hax | hay | haz
    · exact ha_ne_x hax
    · exact ha_ne_y hay
    · exact ha_ne_z haz
  have hpath_neighbors_le :
      (G.neighborSet a ∩ {b : V | b ∈ F.toLinkage.pathYZ.support}).ncard <= 2 :=
    Walk.IsPath.IsChordless.neighborSet_inter_support_ncard_le_two_of_mem_internalVertices
      F.toLinkage.pathYZ_isPath hpathYZ_chordless ha
  have hpath_neighbors_lt_degree :
      (G.neighborSet a ∩ {b : V | b ∈ F.toLinkage.pathYZ.support}).ncard <
        G.degree a := by
    have hdeg := hmin_degree a
    omega
  obtain ⟨u, hu_outside, hua⟩ :=
    exists_neighbor_outside_set_of_inside_neighbors_lt_degree
      (G := G) {b : V | b ∈ F.toLinkage.pathYZ.support}
      hpath_neighbors_lt_degree
  have hu_not_pathYZ : u ∉ F.toLinkage.pathYZ.support := by
    simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hu_outside.2
  have hu_left : u ∈ S.left := by
    by_contra hu_not_left
    have hu_right : u ∈ S.right := S.mem_right_of_not_mem_left hu_not_left
    exact S.no_cross ha_left ha_not_right hu_right hu_not_left hua.symm
  rcases hcover u hu_left with hu_core | hu_path
  · exact ⟨u, hu_core, hua⟩
  · exact False.elim (hu_not_pathYZ hu_path)

theorem FoldedDuplicateLinkageDataInSet.pathYZ_vertices_adjacent_pathXComponentCore_of_left_cover
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hmin_degree : forall v : V, 4 <= G.degree v)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hy_adjacent_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h y)
    (hz_adjacent_core :
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h z) :
    forall a : V, a ∈ F.toLinkage.pathYZ.support ->
      Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h a := by
  intro a ha
  by_cases hay : a = y
  · simpa [hay] using hy_adjacent_core
  by_cases haz : a = z
  · simpa [haz] using hz_adjacent_core
  exact F.internal_pathYZ_vertices_adjacent_pathXComponentCore
    hseparator hmin_degree hpathYZ_chordless hcover ⟨ha, hay, haz⟩

/-- Replace one vertex on the left side of a separation by its unique
left-side neighbour.  The old vertex moves out of the left side and the new
vertex is added to the right side. -/
noncomputable def Separation.replaceLeftVertex
    [DecidableEq V]
    (S : Separation G) (old new : V)
    (hold_right : old ∈ S.right)
    (hnew_left : new ∈ S.left)
    (hnew_ne_old : new ≠ old)
    (hincoming : ∀ a : V, a ∈ S.left → G.Adj a old → a = new) :
    Separation G where
  left := S.left \ {old}
  right := S.right ∪ {new}
  covers := by
    ext v
    constructor
    · intro _
      exact Set.mem_univ v
    · intro _
      by_cases hvold : v = old
      · right
        left
        simpa [hvold] using hold_right
      · rcases S.mem_left_or_right v with hv_left | hv_right
        · exact Or.inl ⟨hv_left, by simpa [Set.mem_singleton_iff] using hvold⟩
        · exact Or.inr (Or.inl hv_right)
  no_cross := by
    intro a b ha ha_not_right hb hb_not_left hab
    have ha_left : a ∈ S.left := ha.1
    have ha_not_Sright : a ∉ S.right := fun ha_right =>
      ha_not_right (Or.inl ha_right)
    have ha_ne_new : a ≠ new := fun ha_new =>
      ha_not_right (Or.inr (by simp [ha_new]))
    rcases hb with hb_right | hb_new
    · by_cases hb_left : b ∈ S.left
      · have hb_eq_old : b = old := by
          by_contra hb_ne_old
          exact hb_not_left
            ⟨hb_left, by simpa [Set.mem_singleton_iff] using hb_ne_old⟩
        exact ha_ne_new
          (hincoming a ha_left (by simpa [hb_eq_old] using hab))
      · exact S.no_cross ha_left ha_not_Sright hb_right hb_left hab
    · have hb_eq_new : b = new := by simpa using hb_new
      exact hb_not_left (by
        rw [hb_eq_new]
        exact ⟨hnew_left, by simpa [Set.mem_singleton_iff] using hnew_ne_old⟩)

theorem Separation.replaceLeftVertex_separator_subset
    [DecidableEq V]
    (S : Separation G) (old new : V)
    (hold_right : old ∈ S.right)
    (hnew_left : new ∈ S.left)
    (hnew_ne_old : new ≠ old)
    (hincoming : ∀ a : V, a ∈ S.left → G.Adj a old → a = new) :
    (S.replaceLeftVertex old new hold_right hnew_left hnew_ne_old hincoming).separator ⊆
      (S.separator \ {old}) ∪ {new} := by
  intro v hv
  change v ∈ (S.left \ {old}) ∩ (S.right ∪ {new}) at hv
  rcases hv with ⟨hv_left, hv_right⟩
  rcases hv_right with hvS_right | hv_new
  · exact Or.inl ⟨⟨hv_left.1, hvS_right⟩, hv_left.2⟩
  · exact Or.inr hv_new

theorem Separation.replaceLeftVertex_proper
    [Fintype V] [DecidableEq V]
    (S : Separation G) (old new : V)
    (hold_right : old ∈ S.right)
    (hnew_left : new ∈ S.left)
    (hnew_ne_old : new ≠ old)
    (hincoming : ∀ a : V, a ∈ S.left → G.Adj a old → a = new)
    (hproper : S.Proper)
    (hleft_only_large : 2 ≤ (S.left \ S.right).ncard) :
    (S.replaceLeftVertex old new hold_right hnew_left hnew_ne_old hincoming).Proper := by
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, ha_ne_new⟩ :=
      S.exists_left_only_ne_of_two_left_only new hleft_only_large
    have ha_ne_old : a ≠ old := fun ha_old =>
      ha.2 (by simpa [ha_old] using hold_right)
    exact ⟨a,
      ⟨ha.1, by simpa [Set.mem_singleton_iff] using ha_ne_old⟩,
      by
        intro ha_right
        rcases ha_right with haS_right | ha_new
        · exact ha.2 haS_right
        · exact ha_ne_new (by simpa using ha_new)⟩
  · rcases hproper.2 with ⟨b, hb_right, hb_not_left⟩
    exact ⟨b, Or.inl hb_right, fun hb_left => hb_not_left hb_left.1⟩

theorem Separation.orderAtMost_three_of_separator_subset_triple
    [Fintype V] [DecidableEq V]
    (S : Separation G) {a b c : V}
    (hsub : S.separator ⊆ ({a, b, c} : Set V)) :
    S.OrderAtMost 3 := by
  have hpair_card : ({b, c} : Set V).ncard ≤ 2 := by
    calc
      ({b, c} : Set V).ncard ≤ ({c} : Set V).ncard + 1 := by
        simpa using Set.ncard_insert_le b ({c} : Set V)
      _ = 2 := by simp
  have htriple_card : ({a, b, c} : Set V).ncard ≤ 3 := by
    calc
      ({a, b, c} : Set V).ncard ≤ ({b, c} : Set V).ncard + 1 :=
        Set.ncard_insert_le a ({b, c} : Set V)
      _ ≤ 3 := by omega
  exact S.orderAtMost_of_separator_ncard_le
    (le_trans (Set.ncard_le_ncard hsub) htriple_card)

theorem FoldedDuplicateLinkageDataInSet.left_neighbor_of_y_eq_pathYZ_snd_of_no_y_adjacent_core
    [DecidableEq V]
    {S : Separation G} {root v1 x y z u : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_y_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h y))
    (hu_left : u ∈ S.left)
    (huy : G.Adj u y) :
    u = F.toLinkage.pathYZ.snd := by
  classical
  have hnot_nil : Not F.toLinkage.pathYZ.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := F.toLinkage.pathYZ) hyz
  rcases hcover u hu_left with hu_core | hu_path
  · exact False.elim (hno_y_adjacent_core u hu_core huy)
  · have hy_path : y ∈ F.toLinkage.pathYZ.support :=
      F.toLinkage.pathYZ.start_mem_support
    have htoSubgraph : F.toLinkage.pathYZ.toSubgraph.Adj y u :=
      Walk.IsChordless.toSubgraph_adj_of_adj hpathYZ_chordless
        hy_path hu_path huy.symm
    have hneighbor : u ∈ F.toLinkage.pathYZ.toSubgraph.neighborSet y := by
      simpa [SimpleGraph.Subgraph.mem_neighborSet] using htoSubgraph
    have hsnd := F.toLinkage.pathYZ_isPath.neighborSet_toSubgraph_startpoint hnot_nil
    rw [hsnd] at hneighbor
    simpa using hneighbor

theorem FoldedDuplicateLinkageDataInSet.left_neighbor_of_z_eq_pathYZ_penultimate_of_no_z_adjacent_core
    [DecidableEq V]
    {S : Separation G} {root v1 x y z u : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_z_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h z))
    (hu_left : u ∈ S.left)
    (huz : G.Adj u z) :
    u = F.toLinkage.pathYZ.penultimate := by
  classical
  have hnot_nil : Not F.toLinkage.pathYZ.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := F.toLinkage.pathYZ) hyz
  rcases hcover u hu_left with hu_core | hu_path
  · exact False.elim (hno_z_adjacent_core u hu_core huz)
  · have hz_path : z ∈ F.toLinkage.pathYZ.support :=
      F.toLinkage.pathYZ.end_mem_support
    have htoSubgraph : F.toLinkage.pathYZ.toSubgraph.Adj z u :=
      Walk.IsChordless.toSubgraph_adj_of_adj hpathYZ_chordless
        hz_path hu_path huz.symm
    have hneighbor : u ∈ F.toLinkage.pathYZ.toSubgraph.neighborSet z := by
      simpa [SimpleGraph.Subgraph.mem_neighborSet] using htoSubgraph
    have hpen := F.toLinkage.pathYZ_isPath.neighborSet_toSubgraph_endpoint hnot_nil
    rw [hpen] at hneighbor
    simpa using hneighbor

noncomputable def FoldedDuplicateLinkageDataInSet.endpointYReplacementSeparation
    [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_y_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h y)) :
    Separation G := by
  have hnot_nil : Not F.toLinkage.pathYZ.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := F.toLinkage.pathYZ) hyz
  apply S.replaceLeftVertex y F.toLinkage.pathYZ.snd
  · exact (S.triple_vertices_mem_right hseparator).2.1
  · exact F.pathYZ_support_subset_set F.toLinkage.pathYZ.snd
      (List.mem_of_mem_tail
        (SimpleGraph.Walk.snd_mem_tail_support hnot_nil))
  · exact (F.toLinkage.pathYZ.adj_snd hnot_nil).ne.symm
  · intro a ha_left hay
    exact F.left_neighbor_of_y_eq_pathYZ_snd_of_no_y_adjacent_core
      hyz hpathYZ_chordless hcover hno_y_adjacent_core ha_left hay

theorem FoldedDuplicateLinkageDataInSet.endpointYReplacementSeparation_separator_subset
    [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_y_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h y)) :
    (F.endpointYReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_y_adjacent_core).separator ⊆
      ({x, z, F.toLinkage.pathYZ.snd} : Set V) := by
  intro v hv
  change
    v ∈ (S.left \ {y}) ∩
      (S.right ∪ {F.toLinkage.pathYZ.snd}) at hv
  rcases hv with ⟨hv_left, hv_right⟩
  have hvS_left : v ∈ S.left := hv_left.1
  have hv_ne_y : v ≠ y := by
    intro hvy
    exact hv_left.2 (by simpa [Set.mem_singleton_iff] using hvy)
  rcases hv_right with hvS_right | hv_snd
  · have hv_sep : v ∈ S.separator := ⟨hvS_left, hvS_right⟩
    have hv_tri : v = x ∨ v = y ∨ v = z := by
      have : v ∈ ({x, y, z} : Set V) := by
        simpa [hseparator] using hv_sep
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hv_tri with rfl | rfl | rfl
    · simp
    · exact False.elim (hv_ne_y rfl)
    · simp
  · have hv_eq_snd : v = F.toLinkage.pathYZ.snd := by
      simpa using hv_snd
    simp [hv_eq_snd]

theorem FoldedDuplicateLinkageDataInSet.endpointYReplacementSeparation_orderAtMost_three
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_y_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h y)) :
    (F.endpointYReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_y_adjacent_core).OrderAtMost 3 := by
  classical
  let T :=
    F.endpointYReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_y_adjacent_core
  have hsub :
      T.separator ⊆ ({x, z, F.toLinkage.pathYZ.snd} : Set V) := by
    simpa [T] using
      F.endpointYReplacementSeparation_separator_subset
        hseparator hyz hpathYZ_chordless hcover hno_y_adjacent_core
  exact T.orderAtMost_three_of_separator_subset_triple hsub

theorem FoldedDuplicateLinkageDataInSet.endpointYReplacementSeparation_proper
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_y_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h y))
    (hproper : S.Proper)
    (hleft_only_large : 2 <= (S.left \ S.right).ncard) :
    (F.endpointYReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_y_adjacent_core).Proper := by
  have hnot_nil : Not F.toLinkage.pathYZ.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := F.toLinkage.pathYZ) hyz
  exact S.replaceLeftVertex_proper y F.toLinkage.pathYZ.snd
    (S.triple_vertices_mem_right hseparator).2.1
    (F.pathYZ_support_subset_set F.toLinkage.pathYZ.snd
      (List.mem_of_mem_tail
        (SimpleGraph.Walk.snd_mem_tail_support hnot_nil)))
    (F.toLinkage.pathYZ.adj_snd hnot_nil).ne.symm
    (fun a ha_left hay =>
      F.left_neighbor_of_y_eq_pathYZ_snd_of_no_y_adjacent_core
        hyz hpathYZ_chordless hcover hno_y_adjacent_core ha_left hay)
    hproper hleft_only_large

noncomputable def FoldedDuplicateLinkageDataInSet.endpointZReplacementSeparation
    [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_z_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h z)) :
    Separation G := by
  have hnot_nil : Not F.toLinkage.pathYZ.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := F.toLinkage.pathYZ) hyz
  apply S.replaceLeftVertex z F.toLinkage.pathYZ.penultimate
  · exact (S.triple_vertices_mem_right hseparator).2.2
  · exact F.pathYZ_support_subset_set F.toLinkage.pathYZ.penultimate
      (List.mem_of_mem_dropLast
        (SimpleGraph.Walk.penultimate_mem_dropLast_support hnot_nil))
  · exact (F.toLinkage.pathYZ.adj_penultimate hnot_nil).ne
  · intro a ha_left haz
    exact F.left_neighbor_of_z_eq_pathYZ_penultimate_of_no_z_adjacent_core
      hyz hpathYZ_chordless hcover hno_z_adjacent_core ha_left haz

theorem FoldedDuplicateLinkageDataInSet.endpointZReplacementSeparation_separator_subset
    [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_z_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h z)) :
    (F.endpointZReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_z_adjacent_core).separator ⊆
      ({x, y, F.toLinkage.pathYZ.penultimate} : Set V) := by
  intro v hv
  change
    v ∈ (S.left \ {z}) ∩
      (S.right ∪ {F.toLinkage.pathYZ.penultimate}) at hv
  rcases hv with ⟨hv_left, hv_right⟩
  have hvS_left : v ∈ S.left := hv_left.1
  have hv_ne_z : v ≠ z := by
    intro hvz
    exact hv_left.2 (by simpa [Set.mem_singleton_iff] using hvz)
  rcases hv_right with hvS_right | hv_penultimate
  · have hv_sep : v ∈ S.separator := ⟨hvS_left, hvS_right⟩
    have hv_tri : v = x ∨ v = y ∨ v = z := by
      have : v ∈ ({x, y, z} : Set V) := by
        simpa [hseparator] using hv_sep
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hv_tri with rfl | rfl | rfl
    · simp
    · simp
    · exact False.elim (hv_ne_z rfl)
  · have hv_eq_penultimate : v = F.toLinkage.pathYZ.penultimate := by
      simpa using hv_penultimate
    simp [hv_eq_penultimate]

theorem FoldedDuplicateLinkageDataInSet.endpointZReplacementSeparation_orderAtMost_three
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_z_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h z)) :
    (F.endpointZReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_z_adjacent_core).OrderAtMost 3 := by
  classical
  let T :=
    F.endpointZReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_z_adjacent_core
  have hsub :
      T.separator ⊆ ({x, y, F.toLinkage.pathYZ.penultimate} : Set V) := by
    simpa [T] using
      F.endpointZReplacementSeparation_separator_subset
        hseparator hyz hpathYZ_chordless hcover hno_z_adjacent_core
  exact T.orderAtMost_three_of_separator_subset_triple hsub

theorem FoldedDuplicateLinkageDataInSet.endpointZReplacementSeparation_proper
    [Fintype V] [DecidableEq V]
    {S : Separation G} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G S.left root v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hcover :
      forall b : V, b ∈ S.left ->
        b ∈ F.pathXComponentCore.verts ∨
          b ∈ F.toLinkage.pathYZ.support)
    (hno_z_adjacent_core :
      forall h : V, h ∈ F.pathXComponentCore.verts -> Not (G.Adj h z))
    (hproper : S.Proper)
    (hleft_only_large : 2 <= (S.left \ S.right).ncard) :
    (F.endpointZReplacementSeparation hseparator hyz hpathYZ_chordless
      hcover hno_z_adjacent_core).Proper := by
  have hnot_nil : Not F.toLinkage.pathYZ.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := F.toLinkage.pathYZ) hyz
  exact S.replaceLeftVertex_proper z F.toLinkage.pathYZ.penultimate
    (S.triple_vertices_mem_right hseparator).2.2
    (F.pathYZ_support_subset_set F.toLinkage.pathYZ.penultimate
      (List.mem_of_mem_dropLast
        (SimpleGraph.Walk.penultimate_mem_dropLast_support hnot_nil)))
    (F.toLinkage.pathYZ.adj_penultimate hnot_nil).ne
    (fun a ha_left haz =>
      F.left_neighbor_of_z_eq_pathYZ_penultimate_of_no_z_adjacent_core
        hyz hpathYZ_chordless hcover hno_z_adjacent_core ha_left haz)
    hproper hleft_only_large

noncomputable def FoldedDuplicateLinkageDataInSet.ofDuplicatePaths
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some x))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some z))
    (hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support})
    (hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hX_left :
      forall o : Option V, o ∈ pXdup.support ->
        o ∈ duplicateVertexSeparationLeft S)
    (hY_left :
      forall o : Option V, o ∈ pYdup.support ->
        o ∈ duplicateVertexSeparationLeft S)
    (hZ_left :
      forall o : Option V, o ∈ pZdup.support ->
        o ∈ duplicateVertexSeparationLeft S) :
    FoldedDuplicateLinkageDataInSet G S.left root v1 x y z := by
  classical
  let fold := duplicateVertexFoldHom G root
  let wX : G.Walk v1 x := pXdup.map fold
  let wYZ : G.Walk y z := (pYdup.map fold).reverse.append (pZdup.map fold)
  let F : FoldedDuplicateLinkageData G root v1 x y z :=
    FoldedDuplicateLinkageData.ofDuplicatePaths
      (G := G) (root := root) pXdup pYdup pZdup hXY hXZ hYZ
  refine {
    toLinkage := F
    pathX_support_subset_set := ?_
    pathYZ_support_subset_set := ?_
  }
  · intro a ha
    have ha_wX : a ∈ wX.support :=
      SimpleGraph.Walk.support_toPath_subset wX (by
        simpa [F, FoldedDuplicateLinkageData.ofDuplicatePaths, wX, fold] using ha)
    change a ∈ (pXdup.map (duplicateVertexFoldHom G root)).support at ha_wX
    have hfold := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pXdup) (x := a)).mp ha_wX
    rcases hfold with hsome | ⟨haroot, hnone⟩
    · have hleft := hX_left (some a) hsome
      simpa [duplicateVertexSeparationLeft] using hleft
    · simpa [haroot] using hroot_left
  · intro a ha
    have ha_wYZ : a ∈ wYZ.support :=
      SimpleGraph.Walk.support_toPath_subset wYZ (by
        simpa [F, FoldedDuplicateLinkageData.ofDuplicatePaths, wYZ, fold] using ha)
    have ha_split :
        a ∈ (pYdup.map fold).support ∨
          a ∈ (pZdup.map fold).support := by
      change a ∈ ((pYdup.map fold).reverse.append (pZdup.map fold)).support at ha_wYZ
      rw [SimpleGraph.Walk.mem_support_append_iff] at ha_wYZ
      rcases ha_wYZ with haY | haZ
      · left
        simpa [SimpleGraph.Walk.support_reverse] using haY
      · exact Or.inr haZ
    rcases ha_split with haY | haZ
    · have hfold := (duplicateVertexFoldHom_mem_support_iff
        (G := G) (root := root) (p := pYdup) (x := a)).mp (by
          change a ∈ (pYdup.map (duplicateVertexFoldHom G root)).support at haY
          exact haY)
      rcases hfold with hsome | ⟨haroot, _hnone⟩
      · have hleft := hY_left (some a) hsome
        simpa [duplicateVertexSeparationLeft] using hleft
      · simpa [haroot] using hroot_left
    · have hfold := (duplicateVertexFoldHom_mem_support_iff
        (G := G) (root := root) (p := pZdup) (x := a)).mp (by
          change a ∈ (pZdup.map (duplicateVertexFoldHom G root)).support at haZ
          exact haZ)
      rcases hfold with hsome | ⟨haroot, _hnone⟩
      · have hleft := hZ_left (some a) hsome
        simpa [duplicateVertexSeparationLeft] using hleft
      · simpa [haroot] using hroot_left

noncomputable def FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExact
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some x))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some z))
    (hpXdup : pXdup.IsPath)
    (hpYdup : pYdup.IsPath)
    (hpZdup : pZdup.IsPath)
    (hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support})
    (hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hX_left :
      forall o : Option V, o ∈ pXdup.support ->
        o ∈ duplicateVertexSeparationLeft S)
    (hY_left :
      forall o : Option V, o ∈ pYdup.support ->
        o ∈ duplicateVertexSeparationLeft S)
    (hZ_left :
      forall o : Option V, o ∈ pZdup.support ->
        o ∈ duplicateVertexSeparationLeft S) :
    FoldedDuplicateLinkageDataInSet G S.left root v1 x y z := by
  classical
  let fold := duplicateVertexFoldHom G root
  let F : FoldedDuplicateLinkageData G root v1 x y z :=
    FoldedDuplicateLinkageData.ofDuplicatePathsExact
      (G := G) (root := root) pXdup pYdup pZdup
      hpXdup hpYdup hpZdup hXY hXZ hYZ
  refine {
    toLinkage := F
    pathX_support_subset_set := ?_
    pathYZ_support_subset_set := ?_
  }
  · intro a ha
    change a ∈ (pXdup.map (duplicateVertexFoldHom G root)).support at ha
    have hfold := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pXdup) (x := a)).mp ha
    rcases hfold with hsome | ⟨haroot, _hnone⟩
    · have hleft := hX_left (some a) hsome
      simpa [duplicateVertexSeparationLeft] using hleft
    · simpa [haroot] using hroot_left
  · intro a ha
    have ha_split :
        a ∈ (pYdup.map fold).support ∨
          a ∈ (pZdup.map fold).support := by
      change a ∈ ((pYdup.map fold).reverse.append (pZdup.map fold)).support at ha
      rw [SimpleGraph.Walk.mem_support_append_iff] at ha
      rcases ha with haY | haZ
      · left
        simpa [SimpleGraph.Walk.support_reverse] using haY
      · exact Or.inr haZ
    rcases ha_split with haY | haZ
    · have hfold := (duplicateVertexFoldHom_mem_support_iff
        (G := G) (root := root) (p := pYdup) (x := a)).mp (by
          change a ∈ (pYdup.map (duplicateVertexFoldHom G root)).support at haY
          exact haY)
      rcases hfold with hsome | ⟨haroot, _hnone⟩
      · have hleft := hY_left (some a) hsome
        simpa [duplicateVertexSeparationLeft] using hleft
      · simpa [haroot] using hroot_left
    · have hfold := (duplicateVertexFoldHom_mem_support_iff
        (G := G) (root := root) (p := pZdup) (x := a)).mp (by
          change a ∈ (pZdup.map (duplicateVertexFoldHom G root)).support at haZ
          exact haZ)
      rcases hfold with hsome | ⟨haroot, _hnone⟩
      · have hleft := hZ_left (some a) hsome
        simpa [duplicateVertexSeparationLeft] using hleft
      · simpa [haroot] using hroot_left

theorem FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExact_root_mem_pathYZ
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some x))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some z))
    (hpXdup : pXdup.IsPath)
    (hpYdup : pYdup.IsPath)
    (hpZdup : pZdup.IsPath)
    (hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support})
    (hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hX_left :
      forall o : Option V, o ∈ pXdup.support ->
        o ∈ duplicateVertexSeparationLeft S)
    (hY_left :
      forall o : Option V, o ∈ pYdup.support ->
        o ∈ duplicateVertexSeparationLeft S)
    (hZ_left :
      forall o : Option V, o ∈ pZdup.support ->
        o ∈ duplicateVertexSeparationLeft S) :
    root ∈
      (FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExact
        (G := G) S hroot_left pXdup pYdup pZdup
        hpXdup hpYdup hpZdup hXY hXZ hYZ hX_left hY_left hZ_left).toLinkage.pathYZ.support := by
  simpa [FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExact] using
    FoldedDuplicateLinkageData.ofDuplicatePathsExact_root_mem_pathYZ
      (G := G) (root := root) pXdup pYdup pZdup
      hpXdup hpYdup hpZdup hXY hXZ hYZ


end Schematic.Math.GraphTheory
