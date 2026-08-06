import Schematic.Math.GraphTheory.PathsTrees.Operations.TreePaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
theorem Subgraph.spanning_subgraph_nontrivial_of_ncard_ge_two
    [Fintype V]
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_spanning : T.IsSpanning)
    (hB_large : 2 <= B.verts.ncard) :
    Nontrivial T.verts := by
  classical
  have hB_one_lt : 1 < B.verts.ncard := by omega
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Set.one_lt_ncard_iff (s := B.verts)).mp hB_one_lt
  refine ⟨⟨⟨a, ha⟩, hT_spanning ⟨a, ha⟩⟩,
    ⟨⟨b, hb⟩, hT_spanning ⟨b, hb⟩⟩, ?_⟩
  intro h
  exact hab (by
    have hval :=
      congrArg (fun x : T.verts => ((x : B.verts) : V)) h
    simpa using hval)

theorem Subgraph.spanning_subgraph_nontrivial_of_ncard_ge_three
    [Fintype V]
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_spanning : T.IsSpanning)
    (hB_large : 3 <= B.verts.ncard) :
    Nontrivial T.verts := by
  exact Subgraph.spanning_subgraph_nontrivial_of_ncard_ge_two
    hT_spanning (by omega)

theorem Subgraph.spanning_tree_delete_degree_one_tree_vertex_connected
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    (vT : T.verts)
    [Fintype (T.coe.neighborSet vT)]
    (hdegree : T.coe.degree vT = 1) :
    (B.deleteVerts ({((vT : B.verts) : V)} : Set V)).coe.Connected := by
  classical
  have hdelete_tree_connected :
      (T.coe.induce ({vT} : Set T.verts)ᶜ).Connected :=
    hT_connected.induce_compl_singleton_of_degree_eq_one (v := vT) hdegree
  let f : (T.coe.induce ({vT} : Set T.verts)ᶜ) →g
      (B.deleteVerts ({((vT : B.verts) : V)} : Set V)).coe := {
    toFun := fun x => by
      refine ⟨((x : T.verts) : B.verts), ?_⟩
      rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
      refine ⟨((x : T.verts) : B.verts).2, ?_⟩
      intro hxv
      have hxT_eq : (x : T.verts) = vT := by
        apply Subtype.ext
        apply Subtype.ext
        exact Set.mem_singleton_iff.mp hxv
      exact x.2 hxT_eq
    map_rel' := by
      intro x y hxy
      change (B.deleteVerts ({((vT : B.verts) : V)} : Set V)).Adj
        (((x : T.verts) : B.verts) : V)
        (((y : T.verts) : B.verts) : V)
      rw [SimpleGraph.Subgraph.deleteVerts_adj]
      refine ⟨((x : T.verts) : B.verts).2, ?_, ((y : T.verts) : B.verts).2, ?_, ?_⟩
      · intro hxv
        have hxT_eq : (x : T.verts) = vT := by
          apply Subtype.ext
          apply Subtype.ext
          exact Set.mem_singleton_iff.mp hxv
        exact x.2 hxT_eq
      · intro hyv
        have hyT_eq : (y : T.verts) = vT := by
          apply Subtype.ext
          apply Subtype.ext
          exact Set.mem_singleton_iff.mp hyv
        exact y.2 hyT_eq
      · exact T.adj_sub hxy }
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨yBdel, hyBdel⟩
    let yB : B.verts := ⟨(yBdel : V), by
      rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hyBdel
      exact hyBdel.1⟩
    have hy_ne_v : (yB : V) ≠ ((vT : B.verts) : V) := by
      rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hyBdel
      intro h
      exact hyBdel.2 (by simpa [h])
    let yT : T.verts := ⟨yB, hT_spanning yB⟩
    have hyT_ne : yT ∈ ({vT} : Set T.verts)ᶜ := by
      intro hy_eq
      exact hy_ne_v (by
        have hval := congrArg (fun x : T.verts => ((x : B.verts) : V)) hy_eq
        simpa [yT, yB] using hval)
    refine ⟨⟨yT, hyT_ne⟩, ?_⟩
    apply Subtype.ext
    rfl
  exact SimpleGraph.Connected.map f hf_surj hdelete_tree_connected

theorem Subgraph.spanning_tree_delete_degree_one_vertex_connected
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {v : V}
    (hvB : v ∈ B.verts)
    [Fintype (T.coe.neighborSet
      (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts))]
    (hdegree :
      T.coe.degree
        (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts) = 1) :
    (B.deleteVerts ({v} : Set V)).coe.Connected := by
  let vB : B.verts := ⟨v, hvB⟩
  let vT : T.verts := ⟨vB, hT_spanning vB⟩
  simpa [vT, vB] using
    Subgraph.spanning_tree_delete_degree_one_tree_vertex_connected
      (G := G) hT_connected hT_spanning vT (by
        simpa [vT, vB] using hdegree)

theorem Subgraph.spanning_tree_degree_one_of_subgraph_degree_one
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    [Nontrivial T.verts]
    {v : V}
    (hvB : v ∈ B.verts)
    [Fintype (B.coe.neighborSet (⟨v, hvB⟩ : B.verts))]
    [Fintype (T.neighborSet (⟨v, hvB⟩ : B.verts))]
    [Fintype (T.coe.neighborSet
      (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts))]
    (hdegreeB : B.coe.degree (⟨v, hvB⟩ : B.verts) = 1) :
    T.coe.degree
        (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts) = 1 := by
  classical
  let vB : B.verts := ⟨v, hvB⟩
  let vT : T.verts := ⟨vB, hT_spanning vB⟩
  have hpos : 0 < T.coe.degree vT :=
    hT_connected.preconnected.degree_pos_of_nontrivial vT
  have hle : T.degree vB <= B.coe.degree vB :=
    SimpleGraph.Subgraph.degree_le T vB
  have hcoe : T.coe.degree vT = T.degree vB := by
    simp [vT]
  have hleT : T.degree vB <= 1 := by
    rw [hdegreeB] at hle
    exact hle
  have hle' : T.coe.degree vT <= 1 := by
    rw [hcoe]
    exact hleT
  change T.coe.degree vT = 1
  exact Nat.le_antisymm hle' hpos

theorem Subgraph.spanning_tree_terminal_degrees_one_of_subgraph_neighbor_ncard_one
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    {ι : Type*}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    [Fintype T.verts]
    [DecidableRel T.coe.Adj]
    [Nontrivial T.verts]
    (terminal : ι -> B.verts)
    (hB_neighbor_finite :
      forall i : ι, Fintype (B.coe.neighborSet (terminal i)))
    (hT_neighbor_finite :
      forall i : ι, Fintype (T.neighborSet (terminal i)))
    (hB_terminal_neighbor_ncard :
      forall i : ι, (B.coe.neighborSet (terminal i)).ncard = 1) :
    forall i : ι,
      T.coe.degree (⟨terminal i, hT_spanning (terminal i)⟩ : T.verts) = 1 := by
  intro i
  letI : Fintype (B.coe.neighborSet (terminal i)) := hB_neighbor_finite i
  letI : Fintype (T.neighborSet (terminal i)) := hT_neighbor_finite i
  have hdegreeB : B.coe.degree (terminal i) = 1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    rw [Set.fintypeCard_eq_ncard]
    exact hB_terminal_neighbor_ncard i
  simpa using
    Subgraph.spanning_tree_degree_one_of_subgraph_degree_one
      (B := B) (T := T) hT_connected hT_spanning
      (terminal i).2 hdegreeB

theorem Subgraph.Connected.exists_minimal_connected_subgraph_containing
    [Fintype V]
    {B : G.Subgraph}
    (hB : B.coe.Connected)
    {ι : Type*}
    (terminal : ι -> V)
    (hterminal : forall i : ι, terminal i ∈ B.verts) :
    Exists fun T : G.Subgraph =>
      T ≤ B ∧
        T.coe.Connected ∧
          (forall i : ι, terminal i ∈ T.verts) ∧
            forall T' : G.Subgraph,
              T' ≤ B ->
                T'.coe.Connected ->
                  (forall i : ι, terminal i ∈ T'.verts) ->
                    T'.verts ⊆ T.verts ->
                      T.verts ⊆ T'.verts := by
  classical
  let P : Nat -> Prop := fun n =>
    Exists fun T : G.Subgraph =>
      T ≤ B ∧ T.coe.Connected ∧
        (forall i : ι, terminal i ∈ T.verts) ∧ T.verts.ncard = n
  have hP : Exists P := by
    exact ⟨B.verts.ncard, B, le_rfl, hB, hterminal, rfl⟩
  obtain ⟨T, hTB, hT_connected, hT_terminal, hT_card⟩ := Nat.find_spec hP
  refine ⟨T, hTB, hT_connected, hT_terminal, ?_⟩
  intro T' hT'B hT'_connected hT'_terminal hT'_subset
  have hT_card_le : T.verts.ncard <= T'.verts.ncard := by
    rw [hT_card]
    exact Nat.find_min' hP
      ⟨T', hT'B, hT'_connected, hT'_terminal, rfl⟩
  have hverts_eq : T'.verts = T.verts :=
    Set.eq_of_subset_of_ncard_le hT'_subset hT_card_le
  exact hverts_eq.symm.subset

theorem Subgraph.connected_subgraph_terminal_neighbor_ncard_one_of_le
    [Fintype V]
    [DecidableRel G.Adj]
    {C B : G.Subgraph}
    {terminal : Fin 3 -> V}
    (hBC : B ≤ C)
    (hB_connected : B.coe.Connected)
    (hterminal_injective : Function.Injective terminal)
    (hterminal_B : forall i : Fin 3, terminal i ∈ B.verts)
    (hC_terminal_neighbor_ncard :
      forall i : Fin 3, (C.neighborSet (terminal i)).ncard = 1) :
    forall i : Fin 3,
      (B.coe.neighborSet (⟨terminal i, hterminal_B i⟩ : B.verts)).ncard = 1 := by
  classical
  have hB_nontrivial : Nontrivial B.verts := by
    let f0 : B.verts := ⟨terminal 0, hterminal_B 0⟩
    let f1 : B.verts := ⟨terminal 1, hterminal_B 1⟩
    refine ⟨⟨f0, f1, ?_⟩⟩
    intro h
    have hterminal : terminal 0 = terminal 1 := by
      have hval := congrArg (fun x : B.verts => (x : V)) h
      simpa [f0, f1] using hval
    exact (by decide : (0 : Fin 3) ≠ 1) (hterminal_injective hterminal)
  letI : Nontrivial B.verts := hB_nontrivial
  intro i
  let vB : B.verts := ⟨terminal i, hterminal_B i⟩
  have hpos_coe : 0 < B.coe.degree vB :=
    hB_connected.preconnected.degree_pos_of_nontrivial vB
  have hcoe_degree :
      B.coe.degree vB = B.degree (terminal i) := by
    simp [vB]
  have hpos : 0 < B.degree (terminal i) := by
    rwa [hcoe_degree] at hpos_coe
  have hCdegree_ncard :
      (C.neighborSet (terminal i)).ncard = C.degree (terminal i) := by
    simp [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
  have hCdegree : C.degree (terminal i) = 1 := by
    rw [← hCdegree_ncard]
    exact hC_terminal_neighbor_ncard i
  have hle : B.degree (terminal i) <= C.degree (terminal i) :=
    SimpleGraph.Subgraph.degree_le' B C hBC (terminal i)
  have hBdegree : B.degree (terminal i) = 1 := by
    rw [hCdegree] at hle
    omega
  have hBdegree_ncard :
      (B.neighborSet (terminal i)).ncard = B.degree (terminal i) := by
    simp [SimpleGraph.Subgraph.degree, Set.ncard_eq_toFinset_card']
  have hcoe_ncard :
      (B.coe.neighborSet vB).ncard =
        (B.neighborSet (terminal i)).ncard := by
    rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
    exact Fintype.card_congr (SimpleGraph.Subgraph.coeNeighborSetEquiv vB)
  rw [hcoe_ncard, hBdegree_ncard, hBdegree]

theorem Subgraph.minimal_connected_subgraph_delete_nonterminal_not_connected
    {C B : G.Subgraph}
    {ι : Type*}
    {terminal : ι -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : ι, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : ι, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {v : V}
    (hvB : v ∈ B.verts)
    (hv_not_terminal : forall i : ι, terminal i ≠ v) :
    Not ((B.deleteVerts ({v} : Set V)).coe.Connected) := by
  intro hdelete_connected
  have hdelete_le_C : B.deleteVerts ({v} : Set V) ≤ C :=
    le_trans (SimpleGraph.Subgraph.deleteVerts_le (G' := B) (s := ({v} : Set V))) hBC
  have hterminal_delete :
      forall i : ι, terminal i ∈ (B.deleteVerts ({v} : Set V)).verts := by
    intro i
    rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff]
    exact ⟨hB_terminal i, by
      intro hmem
      exact hv_not_terminal i (Set.mem_singleton_iff.mp hmem)⟩
  have hdelete_subset_B :
      (B.deleteVerts ({v} : Set V)).verts ⊆ B.verts :=
    (SimpleGraph.Subgraph.deleteVerts_le (G' := B) (s := ({v} : Set V))).left
  have hB_subset_delete :
      B.verts ⊆ (B.deleteVerts ({v} : Set V)).verts :=
    hB_minimal (B.deleteVerts ({v} : Set V)) hdelete_le_C hdelete_connected
      hterminal_delete hdelete_subset_B
  have hv_delete : v ∈ (B.deleteVerts ({v} : Set V)).verts :=
    hB_subset_delete hvB
  rw [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_diff] at hv_delete
  exact hv_delete.2 (by simp)

theorem Subgraph.minimal_connected_spanning_tree_nonterminal_degree_ne_one
    {C B : G.Subgraph}
    {ι : Type*}
    {terminal : ι -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : ι, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : ι, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {v : V}
    (hvB : v ∈ B.verts)
    [Fintype (T.coe.neighborSet
      (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts))]
    (hv_not_terminal : forall i : ι, terminal i ≠ v) :
    T.coe.degree
        (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts) ≠ 1 := by
  intro hdegree
  have hdelete_not_connected :
      Not ((B.deleteVerts ({v} : Set V)).coe.Connected) :=
    Subgraph.minimal_connected_subgraph_delete_nonterminal_not_connected
      hBC hB_terminal hB_minimal hvB hv_not_terminal
  exact hdelete_not_connected
      (Subgraph.spanning_tree_delete_degree_one_vertex_connected
        (B := B) (T := T) hT_connected hT_spanning hvB hdegree)

theorem Subgraph.minimal_connected_spanning_tree_leaf_mem_terminal_range
    {C B : G.Subgraph}
    {ι : Type*}
    {terminal : ι -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : ι, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : ι, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {v : V}
    (hvB : v ∈ B.verts)
    [Fintype (T.coe.neighborSet
      (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts))]
    (hdegree :
      T.coe.degree
        (⟨(⟨v, hvB⟩ : B.verts), hT_spanning (⟨v, hvB⟩ : B.verts)⟩ : T.verts) = 1) :
    v ∈ Set.range terminal := by
  classical
  by_contra hv_not_range
  have hv_not_terminal : forall i : ι, terminal i ≠ v := by
    intro i hi
    exact hv_not_range ⟨i, hi⟩
  exact
    (Subgraph.minimal_connected_spanning_tree_nonterminal_degree_ne_one
      hBC hB_terminal hB_minimal hT_connected hT_spanning hvB
      hv_not_terminal) hdegree

theorem Subgraph.minimal_connected_spanning_tree_tree_vertex_nonterminal_degree_ne_one
    {C B : G.Subgraph}
    {ι : Type*}
    {terminal : ι -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : ι, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : ι, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    (vT : T.verts)
    [Fintype (T.coe.neighborSet vT)]
    (hv_not_terminal : forall i : ι, terminal i ≠ ((vT : B.verts) : V)) :
    T.coe.degree vT ≠ 1 := by
  intro hdegree
  have hvB : ((vT : B.verts) : V) ∈ B.verts := (vT : B.verts).2
  have hdelete_not_connected :
      Not ((B.deleteVerts ({((vT : B.verts) : V)} : Set V)).coe.Connected) :=
    Subgraph.minimal_connected_subgraph_delete_nonterminal_not_connected
      hBC hB_terminal hB_minimal hvB hv_not_terminal
  exact hdelete_not_connected
    (Subgraph.spanning_tree_delete_degree_one_tree_vertex_connected
      (B := B) (T := T) hT_connected hT_spanning vT hdegree)

theorem Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
    {C B : G.Subgraph}
    {ι : Type*}
    {terminal : ι -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : ι, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : ι, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    (vT : T.verts)
    [Fintype (T.coe.neighborSet vT)]
    (hdegree : T.coe.degree vT = 1) :
    ((vT : B.verts) : V) ∈ Set.range terminal := by
  classical
  by_contra hv_not_range
  have hv_not_terminal : forall i : ι, terminal i ≠ ((vT : B.verts) : V) := by
    intro i hi
    exact hv_not_range ⟨i, hi⟩
  exact
    (Subgraph.minimal_connected_spanning_tree_tree_vertex_nonterminal_degree_ne_one
      hBC hB_terminal hB_minimal hT_connected hT_spanning vT
      hv_not_terminal) hdegree

theorem Subgraph.minimal_connected_spanning_tree_exists_two_terminal_leaves
    {C B : G.Subgraph}
    {ι : Type*}
    {terminal : ι -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : ι, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : ι, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    [Fintype T.verts]
    [DecidableRel T.coe.Adj]
    [Nontrivial T.verts]
    (hT_tree : T.coe.IsTree)
    (hT_spanning : T.IsSpanning) :
    Exists fun uT : T.verts =>
      Exists fun vT : T.verts =>
        uT ≠ vT ∧
          T.coe.degree uT = 1 ∧
            T.coe.degree vT = 1 ∧
              ((uT : B.verts) : V) ∈ Set.range terminal ∧
                ((vT : B.verts) : V) ∈ Set.range terminal := by
  classical
  obtain ⟨uT, vT, huv, hu_degree, hv_degree⟩ :=
    IsTree.exists_two_distinct_degree_one_of_nontrivial
      (G := T.coe) hT_tree
  have hu_degree' :
      @SimpleGraph.degree T.verts T.coe uT (SimpleGraph.Subgraph.coeFiniteAt uT) = 1 := by
    simpa [Subsingleton.elim
      (Subtype.fintype (Membership.mem (T.coe.neighborSet uT)))
      (SimpleGraph.Subgraph.coeFiniteAt uT)] using hu_degree
  have hv_degree' :
      @SimpleGraph.degree T.verts T.coe vT (SimpleGraph.Subgraph.coeFiniteAt vT) = 1 := by
    simpa [Subsingleton.elim
      (Subtype.fintype (Membership.mem (T.coe.neighborSet vT)))
      (SimpleGraph.Subgraph.coeFiniteAt vT)] using hv_degree
  have hu_range :
      ((uT : B.verts) : V) ∈ Set.range terminal :=
    Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
      hBC hB_terminal hB_minimal hT_tree.connected hT_spanning uT hu_degree'
  have hv_range :
      ((vT : B.verts) : V) ∈ Set.range terminal :=
    Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
      hBC hB_terminal hB_minimal hT_tree.connected hT_spanning vT hv_degree'
  exact ⟨uT, vT, huv, hu_degree, hv_degree, hu_range, hv_range⟩

theorem Subgraph.minimal_connected_spanning_tree_card_degree_ge_three_le_two_of_four_terminals
    {C B : G.Subgraph}
    {terminal : Fin 4 -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : Fin 4, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : Fin 4, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    [Fintype T.verts]
    [DecidableRel T.coe.Adj]
    [Nontrivial T.verts]
    (hT_tree : T.coe.IsTree)
    (hT_spanning : T.IsSpanning) :
    (Finset.univ.filter fun vT : T.verts => 3 <= T.coe.degree vT).card <= 2 := by
  classical
  let leaf : Finset T.verts :=
    Finset.univ.filter fun vT : T.verts => T.coe.degree vT = 1
  have hleaf_card_le_four : leaf.card <= 4 := by
    let f : leaf -> Fin 4 := fun vT =>
      Classical.choose
        (Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
          hBC hB_terminal hB_minimal hT_tree.connected hT_spanning
          (vT : T.verts)
          (by
            have hv := (Finset.mem_filter.mp (vT : {vT : T.verts // vT ∈ leaf}).2).2
            simpa [leaf] using hv))
    have hf_injective : Function.Injective f := by
      intro x y hxy
      have hx_range :=
        Classical.choose_spec
          (Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
            hBC hB_terminal hB_minimal hT_tree.connected hT_spanning
            (x : T.verts)
            (by
              have hx := (Finset.mem_filter.mp x.2).2
              simpa [leaf] using hx))
      have hy_range :=
        Classical.choose_spec
          (Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
            hBC hB_terminal hB_minimal hT_tree.connected hT_spanning
            (y : T.verts)
            (by
              have hy := (Finset.mem_filter.mp y.2).2
              simpa [leaf] using hy))
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      calc
        ((x : T.verts) : B.verts) = terminal (f x) := hx_range.symm
        _ = terminal (f y) := by rw [hxy]
        _ = ((y : T.verts) : B.verts) := hy_range
    have hcard_subtype :
        Fintype.card leaf <= Fintype.card (Fin 4) :=
      Fintype.card_le_of_injective f hf_injective
    simpa using hcard_subtype
  have hcount :=
    Schematic.Math.GraphTheory.IsTree.card_degree_ge_three_add_two_le_card_degree_one
      (G := T.coe) hT_tree
  have hleaf_card_eq :
      (Finset.univ.filter fun vT : T.verts => T.coe.degree vT = 1).card =
        leaf.card := by
    rfl
  have hbranch_count :
      (Finset.univ.filter fun vT : T.verts => 3 <= T.coe.degree vT).card + 2 <=
        leaf.card := by
    simpa [hleaf_card_eq, leaf] using hcount
  have hgoal :
      (Finset.univ.filter fun vT : T.verts => 3 <= T.coe.degree vT).card <= 2 := by
    omega
  simpa using hgoal

theorem Subgraph.minimal_connected_spanning_tree_card_degree_ge_three_le_one_of_three_terminals
    {C B : G.Subgraph}
    {terminal : Fin 3 -> V}
    (hBC : B ≤ C)
    (hB_terminal : forall i : Fin 3, terminal i ∈ B.verts)
    (hB_minimal :
      forall B' : G.Subgraph,
        B' ≤ C ->
          B'.coe.Connected ->
            (forall i : Fin 3, terminal i ∈ B'.verts) ->
              B'.verts ⊆ B.verts ->
                B.verts ⊆ B'.verts)
    {T : B.coe.Subgraph}
    [Fintype T.verts]
    [DecidableRel T.coe.Adj]
    [Nontrivial T.verts]
    (hT_tree : T.coe.IsTree)
    (hT_spanning : T.IsSpanning) :
    (Finset.univ.filter fun vT : T.verts => 3 <= T.coe.degree vT).card <= 1 := by
  classical
  let leaf : Finset T.verts :=
    Finset.univ.filter fun vT : T.verts => T.coe.degree vT = 1
  have hleaf_card_le_three : leaf.card <= 3 := by
    let f : leaf -> Fin 3 := fun vT =>
      Classical.choose
        (Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
          hBC hB_terminal hB_minimal hT_tree.connected hT_spanning
          (vT : T.verts)
          (by
            have hv := (Finset.mem_filter.mp (vT : {vT : T.verts // vT ∈ leaf}).2).2
            simpa [leaf] using hv))
    have hf_injective : Function.Injective f := by
      intro x y hxy
      have hx_range :=
        Classical.choose_spec
          (Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
            hBC hB_terminal hB_minimal hT_tree.connected hT_spanning
            (x : T.verts)
            (by
              have hx := (Finset.mem_filter.mp x.2).2
              simpa [leaf] using hx))
      have hy_range :=
        Classical.choose_spec
          (Subgraph.minimal_connected_spanning_tree_tree_vertex_leaf_mem_terminal_range
            hBC hB_terminal hB_minimal hT_tree.connected hT_spanning
            (y : T.verts)
            (by
              have hy := (Finset.mem_filter.mp y.2).2
              simpa [leaf] using hy))
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      calc
        ((x : T.verts) : B.verts) = terminal (f x) := hx_range.symm
        _ = terminal (f y) := by rw [hxy]
        _ = ((y : T.verts) : B.verts) := hy_range
    have hcard_subtype :
        Fintype.card leaf <= Fintype.card (Fin 3) :=
      Fintype.card_le_of_injective f hf_injective
    simpa using hcard_subtype
  have hcount :=
    Schematic.Math.GraphTheory.IsTree.card_degree_ge_three_add_two_le_card_degree_one
      (G := T.coe) hT_tree
  have hleaf_card_eq :
      (Finset.univ.filter fun vT : T.verts => T.coe.degree vT = 1).card =
        leaf.card := by
    rfl
  have hbranch_count :
      (Finset.univ.filter fun vT : T.verts => 3 <= T.coe.degree vT).card + 2 <=
        leaf.card := by
    simpa [hleaf_card_eq, leaf] using hcount
  have hgoal :
      (Finset.univ.filter fun vT : T.verts => 3 <= T.coe.degree vT).card <= 1 := by
    omega
  simpa using hgoal


end Schematic.Math.GraphTheory
