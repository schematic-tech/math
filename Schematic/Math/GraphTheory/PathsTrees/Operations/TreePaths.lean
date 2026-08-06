import Schematic.Math.GraphTheory.PathsTrees.Operations.EdgeExpansion

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}
def IsTreeSubgraph {V : Type u} {G : SimpleGraph V} (T : G.Subgraph) : Prop :=
  T.coe.IsTree

theorem Connected.exists_spanning_tree_subgraph
    (hG : G.Connected) :
    Exists fun T : G.Subgraph => T.coe.IsTree ∧ T.IsSpanning := by
  rcases hG.exists_isTree_le with ⟨T, hTG, hT⟩
  let ST : G.Subgraph := SimpleGraph.toSubgraph T hTG
  have hSTspan : ST.IsSpanning := SimpleGraph.toSubgraph.isSpanning T hTG
  refine ⟨ST, ?_, hSTspan⟩
  have hsp : ST.spanningCoe.IsTree := by
    simpa [ST, SimpleGraph.toSubgraph] using hT
  exact
    (SimpleGraph.Subgraph.spanningCoeEquivCoeOfSpanning ST hSTspan).isTree_iff.mp hsp

theorem connected_induce_exists_spanning_tree_subgraph
    {A : Set V}
    (hA : (G.induce A).Connected) :
    Exists fun T : (G.induce A).Subgraph => T.coe.IsTree ∧ T.IsSpanning :=
  Connected.exists_spanning_tree_subgraph hA

theorem connected_induce_exists_spanning_tree_subgraph_containing
    {A : Set V} {ι : Type*}
    (hA : (G.induce A).Connected)
    (terminal : ι -> V)
    (hterminal : forall i : ι, terminal i ∈ A) :
    Exists fun T : (G.induce A).Subgraph =>
      T.coe.IsTree ∧ T.IsSpanning ∧
        forall i : ι, (⟨terminal i, hterminal i⟩ : A) ∈ T.verts := by
  rcases connected_induce_exists_spanning_tree_subgraph (G := G) hA with
    ⟨T, hT_tree, hT_spanning⟩
  exact ⟨T, hT_tree, hT_spanning, fun i => hT_spanning _⟩

theorem Subgraph.Connected.exists_spanning_tree_coe_subgraph_containing
    {B : G.Subgraph}
    (hB : B.coe.Connected)
    {ι : Type*}
    (terminal : ι -> V)
    (hterminal : forall i : ι, terminal i ∈ B.verts) :
    Exists fun T : B.coe.Subgraph =>
      T.coe.IsTree ∧ T.IsSpanning ∧
        forall i : ι, (⟨terminal i, hterminal i⟩ : B.verts) ∈ T.verts := by
  rcases Connected.exists_spanning_tree_subgraph (G := B.coe) hB with
    ⟨T, hT_tree, hT_spanning⟩
  exact ⟨T, hT_tree, hT_spanning, fun i => hT_spanning _⟩

noncomputable def Subgraph.coeSubgraphCoeIso
    {B : G.Subgraph}
    (T : B.coe.Subgraph) :
    T.coe ≃g (SimpleGraph.Subgraph.coeSubgraph T).coe := by
  let toF : T.verts -> (SimpleGraph.Subgraph.coeSubgraph T).verts := fun x =>
    ⟨(((x : T.verts) : B.verts) : V), by simp⟩
  let invF : (SimpleGraph.Subgraph.coeSubgraph T).verts -> T.verts := fun y => by
    let yv : V := y
    have hy : yv ∈ (T.verts : Set V) := by
      change yv ∈ (SimpleGraph.Subgraph.coeSubgraph T).verts
      exact y.2
    let b : B.verts := Classical.choose hy
    have hb := Classical.choose_spec hy
    exact ⟨b, hb.1⟩
  have leftInv : Function.LeftInverse invF toF := by
    intro x
    dsimp [invF, toF]
    let y : (SimpleGraph.Subgraph.coeSubgraph T).verts :=
      ⟨(((x : T.verts) : B.verts) : V), by simp⟩
    let yv : V := y
    have hy : yv ∈ (T.verts : Set V) := by
      change yv ∈ (SimpleGraph.Subgraph.coeSubgraph T).verts
      exact y.2
    let b : B.verts := Classical.choose hy
    have hb := Classical.choose_spec hy
    apply Subtype.ext
    apply Subtype.ext
    exact hb.2
  have rightInv : Function.RightInverse invF toF := by
    intro y
    dsimp [invF, toF]
    let yv : V := y
    have hy : yv ∈ (T.verts : Set V) := by
      change yv ∈ (SimpleGraph.Subgraph.coeSubgraph T).verts
      exact y.2
    let b : B.verts := Classical.choose hy
    have hb := Classical.choose_spec hy
    apply Subtype.ext
    exact hb.2
  refine { toEquiv := ⟨toF, invF, leftInv, rightInv⟩, map_rel_iff' := ?_ }
  intro x y
  dsimp [toF]
  constructor
  · intro h
    change (SimpleGraph.Subgraph.coeSubgraph T).Adj
      (((x : T.verts) : B.verts) : V)
      (((y : T.verts) : B.verts) : V) at h
    rw [SimpleGraph.Subgraph.coeSubgraph_adj] at h
    rcases h with ⟨_hxB, _hyB, hxy⟩
    simpa using hxy
  · intro h
    change (SimpleGraph.Subgraph.coeSubgraph T).Adj
      (((x : T.verts) : B.verts) : V)
      (((y : T.verts) : B.verts) : V)
    rw [SimpleGraph.Subgraph.coeSubgraph_adj]
    exact ⟨(x : T.verts).1.2, (y : T.verts).1.2, h⟩

theorem Subgraph.coeSubgraph_isTree
    {B : G.Subgraph}
    (T : B.coe.Subgraph)
    (hT : T.coe.IsTree) :
    (SimpleGraph.Subgraph.coeSubgraph T).coe.IsTree :=
  (Subgraph.coeSubgraphCoeIso T).isTree_iff.mp hT

theorem Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {u v : V}
    (hu : u ∈ B.verts)
    (hv : v ∈ B.verts) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧
        p.toSubgraph ≤ B ∧
          forall z : V, z ∈ p.support ->
            Exists fun hzB : z ∈ B.verts =>
              (⟨z, hzB⟩ : B.verts) ∈ T.verts := by
  let uB : B.verts := ⟨u, hu⟩
  let vB : B.verts := ⟨v, hv⟩
  have huT : uB ∈ T.verts := hT_spanning uB
  have hvT : vB ∈ T.verts := hT_spanning vB
  obtain ⟨pT, hpT, hpT_le⟩ :=
    Subgraph.Connected.exists_path_between
      (G := B.coe) (H := T) hT_connected huT hvT
  let p : G.Walk u v := pT.map B.hom
  refine ⟨p, ?_, ?_, ?_⟩
  · exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpT
  · simpa [p] using Walk.map_subgraph_toSubgraph_le pT
  · intro z hz
    have hz_map : z ∈ pT.support.map B.hom := by
      change z ∈ (pT.map B.hom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      exact hz
    rcases List.mem_map.mp hz_map with ⟨zB, hzB_support, rfl⟩
    refine ⟨zB.2, ?_⟩
    have hzB_T : (zB : B.verts) ∈ T.verts :=
      hpT_le.left (by
        rw [SimpleGraph.Walk.mem_verts_toSubgraph]
        exact hzB_support)
    exact hzB_T

theorem Subgraph.Connected.exists_coe_path_between_in_spanning_coe_subgraph
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {u v : V}
    (hu : u ∈ B.verts)
    (hv : v ∈ B.verts) :
    Exists fun pB : B.coe.Walk (⟨u, hu⟩ : B.verts) (⟨v, hv⟩ : B.verts) =>
      pB.IsPath ∧ pB.toSubgraph ≤ T := by
  let uB : B.verts := ⟨u, hu⟩
  let vB : B.verts := ⟨v, hv⟩
  have huT : uB ∈ T.verts := hT_spanning uB
  have hvT : vB ∈ T.verts := hT_spanning vB
  exact
    Subgraph.Connected.exists_path_between
      (G := B.coe) (H := T) hT_connected huT hvT

theorem Subgraph.Connected.exists_coe_rooted_paths_in_spanning_coe_subgraph
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {ι : Type*}
    {root : V}
    (hroot : root ∈ B.verts)
    (terminal : ι -> V)
    (hterminal : forall i : ι, terminal i ∈ B.verts) :
    Exists fun stemB :
        forall i : ι,
          B.coe.Walk (⟨root, hroot⟩ : B.verts)
            (⟨terminal i, hterminal i⟩ : B.verts) =>
      (forall i : ι, (stemB i).IsPath) ∧
        forall i : ι, (stemB i).toSubgraph ≤ T := by
  classical
  let stemB :
      forall i : ι,
        B.coe.Walk (⟨root, hroot⟩ : B.verts)
          (⟨terminal i, hterminal i⟩ : B.verts) := fun i =>
    Classical.choose
      (Subgraph.Connected.exists_coe_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot (hterminal i))
  refine ⟨stemB, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_coe_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot (hterminal i))).1
  · intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_coe_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot (hterminal i))).2

theorem Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph_internal_subset
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {u v : V}
    (hu : u ∈ B.verts)
    (hv : v ∈ B.verts) :
    Exists fun p : G.Walk u v =>
      p.IsPath ∧
        p.toSubgraph ≤ B ∧
          (forall z : V, z ∈ p.support ->
            Exists fun hzB : z ∈ B.verts =>
              (⟨z, hzB⟩ : B.verts) ∈ T.verts) ∧
            forall z : V, z ∈ Walk.InternalVertices p ->
              Exists fun hzB : z ∈ B.verts =>
                (⟨z, hzB⟩ : B.verts) ∈ T.verts := by
  obtain ⟨p, hp, hp_le, hp_support⟩ :=
    Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph
      (B := B) (T := T) hT_connected hT_spanning hu hv
  exact ⟨p, hp, hp_le, hp_support, fun z hz =>
    hp_support z ((Walk.internalVertices_subset_support p) hz)⟩

theorem Subgraph.Connected.exists_rooted_paths_in_spanning_coe_subgraph
    {B : G.Subgraph}
    {T : B.coe.Subgraph}
    (hT_connected : T.coe.Connected)
    (hT_spanning : T.IsSpanning)
    {ι : Type*}
    {root : V}
    (hroot : root ∈ B.verts)
    (terminal : ι -> V)
    (hterminal : forall i : ι, terminal i ∈ B.verts) :
    Exists fun stem : forall i : ι, G.Walk root (terminal i) =>
      (forall i : ι, (stem i).IsPath) ∧
        (forall i : ι, (stem i).toSubgraph ≤ B) ∧
          forall i : ι, forall z : V, z ∈ (stem i).support ->
            Exists fun hzB : z ∈ B.verts =>
              (⟨z, hzB⟩ : B.verts) ∈ T.verts := by
  classical
  let stem : forall i : ι, G.Walk root (terminal i) := fun i =>
    Classical.choose
      (Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot (hterminal i))
  refine ⟨stem, ?_, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot
          (hterminal i))).1
  · intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot
          (hterminal i))).2.1
  · intro i z hz
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between_in_spanning_coe_subgraph
        (B := B) (T := T) hT_connected hT_spanning hroot
          (hterminal i))).2.2 z hz

theorem IsTree.path_eq_of_isPath
    {u v : V}
    (hT : G.IsTree)
    {p q : G.Walk u v}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    p = q := by
  exact congrArg Subtype.val
    (hT.isAcyclic.path_unique
      (⟨p, hp⟩ : G.Path u v) (⟨q, hq⟩ : G.Path u v))

theorem IsTree.support_eq_of_isPath
    {u v : V}
    (hT : G.IsTree)
    {p q : G.Walk u v}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    p.support = q.support := by
  rw [IsTree.path_eq_of_isPath hT hp hq]

theorem IsTree.mem_support_iff_of_isPath
    {u v z : V}
    (hT : G.IsTree)
    {p q : G.Walk u v}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    z ∈ p.support ↔ z ∈ q.support := by
  rw [IsTree.support_eq_of_isPath hT hp hq]

theorem IsTree.exists_three_terminal_median
    [DecidableEq V]
    (hT : G.IsTree)
    (terminal : Fin 3 -> V) :
    Exists fun root : V =>
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (terminal i) (terminal j) =>
          p.IsPath ∧ root ∈ p.support := by
  classical
  obtain ⟨p01, hp01⟩ :=
    hT.connected.exists_isPath (terminal (0 : Fin 3)) (terminal (1 : Fin 3))
  obtain ⟨p02, hp02⟩ :=
    hT.connected.exists_isPath (terminal (0 : Fin 3)) (terminal (2 : Fin 3))
  obtain ⟨p12, hp12⟩ :=
    hT.connected.exists_isPath (terminal (1 : Fin 3)) (terminal (2 : Fin 3))
  obtain ⟨root, hroot01_rev, hroot02, hlast⟩ :=
    Walk.IsPath.exists_reverse_takeUntil_first_mem
      (G := G) hp01 {z : V | z ∈ p02.support} p02.start_mem_support
  have hroot01 : root ∈ p01.support := by
    simpa [SimpleGraph.Walk.support_reverse] using hroot01_rev
  have hroot12 : root ∈ p12.support := by
    let q1 : G.Walk (terminal (1 : Fin 3)) root :=
      p01.reverse.takeUntil root hroot01_rev
    let q2 : G.Walk root (terminal (2 : Fin 3)) :=
      p02.dropUntil root hroot02
    have hq1 : q1.IsPath := by
      simpa [q1] using hp01.reverse.takeUntil hroot01_rev
    have hq2 : q2.IsPath := by
      simpa [q2] using hp02.dropUntil hroot02
    have hclean :
        forall z : V, z ∈ q1.support -> z ∈ q2.support -> z = root := by
      intro z hzq1 hzq2
      have hz_p02 : z ∈ p02.support :=
        SimpleGraph.Walk.support_dropUntil_subset p02 hroot02 hzq2
      exact hlast z (by simpa [q1] using hzq1) hz_p02
    have hq : (q1.append q2).IsPath :=
      Walk.IsPath.append_of_support_inter_eq_endpoint hq1 hq2 hclean
    have hroot_q : root ∈ (q1.append q2).support := by
      exact SimpleGraph.Walk.subset_support_append_left q1 q2 q1.end_mem_support
    exact (IsTree.mem_support_iff_of_isPath hT hq hp12).mp hroot_q
  refine ⟨root, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact ⟨p01, hp01, hroot01⟩
  · exact ⟨p02, hp02, hroot02⟩
  · exact ⟨p01.reverse, hp01.reverse, by
      simpa [SimpleGraph.Walk.support_reverse] using hroot01⟩
  · exact False.elim (hij rfl)
  · exact ⟨p12, hp12, hroot12⟩
  · exact ⟨p02.reverse, hp02.reverse, by
      simpa [SimpleGraph.Walk.support_reverse] using hroot02⟩
  · exact ⟨p12.reverse, hp12.reverse, by
      simpa [SimpleGraph.Walk.support_reverse] using hroot12⟩
  · exact False.elim (hij rfl)

theorem Subgraph.tree_exists_three_terminal_median
    {T : G.Subgraph}
    [DecidableEq T.verts]
    (hT : T.coe.IsTree)
    (terminal : Fin 3 -> T.verts) :
    Exists fun root : T.verts =>
      forall {i j : Fin 3}, i ≠ j ->
        Exists fun p : G.Walk (terminal i : V) (terminal j : V) =>
          p.toSubgraph ≤ T ∧ p.IsPath ∧ (root : V) ∈ p.support := by
  classical
  rcases IsTree.exists_three_terminal_median
      (G := T.coe) hT terminal with
    ⟨root, hroot⟩
  refine ⟨root, ?_⟩
  intro i j hij
  rcases hroot hij with ⟨pT, hpT, hroot_pT⟩
  let p : G.Walk (terminal i : V) (terminal j : V) := pT.map T.hom
  refine ⟨p, ?_, ?_, ?_⟩
  · simpa [p] using Walk.map_subgraph_toSubgraph_le pT
  · exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpT
  · change (root : V) ∈ (pT.map T.hom).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨root, hroot_pT, rfl⟩

theorem IsTree.not_mem_support_of_reachable_delete_singleton
    [DecidableEq V]
    {root u v : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hu : u ≠ root)
    (hv : v ≠ root)
    (hreach :
      (G.induce ({root} : Set V)ᶜ).Reachable
        ⟨u, by exact hu⟩ ⟨v, by exact hv⟩) :
    root ∉ p.support := by
  rintro hroot_p
  obtain ⟨qA⟩ := hreach
  let q : G.Walk u v := qA.map (SimpleGraph.Embedding.induce ({root} : Set V)ᶜ).toHom
  have hroot_q :
      root ∈ (q.toPath : G.Walk u v).support := by
    exact (IsTree.mem_support_iff_of_isPath hT hp q.toPath.property).mp hroot_p
  have hroot_q_walk : root ∈ q.support :=
    SimpleGraph.Walk.support_toPath_subset q hroot_q
  have hroot_qA :
      root ∈ (qA.map (SimpleGraph.Embedding.induce ({root} : Set V)ᶜ).toHom).support := by
    simpa [q] using hroot_q_walk
  rw [SimpleGraph.Walk.support_map] at hroot_qA
  rcases List.mem_map.mp hroot_qA with ⟨x, _hx_support, hx_eq⟩
  exact x.2 (by simpa [Set.mem_singleton_iff] using hx_eq)

theorem IsTree.not_reachable_delete_singleton_of_mem_path_support
    [DecidableEq V]
    {root u v : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    (hp : p.IsPath)
    (hroot : root ∈ p.support)
    (hu : u ≠ root)
    (hv : v ≠ root) :
    ¬ (G.induce ({root} : Set V)ᶜ).Reachable
        ⟨u, by exact hu⟩ ⟨v, by exact hv⟩ := by
  intro hreach
  exact (IsTree.not_mem_support_of_reachable_delete_singleton
    hT hp hu hv hreach) hroot

theorem IsTree.exists_path_through_root_of_not_reachable_delete_singleton
    [DecidableEq V]
    {root u v : V}
    (hT : G.IsTree)
    (hu : u ≠ root)
    (hv : v ≠ root)
    (hunreachable :
      ¬ (G.induce ({root} : Set V)ᶜ).Reachable
          ⟨u, by exact hu⟩ ⟨v, by exact hv⟩) :
    Exists fun p : G.Walk u v => p.IsPath ∧ root ∈ p.support := by
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath u v
  refine ⟨p, hp, ?_⟩
  by_contra hroot_not
  have havoid : forall z : V, z ∈ p.support -> z ≠ root := by
    intro z hz hzr
    exact hroot_not (by simpa [hzr] using hz)
  have hreach :
      (G.induce ({root} : Set V)ᶜ).Reachable
        ⟨u, by exact hu⟩ ⟨v, by exact hv⟩ := by
    simpa using
      (Walk.reachable_induce_compl_singleton_of_support_avoids p havoid)
  exact hunreachable hreach

theorem IsTree.pair_paths_through_root_of_not_reachable_delete_singleton
    [DecidableEq V]
    {ι : Type*}
    {root : V}
    {terminal : ι -> V}
    (hT : G.IsTree)
    (hterminal_ne : forall i : ι, terminal i ≠ root)
    (hunreachable :
      forall {i j : ι}, i ≠ j ->
        ¬ (G.induce ({root} : Set V)ᶜ).Reachable
            ⟨terminal i, by exact hterminal_ne i⟩
            ⟨terminal j, by exact hterminal_ne j⟩) :
    forall {i j : ι}, i ≠ j ->
      Exists fun p : G.Walk (terminal i) (terminal j) =>
        p.IsPath ∧ root ∈ p.support := by
  intro i j hij
  exact IsTree.exists_path_through_root_of_not_reachable_delete_singleton
    (G := G) hT (hterminal_ne i) (hterminal_ne j) (hunreachable hij)

noncomputable def Iso.induceComplSingleton
    {V' : Type*}
    {G' : SimpleGraph V'}
    (φ : G ≃g G')
    (root : V) :
    G.induce ({root} : Set V)ᶜ ≃g
      G'.induce ({φ root} : Set V')ᶜ where
  toFun x := ⟨φ x, by
    intro hx
    exact x.2 (by
      have hφ : φ (x : V) = φ root := by
        simpa [Set.mem_singleton_iff] using hx
      simpa [Set.mem_singleton_iff] using φ.injective hφ)⟩
  invFun y := ⟨φ.symm y, by
    intro hy
    exact y.2 (by
      have hφ : φ.symm (y : V') = root := by
        simpa [Set.mem_singleton_iff] using hy
      have hφ' : (y : V') = φ root := by
        simpa using congrArg φ hφ
      simpa [Set.mem_singleton_iff] using hφ')⟩
  left_inv x := by
    apply Subtype.ext
    exact φ.left_inv x
  right_inv y := by
    apply Subtype.ext
    exact φ.right_inv y
  map_rel_iff' := by
    intro x y
    exact φ.map_rel_iff

theorem fin3_exists_distinct_from_pair
    {i j : Fin 3}
    (hij : i ≠ j) :
    Exists fun k : Fin 3 => i ≠ k ∧ j ≠ k := by
  fin_cases i <;> fin_cases j <;> simp at *
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem IsTree.root_mem_terminal_path_of_unique_degree_ge_three
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hT : G.IsTree)
    {terminal : Fin 3 -> V}
    (hterminal_injective : Function.Injective terminal)
    (hterminal_degree : forall i : Fin 3, G.degree (terminal i) = 1)
    {root : V}
    (hroot_unique : forall z : V, 3 <= G.degree z -> z = root)
    {i j : Fin 3}
    (hij : i ≠ j)
    {p : G.Walk (terminal i) (terminal j)}
    (hp : p.IsPath) :
    root ∈ p.support := by
  classical
  by_contra hroot_not_p
  obtain ⟨k, hik, hjk⟩ := fin3_exists_distinct_from_pair hij
  have hterminal_i_ne_j : terminal i ≠ terminal j := by
    intro h
    exact hij (hterminal_injective h)
  have hterminal_j_ne_i : terminal j ≠ terminal i := hterminal_i_ne_j.symm
  have hk_not_p : terminal k ∉ p.support := by
    intro hk_p
    rcases Walk.IsPath.leaf_mem_support_eq_endpoint hp (hterminal_degree k) hk_p with hk_i | hk_j
    · exact hik (hterminal_injective hk_i).symm
    · exact hjk (hterminal_injective hk_j).symm
  obtain ⟨r, hr⟩ := hT.connected.exists_isPath (terminal k) (terminal i)
  obtain ⟨x, hx_r, hx_p, hfirst⟩ :=
    Walk.IsPath.exists_takeUntil_first_mem
      (G := G) hr {z : V | z ∈ p.support} p.start_mem_support
  have hx_ne_k : x ≠ terminal k := by
    intro hxk
    exact hk_not_p (by simpa [hxk] using hx_p)
  let q : G.Walk (terminal k) x := r.takeUntil x hx_r
  have hq_not_nil : Not q.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := q) hx_ne_k.symm
  let y : V := q.penultimate
  have hy_q : y ∈ q.support := by
    exact List.mem_of_mem_dropLast
      (SimpleGraph.Walk.penultimate_mem_dropLast_support hq_not_nil)
  have hy_ne_x : y ≠ x := by
    exact (q.adj_penultimate hq_not_nil).ne
  have hy_not_p : y ∉ p.support := by
    intro hy_p
    have hy_eq_x : y = x := hfirst y (by exact hy_q) hy_p
    exact hy_ne_x hy_eq_x
  have hy_adj_x : G.Adj x y := by
    exact (q.adj_penultimate hq_not_nil).symm
  have hy_not_p_neighbor :
      y ∉ p.toSubgraph.neighborSet x := by
    intro hy_neighbor
    have hy_vert : y ∈ p.toSubgraph.verts :=
      SimpleGraph.Subgraph.neighborSet_subset_verts p.toSubgraph x hy_neighbor
    rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hy_vert
    exact hy_not_p hy_vert
  by_cases hxi : x = terminal i
  · have hdeg_ge_two_top :
        2 <= (⊤ : G.Subgraph).degree (terminal i) := by
      exact
        Walk.IsPath.degree_ge_two_of_start_and_extra_neighbor
          (H := (⊤ : G.Subgraph)) (p := p) le_top hterminal_i_ne_j
          (by simpa [hxi] using hy_adj_x)
          (by simpa [hxi] using hy_not_p_neighbor)
    have hdeg_ge_two : 2 <= G.degree (terminal i) := by
      exact le_trans hdeg_ge_two_top
        (SimpleGraph.Subgraph.degree_le (⊤ : G.Subgraph) (terminal i))
    have hdeg_one := hterminal_degree i
    omega
  · by_cases hxj : x = terminal j
    · have hy_not_reverse_neighbor :
          y ∉ p.reverse.toSubgraph.neighborSet (terminal j) := by
        intro hy_neighbor
        have hy_vert : y ∈ p.reverse.toSubgraph.verts :=
          SimpleGraph.Subgraph.neighborSet_subset_verts p.reverse.toSubgraph
            (terminal j) hy_neighbor
        rw [SimpleGraph.Walk.mem_verts_toSubgraph] at hy_vert
        have hy_p : y ∈ p.support := by
          simpa [SimpleGraph.Walk.support_reverse] using hy_vert
        exact hy_not_p hy_p
      have hdeg_ge_two_top :
          2 <= (⊤ : G.Subgraph).degree (terminal j) := by
        exact
          Walk.IsPath.degree_ge_two_of_start_and_extra_neighbor
            (H := (⊤ : G.Subgraph)) (p := p.reverse) le_top hterminal_j_ne_i
            (by simpa [hxj] using hy_adj_x)
            (by simpa [hxj] using hy_not_reverse_neighbor)
      have hdeg_ge_two : 2 <= G.degree (terminal j) := by
        exact le_trans hdeg_ge_two_top
          (SimpleGraph.Subgraph.degree_le (⊤ : G.Subgraph) (terminal j))
      have hdeg_one := hterminal_degree j
      omega
    · have hx_internal : x ∈ Walk.InternalVertices p :=
        ⟨hx_p, hxi, hxj⟩
      have hdeg_ge_three_top :
          3 <= (⊤ : G.Subgraph).degree x := by
        exact
          Walk.IsPath.degree_ge_three_of_internal_and_extra_neighbor
            (H := (⊤ : G.Subgraph)) hp le_top hx_internal
            (by simpa using hy_adj_x)
            (by simpa using hy_not_p_neighbor)
      have hdeg_ge_three : 3 <= G.degree x := by
        exact le_trans hdeg_ge_three_top
          (SimpleGraph.Subgraph.degree_le (⊤ : G.Subgraph) x)
      have hx_root : x = root := hroot_unique x hdeg_ge_three
      exact hroot_not_p (by simpa [hx_root] using hx_p)

theorem IsTree.not_reachable_delete_singleton_of_unique_degree_ge_three_terminals
    [Fintype V]
    [DecidableEq V]
    [DecidableRel G.Adj]
    (hT : G.IsTree)
    {terminal : Fin 3 -> V}
    (hterminal_injective : Function.Injective terminal)
    (hterminal_degree : forall i : Fin 3, G.degree (terminal i) = 1)
    {root : V}
    (hroot_unique : forall z : V, 3 <= G.degree z -> z = root)
    (hterminal_ne_root : forall i : Fin 3, terminal i ≠ root) :
    forall {i j : Fin 3}, i ≠ j ->
      ¬ (G.induce ({root} : Set V)ᶜ).Reachable
          ⟨terminal i, by exact hterminal_ne_root i⟩
          ⟨terminal j, by exact hterminal_ne_root j⟩ := by
  intro i j hij hreach
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath (terminal i) (terminal j)
  have hroot_p : root ∈ p.support :=
    IsTree.root_mem_terminal_path_of_unique_degree_ge_three
      (G := G) hT hterminal_injective hterminal_degree hroot_unique hij hp
  exact
    (IsTree.not_reachable_delete_singleton_of_mem_path_support
      (G := G) hT hp hroot_p (hterminal_ne_root i) (hterminal_ne_root j))
      hreach

theorem IsTree.rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root
    [DecidableEq V]
    {ι : Type*}
    {root : V}
    {terminal : ι -> V}
    (hT : G.IsTree)
    (stem : forall i : ι, G.Walk root (terminal i))
    (hterminal_ne : forall i : ι, terminal i ≠ root)
    (hstem_path : forall i : ι, (stem i).IsPath)
    (hpair_path_through_root :
      forall {i j : ι}, i ≠ j ->
        Exists fun p : G.Walk (terminal i) (terminal j) =>
          p.IsPath ∧ root ∈ p.support) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).support ∧ z ≠ root}
        {z : V | z ∈ (stem j).support ∧ z ≠ root} := by
  refine walk_family_punctured_supports_disjoint_of_delete_root_unreachable
    (G := G) stem hterminal_ne hstem_path ?_
  intro i j hij
  obtain ⟨p, hp, hroot_p⟩ := hpair_path_through_root hij
  exact IsTree.not_reachable_delete_singleton_of_mem_path_support
    hT hp hroot_p (hterminal_ne i) (hterminal_ne j)

theorem IsTree.rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
    [DecidableEq V]
    {ι : Type*}
    {root : V}
    {terminal : ι -> V}
    (hT : G.IsTree)
    (stem : forall i : ι, G.Walk root (terminal i))
    (hstem_path : forall i : ι, (stem i).IsPath)
    (hpair_path_through_root :
      forall {i j : ι}, i ≠ j ->
        Exists fun p : G.Walk (terminal i) (terminal j) =>
          p.IsPath ∧ root ∈ p.support) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).support ∧ z ≠ root}
        {z : V | z ∈ (stem j).support ∧ z ≠ root} := by
  intro i j hij
  by_cases hi : terminal i = root
  · rw [Set.disjoint_left]
    rintro z ⟨hz_support, hz_ne_root⟩ _hzj
    have hclosed_path : ((stem i).copy rfl hi).IsPath := by
      exact (SimpleGraph.Walk.isPath_copy (stem i) rfl hi).mpr (hstem_path i)
    have hz_copy : z ∈ ((stem i).copy rfl hi).support := by
      simpa using hz_support
    exact hz_ne_root
      (Walk.IsPath.mem_support_eq_of_closed hclosed_path hz_copy)
  · by_cases hj : terminal j = root
    · rw [Set.disjoint_left]
      rintro z _hzi ⟨hz_support, hz_ne_root⟩
      have hclosed_path : ((stem j).copy rfl hj).IsPath := by
        exact (SimpleGraph.Walk.isPath_copy (stem j) rfl hj).mpr (hstem_path j)
      have hz_copy : z ∈ ((stem j).copy rfl hj).support := by
        simpa using hz_support
      exact hz_ne_root
        (Walk.IsPath.mem_support_eq_of_closed hclosed_path hz_copy)
    · rw [Set.disjoint_left]
      rintro z ⟨hzi, hz_ne_root⟩ ⟨hzj, _hzj_ne_root⟩
      have hreach :
          (G.induce ({root} : Set V)ᶜ).Reachable
            ⟨terminal i, by exact hi⟩ ⟨terminal j, by exact hj⟩ :=
        Walk.IsPath.reachable_between_ends_in_delete_start_of_common_nonstart
          (hstem_path i) (hstem_path j) hzi hzj hz_ne_root
      obtain ⟨p, hp, hroot_p⟩ := hpair_path_through_root hij
      exact
        (IsTree.not_reachable_delete_singleton_of_mem_path_support
          hT hp hroot_p hi hj) hreach

theorem IsTree.internalVertices_disjoint_punctured_root_path_of_endpoint_path_through_root
    [DecidableEq V]
    {root a b : V}
    (hT : G.IsTree)
    {p : G.Walk root a}
    {q : G.Walk root b}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (ha : a ≠ root)
    (hb : b ≠ root)
    {r : G.Walk a b}
    (hr : r.IsPath)
    (hroot_r : root ∈ r.support) :
    Disjoint
      (Walk.InternalVertices p)
      {z : V | z ∈ q.support ∧ z ≠ root} := by
  rw [Set.disjoint_left]
  rintro z hz_p ⟨hz_q, hz_ne_root⟩
  have hreach :
      (G.induce ({root} : Set V)ᶜ).Reachable
        ⟨a, by exact ha⟩ ⟨b, by exact hb⟩ :=
    Walk.IsPath.reachable_between_ends_in_delete_start_of_common_nonstart
      hp hq hz_p.1 hz_q hz_ne_root
  exact
    (IsTree.not_reachable_delete_singleton_of_mem_path_support
      hT hr hroot_r ha hb) hreach

theorem IsTree.endpoint_path_avoids_root_of_rooted_paths_common_nonroot
    [DecidableEq V]
    {root a b z : V}
    (hT : G.IsTree)
    {p : G.Walk root a}
    {q : G.Walk root b}
    {r : G.Walk a b}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (ha : a ≠ root)
    (hb : b ≠ root)
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hzroot : z ≠ root) :
    root ∉ r.support := by
  intro hroot_r
  have hreach :
      (G.induce ({root} : Set V)ᶜ).Reachable
        ⟨a, by exact ha⟩ ⟨b, by exact hb⟩ :=
    Walk.IsPath.reachable_between_ends_in_delete_start_of_common_nonstart
      hp hq hzp hzq hzroot
  exact
    (IsTree.not_reachable_delete_singleton_of_mem_path_support
      hT hr hroot_r ha hb) hreach

theorem IsTree.exists_endpoint_path_avoiding_root_of_rooted_paths_common_nonroot
    [DecidableEq V]
    {root a b z : V}
    (hT : G.IsTree)
    {p : G.Walk root a}
    {q : G.Walk root b}
    (hp : p.IsPath)
    (hq : q.IsPath)
    (ha : a ≠ root)
    (hb : b ≠ root)
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hzroot : z ≠ root) :
    Exists fun r : G.Walk a b => r.IsPath ∧ root ∉ r.support := by
  obtain ⟨r, hr⟩ := hT.connected.exists_isPath a b
  exact ⟨r, hr,
    IsTree.endpoint_path_avoids_root_of_rooted_paths_common_nonroot
      hT hp hq hr ha hb hzp hzq hzroot⟩

theorem IsTree.not_mem_root_path_support_of_opposite_path_through_root
    [DecidableEq V]
    {root other terminal : V}
    (hT : G.IsTree)
    {p : G.Walk root terminal}
    (hp : p.IsPath)
    {r : G.Walk other terminal}
    (hr : r.IsPath)
    (hroot_r : root ∈ r.support)
    (hother_ne_root : other ≠ root) :
    other ∉ p.support := by
  intro hother_p
  let q : G.Walk other terminal := p.dropUntil other hother_p
  have hq_path : q.IsPath := by
    simpa [q] using hp.dropUntil hother_p
  have hroot_q : root ∈ q.support := by
    exact (IsTree.mem_support_iff_of_isPath hT hq_path hr).mpr hroot_r
  have hroot_not_q : root ∉ q.support := by
    simpa [q] using
      (Walk.IsPath.start_not_mem_dropUntil_support_of_ne
        hp hother_p hother_ne_root)
  exact hroot_not_q hroot_q

theorem IsTree.punctured_root_path_support_avoids_opposite_of_path_through_root
    [DecidableEq V]
    {root other terminal : V}
    (hT : G.IsTree)
    {p : G.Walk root terminal}
    (hp : p.IsPath)
    {r : G.Walk other terminal}
    (hr : r.IsPath)
    (hroot_r : root ∈ r.support)
    (hother_ne_root : other ≠ root) :
    forall {z : V}, z ∈ p.support -> z ≠ other := by
  intro z hz hz_other
  exact
    (IsTree.not_mem_root_path_support_of_opposite_path_through_root
      hT hp hr hroot_r hother_ne_root) (by simpa [hz_other] using hz)

theorem Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {ι : Type*}
    {root : T.verts}
    {terminal : ι -> T.verts}
    (hT : T.coe.IsTree)
    (stem : forall i : ι, G.Walk (root : V) (terminal i : V))
    (hstem_le : forall i : ι, (stem i).toSubgraph ≤ T)
    (hterminal_ne : forall i : ι, terminal i ≠ root)
    (hstem_path : forall i : ι, (stem i).IsPath)
    (hpair_path_through_root :
      forall {i j : ι}, i ≠ j ->
        Exists fun p : G.Walk (terminal i : V) (terminal j : V) =>
          p.toSubgraph ≤ T ∧ p.IsPath ∧ (root : V) ∈ p.support) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).support ∧ z ≠ (root : V)}
        {z : V | z ∈ (stem j).support ∧ z ≠ (root : V)} := by
  classical
  let stemT :
      forall i : ι, T.coe.Walk root (terminal i) := fun i =>
    (Walk.liftToSubgraph (stem i) (hstem_le i)).copy
      (Subtype.ext rfl) (Subtype.ext rfl)
  have hstemT_path : forall i : ι, (stemT i).IsPath := by
    intro i
    simpa [stemT] using
      (Walk.liftToSubgraph_isPath (hstem_le i) (hstem_path i))
  have hpairT :
      forall {i j : ι}, i ≠ j ->
        Exists fun p : T.coe.Walk (terminal i) (terminal j) =>
          p.IsPath ∧ root ∈ p.support := by
    intro i j hij
    obtain ⟨p, hp_le, hp_path, hroot_p⟩ := hpair_path_through_root hij
    let pT : T.coe.Walk (terminal i) (terminal j) :=
      (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
    have hpT_path : pT.IsPath := by
      simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp_path
    have hroot_pT : root ∈ pT.support := by
      simpa [pT] using
        ((Walk.mem_support_liftToSubgraph_iff hp_le (z := root)).mpr hroot_p)
    exact ⟨pT, hpT_path, hroot_pT⟩
  have hdisjointT :
      forall {i j : ι}, i ≠ j ->
        Disjoint
          {z : T.verts | z ∈ (stemT i).support ∧ z ≠ root}
          {z : T.verts | z ∈ (stemT j).support ∧ z ≠ root} :=
    IsTree.rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root
      (G := T.coe) hT stemT hterminal_ne hstemT_path hpairT
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hzT_mem : z ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le (hstem_le i) hzi.1
  let zT : T.verts := ⟨z, hzT_mem⟩
  have hziT : zT ∈ (stemT i).support := by
    simpa [stemT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff (hstem_le i) (z := zT)).mpr hzi.1)
  have hzjT : zT ∈ (stemT j).support := by
    simpa [stemT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff (hstem_le j) (z := zT)).mpr hzj.1)
  have hzT_ne_root : zT ≠ root := by
    intro h
    exact hzi.2 (by
      have hval := congrArg (fun x : T.verts => (x : V)) h
      simpa [zT] using hval)
  exact Set.disjoint_left.mp (hdisjointT hij)
    ⟨hziT, hzT_ne_root⟩ ⟨hzjT, hzT_ne_root⟩

theorem Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {ι : Type*}
    {root : T.verts}
    {terminal : ι -> T.verts}
    (hT : T.coe.IsTree)
    (stem : forall i : ι, G.Walk (root : V) (terminal i : V))
    (hstem_le : forall i : ι, (stem i).toSubgraph ≤ T)
    (hstem_path : forall i : ι, (stem i).IsPath)
    (hpair_path_through_root :
      forall {i j : ι}, i ≠ j ->
        Exists fun p : G.Walk (terminal i : V) (terminal j : V) =>
          p.toSubgraph ≤ T ∧ p.IsPath ∧ (root : V) ∈ p.support) :
    forall {i j : ι}, i ≠ j ->
      Disjoint
        {z : V | z ∈ (stem i).support ∧ z ≠ (root : V)}
        {z : V | z ∈ (stem j).support ∧ z ≠ (root : V)} := by
  classical
  let stemT :
      forall i : ι, T.coe.Walk root (terminal i) := fun i =>
    (Walk.liftToSubgraph (stem i) (hstem_le i)).copy
      (Subtype.ext rfl) (Subtype.ext rfl)
  have hstemT_path : forall i : ι, (stemT i).IsPath := by
    intro i
    simpa [stemT] using
      (Walk.liftToSubgraph_isPath (hstem_le i) (hstem_path i))
  have hpairT :
      forall {i j : ι}, i ≠ j ->
        Exists fun p : T.coe.Walk (terminal i) (terminal j) =>
          p.IsPath ∧ root ∈ p.support := by
    intro i j hij
    obtain ⟨p, hp_le, hp_path, hroot_p⟩ := hpair_path_through_root hij
    let pT : T.coe.Walk (terminal i) (terminal j) :=
      (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
    have hpT_path : pT.IsPath := by
      simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp_path
    have hroot_pT : root ∈ pT.support := by
      simpa [pT] using
        ((Walk.mem_support_liftToSubgraph_iff hp_le (z := root)).mpr hroot_p)
    exact ⟨pT, hpT_path, hroot_pT⟩
  have hdisjointT :
      forall {i j : ι}, i ≠ j ->
        Disjoint
          {z : T.verts | z ∈ (stemT i).support ∧ z ≠ root}
          {z : T.verts | z ∈ (stemT j).support ∧ z ≠ root} :=
    IsTree.rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
      (G := T.coe) hT stemT hstemT_path hpairT
  intro i j hij
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hzT_mem : z ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le (hstem_le i) hzi.1
  let zT : T.verts := ⟨z, hzT_mem⟩
  have hziT : zT ∈ (stemT i).support := by
    simpa [stemT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff (hstem_le i) (z := zT)).mpr hzi.1)
  have hzjT : zT ∈ (stemT j).support := by
    simpa [stemT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff (hstem_le j) (z := zT)).mpr hzj.1)
  have hzT_ne_root : zT ≠ root := by
    intro h
    exact hzi.2 (by
      have hval := congrArg (fun x : T.verts => (x : V)) h
      simpa [zT] using hval)
  exact Set.disjoint_left.mp (hdisjointT hij)
    ⟨hziT, hzT_ne_root⟩ ⟨hzjT, hzT_ne_root⟩

theorem Subgraph.tree_exists_three_terminal_rooted_paths
    {T : G.Subgraph}
    [DecidableEq T.verts]
    (hT : T.coe.IsTree)
    (terminal : Fin 3 -> T.verts) :
    Exists fun root : T.verts =>
      Exists fun stem : forall i : Fin 3,
        G.Walk (root : V) (terminal i : V) =>
        (forall i : Fin 3, (stem i).toSubgraph ≤ T) ∧
          (forall i : Fin 3, (stem i).IsPath) ∧
            forall {i j : Fin 3}, i ≠ j ->
              Disjoint
                {z : V | z ∈ (stem i).support ∧ z ≠ (root : V)}
                {z : V | z ∈ (stem j).support ∧ z ≠ (root : V)} := by
  classical
  rcases Subgraph.tree_exists_three_terminal_median
      (G := G) (T := T) hT terminal with
    ⟨root, hpair_through_root⟩
  let stem : forall i : Fin 3, G.Walk (root : V) (terminal i : V) := fun i =>
    Classical.choose
      (Subgraph.Connected.exists_path_between
        (G := G) (H := T) hT.connected root.2 (terminal i).2)
  have hstem_path : forall i : Fin 3, (stem i).IsPath := by
    intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between
        (G := G) (H := T) hT.connected root.2 (terminal i).2)).1
  have hstem_le : forall i : Fin 3, (stem i).toSubgraph ≤ T := by
    intro i
    exact (Classical.choose_spec
      (Subgraph.Connected.exists_path_between
        (G := G) (H := T) hT.connected root.2 (terminal i).2)).2
  refine ⟨root, stem, hstem_le, hstem_path, ?_⟩
  exact
    Subgraph.tree_rooted_paths_punctured_supports_disjoint_of_pair_paths_through_root_allow_eq
      (G := G) (T := T) hT stem hstem_le hstem_path
      (by
        intro i j hij
        exact hpair_through_root hij)

theorem Subgraph.tree_internalVertices_disjoint_punctured_root_path_of_endpoint_path_through_root
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {root a b : T.verts}
    (hT : T.coe.IsTree)
    {p : G.Walk (root : V) (a : V)}
    {q : G.Walk (root : V) (b : V)}
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (ha : a ≠ root)
    (hb : b ≠ root)
    {r : G.Walk (a : V) (b : V)}
    (hr_le : r.toSubgraph ≤ T)
    (hr : r.IsPath)
    (hroot_r : (root : V) ∈ r.support) :
    Disjoint
      (Walk.InternalVertices p)
      {z : V | z ∈ q.support ∧ z ≠ (root : V)} := by
  classical
  let pT : T.coe.Walk root a :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let qT : T.coe.Walk root b :=
    (Walk.liftToSubgraph q hq_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let rT : T.coe.Walk a b :=
    (Walk.liftToSubgraph r hr_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hqT : qT.IsPath := by
    simpa [qT] using Walk.liftToSubgraph_isPath hq_le hq
  have hrT : rT.IsPath := by
    simpa [rT] using Walk.liftToSubgraph_isPath hr_le hr
  have hroot_rT : root ∈ rT.support := by
    simpa [rT] using
      ((Walk.mem_support_liftToSubgraph_iff hr_le (z := root)).mpr hroot_r)
  have hdisjointT :
      Disjoint
        (Walk.InternalVertices pT)
        {z : T.verts | z ∈ qT.support ∧ z ≠ root} :=
    IsTree.internalVertices_disjoint_punctured_root_path_of_endpoint_path_through_root
      (G := T.coe) hT hpT hqT ha hb hrT hroot_rT
  rw [Set.disjoint_left]
  rintro z hz_p ⟨hz_q, hz_ne_root⟩
  have hzT_mem : z ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le hz_p.1
  let zT : T.verts := ⟨z, hzT_mem⟩
  have hzT_p_support : zT ∈ pT.support := by
    simpa [pT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff hp_le (z := zT)).mpr hz_p.1)
  have hzT_q_support : zT ∈ qT.support := by
    simpa [qT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff hq_le (z := zT)).mpr hz_q)
  have hzT_ne_root : zT ≠ root := by
    intro h
    exact hz_ne_root (by
      have hval := congrArg (fun x : T.verts => (x : V)) h
      simpa [zT] using hval)
  have hzT_ne_a : zT ≠ a := by
    intro h
    exact hz_p.2.2 (by
      have hval := congrArg (fun x : T.verts => (x : V)) h
      simpa [zT] using hval)
  exact Set.disjoint_left.mp hdisjointT
    ⟨hzT_p_support, hzT_ne_root, hzT_ne_a⟩
    ⟨hzT_q_support, hzT_ne_root⟩

theorem Subgraph.tree_endpoint_path_avoids_root_of_rooted_paths_common_nonroot
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {root a b : T.verts}
    (hT : T.coe.IsTree)
    {p : G.Walk (root : V) (a : V)}
    {q : G.Walk (root : V) (b : V)}
    {r : G.Walk (a : V) (b : V)}
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hr_le : r.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hr : r.IsPath)
    (ha : a ≠ root)
    (hb : b ≠ root)
    {z : V}
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hzroot : z ≠ (root : V)) :
    (root : V) ∉ r.support := by
  classical
  let pT : T.coe.Walk root a :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let qT : T.coe.Walk root b :=
    (Walk.liftToSubgraph q hq_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let rT : T.coe.Walk a b :=
    (Walk.liftToSubgraph r hr_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hqT : qT.IsPath := by
    simpa [qT] using Walk.liftToSubgraph_isPath hq_le hq
  have hrT : rT.IsPath := by
    simpa [rT] using Walk.liftToSubgraph_isPath hr_le hr
  have hzT_mem : z ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le hzp
  let zT : T.verts := ⟨z, hzT_mem⟩
  have hzpT : zT ∈ pT.support := by
    simpa [pT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff hp_le (z := zT)).mpr hzp)
  have hzqT : zT ∈ qT.support := by
    simpa [qT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff hq_le (z := zT)).mpr hzq)
  have hzTroot : zT ≠ root := by
    intro h
    exact hzroot (by
      have hval := congrArg (fun x : T.verts => (x : V)) h
      simpa [zT] using hval)
  have hroot_not_rT :
      root ∉ rT.support :=
    IsTree.endpoint_path_avoids_root_of_rooted_paths_common_nonroot
      (G := T.coe) hT hpT hqT hrT ha hb hzpT hzqT hzTroot
  intro hroot_r
  have hroot_rT : root ∈ rT.support := by
    simpa [rT] using
      ((Walk.mem_support_liftToSubgraph_iff hr_le (z := root)).mpr hroot_r)
  exact hroot_not_rT hroot_rT

theorem Subgraph.tree_exists_endpoint_path_avoiding_root_of_rooted_paths_common_nonroot
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {root a b : T.verts}
    (hT : T.coe.IsTree)
    {p : G.Walk (root : V) (a : V)}
    {q : G.Walk (root : V) (b : V)}
    (hp_le : p.toSubgraph ≤ T)
    (hq_le : q.toSubgraph ≤ T)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (ha : a ≠ root)
    (hb : b ≠ root)
    {z : V}
    (hzp : z ∈ p.support)
    (hzq : z ∈ q.support)
    (hzroot : z ≠ (root : V)) :
    Exists fun r : G.Walk (a : V) (b : V) =>
      r.toSubgraph ≤ T ∧ r.IsPath ∧ (root : V) ∉ r.support := by
  classical
  let pT : T.coe.Walk root a :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let qT : T.coe.Walk root b :=
    (Walk.liftToSubgraph q hq_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hqT : qT.IsPath := by
    simpa [qT] using Walk.liftToSubgraph_isPath hq_le hq
  have hzT_mem : z ∈ T.verts :=
    Walk.support_subset_of_toSubgraph_le hp_le hzp
  let zT : T.verts := ⟨z, hzT_mem⟩
  have hzpT : zT ∈ pT.support := by
    simpa [pT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff hp_le (z := zT)).mpr hzp)
  have hzqT : zT ∈ qT.support := by
    simpa [qT, zT] using
      ((Walk.mem_support_liftToSubgraph_iff hq_le (z := zT)).mpr hzq)
  have hzTroot : zT ≠ root := by
    intro h
    exact hzroot (by
      have hval := congrArg (fun x : T.verts => (x : V)) h
      simpa [zT] using hval)
  obtain ⟨rT, hrT, hroot_not_rT⟩ :=
    IsTree.exists_endpoint_path_avoiding_root_of_rooted_paths_common_nonroot
      (G := T.coe) hT hpT hqT ha hb hzpT hzqT hzTroot
  let r : G.Walk (a : V) (b : V) := rT.map T.hom
  refine ⟨r, ?_, ?_, ?_⟩
  · simpa [r] using Walk.map_subgraph_toSubgraph_le rT
  · exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hrT
  · intro hroot_r
    have hroot_map : (root : V) ∈ (rT.map T.hom).support := by
      simpa [r] using hroot_r
    rw [SimpleGraph.Walk.support_map] at hroot_map
    rcases List.mem_map.mp hroot_map with ⟨x, hx, hx_eq⟩
    have hx_root : x = root := by
      apply Subtype.ext
      exact hx_eq
    exact hroot_not_rT (by simpa [hx_root] using hx)

theorem Subgraph.tree_punctured_root_path_support_avoids_opposite_of_path_through_root
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {root other terminal : T.verts}
    (hT : T.coe.IsTree)
    {p : G.Walk (root : V) (terminal : V)}
    (hp_le : p.toSubgraph ≤ T)
    (hp : p.IsPath)
    {r : G.Walk (other : V) (terminal : V)}
    (hr_le : r.toSubgraph ≤ T)
    (hr : r.IsPath)
    (hroot_r : (root : V) ∈ r.support)
    (hother_ne_root : other ≠ root) :
    forall {z : V}, z ∈ p.support -> z ≠ (other : V) := by
  classical
  let pT : T.coe.Walk root terminal :=
    (Walk.liftToSubgraph p hp_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  let rT : T.coe.Walk other terminal :=
    (Walk.liftToSubgraph r hr_le).copy (Subtype.ext rfl) (Subtype.ext rfl)
  have hpT : pT.IsPath := by
    simpa [pT] using Walk.liftToSubgraph_isPath hp_le hp
  have hrT : rT.IsPath := by
    simpa [rT] using Walk.liftToSubgraph_isPath hr_le hr
  have hroot_rT : root ∈ rT.support := by
    simpa [rT] using
      ((Walk.mem_support_liftToSubgraph_iff hr_le (z := root)).mpr hroot_r)
  have havoidT :
      other ∉ pT.support :=
    IsTree.not_mem_root_path_support_of_opposite_path_through_root
      (G := T.coe) hT hpT hrT hroot_rT hother_ne_root
  intro z hz hz_other
  have hother_pT : other ∈ pT.support := by
    simpa [pT] using
      ((Walk.mem_support_liftToSubgraph_iff hp_le (z := other)).mpr
        (by simpa [hz_other] using hz))
  exact havoidT hother_pT

theorem Subgraph.tree_pair_paths_through_root_of_not_reachable_delete_singleton
    {T : G.Subgraph}
    [DecidableEq T.verts]
    {ι : Type*}
    {root : T.verts}
    {terminal : ι -> T.verts}
    (hT : T.coe.IsTree)
    (hterminal_ne : forall i : ι, terminal i ≠ root)
    (hunreachable :
      forall {i j : ι}, i ≠ j ->
        ¬ (T.coe.induce ({root} : Set T.verts)ᶜ).Reachable
            ⟨terminal i, by exact hterminal_ne i⟩
            ⟨terminal j, by exact hterminal_ne j⟩) :
    forall {i j : ι}, i ≠ j ->
      Exists fun p : G.Walk (terminal i : V) (terminal j : V) =>
        p.toSubgraph ≤ T ∧ p.IsPath ∧ (root : V) ∈ p.support := by
  intro i j hij
  obtain ⟨pT, hpT, hroot_pT⟩ :=
    IsTree.exists_path_through_root_of_not_reachable_delete_singleton
      (G := T.coe) hT (hterminal_ne i) (hterminal_ne j)
      (hunreachable hij)
  let p : G.Walk (terminal i : V) (terminal j : V) := pT.map T.hom
  refine ⟨p, ?_, ?_, ?_⟩
  · simpa [p] using Walk.map_subgraph_toSubgraph_le pT
  · exact SimpleGraph.Walk.map_isPath_of_injective
      SimpleGraph.Subgraph.hom_injective hpT
  · have hroot_map : (root : V) ∈ (pT.map T.hom).support := by
      rw [SimpleGraph.Walk.support_map]
      exact List.mem_map.mpr ⟨root, hroot_pT, rfl⟩
    simpa [p] using hroot_map

theorem IsTree.path_eq_reverse_of_isPath
    {u v : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    p = q.reverse := by
  exact IsTree.path_eq_of_isPath hT hp hq.reverse

theorem IsTree.support_eq_reverse_of_isPath
    {u v : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    p.support = q.reverse.support := by
  rw [IsTree.path_eq_reverse_of_isPath hT hp hq]

theorem IsTree.mem_support_iff_reverse_of_isPath
    {u v z : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    z ∈ p.support ↔ z ∈ q.support := by
  rw [IsTree.support_eq_reverse_of_isPath hT hp hq]
  rw [SimpleGraph.Walk.support_reverse]
  exact ⟨fun hz => List.mem_reverse.mp hz, fun hz => List.mem_reverse.mpr hz⟩

theorem IsTree.internalVertices_eq_reverse_of_isPath
    {u v : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    Walk.InternalVertices p = Walk.InternalVertices q := by
  rw [IsTree.path_eq_reverse_of_isPath hT hp hq]
  exact Walk.internalVertices_reverse q

theorem IsTree.mem_internalVertices_iff_reverse_of_isPath
    {u v z : V}
    (hT : G.IsTree)
    {p : G.Walk u v}
    {q : G.Walk v u}
    (hp : p.IsPath)
    (hq : q.IsPath) :
    z ∈ Walk.InternalVertices p ↔ z ∈ Walk.InternalVertices q := by
  rw [IsTree.internalVertices_eq_reverse_of_isPath hT hp hq]

noncomputable def Subgraph.spanningVertsEquiv
    {B : G.Subgraph}
    (T : B.coe.Subgraph)
    (hT_spanning : T.IsSpanning) :
    B.verts ≃ T.verts where
  toFun v := ⟨v, hT_spanning v⟩
  invFun v := v
  left_inv v := rfl
  right_inv v := by
    exact Subtype.ext rfl


end Schematic.Math.GraphTheory
