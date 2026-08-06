import Schematic.Math.GraphTheory.Minors.Rerouting.FoldedSeparation

/-! The minimal YZ rerouting certificate and contraction consequences. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/--
Specialized certificate for the KNTW/Tutte rerouting step used in the main
induction. KNTW Lemma 2.1 (`prestable`) and Theorem 2.2 (`stable`) are stated
for bridge-stabilizing proper reroutings; this structure records the
consequence needed by `2605.10112_tex/main.tex`, lines 453-470.

`core` is the component called `H` in the paper, after choosing the minimal
rerouted `yz` path. The last field is the key output: every vertex of the
rerouted path has a neighbour in `H`.
-/
structure MinimalYZReroutingCertificate
    {V : Type u} (G : SimpleGraph V) (A : Set V)
    (v1 x y z : V) where
  pathX : G.Walk v1 x
  pathX_isPath : pathX.IsPath
  pathX_support_subset_left :
    forall a : V, a ∈ pathX.support -> a ∈ A
  pathYZ : G.Walk y z
  pathYZ_isPath : pathYZ.IsPath
  pathYZ_chordless : pathYZ.IsChordless
  pathYZ_support_subset_left :
    forall a : V, a ∈ pathYZ.support -> a ∈ A
  pathX_pathYZ_disjoint :
    Disjoint {a : V | a ∈ pathX.support} {a : V | a ∈ pathYZ.support}
  core : G.Subgraph
  core_connected : core.coe.Connected
  core_subset_left : core.verts ⊆ A
  v1_mem_core : v1 ∈ core.verts
  x_mem_core : x ∈ core.verts
  pathX_support_subset_core :
    forall a : V, a ∈ pathX.support -> a ∈ core.verts
  pathYZ_disjoint_core :
    Disjoint {a : V | a ∈ pathYZ.support} core.verts
  pathYZ_vertices_adjacent_core :
    forall a : V, a ∈ pathYZ.support ->
      Exists fun h : V => h ∈ core.verts ∧ G.Adj h a

noncomputable def MinimalYZReroutingCertificate.ofFoldedLinkageAndCore
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageData G root v1 x y z)
    (hpathX_left :
      forall a : V, a ∈ F.pathX.support -> a ∈ A)
    (hpathYZ_left :
      forall a : V, a ∈ F.pathYZ.support -> a ∈ A)
    (hpathYZ_chordless : F.pathYZ.IsChordless)
    (core : G.Subgraph)
    (core_connected : core.coe.Connected)
    (core_subset_left : core.verts ⊆ A)
    (v1_mem_core : v1 ∈ core.verts)
    (x_mem_core : x ∈ core.verts)
    (pathX_support_subset_core :
      forall a : V, a ∈ F.pathX.support -> a ∈ core.verts)
    (pathYZ_disjoint_core :
      Disjoint {a : V | a ∈ F.pathYZ.support} core.verts)
    (pathYZ_vertices_adjacent_core :
      forall a : V, a ∈ F.pathYZ.support ->
        Exists fun h : V => h ∈ core.verts ∧ G.Adj h a) :
    MinimalYZReroutingCertificate G A v1 x y z where
  pathX := F.pathX
  pathX_isPath := F.pathX_isPath
  pathX_support_subset_left := hpathX_left
  pathYZ := F.pathYZ
  pathYZ_isPath := F.pathYZ_isPath
  pathYZ_chordless := hpathYZ_chordless
  pathYZ_support_subset_left := hpathYZ_left
  pathX_pathYZ_disjoint := F.pathX_pathYZ_disjoint
  core := core
  core_connected := core_connected
  core_subset_left := core_subset_left
  v1_mem_core := v1_mem_core
  x_mem_core := x_mem_core
  pathX_support_subset_core := pathX_support_subset_core
  pathYZ_disjoint_core := pathYZ_disjoint_core
  pathYZ_vertices_adjacent_core := pathYZ_vertices_adjacent_core

noncomputable def MinimalYZReroutingCertificate.ofFoldedLinkageInSetAndComponentCore
    [DecidableEq V]
    {A : Set V} {root v1 x y z : V}
    (F : FoldedDuplicateLinkageDataInSet G A root v1 x y z)
    (hpathYZ_chordless : F.toLinkage.pathYZ.IsChordless)
    (hpathYZ_vertices_adjacent_core :
      forall a : V, a ∈ F.toLinkage.pathYZ.support ->
        Exists fun h : V => h ∈ F.pathXComponentCore.verts ∧ G.Adj h a) :
    MinimalYZReroutingCertificate G A v1 x y z :=
  MinimalYZReroutingCertificate.ofFoldedLinkageAndCore
    (G := G) (A := A) F.toLinkage
    F.pathX_support_subset_set
    F.pathYZ_support_subset_set
    hpathYZ_chordless
    F.pathXComponentCore
    F.pathXComponentCore_connected
    F.pathXComponentCore_subset_set
    F.v1_mem_pathXComponentCore
    F.x_mem_pathXComponentCore
    F.pathX_support_subset_pathXComponentCore
    F.pathYZ_disjoint_pathXComponentCore
    hpathYZ_vertices_adjacent_core

theorem MinimalYZReroutingCertificate.y_adjacent_core
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    Exists fun h : V => h ∈ R.core.verts ∧ G.Adj h y := by
  exact R.pathYZ_vertices_adjacent_core y R.pathYZ.start_mem_support

theorem MinimalYZReroutingCertificate.z_adjacent_core
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    Exists fun h : V => h ∈ R.core.verts ∧ G.Adj h z := by
  exact R.pathYZ_vertices_adjacent_core z R.pathYZ.end_mem_support

theorem MinimalYZReroutingCertificate.pathX_support_subset_left_set
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    forall a : V, a ∈ R.pathX.support -> a ∈ A := by
  exact R.pathX_support_subset_left

theorem MinimalYZReroutingCertificate.pathX_support_subset_core_verts
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    forall a : V, a ∈ R.pathX.support -> a ∈ R.core.verts := by
  exact R.pathX_support_subset_core

theorem MinimalYZReroutingCertificate.pathYZ_support_disjoint_core
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    forall a : V, a ∈ R.pathYZ.support -> a ∉ R.core.verts := by
  intro a ha hcore
  exact Set.disjoint_left.mp R.pathYZ_disjoint_core ha hcore

theorem MinimalYZReroutingCertificate.y_not_mem_core
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    y ∉ R.core.verts := by
  exact R.pathYZ_support_disjoint_core y R.pathYZ.start_mem_support

theorem MinimalYZReroutingCertificate.z_not_mem_core
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    z ∉ R.core.verts := by
  exact R.pathYZ_support_disjoint_core z R.pathYZ.end_mem_support

theorem MinimalYZReroutingCertificate.core_right_intersection_eq_x_of_triple_separator
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    forall r : V, r ∈ S.right -> r ∈ R.core.verts -> r = x := by
  intro r hr_right hr_core
  have hr_left : r ∈ S.left := R.core_subset_left hr_core
  have hr_sep : r ∈ S.separator := ⟨hr_left, hr_right⟩
  have hr_xyz : r = x ∨ r = y ∨ r = z := by
    have : r ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using hr_sep
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  rcases hr_xyz with hr_x | hr_y | hr_z
  · exact hr_x
  · exact False.elim (R.y_not_mem_core (by simpa [hr_y] using hr_core))
  · exact False.elim (R.z_not_mem_core (by simpa [hr_z] using hr_core))

theorem MinimalYZReroutingCertificate.pathYZ_toSubgraph_isInduced
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.pathYZ.toSubgraph.IsInduced := by
  exact Schematic.Math.GraphTheory.Walk.IsChordless.toSubgraph_isInduced R.pathYZ_chordless

theorem MinimalYZReroutingCertificate.pathYZ_not_nil
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    ¬ R.pathYZ.Nil :=
  SimpleGraph.Walk.not_nil_of_ne (p := R.pathYZ) hyz

theorem MinimalYZReroutingCertificate.collapse_pathYZ_dropLast_adj_yz
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    let H : G.Subgraph := R.pathYZ.dropLast.toSubgraph
    let hH_connected : H.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZ_isPath (R.pathYZ_not_nil hyz)).1
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G H hH_connected
    C.graph.Adj (C.map y) (C.map z) := by
  intro H hH_connected C
  exact Walk.IsPath.collapse_dropLast_adj_end
    R.pathYZ_isPath (R.pathYZ_not_nil hyz)

theorem MinimalYZReroutingCertificate.collapse_core_adj_pathYZ
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G R.core R.core_connected
    forall a : V, a ∈ R.pathYZ.support -> C.graph.Adj (C.map v1) (C.map a) := by
  classical
  intro C a ha
  obtain ⟨h, hh_core, hha⟩ := R.pathYZ_vertices_adjacent_core a ha
  have ha_not_core : a ∉ R.core.verts := by
    intro ha_core
    exact Set.disjoint_left.mp R.pathYZ_disjoint_core ha ha_core
  have hh_map : C.map h = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G R.core R.core_connected hh_core
  have hv1_map : C.map v1 = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G R.core R.core_connected R.v1_mem_core
  have ha_map :
      C.map a =
        some (⟨a, ha_not_core⟩ : {v : V // v ∉ R.core.verts}) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
        G R.core R.core_connected ha_not_core
  have hne : C.map h ≠ C.map a := by
    rw [hh_map, ha_map]
    simp
  rcases C.map_adj hha with hsame | hadj
  · exact False.elim (hne hsame)
  · simpa [hv1_map, hh_map] using hadj

theorem MinimalYZReroutingCertificate.collapse_core_adj_y
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G R.core R.core_connected
    C.graph.Adj (C.map v1) (C.map y) := by
  intro C
  exact R.collapse_core_adj_pathYZ y R.pathYZ.start_mem_support

theorem MinimalYZReroutingCertificate.collapse_core_adj_z
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G R.core R.core_connected
    C.graph.Adj (C.map v1) (C.map z) := by
  intro C
  exact R.collapse_core_adj_pathYZ z R.pathYZ.end_mem_support

theorem MinimalYZReroutingCertificate.collapse_core_injective_on_set
    {A B : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hcore_intersection : forall r : V, r ∈ B -> r ∈ R.core.verts -> r = x) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G R.core R.core_connected
    Function.Injective (fun r : B => C.map (r : V)) := by
  classical
  intro C r s hrs
  have hcases :
      (((r : V) ∈ R.core.verts ∧ (s : V) ∈ R.core.verts) ∨
        ((r : V) = (s : V) ∧
          (r : V) ∉ R.core.verts ∧ (s : V) ∉ R.core.verts)) := by
    simpa [C] using
      (GraphContraction.collapseSubgraph_map_eq_iff
        G R.core R.core_connected (v := (r : V)) (w := (s : V))).mp hrs
  rcases hcases with hboth | hout
  · have hrx : (r : V) = x := hcore_intersection (r : V) r.2 hboth.1
    have hsx : (s : V) = x := hcore_intersection (s : V) s.2 hboth.2
    exact Subtype.ext (hrx.trans hsx.symm)
  · exact Subtype.ext hout.1

theorem MinimalYZReroutingCertificate.collapse_core_injective_on_right_of_triple_separator
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G R.core R.core_connected
    Function.Injective (fun r : S.right => C.map (r : V)) := by
  intro C
  exact R.collapse_core_injective_on_set
    (B := S.right)
    (R.core_right_intersection_eq_x_of_triple_separator hseparator)

theorem MinimalYZReroutingCertificate.collapse_core_injective_on_pathYZ_support
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    let C : GraphContraction G :=
      GraphContraction.collapseSubgraph G R.core R.core_connected
    Function.Injective
      (fun r : {a : V // a ∈ R.pathYZ.support} => C.map (r : V)) := by
  intro C
  exact R.collapse_core_injective_on_set
    (B := {a : V | a ∈ R.pathYZ.support})
    (by
      intro r hr_path hr_core
      exact False.elim (R.pathYZ_support_disjoint_core r hr_path hr_core))

noncomputable def MinimalYZReroutingCertificate.coreCollapse
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    GraphContraction G :=
  GraphContraction.collapseSubgraph G R.core R.core_connected

@[simp]
theorem MinimalYZReroutingCertificate.coreCollapse_map_v1
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.map v1 = (none : R.coreCollapse.Target) := by
  simpa [MinimalYZReroutingCertificate.coreCollapse] using
    GraphContraction.collapseSubgraph_map_eq_none_of_mem
      G R.core R.core_connected R.v1_mem_core

@[simp]
theorem MinimalYZReroutingCertificate.coreCollapse_map_x
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.map x = (none : R.coreCollapse.Target) := by
  simpa [MinimalYZReroutingCertificate.coreCollapse] using
    GraphContraction.collapseSubgraph_map_eq_none_of_mem
      G R.core R.core_connected R.x_mem_core

theorem MinimalYZReroutingCertificate.coreCollapse_map_x_eq_map_v1
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.map x = R.coreCollapse.map v1 := by
  rw [R.coreCollapse_map_x, R.coreCollapse_map_v1]

theorem MinimalYZReroutingCertificate.coreCollapse_adj_v1_y
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map y) := by
  simpa [MinimalYZReroutingCertificate.coreCollapse] using R.collapse_core_adj_y

theorem MinimalYZReroutingCertificate.coreCollapse_adj_v1_z
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.graph.Adj (R.coreCollapse.map v1) (R.coreCollapse.map z) := by
  simpa [MinimalYZReroutingCertificate.coreCollapse] using R.collapse_core_adj_z

theorem MinimalYZReroutingCertificate.coreCollapse_adj_x_y
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.graph.Adj (R.coreCollapse.map x) (R.coreCollapse.map y) := by
  simpa [R.coreCollapse_map_x_eq_map_v1] using R.coreCollapse_adj_v1_y

theorem MinimalYZReroutingCertificate.coreCollapse_adj_x_z
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.graph.Adj (R.coreCollapse.map x) (R.coreCollapse.map z) := by
  simpa [R.coreCollapse_map_x_eq_map_v1] using R.coreCollapse_adj_v1_z

theorem MinimalYZReroutingCertificate.coreCollapse_injective_on_pathYZ_support_vertices
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    forall a b : V, a ∈ R.pathYZ.support -> b ∈ R.pathYZ.support ->
      R.coreCollapse.map a = R.coreCollapse.map b -> a = b := by
  classical
  have hinj :
      Function.Injective
        (fun r : {a : V // a ∈ R.pathYZ.support} =>
          R.coreCollapse.map (r : V)) := by
    simpa [MinimalYZReroutingCertificate.coreCollapse] using
      R.collapse_core_injective_on_pathYZ_support
  intro a b ha hb hab
  have hsub :
      (fun r : {a : V // a ∈ R.pathYZ.support} =>
        R.coreCollapse.map (r : V)) ⟨a, ha⟩ =
        (fun r : {a : V // a ∈ R.pathYZ.support} =>
          R.coreCollapse.map (r : V)) ⟨b, hb⟩ := hab
  exact congrArg Subtype.val
    (hinj hsub)

noncomputable def MinimalYZReroutingCertificate.pathYZInCoreCollapse
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.coreCollapse.graph.Walk (R.coreCollapse.map y) (R.coreCollapse.map z) :=
  GraphContraction.mapWalkOfSupportInjective R.coreCollapse R.pathYZ
    R.coreCollapse_injective_on_pathYZ_support_vertices

theorem MinimalYZReroutingCertificate.pathYZInCoreCollapse_support
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.pathYZInCoreCollapse.support = R.pathYZ.support.map R.coreCollapse.map := by
  simpa [MinimalYZReroutingCertificate.pathYZInCoreCollapse] using
    GraphContraction.support_mapWalkOfSupportInjective
      R.coreCollapse R.pathYZ
      R.coreCollapse_injective_on_pathYZ_support_vertices

theorem MinimalYZReroutingCertificate.pathYZInCoreCollapse_isPath
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    R.pathYZInCoreCollapse.IsPath := by
  simpa [MinimalYZReroutingCertificate.pathYZInCoreCollapse] using
    GraphContraction.isPath_mapWalkOfSupportInjective
      R.coreCollapse R.pathYZ R.pathYZ_isPath
      R.coreCollapse_injective_on_pathYZ_support_vertices

theorem MinimalYZReroutingCertificate.coreCollapse_adj_pathYZInCoreCollapse_support
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z) :
    forall a : R.coreCollapse.Target, a ∈ R.pathYZInCoreCollapse.support ->
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) a := by
  intro a ha
  rw [R.pathYZInCoreCollapse_support] at ha
  simp only [List.mem_map] at ha
  rcases ha with ⟨b, hb, rfl⟩
  exact R.collapse_core_adj_pathYZ b hb

theorem MinimalYZReroutingCertificate.coreCollapse_map_y_ne_z
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    R.coreCollapse.map y ≠ R.coreCollapse.map z := by
  intro hmap
  exact hyz
    (R.coreCollapse_injective_on_pathYZ_support_vertices y z
      R.pathYZ.start_mem_support R.pathYZ.end_mem_support hmap)

theorem MinimalYZReroutingCertificate.pathYZInCoreCollapse_not_nil
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    ¬ R.pathYZInCoreCollapse.Nil :=
  SimpleGraph.Walk.not_nil_of_ne
    (p := R.pathYZInCoreCollapse) (R.coreCollapse_map_y_ne_z hyz)

theorem MinimalYZReroutingCertificate.pathZYInCoreCollapse_not_nil
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    ¬ R.pathYZInCoreCollapse.reverse.Nil :=
  SimpleGraph.Walk.not_nil_of_ne
    (p := R.pathYZInCoreCollapse.reverse)
    (R.coreCollapse_map_y_ne_z hyz).symm

theorem MinimalYZReroutingCertificate.pathYZInCoreCollapse_dropLast_neighbor_first
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    forall a : R.coreCollapse.Target, a ∈ H2.verts ->
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) a := by
  intro P H2 a ha
  have ha_drop : a ∈ P.dropLast.support := by
    rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at ha
  have ha_support : a ∈ P.support := by
    have hdrop : P.dropLast.support = P.support.dropLast :=
      SimpleGraph.Walk.support_dropLast
        (R.pathYZInCoreCollapse_not_nil hyz)
    rw [hdrop] at ha_drop
    exact List.mem_of_mem_dropLast ha_drop
  exact R.coreCollapse_adj_pathYZInCoreCollapse_support a (by
    simpa [P] using ha_support)

theorem MinimalYZReroutingCertificate.pathZYInCoreCollapse_dropLast_neighbor_first
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    forall a : R.coreCollapse.Target, a ∈ H2.verts ->
      R.coreCollapse.graph.Adj (R.coreCollapse.map v1) a := by
  intro P H2 a ha
  have ha_drop : a ∈ P.dropLast.support := by
    rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at ha
  have ha_support : a ∈ P.support := by
    have hdrop : P.dropLast.support = P.support.dropLast :=
      SimpleGraph.Walk.support_dropLast
        (R.pathZYInCoreCollapse_not_nil hyz)
    rw [hdrop] at ha_drop
    exact List.mem_of_mem_dropLast ha_drop
  exact R.coreCollapse_adj_pathYZInCoreCollapse_support a (by
    simpa [P, SimpleGraph.Walk.support_reverse] using ha_support)

theorem MinimalYZReroutingCertificate.coreCollapse_map_mem_pathYZInCoreCollapse_dropLast
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    {a : V}
    (ha : a ∈ R.pathYZ.support)
    (haz : a ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    R.coreCollapse.map a ∈ P.dropLast.toSubgraph.verts := by
  intro P
  have ha_support : R.coreCollapse.map a ∈ P.support := by
    rw [R.pathYZInCoreCollapse_support]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hmap_ne_z : R.coreCollapse.map a ≠ R.coreCollapse.map z := by
    intro hmap
    exact haz
      (R.coreCollapse_injective_on_pathYZ_support_vertices a z ha
        R.pathYZ.end_mem_support hmap)
  have ha_drop : R.coreCollapse.map a ∈ P.support.dropLast := by
    exact List.mem_dropLast_of_mem_of_ne_getLast ha_support (by
      simpa [SimpleGraph.Walk.getLast_support P] using hmap_ne_z)
  have ha_drop_support : R.coreCollapse.map a ∈ P.dropLast.support := by
    rwa [SimpleGraph.Walk.support_dropLast
      (R.pathYZInCoreCollapse_not_nil hyz)]
  rwa [SimpleGraph.Walk.mem_verts_toSubgraph]

theorem MinimalYZReroutingCertificate.coreCollapse_map_mem_pathZYInCoreCollapse_dropLast
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z)
    {a : V}
    (ha : a ∈ R.pathYZ.support)
    (hay : a ≠ y) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    R.coreCollapse.map a ∈ P.dropLast.toSubgraph.verts := by
  intro P
  have ha_forward : R.coreCollapse.map a ∈ R.pathYZInCoreCollapse.support := by
    rw [R.pathYZInCoreCollapse_support]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have ha_support : R.coreCollapse.map a ∈ P.support := by
    simpa [P, SimpleGraph.Walk.support_reverse] using ha_forward
  have hmap_ne_y : R.coreCollapse.map a ≠ R.coreCollapse.map y := by
    intro hmap
    exact hay
      (R.coreCollapse_injective_on_pathYZ_support_vertices a y ha
        R.pathYZ.start_mem_support hmap)
  have ha_drop : R.coreCollapse.map a ∈ P.support.dropLast := by
    exact List.mem_dropLast_of_mem_of_ne_getLast ha_support (by
      simpa [SimpleGraph.Walk.getLast_support P] using hmap_ne_y)
  have ha_drop_support : R.coreCollapse.map a ∈ P.dropLast.support := by
    rwa [SimpleGraph.Walk.support_dropLast
      (R.pathZYInCoreCollapse_not_nil hyz)]
  rwa [SimpleGraph.Walk.mem_verts_toSubgraph]

theorem MinimalYZReroutingCertificate.right_mem_pathYZ_support_eq_y_or_z
    {S : Separation G} {v1 x y z r : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hr_right : r ∈ S.right)
    (hr_path : r ∈ R.pathYZ.support) :
    r = y ∨ r = z := by
  have hr_left : r ∈ S.left := R.pathYZ_support_subset_left r hr_path
  have hr_sep : r ∈ S.separator := ⟨hr_left, hr_right⟩
  have hr_triple : r = x ∨ r = y ∨ r = z := by
    have : r ∈ ({x, y, z} : Set V) := by
      simpa [hseparator] using hr_sep
    simpa [Set.mem_insert_iff] using this
  rcases hr_triple with rfl | rfl | rfl
  · exact False.elim
      (Set.disjoint_left.mp R.pathYZ_disjoint_core hr_path R.x_mem_core)
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem MinimalYZReroutingCertificate.right_mem_pathYZInCoreCollapse_dropLast_eq_y
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (r : S.right) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    R.coreCollapse.map (r : V) ∈ P.dropLast.toSubgraph.verts ->
      (r : V) = y := by
  intro P hr_mem
  have hr_drop : R.coreCollapse.map (r : V) ∈ P.dropLast.support := by
    rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hr_mem
  have hr_support_P : R.coreCollapse.map (r : V) ∈ P.support := by
    have hdrop : P.dropLast.support = P.support.dropLast :=
      SimpleGraph.Walk.support_dropLast
        (R.pathYZInCoreCollapse_not_nil hyz)
    rw [hdrop] at hr_drop
    exact List.mem_of_mem_dropLast hr_drop
  have hr_support :
      R.coreCollapse.map (r : V) ∈ R.pathYZInCoreCollapse.support := by
    simpa [P] using hr_support_P
  rw [R.pathYZInCoreCollapse_support] at hr_support
  rcases List.mem_map.mp hr_support with ⟨a, ha_path, hmap_a⟩
  have ha_not_core : a ∉ R.core.verts := by
    intro ha_core
    exact Set.disjoint_left.mp R.pathYZ_disjoint_core ha_path ha_core
  have hmap_eq : R.coreCollapse.map a = R.coreCollapse.map (r : V) := hmap_a
  have hcases :
      (a ∈ R.core.verts ∧ (r : V) ∈ R.core.verts) ∨
        (a = (r : V) ∧ a ∉ R.core.verts ∧ (r : V) ∉ R.core.verts) := by
    simpa [MinimalYZReroutingCertificate.coreCollapse] using
      (GraphContraction.collapseSubgraph_map_eq_iff
        G R.core R.core_connected (v := a) (w := (r : V))).mp hmap_eq
  have hr_path : (r : V) ∈ R.pathYZ.support := by
    rcases hcases with hboth | hout
    · exact False.elim (ha_not_core hboth.1)
    · simpa [hout.1] using ha_path
  rcases R.right_mem_pathYZ_support_eq_y_or_z hseparator r.2 hr_path with hr_y | hr_z
  · exact hr_y
  · have hz_not_drop : R.coreCollapse.map z ∉ P.dropLast.support := by
      exact Walk.IsPath.end_notMem_walk_dropLast_support
        R.pathYZInCoreCollapse_isPath (R.pathYZInCoreCollapse_not_nil hyz)
    exact False.elim (hz_not_drop (by simpa [hr_z] using hr_drop))

theorem MinimalYZReroutingCertificate.secondCollapse_injective_on_right_of_triple_separator
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath
        (R.pathYZInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    Function.Injective (fun r : S.right => D.map (R.coreCollapse.map (r : V))) := by
  intro P H2 hH2_connected D
  apply GraphContraction.collapseSubgraph_comp_injective
    R.coreCollapse.graph H2 hH2_connected
    (fun r : S.right => R.coreCollapse.map (r : V))
  · simpa [MinimalYZReroutingCertificate.coreCollapse] using
      R.collapse_core_injective_on_right_of_triple_separator hseparator
  · intro r s hr_mem hs_mem
    have hr_y : (r : V) = y :=
      R.right_mem_pathYZInCoreCollapse_dropLast_eq_y hseparator hyz r (by
        simpa [P, H2] using hr_mem)
    have hs_y : (s : V) = y :=
      R.right_mem_pathYZInCoreCollapse_dropLast_eq_y hseparator hyz s (by
        simpa [P, H2] using hs_mem)
    exact Subtype.ext (hr_y.trans hs_y.symm)

theorem MinimalYZReroutingCertificate.right_mem_pathZYInCoreCollapse_dropLast_eq_z
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z)
    (r : S.right) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    R.coreCollapse.map (r : V) ∈ P.dropLast.toSubgraph.verts ->
      (r : V) = z := by
  intro P hr_mem
  have hr_drop : R.coreCollapse.map (r : V) ∈ P.dropLast.support := by
    rwa [SimpleGraph.Walk.mem_verts_toSubgraph] at hr_mem
  have hr_support_P : R.coreCollapse.map (r : V) ∈ P.support := by
    have hdrop : P.dropLast.support = P.support.dropLast :=
      SimpleGraph.Walk.support_dropLast
        (R.pathZYInCoreCollapse_not_nil hyz)
    rw [hdrop] at hr_drop
    exact List.mem_of_mem_dropLast hr_drop
  have hr_support :
      R.coreCollapse.map (r : V) ∈ R.pathYZInCoreCollapse.support := by
    simpa [P, SimpleGraph.Walk.support_reverse] using hr_support_P
  rw [R.pathYZInCoreCollapse_support] at hr_support
  rcases List.mem_map.mp hr_support with ⟨a, ha_path, hmap_a⟩
  have ha_not_core : a ∉ R.core.verts := by
    intro ha_core
    exact Set.disjoint_left.mp R.pathYZ_disjoint_core ha_path ha_core
  have hmap_eq : R.coreCollapse.map a = R.coreCollapse.map (r : V) := hmap_a
  have hcases :
      (a ∈ R.core.verts ∧ (r : V) ∈ R.core.verts) ∨
        (a = (r : V) ∧ a ∉ R.core.verts ∧ (r : V) ∉ R.core.verts) := by
    simpa [MinimalYZReroutingCertificate.coreCollapse] using
      (GraphContraction.collapseSubgraph_map_eq_iff
        G R.core R.core_connected (v := a) (w := (r : V))).mp hmap_eq
  have hr_path : (r : V) ∈ R.pathYZ.support := by
    rcases hcases with hboth | hout
    · exact False.elim (ha_not_core hboth.1)
    · simpa [hout.1] using ha_path
  rcases R.right_mem_pathYZ_support_eq_y_or_z hseparator r.2 hr_path with hr_y | hr_z
  · have hy_not_drop : R.coreCollapse.map y ∉ P.dropLast.support := by
      exact Walk.IsPath.end_notMem_walk_dropLast_support
        R.pathYZInCoreCollapse_isPath.reverse (R.pathZYInCoreCollapse_not_nil hyz)
    exact False.elim (hy_not_drop (by simpa [hr_y] using hr_drop))
  · exact hr_z

theorem MinimalYZReroutingCertificate.secondReverseCollapse_injective_on_right_of_triple_separator
    {S : Separation G} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G S.left v1 x y z)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hyz : y ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath.reverse
        (R.pathZYInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    Function.Injective (fun r : S.right => D.map (R.coreCollapse.map (r : V))) := by
  intro P H2 hH2_connected D
  apply GraphContraction.collapseSubgraph_comp_injective
    R.coreCollapse.graph H2 hH2_connected
    (fun r : S.right => R.coreCollapse.map (r : V))
  · simpa [MinimalYZReroutingCertificate.coreCollapse] using
      R.collapse_core_injective_on_right_of_triple_separator hseparator
  · intro r s hr_mem hs_mem
    have hr_z : (r : V) = z :=
      R.right_mem_pathZYInCoreCollapse_dropLast_eq_z hseparator hyz r (by
        simpa [P, H2] using hr_mem)
    have hs_z : (s : V) = z :=
      R.right_mem_pathZYInCoreCollapse_dropLast_eq_z hseparator hyz s (by
        simpa [P, H2] using hs_mem)
    exact Subtype.ext (hr_z.trans hs_z.symm)

theorem MinimalYZReroutingCertificate.collapse_pathYZInCoreCollapse_dropLast_adj_yz
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map y) (R.coreCollapse.map z) :=
      R.pathYZInCoreCollapse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath
        (R.pathYZInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    D.graph.Adj
      (D.map (R.coreCollapse.map y))
      (D.map (R.coreCollapse.map z)) := by
  intro P H2 hH2_connected D
  exact Walk.IsPath.collapse_dropLast_adj_end
    R.pathYZInCoreCollapse_isPath
    (R.pathYZInCoreCollapse_not_nil hyz)

theorem MinimalYZReroutingCertificate.collapse_pathZYInCoreCollapse_dropLast_adj_zy
    {A : Set V} {v1 x y z : V}
    (R : MinimalYZReroutingCertificate G A v1 x y z)
    (hyz : y ≠ z) :
    let P : R.coreCollapse.graph.Walk
        (R.coreCollapse.map z) (R.coreCollapse.map y) :=
      R.pathYZInCoreCollapse.reverse
    let H2 : R.coreCollapse.graph.Subgraph := P.dropLast.toSubgraph
    let hH2_connected : H2.coe.Connected :=
      (Walk.IsPath.dropLast_toSubgraph_contracts_to_endpoint_neighbor
        R.pathYZInCoreCollapse_isPath.reverse
        (R.pathZYInCoreCollapse_not_nil hyz)).1
    let D : GraphContraction R.coreCollapse.graph :=
      GraphContraction.collapseSubgraph R.coreCollapse.graph H2 hH2_connected
    D.graph.Adj
      (D.map (R.coreCollapse.map z))
      (D.map (R.coreCollapse.map y)) := by
  intro P H2 hH2_connected D
  exact Walk.IsPath.collapse_dropLast_adj_end
    R.pathYZInCoreCollapse_isPath.reverse
    (R.pathZYInCoreCollapse_not_nil hyz)


end Schematic.Math.GraphTheory
