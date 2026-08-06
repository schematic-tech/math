import Schematic.Math.GraphTheory.Subdivisions

/-!
Foundational planarity interface.

This file intentionally avoids importing the hypermap four-colour development.
The bridge and final theorem wrapper live above it, so the graph-planarity API
can be used by the bridge without an import cycle.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

structure IsPlanar {V : Type u} (G : SimpleGraph V) : Prop where
  no_K5_subdivision : Not (ContainsStrictSubdivision K5Graph G)
  no_K33_subdivision : Not (ContainsStrictSubdivision K33Graph G)

def IsStrictPlanar {V : Type u} (G : SimpleGraph V) : Prop :=
  Not (ContainsStrictSubdivision K5Graph G) ∧
    Not (ContainsStrictSubdivision K33Graph G)

theorem IsPlanar.mono
    {V : Type u} {G H : SimpleGraph V}
    (hHG : H ≤ G)
    (h_planar : IsPlanar G) :
    IsPlanar H := by
  refine ⟨?_, ?_⟩
  · intro hK5
    exact h_planar.no_K5_subdivision (ContainsStrictSubdivision.of_le hHG hK5)
  · intro hK33
    exact h_planar.no_K33_subdivision (ContainsStrictSubdivision.of_le hHG hK33)

theorem IsPlanar.of_injective_hom
    {V : Type u} {U : Type*} {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h_planar : IsPlanar G') :
    IsPlanar G := by
  refine ⟨?_, ?_⟩
  · intro hK5
    exact h_planar.no_K5_subdivision
      (ContainsStrictSubdivision.map f hf hK5)
  · intro hK33
    exact h_planar.no_K33_subdivision
      (ContainsStrictSubdivision.map f hf hK33)

theorem IsPlanar.of_iso
    {V : Type u} {U : Type*} {G : SimpleGraph V} {G' : SimpleGraph U}
    (e : G ≃g G')
    (h_planar : IsPlanar G') :
    IsPlanar G :=
  IsPlanar.of_injective_hom e.toHom e.injective h_planar

theorem IsPlanar.induce
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (S : Set V) :
    IsPlanar (G.induce S) :=
  IsPlanar.of_injective_hom
    (SimpleGraph.Embedding.induce (G := G) S).toHom
    (SimpleGraph.Embedding.induce (G := G) S).injective
    h_planar

/-- Planarity descends to every connected component.  This is the recursive
input needed by the disconnected branch of the Kuratowski/FCT bridge. -/
theorem IsPlanar.connectedComponent_toSimpleGraph
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (C : G.ConnectedComponent) :
    IsPlanar C.toSimpleGraph := by
  simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using
    h_planar.induce C.supp

theorem IsPlanar.deleteEdges
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (S : Set (Sym2 V)) :
    IsPlanar (G.deleteEdges S) :=
  h_planar.mono (SimpleGraph.deleteEdges_le S)

theorem containsStrictSubdivision_K5_induce_support
    {V : Type u} {G : SimpleGraph V}
    (hK5 : ContainsStrictSubdivision K5Graph G) :
    ContainsStrictSubdivision K5Graph (G.induce G.support) :=
  hK5.targetRestrictSupport K5Graph_exists_adj

theorem containsStrictSubdivision_K33_induce_support
    {V : Type u} {G : SimpleGraph V}
    (hK33 : ContainsStrictSubdivision K33Graph G) :
    ContainsStrictSubdivision K33Graph (G.induce G.support) :=
  hK33.targetRestrictSupport K33Graph_exists_adj

theorem containsStrictSubdivision_K5_induce_of_support_subset
    {V : Type u} {G : SimpleGraph V}
    (hK5 : ContainsStrictSubdivision K5Graph G)
    {S : Set V}
    (hS : G.support ⊆ S) :
    ContainsStrictSubdivision K5Graph (G.induce S) :=
  hK5.targetRestrictOfSupportSubset K5Graph_exists_adj hS

theorem containsStrictSubdivision_K33_induce_of_support_subset
    {V : Type u} {G : SimpleGraph V}
    (hK33 : ContainsStrictSubdivision K33Graph G)
    {S : Set V}
    (hS : G.support ⊆ S) :
    ContainsStrictSubdivision K33Graph (G.induce S) :=
  hK33.targetRestrictOfSupportSubset K33Graph_exists_adj hS

theorem IsPlanar.of_induce_support
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar (G.induce G.support)) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact h_planar.no_K5_subdivision
      (containsStrictSubdivision_K5_induce_support hK5)
  · intro hK33
    exact h_planar.no_K33_subdivision
      (containsStrictSubdivision_K33_induce_support hK33)

theorem IsPlanar.of_induce_of_support_subset
    {V : Type u} {G : SimpleGraph V}
    {S : Set V}
    (h_planar : IsPlanar (G.induce S))
    (hS : G.support ⊆ S) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact h_planar.no_K5_subdivision
      (containsStrictSubdivision_K5_induce_of_support_subset hK5 hS)
  · intro hK33
    exact h_planar.no_K33_subdivision
      (containsStrictSubdivision_K33_induce_of_support_subset hK33 hS)

/-- Low-degree vertex extension for the Kuratowski-exclusion interface.  This
is the first formal piece of Skopenkov's proposition: a degree-zero or
degree-one vertex cannot occur in a strict `K_5` or `K_{3,3}` subdivision, so
planarity of the graph with that vertex removed implies planarity of the
original graph. -/
theorem IsPlanar.of_induce_compl_singleton_of_degree_le_one
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v : V}
    (h_planar : IsPlanar (G.induce {z : V | z ≠ v}))
    (hdegree : G.degree v <= 1) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact h_planar.no_K5_subdivision
      (ContainsStrictSubdivision.K5_induce_compl_singleton_of_degree_le_one
        hK5 hdegree)
  · intro hK33
    exact h_planar.no_K33_subdivision
      (ContainsStrictSubdivision.K33_induce_compl_singleton_of_degree_le_one
        hK33 hdegree)

/-- A graph of maximum degree at most three cannot contain a strict
subdivision of `K_5`: every branch vertex of a strict `K_5` subdivision has
host degree at least four. -/
theorem not_containsStrictSubdivision_K5_of_max_degree_le_three
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall v : V, G.degree v <= 3) :
    Not (ContainsStrictSubdivision K5Graph G) := by
  classical
  rintro ⟨M⟩
  let x : Fin 5 := 0
  letI : Fintype (K5Graph.neighborSet x) := inferInstance
  letI : Fintype (G.neighborSet (M.branchVertex x)) := inferInstance
  have hsource :
      K5Graph.degree x <= G.degree (M.branchVertex x) :=
    M.source_degree_le_branchVertex_degree x
  have hhost : G.degree (M.branchVertex x) <= 3 :=
    hdegree (M.branchVertex x)
  rw [K5Graph_degree x] at hsource
  omega

/-- A graph of maximum degree at most two cannot contain a strict
subdivision of `K_{3,3}`: every branch vertex of a strict `K_{3,3}`
subdivision has host degree at least three. -/
theorem not_containsStrictSubdivision_K33_of_max_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall v : V, G.degree v <= 2) :
    Not (ContainsStrictSubdivision K33Graph G) := by
  classical
  rintro ⟨M⟩
  let x : K33Vertex := Sum.inl 0
  letI : Fintype (K33Graph.neighborSet x) := inferInstance
  letI : Fintype (G.neighborSet (M.branchVertex x)) := inferInstance
  have hsource :
      K33Graph.degree x <= G.degree (M.branchVertex x) :=
    M.source_degree_le_branchVertex_degree x
  have hhost : G.degree (M.branchVertex x) <= 2 :=
    hdegree (M.branchVertex x)
  rw [K33Graph_degree x] at hsource
  omega

/-- Source-facing low-degree base case for the Kuratowski-exclusion
interface: maximum-degree-two graphs are planar.  This is the strict
subdivision form of the elementary fact that paths and cycles carry no
Kuratowski obstruction. -/
theorem IsPlanar.of_max_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall v : V, G.degree v <= 2) :
    IsPlanar G := by
  constructor
  · exact not_containsStrictSubdivision_K5_of_max_degree_le_three
      (G := G) (by intro v; exact le_trans (hdegree v) (by omega))
  · exact not_containsStrictSubdivision_K33_of_max_degree_le_two
      (G := G) hdegree

theorem IsPlanar.subgraph_coe
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (H : G.Subgraph) :
    IsPlanar H.coe :=
  IsPlanar.of_injective_hom H.hom SimpleGraph.Subgraph.hom_injective h_planar

theorem IsStrictPlanar.mono
    {V : Type u} {G H : SimpleGraph V}
    (hHG : H ≤ G)
    (h_planar : IsStrictPlanar G) :
    IsStrictPlanar H := by
  constructor
  · intro hK5
    exact h_planar.1 (ContainsStrictSubdivision.of_le hHG hK5)
  · intro hK33
    exact h_planar.2 (ContainsStrictSubdivision.of_le hHG hK33)

theorem IsPlanar.toStrictPlanar
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsPlanar G) :
    IsStrictPlanar G := by
  constructor
  · intro hK5
    exact h_planar.no_K5_subdivision hK5
  · intro hK33
    exact h_planar.no_K33_subdivision hK33

theorem IsPlanar.ofStrictPlanar
    {V : Type u} {G : SimpleGraph V}
    (h_planar : IsStrictPlanar G) :
    IsPlanar G where
  no_K5_subdivision := h_planar.1
  no_K33_subdivision := h_planar.2

theorem isPlanar_iff_isStrictPlanar
    {V : Type u} {G : SimpleGraph V} :
    IsPlanar G ↔ IsStrictPlanar G :=
  ⟨IsPlanar.toStrictPlanar, IsPlanar.ofStrictPlanar⟩

theorem not_isPlanar_of_containsStrictSubdivision_K5
    {V : Type u} {G : SimpleGraph V}
    (hK5 : ContainsStrictSubdivision K5Graph G) :
    Not (IsPlanar G) := by
  intro h_planar
  exact h_planar.no_K5_subdivision hK5

theorem not_isPlanar_of_containsStrictSubdivision_K33
    {V : Type u} {G : SimpleGraph V}
    (hK33 : ContainsStrictSubdivision K33Graph G) :
    Not (IsPlanar G) := by
  intro h_planar
  exact h_planar.no_K33_subdivision hK33

theorem not_isPlanar_iff_containsStrictSubdivision_K5_or_K33
    {V : Type u} {G : SimpleGraph V} :
    Not (IsPlanar G) ↔
      ContainsStrictSubdivision K5Graph G ∨
        ContainsStrictSubdivision K33Graph G := by
  constructor
  · intro hnonplanar
    classical
    by_cases hK5 : ContainsStrictSubdivision K5Graph G
    · exact Or.inl hK5
    · by_cases hK33 : ContainsStrictSubdivision K33Graph G
      · exact Or.inr hK33
      · exact False.elim (hnonplanar ⟨hK5, hK33⟩)
  · rintro (hK5 | hK33)
    · exact not_isPlanar_of_containsStrictSubdivision_K5 hK5
    · exact not_isPlanar_of_containsStrictSubdivision_K33 hK33

/-- A theta-free graph is planar in the repository's Kuratowski-exclusion
interface.  This is the formal version of the source-text observation that a
face boundary or any other theta-free subgraph cannot itself carry either
Kuratowski obstruction: both `K_5` and `K_{3,3}` contain a strict `K_{2,3}`. -/
theorem IsPlanar.of_no_theta
    {V : Type u} {G : SimpleGraph V}
    (hθ : Not (ContainsThetaSubdivision G)) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact hθ (ContainsThetaSubdivision.of_K5 hK5)
  · intro hK33
    exact hθ (ContainsThetaSubdivision.of_K33 hK33)

/-- The same theta-free planarity criterion using the source-facing
homeomorphic theta predicate, which also includes the direct-edge theta case. -/
theorem IsPlanar.of_no_homeomorphicTheta
    {V : Type u} {G : SimpleGraph V}
    (hθ : Not (ContainsHomeomorphicTheta G)) :
    IsPlanar G :=
  IsPlanar.of_no_theta (G := G) (by
    intro hstrict
    exact hθ (ContainsHomeomorphicTheta.of_strict hstrict))

theorem containsStrictSubdivision_self
    {V : Type u}
    (G : SimpleGraph V) :
    ContainsStrictSubdivision G G :=
  containsStrictSubdivision_of_graphEmbedding
    (Function.Embedding.refl V)
    (by
      intro x y hxy
      simpa using hxy)

theorem not_isPlanar_K5Graph :
    Not (IsPlanar K5Graph) :=
  not_isPlanar_of_containsStrictSubdivision_K5
    (containsStrictSubdivision_self K5Graph)

theorem not_isPlanar_K33Graph :
    Not (IsPlanar K33Graph) :=
  not_isPlanar_of_containsStrictSubdivision_K33
    (containsStrictSubdivision_self K33Graph)

def K5Hat.k33Embedding : K33Vertex ↪ Fin 6 where
  toFun
    | Sum.inl 0 => 0
    | Sum.inl 1 => 4
    | Sum.inl 2 => 5
    | Sum.inr 0 => 1
    | Sum.inr 1 => 2
    | Sum.inr 2 => 3
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y <;>
      fin_cases x <;> fin_cases y <;> simp at h ⊢

theorem K5Hat.k33Embedding_adj
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y) :
    K5Hat.Adj (K5Hat.k33Embedding x) (K5Hat.k33Embedding y) := by
  rcases x with x | x <;> rcases y with y | y <;>
    fin_cases x <;> fin_cases y <;> simp [K33Graph] at hxy
  all_goals
    rw [K5Hat, SimpleGraph.fromEdgeSet_adj]
    simp [K5Hat.k33Embedding]

theorem K5Hat_containsStrictSubdivision_K33 :
    ContainsStrictSubdivision K33Graph K5Hat :=
  containsStrictSubdivision_of_graphEmbedding
    K5Hat.k33Embedding
    (by
      intro x y hxy
      exact K5Hat.k33Embedding_adj hxy)

theorem not_isPlanar_K5Hat :
    Not (IsPlanar K5Hat) :=
  not_isPlanar_of_containsStrictSubdivision_K33
    K5Hat_containsStrictSubdivision_K33

theorem not_isPlanar_of_containsStrictSubdivision_K5Hat
    {V : Type u} {G : SimpleGraph V}
    (hK5Hat : ContainsStrictSubdivision K5Hat G) :
    Not (IsPlanar G) :=
  not_isPlanar_of_containsStrictSubdivision_K33
    (ContainsStrictSubdivision.domainRestrict
      K5Hat.k33Embedding
      (by
        intro x y hxy
        exact K5Hat.k33Embedding_adj hxy)
      hK5Hat)

theorem completeGraph_containsSubdivision_K5_of_card_eq_five
    {V : Type u} [Fintype V]
    (h_card : Fintype.card V = 5) :
    ContainsSubdivision K5Graph (SimpleGraph.completeGraph V) := by
  exact completeGraph_containsStrictSubdivision_K5_of_card_ge_five
    (V := V) (by omega)

theorem not_isPlanar_completeGraph_of_card_ge_five
    {V : Type u} [Fintype V]
    (h_card : 5 <= Fintype.card V) :
    Not (IsPlanar (SimpleGraph.completeGraph V)) :=
  not_isPlanar_of_containsStrictSubdivision_K5
    (completeGraph_containsStrictSubdivision_K5_of_card_ge_five h_card)

theorem IsPlanar.card_le_four_of_complete
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_planar : IsPlanar G)
    (h_complete : forall u v : V, u ≠ v -> G.Adj u v) :
    Fintype.card V <= 4 := by
  by_contra hcard
  have h_card_ge_five : 5 <= Fintype.card V := by omega
  have hG_eq : G = SimpleGraph.completeGraph V := by
    ext u v
    constructor
    · intro huv
      exact huv.ne
    · intro huv_ne
      exact h_complete u v huv_ne
  subst G
  exact not_isPlanar_completeGraph_of_card_ge_five h_card_ge_five h_planar

theorem isPlanar_of_card_le_five_of_not_complete
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_card : Fintype.card V <= 5)
    (h_not_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    IsPlanar G := by
  constructor
  · intro hK5
    exact h_not_complete
      (complete_of_containsStrictSubdivision_K5_of_card_le_five h_card hK5)
  · intro hK33
    have hcard_ge : Fintype.card K33Vertex <= Fintype.card V :=
      card_le_of_containsStrictSubdivision hK33
    rw [card_K33Vertex] at hcard_ge
    omega

theorem isPlanar_of_card_le_four
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_card : Fintype.card V <= 4) :
    IsPlanar G := by
  constructor
  · intro hK5
    have hcard_ge : Fintype.card (Fin 5) <= Fintype.card V :=
      card_le_of_containsStrictSubdivision hK5
    simp at hcard_ge
    omega
  · intro hK33
    have hcard_ge : Fintype.card K33Vertex <= Fintype.card V :=
      card_le_of_containsStrictSubdivision hK33
    rw [card_K33Vertex] at hcard_ge
    omega

theorem isPlanar_of_highDegree_bounds
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (hdegree_four : {v : V | 4 <= G.degree v}.ncard <= 4)
    (hdegree_three : {v : V | 3 <= G.degree v}.ncard <= 5) :
    IsPlanar G := by
  constructor
  · intro hK5
    have hge :
        5 <= {v : V | 4 <= G.degree v}.ncard :=
      highDegree_four_ncard_ge_five_of_containsStrictSubdivision_K5 hK5
    omega
  · intro hK33
    have hge :
        6 <= {v : V | 3 <= G.degree v}.ncard :=
      highDegree_three_ncard_ge_six_of_containsStrictSubdivision_K33 hK33
    omega

theorem containsWeakSubdivision_K5_of_connectedComponent_card_ge_five
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (C : G.ConnectedComponent)
    (h_card : 5 <= C.supp.ncard) :
    ContainsWeakSubdivision K5Graph G := by
  classical
  letI : Fintype C.supp := C.supp.toFinite.fintype
  have h_card' : 5 <= Fintype.card C.supp := by
    simpa [Set.fintypeCard_eq_ncard] using h_card
  obtain ⟨e⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 5) (β := C.supp) h_card'
  refine ⟨{
    branchVertex := fun i => (e i : V)
    branchVertex_injective := ?_
    edgePath := ?_
    edgePath_isPath := ?_
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
  }⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i j _hij
    exact Classical.choose
      ((C.reachable_of_mem_supp (e i).2 (e j).2).exists_isPath)
  · intro i j _hij
    exact Classical.choose_spec
      ((C.reachable_of_mem_supp (e i).2 (e j).2).exists_isPath)

theorem containsWeakSubdivision_K5_of_connected_card_ge_five
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_connected : G.Connected)
    (h_card : 5 <= Fintype.card V) :
    ContainsWeakSubdivision K5Graph G := by
  classical
  obtain ⟨e⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin 5) (β := V) h_card
  refine ⟨{
    branchVertex := e
    branchVertex_injective := e.injective
    edgePath := ?_
    edgePath_isPath := ?_
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
  }⟩
  · intro i j _hij
    exact Classical.choose ((h_connected (e i) (e j)).exists_isPath)
  · intro i j _hij
    exact Classical.choose_spec ((h_connected (e i) (e j)).exists_isPath)

theorem IsFourConnected.containsWeakSubdivision_K5
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_four_connected : IsFourConnected G) :
    ContainsWeakSubdivision K5Graph G := by
  have h_card : 5 <= Fintype.card V := by
    have h_nat : 4 < Nat.card V := h_four_connected.1
    rw [Nat.card_eq_fintype_card] at h_nat
    omega
  exact containsWeakSubdivision_K5_of_connected_card_ge_five
    (G := G) h_four_connected.connected h_card

theorem connectedComponent_card_le_four_of_not_containsWeakSubdivision_K5
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (h_no_K5 : Not (ContainsWeakSubdivision K5Graph G))
    (C : G.ConnectedComponent) :
    C.supp.ncard <= 4 := by
  by_contra h
  have h_ge_five : 5 <= C.supp.ncard := by omega
  exact h_no_K5
    (containsWeakSubdivision_K5_of_connectedComponent_card_ge_five (G := G) C h_ge_five)

theorem colorable_four_of_connectedComponent_card_le_four
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_component_card : forall C : G.ConnectedComponent, C.supp.ncard <= 4) :
    G.Colorable 4 := by
  classical
  let componentEmbedding :
      forall C : G.ConnectedComponent, C.supp ↪ Fin 4 := fun C =>
    letI : Fintype C.supp := C.supp.toFinite.fintype
    Classical.choice
      (Function.Embedding.nonempty_of_card_le
        (α := C.supp) (β := Fin 4)
        (by
          simpa [Fintype.card_fin, Set.fintypeCard_eq_ncard] using h_component_card C))
  let componentColor : G.ConnectedComponent -> V -> Fin 4 := fun C v =>
    if hv : v ∈ C.supp then componentEmbedding C ⟨v, hv⟩ else 0
  let color : V -> Fin 4 := fun v =>
    componentColor (G.connectedComponentMk v) v
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro v w hvw h_same
  have h_component_eq :
      G.connectedComponentMk v = G.connectedComponentMk w :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hvw
  have hv_mem_w : v ∈ (G.connectedComponentMk w).supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact h_component_eq
  have h_same_component :
      componentColor (G.connectedComponentMk w) v =
        componentColor (G.connectedComponentMk w) w := by
    simpa [color, h_component_eq] using h_same
  have hv_eq_w : v = w := by
    simpa [componentColor, hvw.reachable] using h_same_component
  exact hvw.ne hv_eq_w

theorem colorable_four_of_not_containsWeakSubdivision_K5
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_no_K5 : Not (ContainsWeakSubdivision K5Graph G)) :
    G.Colorable 4 := by
  exact colorable_four_of_connectedComponent_card_le_four G
    (connectedComponent_card_le_four_of_not_containsWeakSubdivision_K5 h_no_K5)

theorem colorable_four_of_noncolorable_contains_K5_or_K5Hat
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_planar : IsPlanar G)
    (h_near_hajos :
      Not (G.Colorable 4) ->
        ContainsStrictSubdivision K5Graph G ∨
          ContainsStrictSubdivision K5Hat G) :
    G.Colorable 4 := by
  classical
  by_contra h_not_colorable
  rcases h_near_hajos h_not_colorable with hK5 | hK5Hat
  · exact h_planar.no_K5_subdivision hK5
  · exact not_isPlanar_of_containsStrictSubdivision_K5Hat hK5Hat h_planar

theorem exists_connectedComponent_card_ge_five_of_not_colorable_four
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_not_colorable : Not (G.Colorable 4)) :
    Exists fun C : G.ConnectedComponent => 5 <= C.supp.ncard := by
  classical
  by_contra hno
  push Not at hno
  exact h_not_colorable
    (colorable_four_of_connectedComponent_card_le_four G (by
      intro C
      have hlt : C.supp.ncard < 5 := hno C
      omega))

theorem containsWeakSubdivision_K5_of_not_colorable_four
    {V : Type u} [Fintype V]
    (G : SimpleGraph V)
    (h_not_colorable : Not (G.Colorable 4)) :
    ContainsWeakSubdivision K5Graph G := by
  obtain ⟨C, hC⟩ :=
    exists_connectedComponent_card_ge_five_of_not_colorable_four G h_not_colorable
  exact containsWeakSubdivision_K5_of_connectedComponent_card_ge_five (G := G) C hC

end Schematic.Math.GraphTheory
