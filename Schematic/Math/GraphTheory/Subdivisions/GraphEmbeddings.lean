import Schematic.Math.GraphTheory.Subdivisions.HostRerouting

/-! Constructing strict subdivisions from graph embeddings and K5-hat cores. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

def K5Hat : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet {
    s((0 : Fin 6), (1 : Fin 6)),
    s((0 : Fin 6), (2 : Fin 6)),
    s((0 : Fin 6), (3 : Fin 6)),
    s((1 : Fin 6), (4 : Fin 6)),
    s((1 : Fin 6), (5 : Fin 6)),
    s((2 : Fin 6), (3 : Fin 6)),
    s((2 : Fin 6), (4 : Fin 6)),
    s((2 : Fin 6), (5 : Fin 6)),
    s((3 : Fin 6), (4 : Fin 6)),
    s((3 : Fin 6), (5 : Fin 6)),
    s((4 : Fin 6), (5 : Fin 6))
  }

def K5Hat.k4CoreEmbedding : Fin 4 ↪ Fin 6 where
  toFun i := ⟨i + 2, by
    have hi : (i : Nat) < 4 := i.isLt
    omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hnat : (i : Nat) + 2 = (j : Nat) + 2 := Fin.ext_iff.mp hij
    exact Nat.add_right_cancel hnat

theorem K5Hat.k4CoreEmbedding_adj
    {i j : Fin 4}
    (hij : i ≠ j) :
    K5Hat.Adj (K5Hat.k4CoreEmbedding i) (K5Hat.k4CoreEmbedding j) := by
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals
    rw [K5Hat, SimpleGraph.fromEdgeSet_adj]
    simp [K5Hat.k4CoreEmbedding]

def StrictSubdivisionModel.ofGraphEmbedding
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    (h_adj : forall {x y : W}, H.Adj x y -> G.Adj (e x) (e y)) :
    StrictSubdivisionModel H G where
  branchVertex := e
  branchVertex_injective := e.injective
  edgePath := by
    intro x y hxy
    exact (h_adj hxy).toWalk
  edgePath_isPath := by
    intro x y hxy
    exact SimpleGraph.Walk.IsPath.of_adj (h_adj hxy)
  no_internal_branch_vertices := True
  internally_disjoint_edge_paths := True
  no_internal_branch_vertices' := by
    intro x y hxy z hz w
    simp [Walk.InternalVertices] at hz
    rcases hz.1 with hz_eq | hz_eq
    · exact False.elim (hz.2.1 hz_eq)
    · exact False.elim (hz.2.2 hz_eq)
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    rw [Set.disjoint_left]
    intro z hz _hz'
    simp [Walk.InternalVertices] at hz
    rcases hz.1 with hz_eq | hz_eq
    · exact hz.2.1 hz_eq
    · exact hz.2.2 hz_eq

noncomputable def graphEmbeddingWithOneEdgePath_walk
    {W : Type u} {V : Type v}
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    {a b : W}
    (p : G.Walk (e a) (e b))
    (h_adj :
      forall {x y : W},
        H.Adj x y ->
          ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ->
            G.Adj (e x) (e y))
    {x y : W}
    (hxy : H.Adj x y) :
    G.Walk (e x) (e y) := by
  by_cases hab : x = a ∧ y = b
  · rcases hab with ⟨rfl, rfl⟩
    exact p
  · by_cases hba : x = b ∧ y = a
    · rcases hba with ⟨rfl, rfl⟩
      exact p.reverse
    · exact (h_adj hxy (by exact not_or.mpr ⟨hab, hba⟩)).toWalk

theorem graphEmbeddingWithOneEdgePath_walk_forward
    {W : Type u} {V : Type v}
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    {a b : W}
    (p : G.Walk (e a) (e b))
    (h_adj :
      forall {x y : W},
        H.Adj x y ->
          ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ->
            G.Adj (e x) (e y))
    (hxy : H.Adj a b) :
    graphEmbeddingWithOneEdgePath_walk e p h_adj hxy = p := by
  unfold graphEmbeddingWithOneEdgePath_walk
  split
  · rename_i h
    cases h
    rfl
  · rename_i h
    exact False.elim (h ⟨rfl, rfl⟩)

theorem graphEmbeddingWithOneEdgePath_walk_reverse
    {W : Type u} {V : Type v}
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    {a b : W}
    (p : G.Walk (e a) (e b))
    (h_adj :
      forall {x y : W},
        H.Adj x y ->
          ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ->
            G.Adj (e x) (e y))
    (hxy : H.Adj b a) :
    graphEmbeddingWithOneEdgePath_walk e p h_adj hxy = p.reverse := by
  by_cases hba : b = a
  · subst b
    exact False.elim (hxy.ne rfl)
  · unfold graphEmbeddingWithOneEdgePath_walk
    split
    · rename_i h
      exact False.elim (hba h.1)
    · split
      · rename_i h
        cases h
        rfl
      · rename_i h
        exact False.elim (h ⟨rfl, rfl⟩)

theorem graphEmbeddingWithOneEdgePath_walk_of_not_special
    {W : Type u} {V : Type v}
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    {a b x y : W}
    (p : G.Walk (e a) (e b))
    (h_adj :
      forall {x y : W},
        H.Adj x y ->
          ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ->
            G.Adj (e x) (e y))
    (hxy : H.Adj x y)
    (hnot : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) :
    graphEmbeddingWithOneEdgePath_walk e p h_adj hxy =
      (h_adj hxy hnot).toWalk := by
  unfold graphEmbeddingWithOneEdgePath_walk
  split
  · rename_i h
    exact False.elim (hnot (Or.inl h))
  · split
    · rename_i h
      exact False.elim (hnot (Or.inr h))
    · rfl

noncomputable def StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath
    {W : Type u} {V : Type v}
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    {a b : W}
    (p : G.Walk (e a) (e b))
    (hp : p.IsPath)
    (h_adj :
      forall {x y : W},
        H.Adj x y ->
          ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ->
            G.Adj (e x) (e y))
    (hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p -> forall w : W, z ≠ e w) :
    StrictSubdivisionModel H G where
  branchVertex := e
  branchVertex_injective := e.injective
  edgePath hxy := graphEmbeddingWithOneEdgePath_walk e p h_adj hxy
  edgePath_isPath := by
    intro x y hxy
    by_cases hab : x = a ∧ y = b
    · rcases hab with ⟨rfl, rfl⟩
      simpa [graphEmbeddingWithOneEdgePath_walk_forward]
        using hp
    · by_cases hba : x = b ∧ y = a
      · rcases hba with ⟨rfl, rfl⟩
        simpa [graphEmbeddingWithOneEdgePath_walk_reverse]
          using hp.reverse
      · have hnot : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) :=
          not_or.mpr ⟨hab, hba⟩
        simpa [graphEmbeddingWithOneEdgePath_walk_of_not_special,
          hnot] using
          SimpleGraph.Walk.IsPath.of_adj
            (h_adj hxy hnot)
  no_internal_branch_vertices := True
  internally_disjoint_edge_paths := True
  no_internal_branch_vertices' := by
    intro x y hxy z hz w hzw
    by_cases hab : x = a ∧ y = b
    · rcases hab with ⟨rfl, rfl⟩
      have hz_p : z ∈ Walk.InternalVertices p := by
        simpa [graphEmbeddingWithOneEdgePath_walk_forward] using hz
      exact hp_internal_no_branch hz_p w hzw
    · by_cases hba : x = b ∧ y = a
      · rcases hba with ⟨rfl, rfl⟩
        have hz_rev : z ∈ Walk.InternalVertices p.reverse := by
          simpa [graphEmbeddingWithOneEdgePath_walk_reverse] using hz
        have hz_p : z ∈ Walk.InternalVertices p := by
          simpa [Walk.internalVertices_reverse] using hz_rev
        exact hp_internal_no_branch hz_p w hzw
      · have hz_walk :
            z ∈ Walk.InternalVertices
              (h_adj hxy (by exact not_or.mpr ⟨hab, hba⟩)).toWalk := by
          have hnot : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) :=
            not_or.mpr ⟨hab, hba⟩
          simpa [graphEmbeddingWithOneEdgePath_walk_of_not_special,
            hnot] using hz
        exact (Walk.not_mem_internalVertices_toWalk
          (h_adj hxy (by exact not_or.mpr ⟨hab, hba⟩)) hz_walk).elim
  internally_disjoint_edge_paths' := by
    intro x y x' y' hxy hx'y' hne
    rw [Set.disjoint_left]
    intro z hz hz'
    by_cases hab : x = a ∧ y = b
    · have hx : x = a := hab.1
      have hy : y = b := hab.2
      by_cases hab' : x' = a ∧ y' = b
      · exact False.elim
          (hne (Or.inl ⟨hx.trans hab'.1.symm, hy.trans hab'.2.symm⟩))
      · by_cases hba' : x' = b ∧ y' = a
        · exact False.elim
            (hne (Or.inr ⟨hx.trans hba'.2.symm, hy.trans hba'.1.symm⟩))
        · have hz'_walk :
              z ∈ Walk.InternalVertices
                (h_adj hx'y' (by exact not_or.mpr ⟨hab', hba'⟩)).toWalk := by
            have hnot' : ¬ ((x' = a ∧ y' = b) ∨ (x' = b ∧ y' = a)) :=
              not_or.mpr ⟨hab', hba'⟩
            simpa [graphEmbeddingWithOneEdgePath_walk_of_not_special,
              hnot'] using hz'
          exact (Walk.not_mem_internalVertices_toWalk
            (h_adj hx'y' (by exact not_or.mpr ⟨hab', hba'⟩)) hz'_walk).elim
    · by_cases hba : x = b ∧ y = a
      · have hx : x = b := hba.1
        have hy : y = a := hba.2
        by_cases hab' : x' = a ∧ y' = b
        · exact False.elim
            (hne (Or.inr ⟨hx.trans hab'.2.symm, hy.trans hab'.1.symm⟩))
        · by_cases hba' : x' = b ∧ y' = a
          · exact False.elim
              (hne (Or.inl ⟨hx.trans hba'.1.symm, hy.trans hba'.2.symm⟩))
          · have hz'_walk :
                z ∈ Walk.InternalVertices
                  (h_adj hx'y' (by exact not_or.mpr ⟨hab', hba'⟩)).toWalk := by
              have hnot' : ¬ ((x' = a ∧ y' = b) ∨ (x' = b ∧ y' = a)) :=
                not_or.mpr ⟨hab', hba'⟩
              simpa [graphEmbeddingWithOneEdgePath_walk_of_not_special,
                hnot'] using hz'
            exact (Walk.not_mem_internalVertices_toWalk
              (h_adj hx'y' (by exact not_or.mpr ⟨hab', hba'⟩)) hz'_walk).elim
      · have hz_walk :
            z ∈ Walk.InternalVertices
              (h_adj hxy (by exact not_or.mpr ⟨hab, hba⟩)).toWalk := by
          have hnot : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) :=
            not_or.mpr ⟨hab, hba⟩
          simpa [graphEmbeddingWithOneEdgePath_walk_of_not_special,
            hnot] using hz
        exact (Walk.not_mem_internalVertices_toWalk
          (h_adj hxy (by exact not_or.mpr ⟨hab, hba⟩)) hz_walk).elim

theorem StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath_edgeUnsplit_of_not_special
    {W : Type u} {V : Type v}
    [DecidableEq W]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    {a b x y : W}
    (p : G.Walk (e a) (e b))
    (hp : p.IsPath)
    (h_adj :
      forall {x y : W},
        H.Adj x y ->
          ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) ->
            G.Adj (e x) (e y))
    (hp_internal_no_branch :
      forall {z : V}, z ∈ Walk.InternalVertices p -> forall w : W, z ≠ e w)
    (hxy : H.Adj x y)
    (hnot : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))) :
    (StrictSubdivisionModel.ofGraphEmbeddingWithOneEdgePath
      e p hp h_adj hp_internal_no_branch).EdgeUnsplit hxy := by
  change (graphEmbeddingWithOneEdgePath_walk e p h_adj hxy).length = 1
  rw [graphEmbeddingWithOneEdgePath_walk_of_not_special
    (e := e) (p := p) (h_adj := h_adj) hxy hnot]
  simp

def StrictSubdivisionModel.ofCompleteGraphEmbedding
    {V : Type v} {G : SimpleGraph V} {n : Nat}
    (e : Fin n ↪ V)
    (h_adj : forall x y : Fin n, x ≠ y -> G.Adj (e x) (e y)) :
    StrictSubdivisionModel (CompleteGraphOn n) G :=
  StrictSubdivisionModel.ofGraphEmbedding e
    (by
      intro x y hxy
      exact h_adj x y (by simpa [CompleteGraphOn] using hxy.ne))

theorem StrictSubdivisionModel.ofGraphEmbedding_edgeUnsplit
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    (h_adj : forall {x y : W}, H.Adj x y -> G.Adj (e x) (e y))
    {x y : W}
    (hxy : H.Adj x y) :
    (StrictSubdivisionModel.ofGraphEmbedding e h_adj).EdgeUnsplit hxy := by
  simp [StrictSubdivisionModel.EdgeUnsplit,
    StrictSubdivisionModel.ofGraphEmbedding]

theorem containsStrictSubdivision_of_graphEmbedding
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (e : W ↪ V)
    (h_adj : forall {x y : W}, H.Adj x y -> G.Adj (e x) (e y)) :
    ContainsStrictSubdivision H G :=
  ⟨StrictSubdivisionModel.ofGraphEmbedding e h_adj⟩

theorem ContainsEdgeTheta.to_edgeThetaSubdivision
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsEdgeTheta G) :
    ContainsEdgeThetaSubdivision G := by
  classical
  rcases h with
    ⟨x, y, u, w, hxy, hxu, hyu, hxw, hyw, huw⟩
  let f : EdgeThetaVertex ↪ V := {
    toFun
      | Sum.inl 0 => x
      | Sum.inl 1 => y
      | Sum.inr 0 => u
      | Sum.inr 1 => w
    inj' := by
      intro a b hab
      rcases a with a | a <;> rcases b with b | b <;>
        fin_cases a <;> fin_cases b <;>
        simp at hab ⊢
      all_goals
        first
        | exact False.elim (hxy.ne hab)
        | exact False.elim (hxy.ne hab.symm)
        | exact False.elim (hxu.ne hab)
        | exact False.elim (hxu.ne hab.symm)
        | exact False.elim (hyu.ne hab)
        | exact False.elim (hyu.ne hab.symm)
        | exact False.elim (hxw.ne hab)
        | exact False.elim (hxw.ne hab.symm)
        | exact False.elim (hyw.ne hab)
        | exact False.elim (hyw.ne hab.symm)
        | exact False.elim (huw hab)
        | exact False.elim (huw hab.symm) }
  exact containsStrictSubdivision_of_graphEmbedding f (by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;>
      fin_cases a <;> fin_cases b <;>
      simp [EdgeThetaGraph, f] at hab ⊢
    · exact hxy
    · exact hxy.symm
    · exact hxu
    · exact hxw
    · exact hyu
    · exact hyw
    · exact hxu.symm
    · exact hyu.symm
    · exact hxw.symm
    · exact hyw.symm)

theorem K33Graph_containsThetaSubdivision :
    ContainsThetaSubdivision K33Graph :=
  containsStrictSubdivision_of_graphEmbedding
    K23Graph.toK33Embedding
    (by
      intro x y hxy
      exact K23Graph.toK33Embedding_adj hxy)

theorem K5Graph_containsThetaSubdivision :
    ContainsThetaSubdivision K5Graph :=
  containsStrictSubdivision_of_graphEmbedding
    K23Graph.toK5Embedding
    (by
      intro x y hxy
      exact K23Graph.toK5Embedding_adj hxy)

theorem ContainsThetaSubdivision.of_K33
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision K33Graph G) :
    ContainsThetaSubdivision G :=
  ContainsStrictSubdivision.domainRestrict
    K23Graph.toK33Embedding
    (by
      intro x y hxy
      exact K23Graph.toK33Embedding_adj hxy)
    h

theorem ContainsThetaSubdivision.of_K5
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsStrictSubdivision K5Graph G) :
    ContainsThetaSubdivision G :=
  ContainsStrictSubdivision.domainRestrict
    K23Graph.toK5Embedding
    (by
      intro x y hxy
      exact K23Graph.toK5Embedding_adj hxy)
    h

theorem containsStrictSubdivision_completeGraph_of_cliqueEmbedding
    {V : Type v} {G : SimpleGraph V} {n : Nat}
    (e : Fin n ↪ V)
    (h_adj : forall x y : Fin n, x ≠ y -> G.Adj (e x) (e y)) :
    ContainsStrictSubdivision (CompleteGraphOn n) G :=
  ⟨StrictSubdivisionModel.ofCompleteGraphEmbedding e h_adj⟩

theorem K5Hat_containsStrictSubdivision_K4 :
    ContainsStrictSubdivision K4Graph K5Hat :=
  containsStrictSubdivision_completeGraph_of_cliqueEmbedding
    K5Hat.k4CoreEmbedding
    (by
      intro i j hij
      exact K5Hat.k4CoreEmbedding_adj hij)

def K5Hat.k4CoreStrictSubdivisionModel :
    StrictSubdivisionModel K4Graph K5Hat :=
  StrictSubdivisionModel.ofCompleteGraphEmbedding
    K5Hat.k4CoreEmbedding
    (by
      intro i j hij
      exact K5Hat.k4CoreEmbedding_adj hij)

def K5Graph.k4CoreEmbedding : Fin 4 ↪ Fin 5 where
  toFun i := ⟨i, by
    have hi : (i : Nat) < 4 := i.isLt
    omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    simpa using Fin.ext_iff.mp hij

theorem K5Graph.k4CoreEmbedding_adj
    {i j : Fin 4}
    (hij : i ≠ j) :
    K5Graph.Adj (K5Graph.k4CoreEmbedding i) (K5Graph.k4CoreEmbedding j) := by
  simpa [K5Graph, CompleteGraphOn] using hij

theorem K5Graph_containsStrictSubdivision_K4 :
    ContainsStrictSubdivision K4Graph K5Graph :=
  containsStrictSubdivision_completeGraph_of_cliqueEmbedding
    K5Graph.k4CoreEmbedding
    (by
      intro i j hij
      exact K5Graph.k4CoreEmbedding_adj hij)

def K5Graph.k4CoreStrictSubdivisionModel :
    StrictSubdivisionModel K4Graph K5Graph :=
  StrictSubdivisionModel.ofCompleteGraphEmbedding
    K5Graph.k4CoreEmbedding
    (by
      intro i j hij
      exact K5Graph.k4CoreEmbedding_adj hij)

theorem StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit
    {V : Type v} {G : SimpleGraph V} {n : Nat}
    (e : Fin n ↪ V)
    (h_adj : forall x y : Fin n, x ≠ y -> G.Adj (e x) (e y))
    {x y : Fin n}
    (hxy : (CompleteGraphOn n).Adj x y) :
    (StrictSubdivisionModel.ofCompleteGraphEmbedding e h_adj).EdgeUnsplit hxy := by
  simpa [StrictSubdivisionModel.ofCompleteGraphEmbedding] using
    StrictSubdivisionModel.ofGraphEmbedding_edgeUnsplit e
      (by
        intro x y hxy
        exact h_adj x y (by simpa [CompleteGraphOn] using hxy.ne))
      hxy

theorem K5Hat.k4CoreStrictSubdivisionModel_edgeUnsplit
    {x y : Fin 4}
    (hxy : K4Graph.Adj x y) :
    K5Hat.k4CoreStrictSubdivisionModel.EdgeUnsplit hxy := by
  simpa [K5Hat.k4CoreStrictSubdivisionModel] using
    StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit
      K5Hat.k4CoreEmbedding
      (by
        intro i j hij
        exact K5Hat.k4CoreEmbedding_adj hij)
      hxy

theorem K5Graph.k4CoreStrictSubdivisionModel_edgeUnsplit
    {x y : Fin 4}
    (hxy : K4Graph.Adj x y) :
    K5Graph.k4CoreStrictSubdivisionModel.EdgeUnsplit hxy := by
  simpa [K5Graph.k4CoreStrictSubdivisionModel] using
    StrictSubdivisionModel.ofCompleteGraphEmbedding_edgeUnsplit
      K5Graph.k4CoreEmbedding
      (by
        intro i j hij
        exact K5Graph.k4CoreEmbedding_adj hij)
      hxy

theorem completeGraph_containsStrictSubdivision_completeGraph_of_card_le
    {V : Type v} [Fintype V] {n : Nat}
    (h_card : n <= Fintype.card V) :
    ContainsStrictSubdivision (CompleteGraphOn n) (SimpleGraph.completeGraph V) := by
  classical
  obtain ⟨e⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin n) (β := V) (by simpa using h_card)
  exact containsStrictSubdivision_completeGraph_of_cliqueEmbedding e
    (by
      intro x y hxy
      exact show (SimpleGraph.completeGraph V).Adj (e x) (e y) from by
        simpa using hxy)

theorem completeGraph_containsStrictSubdivision_K5_of_card_ge_five
    {V : Type v} [Fintype V]
    (h_card : 5 <= Fintype.card V) :
    ContainsStrictSubdivision K5Graph (SimpleGraph.completeGraph V) :=
  completeGraph_containsStrictSubdivision_completeGraph_of_card_le
    (V := V) (n := 5) h_card

theorem completeGraph_containsStrictSubdivision_K4_of_card_ge_four
    {V : Type v} [Fintype V]
    (h_card : 4 <= Fintype.card V) :
    ContainsStrictSubdivision K4Graph (SimpleGraph.completeGraph V) :=
  completeGraph_containsStrictSubdivision_completeGraph_of_card_le
    (V := V) (n := 4) h_card

theorem complete_of_containsStrictSubdivision_completeGraph_of_card_le
    {V : Type v} [Fintype V] {n : Nat}
    {G : SimpleGraph V}
    (h_card : Fintype.card V <= n)
    (hK : ContainsStrictSubdivision (CompleteGraphOn n) G) :
    forall u v : V, u ≠ v -> G.Adj u v := by
  classical
  rcases hK with ⟨M⟩
  have hcard_ge : Fintype.card (Fin n) <= Fintype.card V :=
    Fintype.card_le_of_injective M.branchVertex M.branchVertex_injective
  have hcard_ge_n : n <= Fintype.card V := by
    simpa [Fintype.card_fin] using hcard_ge
  have hcard_V : Fintype.card V = n := by omega
  have hcard_eq : Fintype.card (Fin n) = Fintype.card V := by
    simp [hcard_V]
  have hsurj : Function.Surjective M.branchVertex :=
    (Fintype.bijective_iff_injective_and_card M.branchVertex).mpr
      ⟨M.branchVertex_injective, hcard_eq⟩ |>.2
  intro u v huv
  obtain ⟨x, rfl⟩ := hsurj u
  obtain ⟨y, rfl⟩ := hsurj v
  have hxy : x ≠ y := by
    intro h
    exact huv (by simp [h])
  have hKxy : (CompleteGraphOn n).Adj x y := by
    simpa [CompleteGraphOn] using hxy
  let p : G.Walk (M.branchVertex x) (M.branchVertex y) := M.edgePath hKxy
  have hp_not_nil : Not p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := p) (by
      intro h
      exact hxy (M.branchVertex_injective h))
  have hsnd_eq : p.snd = M.branchVertex y := by
    by_contra hsnd_ne
    have hsnd_support : p.snd ∈ p.support := by
      rw [← SimpleGraph.Walk.cons_tail_eq p hp_not_nil]
      simp [SimpleGraph.Walk.support_cons]
    have hsnd_internal : p.snd ∈ Walk.InternalVertices p := by
      exact ⟨hsnd_support, (p.adj_snd hp_not_nil).ne.symm, hsnd_ne⟩
    obtain ⟨w, hw⟩ := hsurj p.snd
    exact M.no_internal_branch_vertices' hKxy hsnd_internal w hw.symm
  simpa [p, hsnd_eq] using p.adj_snd hp_not_nil

theorem complete_of_containsStrictSubdivision_K5_of_card_le_five
    {V : Type v} [Fintype V]
    {G : SimpleGraph V}
    (h_card : Fintype.card V <= 5)
    (hK5 : ContainsStrictSubdivision K5Graph G) :
    forall u v : V, u ≠ v -> G.Adj u v :=
  complete_of_containsStrictSubdivision_completeGraph_of_card_le h_card hK5

theorem complete_of_containsStrictSubdivision_K4_of_card_le_four
    {V : Type v} [Fintype V]
    {G : SimpleGraph V}
    (h_card : Fintype.card V <= 4)
    (hK4 : ContainsStrictSubdivision K4Graph G) :
    forall u v : V, u ≠ v -> G.Adj u v :=
  complete_of_containsStrictSubdivision_completeGraph_of_card_le h_card hK4


end Schematic.Math.GraphTheory
