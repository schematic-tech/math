import Schematic.Math.GraphTheory.Subdivisions.GraphEmbeddings

/-! Converting complete minor models into weak complete subdivisions. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

theorem complete_minor_contains_weak_complete_subdivision
    {V : Type v} {G : SimpleGraph V} {n : Nat}
    (h : ContainsMinor (CompleteGraphOn n) G) :
    ContainsWeakSubdivision (CompleteGraphOn n) G := by
  classical
  rcases h with ⟨M⟩
  let bv : Fin n -> V := fun x => (M.nonempty x).some
  have hbv : forall x : Fin n, bv x ∈ (M.branch x).verts := by
    intro x
    exact (M.nonempty x).some_mem
  refine ⟨{
    branchVertex := bv
    branchVertex_injective := ?_
    edgePath := ?_
    edgePath_isPath := ?_
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
  }⟩
  · intro x y hxy
    by_contra hne
    have hdis := M.vertex_disjoint x y hne
    exact (Set.disjoint_left.mp hdis (hbv x)) (by simpa [bv, hxy] using hbv y)
  · intro x y hxy
    let a : V := (M.edge_realized hxy).choose
    let b : V := ((M.edge_realized hxy).choose_spec).choose
    have hspec :
        a ∈ (M.branch x).verts ∧ b ∈ (M.branch y).verts ∧ G.Adj a b :=
      ((M.edge_realized hxy).choose_spec).choose_spec
    let bx : (M.branch x).verts := ⟨bv x, hbv x⟩
    let ax : (M.branch x).verts := ⟨a, hspec.1⟩
    let byv : (M.branch y).verts := ⟨bv y, hbv y⟩
    let ay : (M.branch y).verts := ⟨b, hspec.2.1⟩
    let p₁ : (M.branch x).coe.Walk bx ax := Classical.choice ((M.connected x) bx ax)
    let p₂ : (M.branch y).coe.Walk ay byv := Classical.choice ((M.connected y) ay byv)
    exact ((p₁.map (M.branch x).hom).append
      ((SimpleGraph.Walk.cons hspec.2.2 (p₂.map (M.branch y).hom)))).bypass
  · intro x y hxy
    exact SimpleGraph.Walk.bypass_isPath _

theorem k4_minor_contains_k4_subdivision
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsMinor K4Graph G) :
    ContainsWeakSubdivision K4Graph G := by
  classical
  rcases h with ⟨M⟩
  let bv : Fin 4 -> V := fun x => (M.nonempty x).some
  have hbv : forall x : Fin 4, bv x ∈ (M.branch x).verts := by
    intro x
    exact (M.nonempty x).some_mem
  refine ⟨{
    branchVertex := bv
    branchVertex_injective := ?_
    edgePath := ?_
    edgePath_isPath := ?_
    no_internal_branch_vertices := True
    internally_disjoint_edge_paths := True
  }⟩
  · intro x y hxy
    by_contra hne
    have hdis := M.vertex_disjoint x y hne
    exact (Set.disjoint_left.mp hdis (hbv x)) (by simpa [bv, hxy] using hbv y)
  · intro x y hxy
    let a : V := (M.edge_realized hxy).choose
    let b : V := ((M.edge_realized hxy).choose_spec).choose
    have hspec :
        a ∈ (M.branch x).verts ∧ b ∈ (M.branch y).verts ∧ G.Adj a b :=
      ((M.edge_realized hxy).choose_spec).choose_spec
    let bx : (M.branch x).verts := ⟨bv x, hbv x⟩
    let ax : (M.branch x).verts := ⟨a, hspec.1⟩
    let byv : (M.branch y).verts := ⟨bv y, hbv y⟩
    let ay : (M.branch y).verts := ⟨b, hspec.2.1⟩
    let p₁ : (M.branch x).coe.Walk bx ax := Classical.choice ((M.connected x) bx ax)
    let p₂ : (M.branch y).coe.Walk ay byv := Classical.choice ((M.connected y) ay byv)
    exact ((p₁.map (M.branch x).hom).append
      ((SimpleGraph.Walk.cons hspec.2.2 (p₂.map (M.branch y).hom)))).bypass
  · intro x y hxy
    exact SimpleGraph.Walk.bypass_isPath _

end Schematic.Math.GraphTheory
