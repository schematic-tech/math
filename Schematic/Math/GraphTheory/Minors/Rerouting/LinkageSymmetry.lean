import Schematic.Math.GraphTheory.Minors.Rerouting.MinimalYZCertificate

/-! Symmetry and small-graph existence for vertex-disjoint linkages. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def VertexDisjointLinkage.symm
    {left right : Fin 3 -> V}
    (L : VertexDisjointLinkage G left right) :
    VertexDisjointLinkage G right left where
  path i := (L.path i).reverse
  isPath i := (L.isPath i).reverse
  pairwise_internally_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.mp (L.pairwise_internally_vertex_disjoint i j hij)
      (by simpa [Walk.InternalVertices, and_comm, and_left_comm, and_assoc] using hxi)
      (by simpa [Walk.InternalVertices, and_comm, and_left_comm, and_assoc] using hxj)

theorem HasVertexDisjointLinkage.symm
    {left right : Fin 3 -> V}
    (h : HasVertexDisjointLinkage G left right) :
    HasVertexDisjointLinkage G right left := by
  rcases h with ⟨L⟩
  exact ⟨L.symm⟩

theorem hasVertexDisjointLinkage_refl
    (points : Fin 3 -> V) :
    HasVertexDisjointLinkage G points points := by
  refine ⟨{
    path := fun _ => SimpleGraph.Walk.nil
    isPath := fun _ => SimpleGraph.Walk.IsPath.nil
    pairwise_internally_vertex_disjoint := ?_
  }⟩
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx
  simp [Walk.InternalVertices] at hx

theorem hasVertexDisjointLinkage_of_equal_or_adjacent
    (left right : Fin 3 -> V)
    (hstep : forall i : Fin 3, left i = right i ∨ G.Adj (left i) (right i)) :
    HasVertexDisjointLinkage G left right := by
  classical
  let path : forall i : Fin 3, G.Walk (left i) (right i) := fun i =>
    if h : left i = right i then
      (SimpleGraph.Walk.nil : G.Walk (left i) (left i)).copy rfl h
    else
      (hstep i).resolve_left h |>.toWalk
  refine ⟨{
    path := path
    isPath := ?_
    pairwise_internally_vertex_disjoint := ?_
  }⟩
  · intro i
    by_cases h : left i = right i
    · simp [path, h]
    · have hadj : G.Adj (left i) (right i) := (hstep i).resolve_left h
      simp [path, h, SimpleGraph.Walk.IsPath.of_adj hadj]
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi
    by_cases hi : left i = right i
    · simp [path, hi, Walk.InternalVertices] at hxi
    · simp [path, hi, Walk.InternalVertices] at hxi
      rcases hxi with ⟨hx | hx, hx_left, hx_right⟩
      · exact False.elim (hx_left hx)
      · exact False.elim (hx_right hx)

private theorem complete_of_three_connected_card_four
    [Fintype V]
    (h_three_connected : IsThreeConnected G)
    (h_card : Fintype.card V = 4) :
    forall u v : V, u ≠ v -> G.Adj u v := by
  classical
  intro u v huv
  by_contra hnot_adj
  let Sfin : Finset V := (Finset.univ.erase u).erase v
  have hv_mem : v ∈ Finset.univ.erase u := by
    rw [Finset.mem_erase]
    exact ⟨huv.symm, Finset.mem_univ v⟩
  have hSfin_card : Sfin.card = 2 := by
    rw [Finset.card_erase_of_mem hv_mem]
    rw [Finset.card_erase_of_mem (Finset.mem_univ u)]
    rw [Finset.card_univ, h_card]
  have hS_card : ((Sfin : Set V).ncard) < 3 := by
    rw [Set.ncard_coe_finset, hSfin_card]
    omega
  have hu_compl : u ∈ (Sfin : Set V)ᶜ := by
    simp [Sfin]
  have hv_compl : v ∈ (Sfin : Set V)ᶜ := by
    simp [Sfin, huv.symm]
  let u' : ((Sfin : Set V)ᶜ : Set V) := ⟨u, hu_compl⟩
  let v' : ((Sfin : Set V)ᶜ : Set V) := ⟨v, hv_compl⟩
  have huv_subtype : u' ≠ v' := by
    intro h
    exact huv (congrArg Subtype.val h)
  have hbot : G.induce ((Sfin : Set V)ᶜ) = ⊥ := by
    ext a b
    constructor
    · intro hab
      have ha : (a : V) = u ∨ (a : V) = v := by
        have ha_not : (a : V) ∉ Sfin := a.2
        by_cases hau : (a : V) = u
        · exact Or.inl hau
        · right
          by_contra hav
          exact ha_not (by simp [Sfin, hau, hav])
      have hb : (b : V) = u ∨ (b : V) = v := by
        have hb_not : (b : V) ∉ Sfin := b.2
        by_cases hbu : (b : V) = u
        · exact Or.inl hbu
        · right
          by_contra hbv
          exact hb_not (by simp [Sfin, hbu, hbv])
      rcases ha with ha_u | ha_v <;> rcases hb with hb_u | hb_v
      · exact False.elim (hab.ne (Subtype.ext (ha_u.trans hb_u.symm)))
      · have huv_adj : G.Adj u v := by
          simpa [ha_u, hb_v] using hab
        exact False.elim (hnot_adj huv_adj)
      · have hvu_adj : G.Adj v u := by
          simpa [ha_v, hb_u] using hab
        exact False.elim (hnot_adj hvu_adj.symm)
      · exact False.elim (hab.ne (Subtype.ext (ha_v.trans hb_v.symm)))
    · intro hab
      simp at hab
  have hconn : (G.induce ((Sfin : Set V)ᶜ)).Connected :=
    h_three_connected.2 (Sfin : Set V) hS_card
  have hreach : (G.induce ((Sfin : Set V)ᶜ)).Reachable u' v' :=
    hconn u' v'
  rw [hbot, SimpleGraph.reachable_bot] at hreach
  exact huv_subtype hreach

theorem menger_three_linkage_of_equal_or_adjacent
    (left right : Fin 3 -> V)
    (hstep : forall i : Fin 3, left i = right i ∨ G.Adj (left i) (right i)) :
    HasVertexDisjointLinkage G left right := by
  exact hasVertexDisjointLinkage_of_equal_or_adjacent left right hstep

theorem menger_three_linkage_of_card_four
    [Fintype V]
    (h_three_connected : IsThreeConnected G)
    (left right : Fin 3 -> V)
    (hcard : Fintype.card V = 4) :
    HasVertexDisjointLinkage G left right := by
  exact menger_three_linkage_of_equal_or_adjacent
    (G := G) left right (by
      intro i
      by_cases hsame : left i = right i
      · exact Or.inl hsame
      · exact Or.inr
          (complete_of_three_connected_card_four
            (G := G) h_three_connected hcard (left i) (right i) hsame))


end Schematic.Math.GraphTheory
