import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.Attachments

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem k5TieK33Branch_injective
    {V : Type u}
    {a b p q r s : V}
    (hab : a ≠ b)
    (ha_p : a ≠ p) (ha_q : a ≠ q) (ha_r : a ≠ r) (ha_s : a ≠ s)
    (hb_p : b ≠ p) (hb_q : b ≠ q) (hb_r : b ≠ r) (hb_s : b ≠ s)
    (hp_q : p ≠ q) (hp_r : p ≠ r) (hp_s : p ≠ s)
    (hq_r : q ≠ r) (hq_s : q ≠ s) (hr_s : r ≠ s) :
    Function.Injective (k5TieK33Branch a b p q r s) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y <;>
    fin_cases x <;> fin_cases y <;>
      simp [k5TieK33Branch] at hxy ⊢
  all_goals
    first
    | exact False.elim (hab hxy)
    | exact False.elim (hab hxy.symm)
    | exact False.elim (ha_p hxy)
    | exact False.elim (ha_p hxy.symm)
    | exact False.elim (ha_q hxy)
    | exact False.elim (ha_q hxy.symm)
    | exact False.elim (ha_r hxy)
    | exact False.elim (ha_r hxy.symm)
    | exact False.elim (ha_s hxy)
    | exact False.elim (ha_s hxy.symm)
    | exact False.elim (hb_p hxy)
    | exact False.elim (hb_p hxy.symm)
    | exact False.elim (hb_q hxy)
    | exact False.elim (hb_q hxy.symm)
    | exact False.elim (hb_r hxy)
    | exact False.elim (hb_r hxy.symm)
    | exact False.elim (hb_s hxy)
    | exact False.elim (hb_s hxy.symm)
    | exact False.elim (hp_q hxy)
    | exact False.elim (hp_q hxy.symm)
    | exact False.elim (hp_r hxy)
    | exact False.elim (hp_r hxy.symm)
    | exact False.elim (hp_s hxy)
    | exact False.elim (hp_s hxy.symm)
    | exact False.elim (hq_r hxy)
    | exact False.elim (hq_r hxy.symm)
    | exact False.elim (hq_s hxy)
    | exact False.elim (hq_s hxy.symm)
    | exact False.elim (hr_s hxy)
    | exact False.elim (hr_s hxy.symm)

noncomputable def k5TieK33EdgePath
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    (ab : G.Walk a b)
    (ap : G.Walk a p)
    (aq : G.Walk a q)
    (br : G.Walk b r)
    (bs : G.Walk b s)
    (rp : G.Walk r p)
    (rq : G.Walk r q)
    (sp : G.Walk s p)
    (sq : G.Walk s q)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y) :
    G.Walk
      (k5TieK33Branch a b p q r s x)
      (k5TieK33Branch a b p q r s y) := by
  rcases x with x | x
  · rcases y with y | y
    · simp [K33Graph] at hxy
    · exact
        match x, y with
        | 0, 0 => ab
        | 0, 1 => ap
        | 0, 2 => aq
        | 1, 0 => br.reverse
        | 1, 1 => rp
        | 1, 2 => rq
        | 2, 0 => bs.reverse
        | 2, 1 => sp
        | 2, 2 => sq
  · rcases y with y | y
    · exact
        match x, y with
        | 0, 0 => ab.reverse
        | 0, 1 => br
        | 0, 2 => bs
        | 1, 0 => ap.reverse
        | 1, 1 => rp.reverse
        | 1, 2 => sp.reverse
        | 2, 0 => aq.reverse
        | 2, 1 => rq.reverse
        | 2, 2 => sq.reverse
    · simp [K33Graph] at hxy

theorem k5TieK33EdgePath_isPath
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    {ab : G.Walk a b}
    {ap : G.Walk a p}
    {aq : G.Walk a q}
    {br : G.Walk b r}
    {bs : G.Walk b s}
    {rp : G.Walk r p}
    {rq : G.Walk r q}
    {sp : G.Walk s p}
    {sq : G.Walk s q}
    (hab : ab.IsPath)
    (hap : ap.IsPath)
    (haq : aq.IsPath)
    (hbr : br.IsPath)
    (hbs : bs.IsPath)
    (hrp : rp.IsPath)
    (hrq : rq.IsPath)
    (hsp : sp.IsPath)
    (hsq : sq.IsPath)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y) :
    (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy).IsPath := by
  rcases x with x | x <;> rcases y with y | y
  · simp [K33Graph] at hxy
  · fin_cases x <;> fin_cases y <;> simp [k5TieK33EdgePath]
    · exact hab
    · exact hap
    · exact haq
    · exact hbr.reverse
    · exact hrp
    · exact hrq
    · exact hbs.reverse
    · exact hsp
    · exact hsq
  · fin_cases x <;> fin_cases y <;> simp [k5TieK33EdgePath]
    · exact hab.reverse
    · exact hbr
    · exact hbs
    · exact hap.reverse
    · exact hrp.reverse
    · exact hsp.reverse
    · exact haq.reverse
    · exact hrq.reverse
    · exact hsq.reverse
  · simp [K33Graph] at hxy

theorem k5TieK33EdgePath_no_internal_branch_vertices
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    {ab : G.Walk a b}
    {ap : G.Walk a p}
    {aq : G.Walk a q}
    {br : G.Walk b r}
    {bs : G.Walk b s}
    {rp : G.Walk r p}
    {rq : G.Walk r q}
    {sp : G.Walk s p}
    {sq : G.Walk s q}
    (hab :
      forall {z : V}, z ∈ Walk.InternalVertices ab ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hap :
      forall {z : V}, z ∈ Walk.InternalVertices ap ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (haq :
      forall {z : V}, z ∈ Walk.InternalVertices aq ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hbr :
      forall {z : V}, z ∈ Walk.InternalVertices br ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hbs :
      forall {z : V}, z ∈ Walk.InternalVertices bs ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hrp :
      forall {z : V}, z ∈ Walk.InternalVertices rp ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hrq :
      forall {z : V}, z ∈ Walk.InternalVertices rq ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hsp :
      forall {z : V}, z ∈ Walk.InternalVertices sp ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hsq :
      forall {z : V}, z ∈ Walk.InternalVertices sq ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y)
    {z : V}
    (hz : z ∈ Walk.InternalVertices
      (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy))
    (w : K33Vertex) :
    z ≠ k5TieK33Branch a b p q r s w := by
  rcases x with x | x <;> rcases y with y | y
  · simp [K33Graph] at hxy
  · fin_cases x <;> fin_cases y <;> simp [k5TieK33EdgePath] at hz
    · exact hab hz w
    · exact hap hz w
    · exact haq hz w
    · exact hbr ((Walk.mem_internalVertices_reverse_iff br).mp hz) w
    · exact hrp hz w
    · exact hrq hz w
    · exact hbs ((Walk.mem_internalVertices_reverse_iff bs).mp hz) w
    · exact hsp hz w
    · exact hsq hz w
  · fin_cases x <;> fin_cases y <;> simp [k5TieK33EdgePath] at hz
    · exact hab ((Walk.mem_internalVertices_reverse_iff ab).mp hz) w
    · exact hbr hz w
    · exact hbs hz w
    · exact hap ((Walk.mem_internalVertices_reverse_iff ap).mp hz) w
    · exact hrp ((Walk.mem_internalVertices_reverse_iff rp).mp hz) w
    · exact hsp ((Walk.mem_internalVertices_reverse_iff sp).mp hz) w
    · exact haq ((Walk.mem_internalVertices_reverse_iff aq).mp hz) w
    · exact hrq ((Walk.mem_internalVertices_reverse_iff rq).mp hz) w
    · exact hsq ((Walk.mem_internalVertices_reverse_iff sq).mp hz) w
  · simp [K33Graph] at hxy

def k5TieK33PathIndex : K33Vertex -> K33Vertex -> Fin 9
  | Sum.inl 0, Sum.inr 0 => 0
  | Sum.inr 0, Sum.inl 0 => 0
  | Sum.inl 0, Sum.inr 1 => 1
  | Sum.inr 1, Sum.inl 0 => 1
  | Sum.inl 0, Sum.inr 2 => 2
  | Sum.inr 2, Sum.inl 0 => 2
  | Sum.inl 1, Sum.inr 0 => 3
  | Sum.inr 0, Sum.inl 1 => 3
  | Sum.inl 2, Sum.inr 0 => 4
  | Sum.inr 0, Sum.inl 2 => 4
  | Sum.inl 1, Sum.inr 1 => 5
  | Sum.inr 1, Sum.inl 1 => 5
  | Sum.inl 1, Sum.inr 2 => 6
  | Sum.inr 2, Sum.inl 1 => 6
  | Sum.inl 2, Sum.inr 1 => 7
  | Sum.inr 1, Sum.inl 2 => 7
  | Sum.inl 2, Sum.inr 2 => 8
  | Sum.inr 2, Sum.inl 2 => 8
  | _, _ => 0

def k5TieK33PathSet
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    (ab : G.Walk a b)
    (ap : G.Walk a p)
    (aq : G.Walk a q)
    (br : G.Walk b r)
    (bs : G.Walk b s)
    (rp : G.Walk r p)
    (rq : G.Walk r q)
    (sp : G.Walk s p)
    (sq : G.Walk s q) :
    Fin 9 -> Set V
  | 0 => Walk.InternalVertices ab
  | 1 => Walk.InternalVertices ap
  | 2 => Walk.InternalVertices aq
  | 3 => Walk.InternalVertices br
  | 4 => Walk.InternalVertices bs
  | 5 => Walk.InternalVertices rp
  | 6 => Walk.InternalVertices rq
  | 7 => Walk.InternalVertices sp
  | 8 => Walk.InternalVertices sq

theorem k5TieK33EdgePath_internalVertices_eq_pathSet
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    {ab : G.Walk a b}
    {ap : G.Walk a p}
    {aq : G.Walk a q}
    {br : G.Walk b r}
    {bs : G.Walk b s}
    {rp : G.Walk r p}
    {rq : G.Walk r q}
    {sp : G.Walk s p}
    {sq : G.Walk s q}
    {x y : K33Vertex}
    (hxy : K33Graph.Adj x y) :
    Walk.InternalVertices
        (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy) =
      k5TieK33PathSet ab ap aq br bs rp rq sp sq
        (k5TieK33PathIndex x y) := by
  ext z
  rcases x with x | x <;> rcases y with y | y
  · simp [K33Graph] at hxy
  · fin_cases x <;> fin_cases y <;>
      simp [k5TieK33EdgePath, k5TieK33PathSet, k5TieK33PathIndex]
    · rfl
    · rfl
    · rfl
    · exact Walk.mem_internalVertices_reverse_iff br
    · rfl
    · rfl
    · exact Walk.mem_internalVertices_reverse_iff bs
    · rfl
    · rfl
  · fin_cases x <;> fin_cases y <;>
      simp [k5TieK33EdgePath, k5TieK33PathSet, k5TieK33PathIndex]
    · exact Walk.mem_internalVertices_reverse_iff ab
    · rfl
    · rfl
    · exact Walk.mem_internalVertices_reverse_iff ap
    · exact Walk.mem_internalVertices_reverse_iff rp
    · exact Walk.mem_internalVertices_reverse_iff sp
    · exact Walk.mem_internalVertices_reverse_iff aq
    · exact Walk.mem_internalVertices_reverse_iff rq
    · exact Walk.mem_internalVertices_reverse_iff sq
  · simp [K33Graph] at hxy

theorem k5TieK33PathIndex_ne_of_not_same_or_reverse
    {x y x' y' : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hx'y' : K33Graph.Adj x' y')
    (hne : Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) :
    k5TieK33PathIndex x y ≠ k5TieK33PathIndex x' y' := by
  rcases x with x | x <;> rcases y with y | y <;>
    rcases x' with x' | x' <;> rcases y' with y' | y'
  all_goals
    try simp [K33Graph] at hxy
  all_goals
    try simp [K33Graph] at hx'y'
  all_goals
    fin_cases x <;> fin_cases y <;>
      fin_cases x' <;> fin_cases y' <;>
        simp [k5TieK33PathIndex] at hne ⊢

theorem k5TieK33EdgePaths_internally_disjoint
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    {ab : G.Walk a b}
    {ap : G.Walk a p}
    {aq : G.Walk a q}
    {br : G.Walk b r}
    {bs : G.Walk b s}
    {rp : G.Walk r p}
    {rq : G.Walk r q}
    {sp : G.Walk s p}
    {sq : G.Walk s q}
    (hpair :
      forall i j : Fin 9, i ≠ j ->
        Disjoint
          (k5TieK33PathSet ab ap aq br bs rp rq sp sq i)
          (k5TieK33PathSet ab ap aq br bs rp rq sp sq j))
    {x y x' y' : K33Vertex}
    (hxy : K33Graph.Adj x y)
    (hx'y' : K33Graph.Adj x' y')
    (hne : Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))) :
    Disjoint
      (Walk.InternalVertices
        (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy))
      (Walk.InternalVertices
        (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hx'y')) := by
  rw [k5TieK33EdgePath_internalVertices_eq_pathSet hxy,
    k5TieK33EdgePath_internalVertices_eq_pathSet hx'y']
  exact hpair _ _
    (k5TieK33PathIndex_ne_of_not_same_or_reverse hxy hx'y' hne)

theorem containsStrictSubdivision_K33_of_k5TieK33_paths
    {V : Type u} {G : SimpleGraph V}
    {a b p q r s : V}
    {ab : G.Walk a b}
    {ap : G.Walk a p}
    {aq : G.Walk a q}
    {br : G.Walk b r}
    {bs : G.Walk b s}
    {rp : G.Walk r p}
    {rq : G.Walk r q}
    {sp : G.Walk s p}
    {sq : G.Walk s q}
    (hbranch :
      Function.Injective (k5TieK33Branch a b p q r s))
    (hab : ab.IsPath)
    (hap : ap.IsPath)
    (haq : aq.IsPath)
    (hbr : br.IsPath)
    (hbs : bs.IsPath)
    (hrp : rp.IsPath)
    (hrq : rq.IsPath)
    (hsp : sp.IsPath)
    (hsq : sq.IsPath)
    (hab_no :
      forall {z : V}, z ∈ Walk.InternalVertices ab ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hap_no :
      forall {z : V}, z ∈ Walk.InternalVertices ap ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (haq_no :
      forall {z : V}, z ∈ Walk.InternalVertices aq ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hbr_no :
      forall {z : V}, z ∈ Walk.InternalVertices br ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hbs_no :
      forall {z : V}, z ∈ Walk.InternalVertices bs ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hrp_no :
      forall {z : V}, z ∈ Walk.InternalVertices rp ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hrq_no :
      forall {z : V}, z ∈ Walk.InternalVertices rq ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hsp_no :
      forall {z : V}, z ∈ Walk.InternalVertices sp ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hsq_no :
      forall {z : V}, z ∈ Walk.InternalVertices sq ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w)
    (hpair :
      forall i j : Fin 9, i ≠ j ->
        Disjoint
          (k5TieK33PathSet ab ap aq br bs rp rq sp sq i)
          (k5TieK33PathSet ab ap aq br bs rp rq sp sq j)) :
    ContainsStrictSubdivision K33Graph G := by
  exact ⟨{
    toSubdivisionModel := {
      branchVertex := k5TieK33Branch a b p q r s
      branchVertex_injective := hbranch
      edgePath := fun {x y} hxy =>
        k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy
      edgePath_isPath := by
        intro x y hxy
        exact
          k5TieK33EdgePath_isPath hab hap haq hbr hbs hrp hrq hsp hsq
            hxy
      no_internal_branch_vertices :=
        forall {x y : K33Vertex} (hxy : K33Graph.Adj x y) {z : V},
          z ∈ Walk.InternalVertices
            (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy) ->
          forall w : K33Vertex, z ≠ k5TieK33Branch a b p q r s w
      internally_disjoint_edge_paths :=
        forall {x y x' y' : K33Vertex}
          (hxy : K33Graph.Adj x y) (hx'y' : K33Graph.Adj x' y'),
          Not ((x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) ->
          Disjoint
            (Walk.InternalVertices
              (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hxy))
            (Walk.InternalVertices
              (k5TieK33EdgePath ab ap aq br bs rp rq sp sq hx'y')) }
    no_internal_branch_vertices' := by
      intro x y hxy z hz w hzw
      exact
        k5TieK33EdgePath_no_internal_branch_vertices
          hab_no hap_no haq_no hbr_no hbs_no hrp_no hrq_no hsp_no hsq_no
          hxy hz w hzw
    internally_disjoint_edge_paths' := by
      intro x y x' y' hxy hx'y' hne
      exact
        k5TieK33EdgePaths_internally_disjoint
          hpair hxy hx'y' hne }⟩

noncomputable def strictSubdivisionModel_collapseEdge_branch_root_branchVertex
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    W -> V :=
  fun w =>
    if hw : w = c then root
    else
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w)
        (by
          intro hw_none
          exact hw
            (M.branchVertex_injective (hw_none.trans hc.symm)))
end FourColor

end Schematic.Math.GraphTheory
