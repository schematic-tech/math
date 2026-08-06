import Schematic.Math.GraphTheory.Subdivisions.StandardGraphs

/-! Homeomorphic theta witnesses and cycle extraction. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u v

/-- Source-facing theta predicate: either a strict `K_{2,3}` subdivision, or
the same theta after one degree-two vertex has been suppressed to a direct edge
between the two branch vertices. The suppressed-edge branch is represented both
as the general strict subdivision of `EdgeThetaGraph` and by the older
four-vertex unsplit witness used by earlier local counting lemmas. -/
def ContainsHomeomorphicTheta {V : Type v} (G : SimpleGraph V) : Prop :=
  ContainsThetaSubdivision G ∨ ContainsEdgeThetaSubdivision G ∨ ContainsEdgeTheta G

/-- Every supported theta presentation retains a degree-three branch with
three pairwise branch-avoiding alternate walks.  This is the graph-facing
input needed by the face-orbit/Jordan bridge. -/
theorem ContainsHomeomorphicTheta.exists_thetaBranchPaths
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsHomeomorphicTheta G) :
    Nonempty (ThetaBranchPaths G) := by
  rcases h with hK23 | hEdge
  · rcases hK23 with ⟨M⟩
    let x : K23Vertex := Sum.inl (0 : Fin 2)
    let y : K23Vertex := Sum.inl (1 : Fin 2)
    let a : K23Vertex := Sum.inr (0 : Fin 3)
    let b : K23Vertex := Sum.inr (1 : Fin 3)
    let c : K23Vertex := Sum.inr (2 : Fin 3)
    have hxa : K23Graph.Adj x a := by simp [K23Graph, x, a]
    have hxb : K23Graph.Adj x b := by simp [K23Graph, x, b]
    have hxc : K23Graph.Adj x c := by simp [K23Graph, x, c]
    have hay : K23Graph.Adj a y := by simp [K23Graph, a, y]
    have hby : K23Graph.Adj b y := by simp [K23Graph, b, y]
    have hcy : K23Graph.Adj c y := by simp [K23Graph, c, y]
    exact ⟨M.thetaBranchPaths hxa hxb hxc hay hby hcy
      (by simp [a, b]) (by simp [a, c]) (by simp [b, c])
      (by simp [x, y])⟩
  · rcases hEdge with hEdgeSub | hDirect
    · rcases hEdgeSub with ⟨M⟩
      let x : EdgeThetaVertex := Sum.inl (0 : Fin 2)
      let y : EdgeThetaVertex := Sum.inl (1 : Fin 2)
      let a : EdgeThetaVertex := Sum.inr (0 : Fin 2)
      let b : EdgeThetaVertex := Sum.inr (1 : Fin 2)
      have hxy : EdgeThetaGraph.Adj x y := by
        simp [EdgeThetaGraph, x, y]
      have hxa : EdgeThetaGraph.Adj x a := by
        simp [EdgeThetaGraph, x, a]
      have hay : EdgeThetaGraph.Adj a y := by
        simp [EdgeThetaGraph, a, y]
      have hxb : EdgeThetaGraph.Adj x b := by
        simp [EdgeThetaGraph, x, b]
      have hby : EdgeThetaGraph.Adj b y := by
        simp [EdgeThetaGraph, b, y]
      exact ⟨M.edgeThetaBranchPaths hxy hxa hay hxb hby
        (by simp [a, b])⟩
    · rcases hDirect with
        ⟨x, y, a, b, hxy, hxa, hya, hxb, hyb, hab⟩
      let pay : G.Walk a y := hya.symm.toWalk
      let pyb : G.Walk y b := hyb.toWalk
      refine ⟨{
        branch := x
        first := y
        second := a
        third := b
        adj_first := hxy
        adj_second := hxa
        adj_third := hxb
        first_ne_second := hya.ne
        first_ne_third := hyb.ne
        second_ne_third := hab
        firstSecond := hya.toWalk
        firstThird := hyb.toWalk
        secondThird := pay.append pyb
        branch_not_mem_firstSecond := ?_
        branch_not_mem_firstThird := ?_
        branch_not_mem_secondThird := ?_
      }⟩
      · simp [hxy.ne, hxa.ne]
      · simp [hxy.ne, hxb.ne]
      · intro hxmem
        rw [SimpleGraph.Walk.mem_support_append_iff] at hxmem
        rcases hxmem with hpay | hpyb
        · have : x = a ∨ x = y := by simpa [pay] using hpay
          exact this.elim hxa.ne hxy.ne
        · have : x = y ∨ x = b := by simpa [pyb] using hpyb
          exact this.elim hxy.ne hxb.ne

theorem ContainsHomeomorphicTheta.of_strict
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsThetaSubdivision G) :
    ContainsHomeomorphicTheta G :=
  Or.inl h

theorem ContainsHomeomorphicTheta.of_edgeSubdivision
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsEdgeThetaSubdivision G) :
    ContainsHomeomorphicTheta G :=
  Or.inr (Or.inl h)

theorem ContainsHomeomorphicTheta.of_edge
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsEdgeTheta G) :
    ContainsHomeomorphicTheta G :=
  Or.inr (Or.inr h)

theorem ContainsEdgeTheta.map
    {V : Type v} {U : Type*}
    {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h : ContainsEdgeTheta G) :
    ContainsEdgeTheta G' := by
  rcases h with
    ⟨x, y, a, b, hxy, hxa, hya, hxb, hyb, hab⟩
  exact
    ⟨f x, f y, f a, f b,
      f.map_rel hxy, f.map_rel hxa, f.map_rel hya,
      f.map_rel hxb, f.map_rel hyb,
      fun hfab => hab (hf hfab)⟩

/-- A strict subdivision of the suppressed-edge theta contains a simple
cycle. -/
theorem ContainsEdgeThetaSubdivision.exists_isCycle
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsEdgeThetaSubdivision G) :
    Exists fun x : V => Exists fun c : G.Walk x x => c.IsCycle := by
  rcases h with ⟨M⟩
  let x : EdgeThetaVertex := Sum.inl (0 : Fin 2)
  let y : EdgeThetaVertex := Sum.inl (1 : Fin 2)
  let z : EdgeThetaVertex := Sum.inr (0 : Fin 2)
  have hxy : EdgeThetaGraph.Adj x y := by
    simp [EdgeThetaGraph, x, y]
  have hyz : EdgeThetaGraph.Adj y z := by
    simp [EdgeThetaGraph, y, z]
  have hxz : EdgeThetaGraph.Adj x z := by
    simp [EdgeThetaGraph, x, z]
  let p : G.Walk (M.branchVertex x) (M.branchVertex y) :=
    M.edgePath hxy
  let q₁ : G.Walk (M.branchVertex y) (M.branchVertex z) :=
    M.edgePath hyz
  let q₂ : G.Walk (M.branchVertex z) (M.branchVertex x) :=
    (M.edgePath hxz).reverse
  let q : G.Walk (M.branchVertex y) (M.branchVertex x) :=
    q₁.append q₂
  have hp : p.IsPath := by
    simpa [p] using M.edgePath_isPath hxy
  have hq₁ : q₁.IsPath := by
    simpa [q₁] using M.edgePath_isPath hyz
  have hq₂ : q₂.IsPath := by
    simpa [q₂] using (M.edgePath_isPath hxz).reverse
  have h_yz_xz :
      forall t : V,
        t ∈ (M.edgePath hyz).support ->
          t ∈ (M.edgePath hxz).support ->
            t = M.branchVertex z := by
    intro t ht_yz ht_xz
    have hne :
        Not ((y = x ∧ z = z) ∨ (y = z ∧ z = x)) := by
      rintro (hsame | hrev)
      · exact hxy.ne hsame.1.symm
      · exact hyz.ne hrev.1
    have hunique :
        forall w : EdgeThetaVertex,
          (w = y ∨ w = z) -> (w = x ∨ w = z) -> w = z := by
      intro w hw_yz hw_xz
      rcases hw_yz with rfl | rfl
      · rcases hw_xz with hyx | hyz'
        · exact False.elim (hxy.ne hyx.symm)
        · exact hyz'
      · rfl
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hyz hxz hne hunique ht_yz ht_xz
  have h_xy_yz :
      forall t : V,
        t ∈ (M.edgePath hxy).support ->
          t ∈ (M.edgePath hyz).support ->
            t = M.branchVertex y := by
    intro t ht_xy ht_yz
    have hne :
        Not ((x = y ∧ y = z) ∨ (x = z ∧ y = y)) := by
      rintro (hsame | hrev)
      · exact hxy.ne hsame.1
      · exact hxz.ne hrev.1
    have hunique :
        forall w : EdgeThetaVertex,
          (w = x ∨ w = y) -> (w = y ∨ w = z) -> w = y := by
      intro w hw_xy hw_yz
      rcases hw_xy with rfl | rfl
      · rcases hw_yz with hxy' | hxz'
        · exact False.elim (hxy.ne hxy')
        · exact False.elim (hxz.ne hxz')
      · rfl
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hxy hyz hne hunique ht_xy ht_yz
  have h_xy_xz :
      forall t : V,
        t ∈ (M.edgePath hxy).support ->
          t ∈ (M.edgePath hxz).support ->
            t = M.branchVertex x := by
    intro t ht_xy ht_xz
    have hne :
        Not ((x = x ∧ y = z) ∨ (x = z ∧ y = x)) := by
      rintro (hsame | hrev)
      · exact hyz.ne hsame.2
      · exact hxz.ne hrev.1
    have hunique :
        forall w : EdgeThetaVertex,
          (w = x ∨ w = y) -> (w = x ∨ w = z) -> w = x := by
      intro w hw_xy hw_xz
      rcases hw_xy with rfl | rfl
      · rfl
      · rcases hw_xz with hyx | hyz'
        · exact False.elim (hxy.ne hyx.symm)
        · exact False.elim (hyz.ne hyz')
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hxy hxz hne hunique ht_xy ht_xz
  have hq : q.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint hq₁ hq₂ ?_
    intro t ht₁ ht₂
    have ht₂' : t ∈ (M.edgePath hxz).support := by
      change t ∈ ((M.edgePath hxz).reverse).support at ht₂
      rw [SimpleGraph.Walk.support_reverse] at ht₂
      exact List.mem_reverse.mp ht₂
    exact h_yz_xz t (by simpa [q₁] using ht₁) ht₂'
  have hinter :
      forall t : V, t ∈ p.support -> t ∈ q.support ->
        t = M.branchVertex x ∨ t = M.branchVertex y := by
    intro t htp htq
    change t ∈ (q₁.append q₂).support at htq
    rw [SimpleGraph.Walk.mem_support_append_iff] at htq
    rcases htq with htq₁ | htq₂
    · right
      exact h_xy_yz t (by simpa [p] using htp) (by simpa [q₁] using htq₁)
    · left
      have htq₂' : t ∈ (M.edgePath hxz).support := by
        change t ∈ ((M.edgePath hxz).reverse).support at htq₂
        rw [SimpleGraph.Walk.support_reverse] at htq₂
        exact List.mem_reverse.mp htq₂
      exact h_xy_xz t (by simpa [p] using htp) htq₂'
  have hedges :
      forall e : Sym2 V, e ∈ p.edges -> e ∈ q.edges -> False := by
    intro e hep heq
    change e ∈ (q₁.append q₂).edges at heq
    rw [SimpleGraph.Walk.edges_append] at heq
    rcases List.mem_append.mp heq with heq₁ | heq₂
    · exact
        Walk.edges_disjoint_of_support_inter_subset_singleton
          (p := p) (q := q₁)
          (fun t ht_p ht_q₁ =>
            h_xy_yz t (by simpa [p] using ht_p) (by simpa [q₁] using ht_q₁))
          e hep heq₁
    · have heq₂' : e ∈ (M.edgePath hxz).edges := by
        change e ∈ ((M.edgePath hxz).reverse).edges at heq₂
        rw [SimpleGraph.Walk.edges_reverse] at heq₂
        exact List.mem_reverse.mp heq₂
      exact
        Walk.edges_disjoint_of_support_inter_subset_singleton
          (p := p) (q := M.edgePath hxz)
          (fun t ht_p ht_xz =>
            h_xy_xz t (by simpa [p] using ht_p) ht_xz)
          e hep heq₂'
  have hp_not_nil : ¬ p.Nil := by
    have hbranch_ne : M.branchVertex x ≠ M.branchVertex y := by
      intro hxy_branch
      exact hxy.ne (M.branchVertex_injective hxy_branch)
    exact SimpleGraph.Walk.not_nil_of_ne (p := p) hbranch_ne
  exact
    ⟨M.branchVertex x, p.append q,
      Walk.IsPath.append_isCycle_of_support_inter_subset_endpoints
        hp hq hedges hinter hp_not_nil⟩

/-- A strict `K₂,₃` subdivision contains a simple cycle. -/
theorem ContainsThetaSubdivision.exists_isCycle
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsThetaSubdivision G) :
    Exists fun x : V => Exists fun c : G.Walk x x => c.IsCycle := by
  rcases h with ⟨M⟩
  let a : K23Vertex := Sum.inl (0 : Fin 2)
  let b : K23Vertex := Sum.inl (1 : Fin 2)
  let c : K23Vertex := Sum.inr (0 : Fin 3)
  let d : K23Vertex := Sum.inr (1 : Fin 3)
  have hac : K23Graph.Adj a c := by
    simp [K23Graph, a, c]
  have hbc : K23Graph.Adj b c := by
    simp [K23Graph, b, c]
  have hbd : K23Graph.Adj b d := by
    simp [K23Graph, b, d]
  have had : K23Graph.Adj a d := by
    simp [K23Graph, a, d]
  let p : G.Walk (M.branchVertex a) (M.branchVertex c) :=
    M.edgePath hac
  let q₁ : G.Walk (M.branchVertex c) (M.branchVertex b) :=
    (M.edgePath hbc).reverse
  let q₂ : G.Walk (M.branchVertex b) (M.branchVertex d) :=
    M.edgePath hbd
  let q₃ : G.Walk (M.branchVertex d) (M.branchVertex a) :=
    (M.edgePath had).reverse
  let r : G.Walk (M.branchVertex c) (M.branchVertex d) :=
    q₁.append q₂
  let q : G.Walk (M.branchVertex c) (M.branchVertex a) :=
    r.append q₃
  have hp : p.IsPath := by
    simpa [p] using M.edgePath_isPath hac
  have hq₁ : q₁.IsPath := by
    simpa [q₁] using (M.edgePath_isPath hbc).reverse
  have hq₂ : q₂.IsPath := by
    simpa [q₂] using M.edgePath_isPath hbd
  have hq₃ : q₃.IsPath := by
    simpa [q₃] using (M.edgePath_isPath had).reverse
  have h_bc_bd :
      forall t : V,
        t ∈ (M.edgePath hbc).support ->
          t ∈ (M.edgePath hbd).support ->
            t = M.branchVertex b := by
    intro t ht_bc ht_bd
    have hne :
        Not ((b = b ∧ c = d) ∨ (b = d ∧ c = b)) := by
      simp [b, c, d]
    have hunique :
        forall w : K23Vertex,
          (w = b ∨ w = c) -> (w = b ∨ w = d) -> w = b := by
      intro w hw_bc hw_bd
      rcases hw_bc with rfl | rfl
      · rfl
      · rcases hw_bd with hcb | hcd
        · simp [b, c] at hcb
        · simp [c, d] at hcd
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hbc hbd hne hunique ht_bc ht_bd
  have h_bd_ad :
      forall t : V,
        t ∈ (M.edgePath hbd).support ->
          t ∈ (M.edgePath had).support ->
            t = M.branchVertex d := by
    intro t ht_bd ht_ad
    have hne :
        Not ((b = a ∧ d = d) ∨ (b = d ∧ d = a)) := by
      simp [a, b, d]
    have hunique :
        forall w : K23Vertex,
          (w = b ∨ w = d) -> (w = a ∨ w = d) -> w = d := by
      intro w hw_bd hw_ad
      rcases hw_bd with rfl | rfl
      · rcases hw_ad with hba | hbd'
        · simp [a, b] at hba
        · simp [b, d] at hbd'
      · rfl
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hbd had hne hunique ht_bd ht_ad
  have h_ac_bc :
      forall t : V,
        t ∈ (M.edgePath hac).support ->
          t ∈ (M.edgePath hbc).support ->
            t = M.branchVertex c := by
    intro t ht_ac ht_bc
    have hne :
        Not ((a = b ∧ c = c) ∨ (a = c ∧ c = b)) := by
      simp [a, b, c]
    have hunique :
        forall w : K23Vertex,
          (w = a ∨ w = c) -> (w = b ∨ w = c) -> w = c := by
      intro w hw_ac hw_bc
      rcases hw_ac with rfl | rfl
      · rcases hw_bc with hab | hac'
        · simp [a, b] at hab
        · simp [a, c] at hac'
      · rfl
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hac hbc hne hunique ht_ac ht_bc
  have h_ac_ad :
      forall t : V,
        t ∈ (M.edgePath hac).support ->
          t ∈ (M.edgePath had).support ->
            t = M.branchVertex a := by
    intro t ht_ac ht_ad
    have hne :
        Not ((a = a ∧ c = d) ∨ (a = d ∧ c = a)) := by
      simp [a, c, d]
    have hunique :
        forall w : K23Vertex,
          (w = a ∨ w = c) -> (w = a ∨ w = d) -> w = a := by
      intro w hw_ac hw_ad
      rcases hw_ac with rfl | rfl
      · rfl
      · rcases hw_ad with hca | hcd
        · simp [a, c] at hca
        · simp [c, d] at hcd
    exact
      M.edgePath_support_inter_eq_common_branchVertex
        hac had hne hunique ht_ac ht_ad
  have h_bc_ad_disjoint :
      Disjoint
        {t : V | t ∈ (M.edgePath hbc).support}
        {t : V | t ∈ (M.edgePath had).support} := by
    exact
      M.edgePath_support_disjoint_of_no_common_endpoint
        hbc had
        (by simp [a, b])
        (by simp [b, d])
        (by simp [a, c])
        (by simp [c, d])
  have h_ac_bd_disjoint :
      Disjoint
        {t : V | t ∈ (M.edgePath hac).support}
        {t : V | t ∈ (M.edgePath hbd).support} := by
    exact
      M.edgePath_support_disjoint_of_no_common_endpoint
        hac hbd
        (by simp [a, b])
        (by simp [a, d])
        (by simp [b, c])
        (by simp [c, d])
  have hr : r.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint hq₁ hq₂ ?_
    intro t ht₁ ht₂
    have ht₁' : t ∈ (M.edgePath hbc).support := by
      change t ∈ ((M.edgePath hbc).reverse).support at ht₁
      rw [SimpleGraph.Walk.support_reverse] at ht₁
      exact List.mem_reverse.mp ht₁
    exact h_bc_bd t ht₁' (by simpa [q₂] using ht₂)
  have hq : q.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint hr hq₃ ?_
    intro t htr ht₃
    change t ∈ (q₁.append q₂).support at htr
    rw [SimpleGraph.Walk.mem_support_append_iff] at htr
    have ht₃' : t ∈ (M.edgePath had).support := by
      change t ∈ ((M.edgePath had).reverse).support at ht₃
      rw [SimpleGraph.Walk.support_reverse] at ht₃
      exact List.mem_reverse.mp ht₃
    rcases htr with ht₁ | ht₂
    · have ht₁' : t ∈ (M.edgePath hbc).support := by
        change t ∈ ((M.edgePath hbc).reverse).support at ht₁
        rw [SimpleGraph.Walk.support_reverse] at ht₁
        exact List.mem_reverse.mp ht₁
      exact False.elim
        (Set.disjoint_left.mp h_bc_ad_disjoint ht₁' ht₃')
    · exact h_bd_ad t (by simpa [q₂] using ht₂) ht₃'
  have hinter :
      forall t : V, t ∈ p.support -> t ∈ q.support ->
        t = M.branchVertex a ∨ t = M.branchVertex c := by
    intro t htp htq
    change t ∈ (r.append q₃).support at htq
    rw [SimpleGraph.Walk.mem_support_append_iff] at htq
    rcases htq with htr | ht₃
    · change t ∈ (q₁.append q₂).support at htr
      rw [SimpleGraph.Walk.mem_support_append_iff] at htr
      rcases htr with ht₁ | ht₂
      · right
        have ht₁' : t ∈ (M.edgePath hbc).support := by
          change t ∈ ((M.edgePath hbc).reverse).support at ht₁
          rw [SimpleGraph.Walk.support_reverse] at ht₁
          exact List.mem_reverse.mp ht₁
        exact h_ac_bc t (by simpa [p] using htp) ht₁'
      · exact False.elim
          (Set.disjoint_left.mp h_ac_bd_disjoint
            (by simpa [p] using htp) (by simpa [q₂] using ht₂))
    · left
      have ht₃' : t ∈ (M.edgePath had).support := by
        change t ∈ ((M.edgePath had).reverse).support at ht₃
        rw [SimpleGraph.Walk.support_reverse] at ht₃
        exact List.mem_reverse.mp ht₃
      exact h_ac_ad t (by simpa [p] using htp) ht₃'
  have hedges :
      forall e : Sym2 V, e ∈ p.edges -> e ∈ q.edges -> False := by
    intro e hep heq
    change e ∈ (r.append q₃).edges at heq
    rw [SimpleGraph.Walk.edges_append] at heq
    rcases List.mem_append.mp heq with her | he₃
    · change e ∈ (q₁.append q₂).edges at her
      rw [SimpleGraph.Walk.edges_append] at her
      rcases List.mem_append.mp her with he₁ | he₂
      · have he₁' : e ∈ (M.edgePath hbc).edges := by
          change e ∈ ((M.edgePath hbc).reverse).edges at he₁
          rw [SimpleGraph.Walk.edges_reverse] at he₁
          exact List.mem_reverse.mp he₁
        exact
          Walk.edges_disjoint_of_support_inter_subset_singleton
            (p := p) (q := M.edgePath hbc)
            (fun t ht_p ht_bc =>
              h_ac_bc t (by simpa [p] using ht_p) ht_bc)
            e hep he₁'
      · exact
          Walk.edges_disjoint_of_support_disjoint
            (p := p) (q := q₂)
            (by
              simpa [p, q₂] using h_ac_bd_disjoint)
            e hep he₂
    · have he₃' : e ∈ (M.edgePath had).edges := by
        change e ∈ ((M.edgePath had).reverse).edges at he₃
        rw [SimpleGraph.Walk.edges_reverse] at he₃
        exact List.mem_reverse.mp he₃
      exact
        Walk.edges_disjoint_of_support_inter_subset_singleton
          (p := p) (q := M.edgePath had)
          (fun t ht_p ht_ad =>
            h_ac_ad t (by simpa [p] using ht_p) ht_ad)
          e hep he₃'
  have hp_not_nil : ¬ p.Nil := by
    have hbranch_ne : M.branchVertex a ≠ M.branchVertex c := by
      intro hac_branch
      exact hac.ne (M.branchVertex_injective hac_branch)
    exact SimpleGraph.Walk.not_nil_of_ne (p := p) hbranch_ne
  exact
    ⟨M.branchVertex a, p.append q,
      Walk.IsPath.append_isCycle_of_support_inter_subset_endpoints
        hp hq hedges hinter hp_not_nil⟩

/-- The explicit suppressed-edge theta contains a simple cycle. -/
theorem ContainsEdgeTheta.exists_isCycle
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsEdgeTheta G) :
    Exists fun x : V => Exists fun c : G.Walk x x => c.IsCycle := by
  rcases h with
    ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv⟩
  let p : G.Walk u x :=
    SimpleGraph.Walk.cons hyu.symm
      (SimpleGraph.Walk.cons hyv
        (SimpleGraph.Walk.cons hxv.symm SimpleGraph.Walk.nil))
  refine ⟨x, SimpleGraph.Walk.cons hxu p, ?_⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · simp [p, SimpleGraph.Walk.cons_isPath_iff,
      hxy.ne.symm, hxu.ne.symm, hyu.ne.symm, hxv.ne.symm, hyv.ne, huv]
  · simp [p, Sym2.eq, hxy.ne, hxu.ne, hxu.ne.symm, hyu.ne.symm,
      hxv.ne, huv]

/-- Every source-facing homeomorphic theta branch contains a simple cycle. -/
theorem ContainsHomeomorphicTheta.exists_isCycle
    {V : Type v} {G : SimpleGraph V}
    (h : ContainsHomeomorphicTheta G) :
    Exists fun x : V => Exists fun c : G.Walk x x => c.IsCycle := by
  rcases h with hstrict | hedgeSub | hedge
  · exact ContainsThetaSubdivision.exists_isCycle hstrict
  · exact ContainsEdgeThetaSubdivision.exists_isCycle hedgeSub
  · exact ContainsEdgeTheta.exists_isCycle hedge

theorem ContainsHomeomorphicTheta.map
    {V : Type v} {U : Type*}
    {G : SimpleGraph V} {G' : SimpleGraph U}
    (f : G →g G')
    (hf : Function.Injective f)
    (h : ContainsHomeomorphicTheta G) :
    ContainsHomeomorphicTheta G' := by
  rcases h with htheta | hedgeThetaOr
  · exact ContainsHomeomorphicTheta.of_strict
      (ContainsStrictSubdivision.map f hf htheta)
  rcases hedgeThetaOr with hedgeSubdivision | hedge
  · exact ContainsHomeomorphicTheta.of_edgeSubdivision
      (ContainsStrictSubdivision.map f hf hedgeSubdivision)
  · exact ContainsHomeomorphicTheta.of_edge (ContainsEdgeTheta.map f hf hedge)

/-- A homeomorphic theta in the spanning-coercion graph of a subgraph already
lives in the induced `coe` graph of that subgraph; isolated vertices added by
`spanningCoe` cannot participate in any theta branch. -/
theorem ContainsHomeomorphicTheta.coe_of_spanningCoe
    {V : Type v} {G : SimpleGraph V}
    (S : G.Subgraph)
    (h : ContainsHomeomorphicTheta S.spanningCoe) :
    ContainsHomeomorphicTheta S.coe := by
  rcases h with hstrict | hedgeSub | hedge
  · have hsource :
        forall x : K23Vertex, Exists fun y : K23Vertex => K23Graph.Adj x y := by
      intro x
      rcases x with i | j
      · exact ⟨Sum.inr 0, by simp [K23Graph]⟩
      · exact ⟨Sum.inl 0, by simp [K23Graph]⟩
    have hsupport : S.spanningCoe.support ⊆ S.verts := by
      intro z hz
      rcases (SimpleGraph.mem_support S.spanningCoe).mp hz with ⟨w, hzw⟩
      have hzw' : S.coe.spanningCoe.Adj z w := by
        simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hzw
      exact SimpleGraph.Subgraph.mem_of_adj_spanningCoe S.coe hzw'
    have hrestrict :
        ContainsThetaSubdivision (S.spanningCoe.induce S.verts) :=
      ContainsStrictSubdivision.targetRestrictOfSupportSubset
        hstrict hsource hsupport
    exact ContainsHomeomorphicTheta.of_strict (by
      simpa [SimpleGraph.induce, SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using
        hrestrict)
  · have hsource :
        forall x : EdgeThetaVertex,
          Exists fun y : EdgeThetaVertex => EdgeThetaGraph.Adj x y := by
      intro x
      rcases x with i | j
      · exact ⟨Sum.inr 0, by simp [EdgeThetaGraph]⟩
      · exact ⟨Sum.inl 0, by simp [EdgeThetaGraph]⟩
    have hsupport : S.spanningCoe.support ⊆ S.verts := by
      intro z hz
      rcases (SimpleGraph.mem_support S.spanningCoe).mp hz with ⟨w, hzw⟩
      have hzw' : S.coe.spanningCoe.Adj z w := by
        simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hzw
      exact SimpleGraph.Subgraph.mem_of_adj_spanningCoe S.coe hzw'
    have hrestrict :
        ContainsEdgeThetaSubdivision (S.spanningCoe.induce S.verts) :=
      ContainsStrictSubdivision.targetRestrictOfSupportSubset
        hedgeSub hsource hsupport
    exact ContainsHomeomorphicTheta.of_edgeSubdivision (by
      simpa [SimpleGraph.induce, SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using
        hrestrict)
  · rcases hedge with
      ⟨x, y, u, w, hxy, hxu, hyu, hxw, hyw, huw⟩
    have hxy' : S.coe.spanningCoe.Adj x y := by
      simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hxy
    have hxu' : S.coe.spanningCoe.Adj x u := by
      simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hxu
    have hyu' : S.coe.spanningCoe.Adj y u := by
      simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hyu
    have hxw' : S.coe.spanningCoe.Adj x w := by
      simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hxw
    have hyw' : S.coe.spanningCoe.Adj y w := by
      simpa [SimpleGraph.Subgraph.spanningCoe_coe] using hyw
    let x' : S.verts :=
      ⟨x, SimpleGraph.Subgraph.mem_of_adj_spanningCoe S.coe hxy'⟩
    let y' : S.verts :=
      ⟨y, SimpleGraph.Subgraph.mem_of_adj_spanningCoe S.coe hxy'.symm⟩
    let u' : S.verts :=
      ⟨u, SimpleGraph.Subgraph.mem_of_adj_spanningCoe S.coe hxu'.symm⟩
    let w' : S.verts :=
      ⟨w, SimpleGraph.Subgraph.mem_of_adj_spanningCoe S.coe hxw'.symm⟩
    exact ContainsHomeomorphicTheta.of_edge
      ⟨x', y', u', w',
        (by simpa [x', y', SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using hxy),
        (by simpa [x', u', SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using hxu),
        (by simpa [y', u', SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using hyu),
        (by simpa [x', w', SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using hxw),
        (by simpa [y', w', SimpleGraph.Subgraph.spanningCoe, SimpleGraph.Subgraph.coe] using hyw),
        (by
          intro huw'
          exact huw (congrArg Subtype.val huw'))⟩

/-- If a displayed four-vertex suppressed-edge theta in `G` is not already a
theta in a same-vertex graph `G₀`, at least one of its five displayed edges is
outside `G₀`. -/
theorem ContainsEdgeTheta.exists_edge_not_mem_edgeSet_of_not_contains
    {V : Type v}
    {G G₀ : SimpleGraph V}
    (h : ContainsEdgeTheta G)
    (hno : Not (ContainsEdgeTheta G₀)) :
    Exists fun e : Sym2 V => e ∈ G.edgeSet ∧ e ∉ G₀.edgeSet := by
  rcases h with ⟨x, y, u, w, hxy, hxu, hyu, hxw, hyw, huw⟩
  by_contra hnone
  have hmem :
      forall e : Sym2 V, e ∈ G.edgeSet -> e ∈ G₀.edgeSet := by
    intro e he
    by_contra he_not
    exact hnone ⟨e, he, he_not⟩
  apply hno
  refine ⟨x, y, u, w, ?_, ?_, ?_, ?_, ?_, huw⟩
  · rw [← SimpleGraph.mem_edgeSet]
    exact hmem s(x, y) (by rwa [SimpleGraph.mem_edgeSet])
  · rw [← SimpleGraph.mem_edgeSet]
    exact hmem s(x, u) (by rwa [SimpleGraph.mem_edgeSet])
  · rw [← SimpleGraph.mem_edgeSet]
    exact hmem s(y, u) (by rwa [SimpleGraph.mem_edgeSet])
  · rw [← SimpleGraph.mem_edgeSet]
    exact hmem s(x, w) (by rwa [SimpleGraph.mem_edgeSet])
  · rw [← SimpleGraph.mem_edgeSet]
    exact hmem s(y, w) (by rwa [SimpleGraph.mem_edgeSet])

/-- Makarychev-style edge extraction: if a homeomorphic theta in `G` is not
contained in a same-vertex graph `G₀`, then some edge used by that theta is an
edge of `G` outside `G₀`. -/
theorem ContainsHomeomorphicTheta.exists_edge_not_mem_edgeSet_of_not_contains
    {V : Type v}
    {G G₀ : SimpleGraph V}
    (h : ContainsHomeomorphicTheta G)
    (hno : Not (ContainsHomeomorphicTheta G₀)) :
    Exists fun e : Sym2 V => e ∈ G.edgeSet ∧ e ∉ G₀.edgeSet := by
  rcases h with hstrict | hedgeSub | hedge
  · have hnoStrict :
        Not (ContainsThetaSubdivision G₀) := by
      intro hstrict₀
      exact hno (ContainsHomeomorphicTheta.of_strict hstrict₀)
    rcases
        ContainsStrictSubdivision.exists_model_edge_not_mem_edgeSet_of_not_contains
          hstrict hnoStrict with
      ⟨x, y, hxy, e, he, he_not⟩
    exact
      ⟨e, (Classical.choice hstrict).edgePath hxy |>.edges_subset_edgeSet he,
        he_not⟩
  · have hnoEdgeSub :
        Not (ContainsEdgeThetaSubdivision G₀) := by
      intro hedgeSub₀
      exact hno (ContainsHomeomorphicTheta.of_edgeSubdivision hedgeSub₀)
    rcases
        ContainsStrictSubdivision.exists_model_edge_not_mem_edgeSet_of_not_contains
          hedgeSub hnoEdgeSub with
      ⟨x, y, hxy, e, he, he_not⟩
    exact
      ⟨e, (Classical.choice hedgeSub).edgePath hxy |>.edges_subset_edgeSet he,
        he_not⟩
  · have hnoEdge :
        Not (ContainsEdgeTheta G₀) := by
      intro hedge₀
      exact hno (ContainsHomeomorphicTheta.of_edge hedge₀)
    exact ContainsEdgeTheta.exists_edge_not_mem_edgeSet_of_not_contains hedge hnoEdge

theorem not_containsHomeomorphicTheta_induce
    {V : Type v}
    {G : SimpleGraph V}
    (S : Set V)
    (hno : Not (ContainsHomeomorphicTheta G)) :
    Not (ContainsHomeomorphicTheta (G.induce S)) := by
  intro htheta
  exact hno
    (ContainsHomeomorphicTheta.map
      (SimpleGraph.Embedding.induce (G := G) S).toHom
      (SimpleGraph.Embedding.induce (G := G) S).injective
      htheta)

end Schematic.Math.GraphTheory
