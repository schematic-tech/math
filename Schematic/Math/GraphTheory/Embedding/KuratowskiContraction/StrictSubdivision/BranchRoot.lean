import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.TieK33

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

@[simp]
theorem strictSubdivisionModel_collapseEdge_branch_root_branchVertex_self
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
    strictSubdivisionModel_collapseEdge_branch_root_branchVertex
      hab M hc (root := root) c = root := by
  simp [strictSubdivisionModel_collapseEdge_branch_root_branchVertex]

theorem strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c w : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hwc : w ≠ c) :
    strictSubdivisionModel_collapseEdge_branch_root_branchVertex
      hab M hc (root := root) w =
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w)
        (by
          intro hw_none
          exact hwc
            (M.branchVertex_injective (hw_none.trans hc.symm))) := by
  simp [strictSubdivisionModel_collapseEdge_branch_root_branchVertex, hwc]

theorem strictSubdivisionModel_collapseEdge_branch_root_branchVertex_injective
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root : V}
    (hab : G.Adj a b)
    (hroot_pair : root ∈ ({a, b} : Set V))
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    Function.Injective
      (strictSubdivisionModel_collapseEdge_branch_root_branchVertex
        hab M hc (root := root)) := by
  classical
  intro x y hxy
  by_cases hxc : x = c
  · by_cases hyc : y = c
    · exact hxc.trans hyc.symm
    · subst x
      have hy_ne :
          M.branchVertex y ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hy_none
        exact hyc (M.branchVertex_injective (hy_none.trans hc.symm))
      have hroot_eq :
          root =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy_ne := by
        simpa
          [strictSubdivisionModel_collapseEdge_branch_root_branchVertex,
            hyc] using hxy
      exact False.elim
        (GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hy_ne
          (by simpa [hroot_eq] using hroot_pair))
  · by_cases hyc : y = c
    · subst y
      have hx_ne :
          M.branchVertex x ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hx_none
        exact hxc (M.branchVertex_injective (hx_none.trans hc.symm))
      have hroot_eq :
          root =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex x) hx_ne := by
        simpa
          [strictSubdivisionModel_collapseEdge_branch_root_branchVertex,
            hxc] using hxy.symm
      exact False.elim
        (GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab hx_ne
          (by simpa [hroot_eq] using hroot_pair))
    · have hx_ne :
          M.branchVertex x ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hx_none
        exact hxc (M.branchVertex_injective (hx_none.trans hc.symm))
      have hy_ne :
          M.branchVertex y ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hy_none
        exact hyc (M.branchVertex_injective (hy_none.trans hc.symm))
      have huncollapsed :
          GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex x) hx_ne =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex y) hy_ne := by
        simpa
          [strictSubdivisionModel_collapseEdge_branch_root_branchVertex,
            hxc, hyc] using hxy
      exact M.branchVertex_injective
        (GraphContraction.collapseEdgeUncollapse_injective G hab
          hx_ne hy_ne huncollapsed)

structure CollapseEdgeBranchIncidentTail
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y : W}
    (hcy : K.Adj c y)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) where
  hy :
    M.branchVertex y ≠
      (none : (GraphContraction.collapseEdge G hab).Target)
  v : V
  q :
    G.Walk v
      (GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex y) hy)
  hside : G.Adj a v ∨ G.Adj b v
  q_isPath : q.IsPath
  q_outside :
    forall z : V, z ∈ q.support -> z ∉ ({a, b} : Set V)
  q_reflect :
    forall z : V, z ∈ q.support ->
      Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
        qv ∈ (M.edgePath hcy).support ∧
          Exists fun hqv_ne :
            qv ≠ (none : (GraphContraction.collapseEdge G hab).Target) =>
            GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z

noncomputable def CollapseEdgeBranchIncidentTail.ofModel
    {W : Type*} {V : Type u} [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c y : W}
    (hcy : K.Adj c y)
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    CollapseEdgeBranchIncidentTail hab M hcy hc := by
  classical
  let E :=
    strictSubdivisionModel_collapseEdge_branch_incident_tail_lift
      hab M hcy hc
  let hy := Classical.choose E
  let Ehy := Classical.choose_spec E
  let v := Classical.choose Ehy
  let Hv := Classical.choose_spec Ehy
  let q := Classical.choose Hv.2
  let Hq := Classical.choose_spec Hv.2
  exact {
    hy := hy
    v := v
    q := q
    hside := Hq.1
    q_isPath := Hq.2.1
    q_outside := Hq.2.2.1
    q_reflect := Hq.2.2.2 }

structure CollapseEdgeBranchRootData
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (root other : V) where
  hroot_pair : root ∈ ({a, b} : Set V)
  hother_pair : other ∈ ({a, b} : Set V)
  hroot_other : G.Adj root other
  hy :
    forall {y : W}, K.Adj c y ->
      M.branchVertex y ≠
        (none : (GraphContraction.collapseEdge G hab).Target)
  v : forall {y : W}, K.Adj c y -> V
  q :
    forall {y : W} (hcy : K.Adj c y),
      G.Walk (v hcy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex y) (hy hcy))
  hside :
    forall {y : W} (hcy : K.Adj c y),
      G.Adj root (v hcy) ∨ G.Adj other (v hcy)
  q_isPath :
    forall {y : W} (hcy : K.Adj c y), (q hcy).IsPath
  q_outside :
    forall {y : W} (hcy : K.Adj c y) (z : V),
      z ∈ (q hcy).support -> z ∉ ({a, b} : Set V)
  q_reflect :
    forall {y : W} (hcy : K.Adj c y) (z : V),
      z ∈ (q hcy).support ->
        Exists fun qv : (GraphContraction.collapseEdge G hab).Target =>
          qv ∈ (M.edgePath hcy).support ∧
            Exists fun hqv_ne :
              qv ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne = z
  q_disjoint :
    forall {y z : W} (hcy : K.Adj c y) (hcz : K.Adj c z),
      y ≠ z ->
        Disjoint
          {t : V | t ∈ (q hcy).support}
          {t : V | t ∈ (q hcz).support}
  pair_direct :
    forall {y z : W} (hcy : K.Adj c y) (hcz : K.Adj c z),
      y ≠ z -> G.Adj root (v hcy) ∨ G.Adj root (v hcz)

noncomputable def CollapseEdgeBranchRootData.ofIncidentTails
    {W : Type*} {V : Type u} [DecidableEq W] [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (T : forall {y : W} (hcy : K.Adj c y),
      CollapseEdgeBranchIncidentTail hab M hcy hc)
    (hpair_direct :
      forall {y z : W} (hcy : K.Adj c y) (hcz : K.Adj c z),
        y ≠ z -> G.Adj root ((T hcy).v) ∨ G.Adj root ((T hcz).v)) :
    CollapseEdgeBranchRootData hab M hc root other where
  hroot_pair := hroot_pair
  hother_pair := hother_pair
  hroot_other := hroot_other
  hy := fun hcy => (T hcy).hy
  v := fun hcy => (T hcy).v
  q := fun hcy => (T hcy).q
  hside := fun hcy =>
    collapseEdge_pair_side_to_root_other
      hroot_pair hother_pair hroot_other (T hcy).hside
  q_isPath := fun hcy => (T hcy).q_isPath
  q_outside := fun hcy => (T hcy).q_outside
  q_reflect := fun hcy => (T hcy).q_reflect
  q_disjoint := by
    intro y z hcy hcz hyz
    exact
      strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
        hab M hcy hcz hyz hc (T hcy).q_reflect (T hcz).q_reflect
  pair_direct := hpair_direct

noncomputable def CollapseEdgeBranchRootData.ofModel
    {W : Type*} {V : Type u} [DecidableEq W] [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (hpair_direct :
      forall {y z : W} (hcy : K.Adj c y) (hcz : K.Adj c z),
        y ≠ z ->
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) ∨
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcz hc).v)) :
    CollapseEdgeBranchRootData hab M hc root other :=
  CollapseEdgeBranchRootData.ofIncidentTails hab M hc
    hroot_pair hother_pair hroot_other
    (fun hcy => CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc)
    hpair_direct

theorem k5TieK33Branch_injective_of_collapseEdge_K5_two_two
    {V : Type u} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c p q r s : Fin 5}
    {hcp : K5Graph.Adj c p}
    {hcq : K5Graph.Adj c q}
    {hcr : K5Graph.Adj c r}
    {hcs : K5Graph.Adj c s}
    {hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)}
    (Tp : CollapseEdgeBranchIncidentTail hab M hcp hc)
    (Tq : CollapseEdgeBranchIncidentTail hab M hcq hc)
    (Tr : CollapseEdgeBranchIncidentTail hab M hcr hc)
    (Ts : CollapseEdgeBranchIncidentTail hab M hcs hc)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    Function.Injective
      (k5TieK33Branch a b
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex p) Tp.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex q) Tq.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex r) Tr.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex s) Ts.hy)) := by
  classical
  let bp :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex p) Tp.hy
  let bq :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex q) Tq.hy
  let br :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex r) Tr.hy
  let bs :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex s) Ts.hy
  have hbp_pair : bp ∉ ({a, b} : Set V) := by
    simpa [bp] using
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab Tp.hy
  have hbq_pair : bq ∉ ({a, b} : Set V) := by
    simpa [bq] using
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab Tq.hy
  have hbr_pair : br ∉ ({a, b} : Set V) := by
    simpa [br] using
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab Tr.hy
  have hbs_pair : bs ∉ ({a, b} : Set V) := by
    simpa [bs] using
      GraphContraction.collapseEdgeUncollapse_not_mem_pair G hab Ts.hy
  have ha_bp : a ≠ bp := by
    intro h
    exact hbp_pair (by simp [← h])
  have ha_bq : a ≠ bq := by
    intro h
    exact hbq_pair (by simp [← h])
  have ha_br : a ≠ br := by
    intro h
    exact hbr_pair (by simp [← h])
  have ha_bs : a ≠ bs := by
    intro h
    exact hbs_pair (by simp [← h])
  have hb_bp : b ≠ bp := by
    intro h
    exact hbp_pair (by simp [← h])
  have hb_bq : b ≠ bq := by
    intro h
    exact hbq_pair (by simp [← h])
  have hb_br : b ≠ br := by
    intro h
    exact hbr_pair (by simp [← h])
  have hb_bs : b ≠ bs := by
    intro h
    exact hbs_pair (by simp [← h])
  have hbp_bq : bp ≠ bq := by
    intro h
    have hM : M.branchVertex p = M.branchVertex q :=
      GraphContraction.collapseEdgeUncollapse_injective G hab Tp.hy Tq.hy h
    exact hpq (M.branchVertex_injective hM)
  have hbp_br : bp ≠ br := by
    intro h
    have hM : M.branchVertex p = M.branchVertex r :=
      GraphContraction.collapseEdgeUncollapse_injective G hab Tp.hy Tr.hy h
    exact hpr (M.branchVertex_injective hM)
  have hbp_bs : bp ≠ bs := by
    intro h
    have hM : M.branchVertex p = M.branchVertex s :=
      GraphContraction.collapseEdgeUncollapse_injective G hab Tp.hy Ts.hy h
    exact hps (M.branchVertex_injective hM)
  have hbq_br : bq ≠ br := by
    intro h
    have hM : M.branchVertex q = M.branchVertex r :=
      GraphContraction.collapseEdgeUncollapse_injective G hab Tq.hy Tr.hy h
    exact hqr (M.branchVertex_injective hM)
  have hbq_bs : bq ≠ bs := by
    intro h
    have hM : M.branchVertex q = M.branchVertex s :=
      GraphContraction.collapseEdgeUncollapse_injective G hab Tq.hy Ts.hy h
    exact hqs (M.branchVertex_injective hM)
  have hbr_bs : br ≠ bs := by
    intro h
    have hM : M.branchVertex r = M.branchVertex s :=
      GraphContraction.collapseEdgeUncollapse_injective G hab Tr.hy Ts.hy h
    exact hrs (M.branchVertex_injective hM)
  simpa [bp, bq, br, bs] using
    k5TieK33Branch_injective
      hab.ne ha_bp ha_bq ha_br ha_bs
      hb_bp hb_bq hb_br hb_bs
      hbp_bq hbp_br hbp_bs hbq_br hbq_bs hbr_bs

theorem k5TieK33Branch_cases_of_collapseEdge_K5_two_two_ab
    {V : Type u} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c p q r s : Fin 5}
    {hcp : K5Graph.Adj c p}
    {hcq : K5Graph.Adj c q}
    {hcr : K5Graph.Adj c r}
    {hcs : K5Graph.Adj c s}
    {hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)}
    (Tp : CollapseEdgeBranchIncidentTail hab M hcp hc)
    (Tq : CollapseEdgeBranchIncidentTail hab M hcq hc)
    (Tr : CollapseEdgeBranchIncidentTail hab M hcr hc)
    (Ts : CollapseEdgeBranchIncidentTail hab M hcs hc) :
    forall w : K33Vertex,
      k5TieK33Branch a b
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex p) Tp.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex q) Tq.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex r) Tr.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex s) Ts.hy) w = a ∨
      k5TieK33Branch a b
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex p) Tp.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex q) Tq.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex r) Tr.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex s) Ts.hy) w = b ∨
      Exists fun x : Fin 5 =>
        x ≠ c ∧
          Exists fun hx :
            M.branchVertex x ≠
              (none : (GraphContraction.collapseEdge G hab).Target) =>
            k5TieK33Branch a b
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex p) Tp.hy)
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex q) Tq.hy)
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex r) Tr.hy)
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) Ts.hy) w =
                GraphContraction.collapseEdgeUncollapse G hab
                  (M.branchVertex x) hx := by
  intro w
  rcases w with w | w
  · fin_cases w
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨r, hcr.ne.symm, Tr.hy, rfl⟩)
    · exact Or.inr (Or.inr ⟨s, hcs.ne.symm, Ts.hy, rfl⟩)
  · fin_cases w
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨p, hcp.ne.symm, Tp.hy, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hcq.ne.symm, Tq.hy, rfl⟩)

theorem k5TieK33Branch_cases_of_collapseEdge_K5_two_two_ba
    {V : Type u} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c p q r s : Fin 5}
    {hcp : K5Graph.Adj c p}
    {hcq : K5Graph.Adj c q}
    {hcr : K5Graph.Adj c r}
    {hcs : K5Graph.Adj c s}
    {hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)}
    (Tp : CollapseEdgeBranchIncidentTail hab M hcp hc)
    (Tq : CollapseEdgeBranchIncidentTail hab M hcq hc)
    (Tr : CollapseEdgeBranchIncidentTail hab M hcr hc)
    (Ts : CollapseEdgeBranchIncidentTail hab M hcs hc) :
    forall w : K33Vertex,
      k5TieK33Branch a b
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex p) Tp.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex q) Tq.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex r) Tr.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex s) Ts.hy) w = b ∨
      k5TieK33Branch a b
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex p) Tp.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex q) Tq.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex r) Tr.hy)
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex s) Ts.hy) w = a ∨
      Exists fun x : Fin 5 =>
        x ≠ c ∧
          Exists fun hx :
            M.branchVertex x ≠
              (none : (GraphContraction.collapseEdge G hab).Target) =>
            k5TieK33Branch a b
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex p) Tp.hy)
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex q) Tq.hy)
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex r) Tr.hy)
              (GraphContraction.collapseEdgeUncollapse G hab
                (M.branchVertex s) Ts.hy) w =
                GraphContraction.collapseEdgeUncollapse G hab
                  (M.branchVertex x) hx := by
  intro w
  rcases
      k5TieK33Branch_cases_of_collapseEdge_K5_two_two_ab
        hab M Tp Tq Tr Ts w with
    ha | hb | hrest
  · exact Or.inr (Or.inl ha)
  · exact Or.inl hb
  · exact Or.inr (Or.inr hrest)

noncomputable def strictSubdivisionModel_collapseEdge_branch_root_edgePath
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (D : CollapseEdgeBranchRootData hab M hc root other)
    {s t : W}
    (hst : K.Adj s t) :
    G.Walk
      (strictSubdivisionModel_collapseEdge_branch_root_branchVertex
        hab M hc (root := root) s)
      (strictSubdivisionModel_collapseEdge_branch_root_branchVertex
        hab M hc (root := root) t) := by
  classical
  by_cases hsc : s = c
  · subst s
    have htc : t ≠ c := fun htc => hst.ne htc.symm
    let p : G.Walk root
        (GraphContraction.collapseEdgeUncollapse G hab
          (M.branchVertex t) (D.hy hst)) :=
      Walk.branchAttachmentPath D.hroot_other
        (D.hside hst) (D.q hst)
    refine p.copy ?_ ?_
    · simp [strictSubdivisionModel_collapseEdge_branch_root_branchVertex]
    · calc
        GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t) (D.hy hst) =
          GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t)
            (by
              intro ht_none
              exact htc
                (M.branchVertex_injective (ht_none.trans hc.symm))) :=
            GraphContraction.collapseEdgeUncollapse_congr G hab
              (D.hy hst) _ rfl
        _ =
          strictSubdivisionModel_collapseEdge_branch_root_branchVertex
            hab M hc (root := root) t := by
            rw [strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
              (root := root) hab M hc htc]
  · by_cases htc : t = c
    · subst t
      have hcs : K.Adj c s := hst.symm
      let p : G.Walk root
          (GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex s) (D.hy hcs)) :=
        Walk.branchAttachmentPath D.hroot_other
          (D.hside hcs) (D.q hcs)
      refine p.reverse.copy ?_ ?_
      · calc
          GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s) (D.hy hcs) =
            GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s)
              (by
                intro hs_none
                exact hsc
                  (M.branchVertex_injective (hs_none.trans hc.symm))) :=
              GraphContraction.collapseEdgeUncollapse_congr G hab
                (D.hy hcs) _ rfl
          _ =
            strictSubdivisionModel_collapseEdge_branch_root_branchVertex
              hab M hc (root := root) s := by
              rw [strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
                (root := root) hab M hc hsc]
      · simp [strictSubdivisionModel_collapseEdge_branch_root_branchVertex]
    · have hs_ne :
          M.branchVertex s ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hs_none
        exact hsc (M.branchVertex_injective (hs_none.trans hc.symm))
      have ht_ne :
          M.branchVertex t ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro ht_none
        exact htc (M.branchVertex_injective (ht_none.trans hc.symm))
      let havoid :=
        strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
          hab M hst hc hsc htc
      let p : G.Walk
          (GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex s) hs_ne)
          (GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t) ht_ne) :=
        GraphContraction.collapseEdgeWalkOutside G hab
          hs_ne ht_ne (M.edgePath hst) havoid
      refine p.copy ?_ ?_
      · rw [strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
          (root := root) hab M hc hsc]
      · rw [strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
          (root := root) hab M hc htc]

theorem strictSubdivisionModel_collapseEdge_branch_root_edgePath_isPath
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (D : CollapseEdgeBranchRootData hab M hc root other)
    {s t : W}
    (hst : K.Adj s t) :
    (strictSubdivisionModel_collapseEdge_branch_root_edgePath
      hab M hc D hst).IsPath := by
  classical
  unfold strictSubdivisionModel_collapseEdge_branch_root_edgePath
  split_ifs with hsc htc
  · subst s
    have hroot_not : root ∉ (D.q hst).support := by
      intro hroot
      exact D.q_outside hst root hroot D.hroot_pair
    have hother_not : other ∉ (D.q hst).support := by
      intro hother
      exact D.q_outside hst other hother D.hother_pair
    exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr
      (Walk.branchAttachmentPath_isPath D.hroot_other
        (D.hside hst) (D.q_isPath hst)
        hroot_not hother_not)
  · subst t
    have hcs : K.Adj c s := hst.symm
    have hroot_not : root ∉ (D.q hcs).support := by
      intro hroot
      exact D.q_outside hcs root hroot D.hroot_pair
    have hother_not : other ∉ (D.q hcs).support := by
      intro hother
      exact D.q_outside hcs other hother D.hother_pair
    exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr
      (Walk.branchAttachmentPath_isPath D.hroot_other
        (D.hside hcs) (D.q_isPath hcs)
        hroot_not hother_not).reverse
  · have hs_ne :
        M.branchVertex s ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      intro hs_none
      exact hsc (M.branchVertex_injective (hs_none.trans hc.symm))
    have ht_ne :
        M.branchVertex t ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      intro ht_none
      exact htc (M.branchVertex_injective (ht_none.trans hc.symm))
    let havoid :=
      strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
        hab M hst hc hsc htc
    exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr
      (GraphContraction.collapseEdgeWalkOutside_isPath G hab
        hs_ne ht_ne (M.edgePath hst) havoid (M.edgePath_isPath hst))

theorem strictSubdivisionModel_collapseEdge_clean_lift_no_internal_branch_vertex_local
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {s t w : W}
    (hst : K.Adj s t)
    (hs :
      M.branchVertex s ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (ht :
      M.branchVertex t ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hw :
      M.branchVertex w ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    {z : V}
    (hz : z ∈ Walk.InternalVertices
      (GraphContraction.collapseEdgeWalkOutside G hab
        hs ht (M.edgePath hst) havoid)) :
    z ≠
      GraphContraction.collapseEdgeUncollapse G hab
        (M.branchVertex w) hw := by
  intro hzw
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab hs ht (M.edgePath hst) havoid hz.1 with
    ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  have hqv_branch : qv = M.branchVertex w :=
    GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne
      hw (hqv_eq.trans hzw)
  have hw_endpoint : w = s ∨ w = t := by
    have hmem : M.branchVertex w ∈ (M.edgePath hst).support := by
      simpa [hqv_branch] using hqv_mem
    exact (M.branchVertex_mem_edgePath_support_iff hst).mp hmem
  rcases hw_endpoint with rfl | rfl
  · exact hz.2.1 hzw
  · exact hz.2.2 hzw

theorem strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
    {W : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {s t s' t' : W}
    (hst : K.Adj s t)
    (hs't' : K.Adj s' t')
    (hne : Not ((s = s' ∧ t = t') ∨ (s = t' ∧ t = s')))
    (hs :
      M.branchVertex s ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (ht :
      M.branchVertex t ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hs' :
      M.branchVertex s' ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (ht' :
      M.branchVertex t' ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid' : forall qv, qv ∈ (M.edgePath hs't').support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target)) :
    Disjoint
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          hs ht (M.edgePath hst) havoid))
      (Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          hs' ht' (M.edgePath hs't') havoid')) := by
  classical
  rw [Set.disjoint_left]
  intro z hz hz'
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab hs ht (M.edgePath hst) havoid hz.1 with
    ⟨qv, hqv_mem, hqv_ne, hqv_eq⟩
  rcases
      GraphContraction.collapseEdgeWalkOutside_support_reflects
        G hab hs' ht' (M.edgePath hs't') havoid' hz'.1 with
    ⟨rv, hrv_mem, hrv_ne, hrv_eq⟩
  have hqv_rv : qv = rv :=
    GraphContraction.collapseEdgeUncollapse_injective G hab hqv_ne hrv_ne
      (hqv_eq.trans hrv_eq.symm)
  have hqv_internal : qv ∈ Walk.InternalVertices (M.edgePath hst) := by
    refine ⟨hqv_mem, ?_, ?_⟩
    · intro hqs
      have hz_start :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex s) hs := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
            hqv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s) hs :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
              hs hqs
      exact hz.2.1 hz_start
    · intro hqt
      have hz_end :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t) ht := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab qv hqv_ne :=
            hqv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex t) ht :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hqv_ne
              ht hqt
      exact hz.2.2 hz_end
  have hrv_internal : rv ∈ Walk.InternalVertices (M.edgePath hs't') := by
    refine ⟨hrv_mem, ?_, ?_⟩
    · intro hrs
      have hz_start :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex s') hs' := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
            hrv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex s') hs' :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
              hs' hrs
      exact hz'.2.1 hz_start
    · intro hrt
      have hz_end :
          z = GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex t') ht' := by
        calc
          z = GraphContraction.collapseEdgeUncollapse G hab rv hrv_ne :=
            hrv_eq.symm
          _ = GraphContraction.collapseEdgeUncollapse G hab
              (M.branchVertex t') ht' :=
            GraphContraction.collapseEdgeUncollapse_congr G hab hrv_ne
              ht' hrt
      exact hz'.2.2 hz_end
  exact Set.disjoint_left.mp
    (M.internally_disjoint_edge_paths' hst hs't' hne)
    hqv_internal (by simpa [hqv_rv] using hrv_internal)

theorem strictSubdivisionModel_collapseEdge_clean_lift_no_listed_branches
    {W B : Type*} {V : Type u}
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {s t : W}
    (hst : K.Adj s t)
    (hs :
      M.branchVertex s ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (ht :
      M.branchVertex t ≠
        (none : (GraphContraction.collapseEdge G hab).Target))
    (havoid : forall qv, qv ∈ (M.edgePath hst).support ->
      qv ≠ (none : (GraphContraction.collapseEdge G hab).Target))
    (branch : B -> V)
    (hbranch_cases :
      forall w : B,
        branch w = a ∨ branch w = b ∨
          Exists fun x : W =>
            Exists fun hx :
              M.branchVertex x ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              branch w =
                GraphContraction.collapseEdgeUncollapse G hab
                  (M.branchVertex x) hx)
    {z : V}
    (hz :
      z ∈ Walk.InternalVertices
        (GraphContraction.collapseEdgeWalkOutside G hab
          hs ht (M.edgePath hst) havoid))
    (w : B) :
    z ≠ branch w := by
  classical
  rcases hbranch_cases w with ha | hb | huncollapsed
  · intro hzw
    have hzout :
        z ∉ ({a, b} : Set V) :=
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab
        hs ht (M.edgePath hst) havoid hz.1
    exact hzout (by
      rw [hzw, ha]
      simp)
  · intro hzw
    have hzout :
        z ∉ ({a, b} : Set V) :=
      GraphContraction.collapseEdgeWalkOutside_support_outside G hab
        hs ht (M.edgePath hst) havoid hz.1
    exact hzout (by
      rw [hzw, hb]
      simp)
  · rcases huncollapsed with ⟨x, hx, hw_eq⟩
    have hz_ne :=
      strictSubdivisionModel_collapseEdge_clean_lift_no_internal_branch_vertex_local
        hab M hst hs ht hx havoid hz
    intro hzw
    apply hz_ne
    calc
      z = branch w := hzw
      _ =
          GraphContraction.collapseEdgeUncollapse G hab
            (M.branchVertex x) hx := hw_eq
end FourColor

end Schematic.Math.GraphTheory
