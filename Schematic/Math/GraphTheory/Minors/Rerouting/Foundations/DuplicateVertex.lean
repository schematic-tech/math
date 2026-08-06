import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.VertexTriples

/-! Duplicating and folding a separator vertex. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def duplicateVertexGraph (G : SimpleGraph V) (root : V) :
    SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some x, some y => G.Adj x y
    | none, some y => G.Adj root y
    | some x, none => G.Adj x root
    | none, none => False
  symm := by
    intro a b h
    cases a <;> cases b <;> simp at h ⊢
    all_goals exact h.symm
  loopless := by
    constructor
    intro a h
    cases a <;> simp at h

def duplicateVertexFoldHom (G : SimpleGraph V) (root : V) :
    duplicateVertexGraph G root →g G where
  toFun
    | none => root
    | some v => v
  map_rel' := by
    intro a b h
    cases a <;> cases b <;> simp [duplicateVertexGraph] at h ⊢
    all_goals exact h

def duplicateVertexOriginalHom (G : SimpleGraph V) (root : V) :
    G →g duplicateVertexGraph G root where
  toFun v := some v
  map_rel' := by
    intro a b h
    simpa [duplicateVertexGraph] using h

theorem duplicateVertexGraph_original_adj_iff
    (G : SimpleGraph V) (root a b : V) :
    (duplicateVertexGraph G root).Adj (some a) (some b) ↔ G.Adj a b := by
  simp [duplicateVertexGraph]

theorem duplicateVertexGraph_twin_adj_iff
    (G : SimpleGraph V) (root a : V) :
    (duplicateVertexGraph G root).Adj none (some a) ↔ G.Adj root a := by
  simp [duplicateVertexGraph]

theorem duplicateVertexGraph_adj_twin_iff
    (G : SimpleGraph V) (root a : V) :
    (duplicateVertexGraph G root).Adj (some a) none ↔ G.Adj a root := by
  simp [duplicateVertexGraph]

theorem duplicateVertexGraph_not_adj_self_twin
    (G : SimpleGraph V) (root : V) :
    Not ((duplicateVertexGraph G root).Adj (some root) none) := by
  simp [duplicateVertexGraph]

def duplicateVertexSeparationLeft (S : Separation G) : Set (Option V) :=
  fun o : Option V =>
    match o with
    | none => True
    | some v => v ∈ S.left

def duplicateVertexSeparationRight (S : Separation G) : Set (Option V) :=
  fun o : Option V =>
    match o with
    | none => False
    | some v => v ∈ S.right

def duplicateVertexSeparation
    (S : Separation G) {root : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right) :
    Separation (duplicateVertexGraph G root) where
  left := duplicateVertexSeparationLeft S
  right := duplicateVertexSeparationRight S
  covers := by
    ext o
    constructor
    · intro _ho
      exact Set.mem_univ o
    · intro _ho
      cases o with
      | none =>
          exact Or.inl trivial
      | some v =>
          simpa [duplicateVertexSeparationLeft, duplicateVertexSeparationRight]
            using S.mem_left_or_right v
  no_cross := by
    intro a b ha han hb hbn hab
    cases a with
    | none =>
        cases b with
        | none =>
            simp [duplicateVertexGraph] at hab
        | some bv =>
            have hb_right : bv ∈ S.right := by
              simpa [duplicateVertexSeparationRight] using hb
            have hb_not_left : bv ∉ S.left := by
              intro hb_left
              exact hbn (by simpa [duplicateVertexSeparationLeft] using hb_left)
            have hroot_adj : G.Adj root bv := by
              simpa [duplicateVertexGraph] using hab
            exact S.no_cross hroot_left hroot_not_right hb_right hb_not_left hroot_adj
    | some av =>
        cases b with
        | none =>
            simpa [duplicateVertexSeparationRight] using hb
        | some bv =>
            have ha_left : av ∈ S.left := by
              simpa [duplicateVertexSeparationLeft] using ha
            have ha_not_right : av ∉ S.right := by
              intro ha_right
              exact han (by simpa [duplicateVertexSeparationRight] using ha_right)
            have hb_right : bv ∈ S.right := by
              simpa [duplicateVertexSeparationRight] using hb
            have hb_not_left : bv ∉ S.left := by
              intro hb_left
              exact hbn (by simpa [duplicateVertexSeparationLeft] using hb_left)
            have habG : G.Adj av bv := by
              simpa [duplicateVertexGraph] using hab
            exact S.no_cross ha_left ha_not_right hb_right hb_not_left habG

@[simp] theorem duplicateVertexSeparation_none_left
    (S : Separation G) {root : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right) :
    none ∈ (duplicateVertexSeparation S hroot_left hroot_not_right).left := by
  exact trivial

@[simp] theorem duplicateVertexSeparation_none_right
    (S : Separation G) {root : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right) :
    Not (none ∈ (duplicateVertexSeparation S hroot_left hroot_not_right).right) := by
  intro h
  exact h

@[simp] theorem duplicateVertexSeparation_some_left
    (S : Separation G) {root v : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right) :
    some v ∈ (duplicateVertexSeparation S hroot_left hroot_not_right).left ↔
      v ∈ S.left := by
  rfl

@[simp] theorem duplicateVertexSeparation_some_right
    (S : Separation G) {root v : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right) :
    some v ∈ (duplicateVertexSeparation S hroot_left hroot_not_right).right ↔
      v ∈ S.right := by
  rfl

theorem duplicateVertexSeparation_separator
    (S : Separation G) {root : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right) :
    (duplicateVertexSeparation S hroot_left hroot_not_right).separator =
      some '' S.separator := by
  ext o
  cases o with
  | none =>
      constructor
      · intro h
        exact False.elim h.2
      · rintro ⟨v, _hv, hsome⟩
        cases hsome
  | some v =>
      constructor
      · intro h
        exact ⟨v, h, rfl⟩
      · rintro ⟨w, hw, hsome⟩
        have hwv : w = v := Option.some.inj hsome
        simpa [hwv] using hw

theorem duplicateVertexSeparation_separator_triple
    (S : Separation G) {root x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hseparator : S.separator = ({x, y, z} : Set V)) :
    (duplicateVertexSeparation S hroot_left hroot_not_right).separator =
      ({some x, some y, some z} : Set (Option V)) := by
  rw [duplicateVertexSeparation_separator S hroot_left hroot_not_right, hseparator]
  ext o
  cases o <;> simp [Set.mem_insert_iff]

theorem duplicateVertexSeparation_proper
    (S : Separation G) {root : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hproper : S.Proper) :
    (duplicateVertexSeparation S hroot_left hroot_not_right).Proper := by
  refine ⟨?_, ?_⟩
  · exact ⟨none, by exact trivial, by intro h; exact h⟩
  · rcases hproper.2 with ⟨v, hv_right, hv_not_left⟩
    exact ⟨some v, by simpa [duplicateVertexSeparationRight] using hv_right,
      by
        intro hv_left_dup
        exact hv_not_left (by
          simpa [duplicateVertexSeparationLeft] using hv_left_dup)⟩

theorem duplicateVertexSeparation_orderAtMost
    [DecidableEq V]
    (S : Separation G) {root : V} {t : Nat}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (horder : S.OrderAtMost t) :
    (duplicateVertexSeparation S hroot_left hroot_not_right).OrderAtMost t := by
  rcases horder with ⟨F, hF, hcard⟩
  refine ⟨F.image some, ?_, ?_⟩
  · ext o
    cases o with
    | none =>
        constructor
        · intro h
          simp at h
        · intro h
          exact False.elim h.2
    | some v =>
        constructor
        · intro hvF
          have hvF_original : v ∈ F := by
            simpa using hvF
          have hv_sep : v ∈ S.separator := by
            rw [← hF]
            exact hvF_original
          change v ∈ S.left ∧ v ∈ S.right
          simpa [Separation.separator] using hv_sep
        · intro hv_sep
          have hvS : v ∈ S.separator := by
            change v ∈ S.left ∧ v ∈ S.right at hv_sep
            simpa [Separation.separator] using hv_sep
          have hvF_original : v ∈ F := by
            change v ∈ (F : Set V)
            rwa [hF]
          simpa using hvF_original
  · exact le_trans (Finset.card_image_le) hcard

def duplicateVertexOriginalDeleted (S : Set (Option V)) : Set V :=
  {v : V | some v ∈ S}

theorem duplicateVertexOriginalDeleted_mem
    (S : Set (Option V)) (v : V) :
    v ∈ duplicateVertexOriginalDeleted (V := V) S ↔ some v ∈ S := by
  rfl

theorem duplicateVertexOriginalDeleted_ncard_le
    [Fintype V]
    (S : Set (Option V)) :
    (duplicateVertexOriginalDeleted (V := V) S).ncard <= S.ncard := by
  classical
  exact Set.ncard_le_ncard_of_injOn
    (s := duplicateVertexOriginalDeleted (V := V) S)
    (t := S)
    (f := fun v : V => some v)
    (by
      intro v hv
      exact hv)
    (by
      intro a ha b hb h
      exact Option.some.inj h)

theorem duplicateVertexOriginalDeleted_ncard_lt_three
    [Fintype V]
    {S : Set (Option V)}
    (hS : S.ncard < 3) :
    (duplicateVertexOriginalDeleted (V := V) S).ncard < 3 := by
  have hle := duplicateVertexOriginalDeleted_ncard_le (V := V) S
  omega

theorem duplicateVertexGraph_exists_twin_neighbor_after_small_delete
    [Fintype V] [DecidableRel G.Adj]
    {root : V}
    (hroot_degree : 3 <= G.degree root)
    {S : Set (Option V)}
    (hS : S.ncard < 3) :
    Exists fun n : V =>
      some n ∉ S ∧ G.Adj root n := by
  classical
  let S₀ : Set V := duplicateVertexOriginalDeleted (V := V) S
  have hS₀_lt : S₀.ncard < 3 :=
    duplicateVertexOriginalDeleted_ncard_lt_three (V := V) hS
  have hinside_le :
      (G.neighborSet root ∩ S₀).ncard <= S₀.ncard :=
    Set.ncard_inter_le_ncard_right (G.neighborSet root) S₀
  have hinside_lt :
      (G.neighborSet root ∩ S₀).ncard < G.degree root := by
    omega
  obtain ⟨n, hn_delete, hnr⟩ :=
    exists_neighbor_outside_set_of_inside_neighbors_lt_degree
      (G := G) S₀ (v := root) hinside_lt
  have hnS₀ : n ∉ S₀ := by
    simpa [SimpleGraph.Subgraph.deleteVerts_verts] using hn_delete
  exact ⟨n, by simpa [S₀, duplicateVertexOriginalDeleted] using hnS₀, hnr.symm⟩

theorem duplicateVertexGraph_reachable_some_some_after_delete
    [Fintype V]
    (hG : IsThreeConnected G)
    {root u v : V}
    {S : Set (Option V)}
    (hS : S.ncard < 3)
    (hu : some u ∉ S)
    (hv : some v ∉ S) :
    ((duplicateVertexGraph G root).induce Sᶜ).Reachable
      ⟨some u, hu⟩ ⟨some v, hv⟩ := by
  classical
  let S₀ : Set V := duplicateVertexOriginalDeleted (V := V) S
  have hS₀_lt : S₀.ncard < 3 :=
    duplicateVertexOriginalDeleted_ncard_lt_three (V := V) hS
  have huS₀ : u ∈ S₀ᶜ := by
    simpa [S₀, duplicateVertexOriginalDeleted] using hu
  have hvS₀ : v ∈ S₀ᶜ := by
    simpa [S₀, duplicateVertexOriginalDeleted] using hv
  have hconn₀ : (G.induce S₀ᶜ).Connected := hG.2 S₀ hS₀_lt
  obtain ⟨p, hp_support⟩ :=
    connected_induce_exists_walk_support_subset
      (G := G) hconn₀ huS₀ hvS₀
  let q : (duplicateVertexGraph G root).Walk (some u) (some v) :=
    p.map (duplicateVertexOriginalHom G root)
  have hq_support :
      forall a : Option V, a ∈ q.support -> a ∈ Sᶜ := by
    intro a ha
    change a ∉ S
    change a ∈ (p.map (duplicateVertexOriginalHom G root)).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    have ha_map : a ∈ p.support.map (fun x : V => some x) := by
      simpa [duplicateVertexOriginalHom] using ha
    simp only [List.mem_map] at ha_map
    rcases ha_map with ⟨w, hw, rfl⟩
    exact hp_support w hw
  exact Walk.reachable_induce_of_support_subset q hq_support

theorem duplicateVertexGraph_reachable_twin_some_after_delete
    [Fintype V] [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    {root v : V}
    (hroot_degree : 3 <= G.degree root)
    {S : Set (Option V)}
    (hS : S.ncard < 3)
    (hnone : none ∉ S)
    (hv : some v ∉ S) :
    ((duplicateVertexGraph G root).induce Sᶜ).Reachable
      ⟨none, hnone⟩ ⟨some v, hv⟩ := by
  classical
  obtain ⟨n, hnS, hrn⟩ :=
    duplicateVertexGraph_exists_twin_neighbor_after_small_delete
      (G := G) (root := root) hroot_degree hS
  have hnone_adj_n :
      ((duplicateVertexGraph G root).induce Sᶜ).Adj
        ⟨none, hnone⟩ ⟨some n, hnS⟩ := by
    simpa [duplicateVertexGraph] using hrn
  exact (SimpleGraph.Adj.reachable hnone_adj_n).trans
    (duplicateVertexGraph_reachable_some_some_after_delete
      (G := G) hG hS hnS hv)

theorem duplicateVertexGraph_connected_after_small_delete
    [Fintype V] [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    {root : V}
    (hroot_degree : 3 <= G.degree root)
    {S : Set (Option V)}
    (hS : S.ncard < 3) :
    ((duplicateVertexGraph G root).induce Sᶜ).Connected := by
  classical
  let S₀ : Set V := duplicateVertexOriginalDeleted (V := V) S
  have hS₀_lt : S₀.ncard < 3 :=
    duplicateVertexOriginalDeleted_ncard_lt_three (V := V) hS
  have hconn₀ : (G.induce S₀ᶜ).Connected := hG.2 S₀ hS₀_lt
  obtain ⟨u₀⟩ := hconn₀.nonempty
  have hsome_u₀ : some (u₀ : V) ∉ S := by
    have hu₀_not_S₀ : (u₀ : V) ∉ S₀ := by
      exact u₀.2
    simpa [S₀, duplicateVertexOriginalDeleted] using hu₀_not_S₀
  refine {
    preconnected := ?_
    nonempty := ⟨⟨some (u₀ : V), hsome_u₀⟩⟩
  }
  intro a b
  cases a with
  | mk a ha =>
      cases b with
      | mk b hb =>
          cases a with
          | none =>
              cases b with
              | none =>
                  have hsame :
                      (⟨none, ha⟩ : (Sᶜ : Set (Option V))) =
                        ⟨none, hb⟩ := Subtype.ext rfl
                  rw [← hsame]
              | some v =>
                  exact duplicateVertexGraph_reachable_twin_some_after_delete
                    (G := G) hG hroot_degree hS ha hb
          | some u =>
              cases b with
              | none =>
                  exact (duplicateVertexGraph_reachable_twin_some_after_delete
                    (G := G) hG hroot_degree hS hb ha).symm
              | some v =>
                  exact duplicateVertexGraph_reachable_some_some_after_delete
                    (G := G) hG hS ha hb

theorem duplicateVertexGraph_three_connected
    [Fintype V] [DecidableRel G.Adj]
    (hG : IsThreeConnected G)
    {root : V}
    (hroot_degree : 3 <= G.degree root) :
    IsThreeConnected (duplicateVertexGraph G root) := by
  classical
  refine ⟨?_, ?_⟩
  · have hV : 3 < Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using hG.1
    rw [Nat.card_eq_fintype_card, Fintype.card_option]
    omega
  · intro S hS
    exact duplicateVertexGraph_connected_after_small_delete
      (G := G) hG hroot_degree hS

theorem duplicateVertexFoldHom_mem_support_iff
    {root x : V} {a b : Option V}
    {p : (duplicateVertexGraph G root).Walk a b} :
    x ∈ (p.map (duplicateVertexFoldHom G root)).support ↔
      some x ∈ p.support ∨ x = root ∧ none ∈ p.support := by
  rw [SimpleGraph.Walk.support_map]
  constructor
  · intro hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨o, ho, hox⟩
    cases o with
    | none =>
        right
        simp [duplicateVertexFoldHom] at hox
        exact ⟨hox.symm, ho⟩
    | some y =>
        left
        simp [duplicateVertexFoldHom] at hox
        simpa [hox] using ho
  · intro hx
    simp only [List.mem_map]
    rcases hx with hx | ⟨rfl, hnone⟩
    · exact ⟨some x, hx, by simp [duplicateVertexFoldHom]⟩
    · exact ⟨none, hnone, by simp [duplicateVertexFoldHom]⟩

theorem duplicateVertexFoldHom_injOn_support_of_not_none
    {root : V} {a b : Option V}
    {p : (duplicateVertexGraph G root).Walk a b}
    (hnone : none ∉ p.support) :
    Set.InjOn (duplicateVertexFoldHom G root)
      {o : Option V | o ∈ p.support} := by
  intro o ho q hq hoq
  cases o with
  | none =>
      exact False.elim (hnone ho)
  | some ov =>
      cases q with
      | none =>
          exact False.elim (hnone hq)
      | some qv =>
          simp [duplicateVertexFoldHom] at hoq
          simp [hoq]

theorem duplicateVertexFoldHom_injOn_support_of_not_some_root
    {root : V} {a b : Option V}
    {p : (duplicateVertexGraph G root).Walk a b}
    (hsome_root : some root ∉ p.support) :
    Set.InjOn (duplicateVertexFoldHom G root)
      {o : Option V | o ∈ p.support} := by
  intro o ho q hq hoq
  cases o with
  | none =>
      cases q with
      | none =>
          rfl
      | some qv =>
          simp [duplicateVertexFoldHom] at hoq
          exact False.elim (hsome_root (by simpa [hoq] using hq))
  | some ov =>
      cases q with
      | none =>
          simp [duplicateVertexFoldHom] at hoq
          exact False.elim (hsome_root (by simpa [hoq] using ho))
      | some qv =>
          simp [duplicateVertexFoldHom] at hoq
          simp [hoq]

theorem duplicateVertexFoldHom_map_isPath_of_not_none
    {root : V} {a b : Option V}
    {p : (duplicateVertexGraph G root).Walk a b}
    (hp : p.IsPath)
    (hnone : none ∉ p.support) :
    (p.map (duplicateVertexFoldHom G root)).IsPath :=
  Walk.map_isPath_of_injOn_support
    (duplicateVertexFoldHom G root)
    (duplicateVertexFoldHom_injOn_support_of_not_none
      (G := G) (root := root) (p := p) hnone)
    hp

theorem duplicateVertexFoldHom_map_isPath_of_not_some_root
    {root : V} {a b : Option V}
    {p : (duplicateVertexGraph G root).Walk a b}
    (hp : p.IsPath)
    (hsome_root : some root ∉ p.support) :
    (p.map (duplicateVertexFoldHom G root)).IsPath :=
  Walk.map_isPath_of_injOn_support
    (duplicateVertexFoldHom G root)
    (duplicateVertexFoldHom_injOn_support_of_not_some_root
      (G := G) (root := root) (p := p) hsome_root)
    hp

theorem duplicateVertexFoldHom_reverse_append_isPath
    {root y z : V}
    {pYdup : (duplicateVertexGraph G root).Walk (some root) (some y)}
    {pZdup : (duplicateVertexGraph G root).Walk none (some z)}
    (hpY : pYdup.IsPath)
    (hpZ : pZdup.IsPath)
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support}) :
    let fold := duplicateVertexFoldHom G root
    ((pYdup.map fold).reverse.append (pZdup.map fold)).IsPath := by
  classical
  intro fold
  have hnone_not_Y : none ∉ pYdup.support := by
    intro hnoneY
    exact Set.disjoint_left.mp hYZ hnoneY pZdup.start_mem_support
  have hsome_root_not_Z : some root ∉ pZdup.support := by
    intro hrootZ
    exact Set.disjoint_left.mp hYZ pYdup.start_mem_support hrootZ
  have hpYmap : (pYdup.map fold).IsPath := by
    simpa [fold] using
      duplicateVertexFoldHom_map_isPath_of_not_none
        (G := G) (root := root) hpY hnone_not_Y
  have hpZmap : (pZdup.map fold).IsPath := by
    simpa [fold] using
      duplicateVertexFoldHom_map_isPath_of_not_some_root
        (G := G) (root := root) hpZ hsome_root_not_Z
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
    List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · simpa [SimpleGraph.Walk.support_reverse] using hpYmap.reverse.support_nodup
  · exact hpZmap.support_nodup.tail
  · intro a haY b hbZtail hab
    subst b
    have haY_support : a ∈ (pYdup.map fold).support := by
      rw [SimpleGraph.Walk.support_reverse] at haY
      exact List.mem_reverse.mp haY
    have haZ_support : a ∈ (pZdup.map fold).support :=
      List.mem_of_mem_tail hbZtail
    have ha_ne_root : a ≠ root := by
      intro haroot
      exact Walk.IsPath.start_notMem_tail_support hpZmap (by
        simpa [haroot, fold, duplicateVertexFoldHom] using hbZtail)
    have hfoldY := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pYdup) (x := a)).mp (by
        simpa [fold] using haY_support)
    have hsome_a_Y : some a ∈ pYdup.support := by
      rcases hfoldY with hsome | ⟨haroot, hnone⟩
      · exact hsome
      · exact False.elim (hnone_not_Y hnone)
    have hfoldZ := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pZdup) (x := a)).mp (by
        simpa [fold] using haZ_support)
    rcases hfoldZ with hsomeZ | ⟨haroot, _hnoneZ⟩
    · exact Set.disjoint_left.mp hYZ hsome_a_Y hsomeZ
    · exact ha_ne_root haroot


end Schematic.Math.GraphTheory
