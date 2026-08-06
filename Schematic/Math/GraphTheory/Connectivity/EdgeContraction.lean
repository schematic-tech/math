import Schematic.Math.GraphTheory.Connectivity.Definitions
import Schematic.Math.GraphTheory.Contractions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
Connectivity under vertex deletion and edge contraction.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem IsFourConnected.connected
    (hG : IsFourConnected G) :
    G.Connected :=
  IsKConnected.connected hG (by decide)

theorem IsFourConnected.delete_fin3_range_connected
    [Fintype V]
    (hG : IsFourConnected G)
    {feet : Fin 3 -> V}
    (hfeet_injective : Function.Injective feet) :
    (G.induce (Set.range feet)ᶜ).Connected := by
  have hrange : (Set.range feet).ncard = 3 := by
    rw [Set.ncard_range_of_injective hfeet_injective]
    simp
  exact hG.2 (Set.range feet) (by omega)

theorem IsThreeConnected.delete_vertex_isTwoConnected
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (v : V) :
    IsTwoConnected (G.induce {z : V | z ≠ v}) := by
  classical
  let V' := {z : V // z ≠ v}
  let G' : SimpleGraph V' := G.induce {z : V | z ≠ v}
  have hcard : 2 < Nat.card V' := by
    rw [Nat.card_eq_fintype_card]
    change 2 < Fintype.card {z : V // z ≠ v}
    have hdel :
        Fintype.card {z : V // z ≠ v} = Fintype.card V - 1 :=
      Set.card_ne_eq v
    rw [hdel]
    have hcardG : 3 < Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using hG.1
    omega
  refine ⟨hcard, ?_⟩
  intro S hS
  let T : Set V := insert v (Subtype.val '' S)
  have hT : T.ncard < 3 := by
    have himage :
        (Subtype.val '' S : Set V).ncard = S.ncard :=
      Set.ncard_image_of_injective S Subtype.val_injective
    have hinsert :
        T.ncard ≤ (Subtype.val '' S : Set V).ncard + 1 := by
      simpa [T, Nat.add_comm] using
        Set.ncard_insert_le v (Subtype.val '' S : Set V)
    omega
  have hconnected : (G.induce Tᶜ).Connected := hG.2 T hT
  let e : G.induce Tᶜ ≃g G'.induce Sᶜ :=
    { toEquiv :=
        { toFun := fun z => by
            have hzv : z.1 ≠ v := by
              intro hz
              apply z.2
              simp [T, hz]
            refine ⟨⟨z.1, hzv⟩, ?_⟩
            intro hzS
            apply z.2
            exact Set.mem_insert_iff.mpr
              (Or.inr ⟨⟨z.1, hzv⟩, hzS, rfl⟩)
          invFun := fun z => by
            refine ⟨z.1.1, ?_⟩
            intro hzT
            rcases Set.mem_insert_iff.mp hzT with hzv | hzS
            · exact z.1.2 hzv
            · rcases hzS with ⟨w, hwS, hw⟩
              apply z.2
              have hwz : w = z.1 := Subtype.ext hw
              simpa [hwz] using hwS
          left_inv := by
            intro z
            rfl
          right_inv := by
            intro z
            rfl }
      map_rel_iff' := by
        intro x y
        rfl }
  exact e.connected_iff.mp hconnected

theorem IsThreeConnected.collapseEdge_isTwoConnected
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    {a b : V}
    (hab : G.Adj a b) :
    IsTwoConnected (GraphContraction.collapseEdge G hab).graph := by
  classical
  let C : GraphContraction G := GraphContraction.collapseEdge G hab
  letI : Fintype C.Target :=
    GraphContraction.collapseEdgeTargetFintype G hab
  have hcard : 2 < Nat.card C.Target := by
    have hinj :
        Function.Injective
          (GraphContraction.collapseEdgeDeleteRightHom G hab) :=
      GraphContraction.collapseEdgeDeleteRightHom_injective G hab
    have hle :
        Fintype.card {z : V // z ≠ b} ≤ Fintype.card C.Target :=
      Fintype.card_le_of_injective
        (GraphContraction.collapseEdgeDeleteRightHom G hab) hinj
    have hdel :
        Fintype.card {z : V // z ≠ b} = Fintype.card V - 1 :=
      Set.card_ne_eq b
    have hcardG : 3 < Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using hG.1
    simpa [Nat.card_eq_fintype_card, C] using
      (show 2 < Fintype.card C.Target by omega)
  refine ⟨hcard, ?_⟩
  intro S hS
  let T : Set V := insert b (C.map ⁻¹' S)
  let D : Set V := T \ {b}
  have hD_injective : Set.InjOn C.map D := by
    intro x hx y hy hxy
    exact
      GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
        G hab D
        (by
          rintro ⟨_ha, hb⟩
          exact hb.2 rfl)
        x y hx hy hxy
  have hD_image_subset : C.map '' D ⊆ S := by
    rintro y ⟨x, hxD, rfl⟩
    rcases Set.mem_insert_iff.mp hxD.1 with hxb | hxS
    · exact False.elim (hxD.2 hxb)
    · exact hxS
  have hDcard : D.ncard ≤ S.ncard := by
    calc
      D.ncard = (C.map '' D).ncard := hD_injective.ncard_image.symm
      _ ≤ S.ncard := Set.ncard_le_ncard hD_image_subset
  have hT_subset : T ⊆ insert b D := by
    intro x hxT
    by_cases hxb : x = b
    · exact Set.mem_insert_iff.mpr (Or.inl hxb)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hxT, hxb⟩)
  have hT : T.ncard < 3 := by
    have hTcard : T.ncard ≤ (insert b D).ncard :=
      Set.ncard_le_ncard hT_subset
    have hinsert : (insert b D).ncard ≤ D.ncard + 1 :=
      Set.ncard_insert_le b D
    omega
  have hsource : (G.induce Tᶜ).Connected := hG.2 T hT
  let f : G.induce Tᶜ →g C.graph.induce Sᶜ :=
    { toFun := fun x => by
        refine ⟨C.map x.1, ?_⟩
        intro hxS
        exact x.2 (Set.mem_insert_iff.mpr (Or.inr hxS))
      map_rel' := by
        intro x y hxy
        rcases C.map_adj hxy with hsame | hadj
        · have hxy_val : x.1 = y.1 :=
            GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
              G hab Tᶜ
              (by
                rintro ⟨_ha, hb⟩
                exact hb (Set.mem_insert b (C.map ⁻¹' S)))
              x.1 y.1 x.2 y.2 hsame
          exact False.elim (hxy.ne (Subtype.ext hxy_val))
        · exact hadj }
  have hf_surjective : Function.Surjective f := by
    intro y
    obtain ⟨v, hv⟩ := C.surjective y.1
    by_cases hvb : v = b
    · subst v
      have hab_map : C.map a = C.map b :=
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := a) (w := b)).mpr
          (Or.inl (by simp))
      have ha_not_T : a ∉ T := by
        intro haT
        rcases Set.mem_insert_iff.mp haT with hab_eq | haS
        · exact hab.ne hab_eq
        · apply y.2
          rw [← hv, ← hab_map]
          exact haS
      refine ⟨⟨a, ha_not_T⟩, ?_⟩
      apply Subtype.ext
      exact hab_map.trans hv
    · have hv_not_T : v ∉ T := by
        intro hvT
        rcases Set.mem_insert_iff.mp hvT with hvb' | hvS
        · exact hvb hvb'
        · exact y.2 (hv.symm ▸ hvS)
      refine ⟨⟨v, hv_not_T⟩, ?_⟩
      apply Subtype.ext
      exact hv
  exact SimpleGraph.Connected.map f hf_surjective hsource

theorem IsThreeConnected.exists_three_vertex_cut_of_not_collapseEdge_isThreeConnected
    [Fintype V] [DecidableEq V]
    (hG : IsThreeConnected G)
    (hcard : 4 < Nat.card V)
    {a b : V}
    (hab : G.Adj a b)
    (hnot :
      ¬ IsThreeConnected
        (GraphContraction.collapseEdge G hab).graph) :
    Exists fun z : V =>
      ¬ (G.induce (({a, b, z} : Set V)ᶜ)).Connected := by
  classical
  let C : GraphContraction G := GraphContraction.collapseEdge G hab
  letI : Fintype C.Target :=
    GraphContraction.collapseEdgeTargetFintype G hab
  have hcardC : 3 < Nat.card C.Target := by
    have hinj :
        Function.Injective
          (GraphContraction.collapseEdgeDeleteRightHom G hab) :=
      GraphContraction.collapseEdgeDeleteRightHom_injective G hab
    have hle :
        Fintype.card {z : V // z ≠ b} ≤ Fintype.card C.Target :=
      Fintype.card_le_of_injective
        (GraphContraction.collapseEdgeDeleteRightHom G hab) hinj
    have hdel :
        Fintype.card {z : V // z ≠ b} = Fintype.card V - 1 :=
      Set.card_ne_eq b
    have hcardG : 4 < Fintype.card V := by
      simpa [Nat.card_eq_fintype_card] using hcard
    simpa [Nat.card_eq_fintype_card, C] using
      (show 3 < Fintype.card C.Target by omega)
  obtain ⟨S, hSsmall, hSdisc⟩ :=
    not_isKConnected_exists_small_cut
      (G := C.graph) hcardC hnot
  have hCtwo : IsTwoConnected C.graph := by
    simpa [C] using hG.collapseEdge_isTwoConnected hab
  have hScard : S.ncard = 2 := by
    have hSnot_small : ¬ S.ncard < 2 := by
      intro hSlt
      exact hSdisc (hCtwo.2 S hSlt)
    omega
  have hab_map : C.map a = C.map b := by
    simpa [C] using
      (GraphContraction.collapseEdge_map_eq_iff
        (G := G) hab (v := a) (w := b)).mpr
        (Or.inl (by simp))
  have hcollapsed_mem : C.map a ∈ S := by
    by_contra hcollapsed
    let T : Set V := C.map ⁻¹' S
    have hT_injective : Set.InjOn C.map T := by
      intro x hx y hy hxy
      exact
        GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
          G hab T
          (by
            rintro ⟨ha, _hb⟩
            exact hcollapsed ha)
          x y hx hy hxy
    have himage : C.map '' T = S := by
      apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hx
      · intro y hy
        obtain ⟨x, hx⟩ := C.surjective y
        refine ⟨x, ?_, hx⟩
        change C.map x ∈ S
        rw [hx]
        exact hy
    have hTcard : T.ncard = S.ncard := by
      calc
        T.ncard = (C.map '' T).ncard := hT_injective.ncard_image.symm
        _ = S.ncard := congrArg Set.ncard himage
    have hTsmall : T.ncard < 3 := by omega
    have hsource : (G.induce Tᶜ).Connected := hG.2 T hTsmall
    let f :
        {x : V // x ∈ Tᶜ} →
          {y : C.Target // y ∈ Sᶜ} :=
      fun x => ⟨C.map x.1, x.2⟩
    have hf_adj :
        forall {x y : {x : V // x ∈ Tᶜ}},
          (G.induce Tᶜ).Adj x y →
            f x = f y ∨ (C.graph.induce Sᶜ).Adj (f x) (f y) := by
      intro x y hxy
      rcases C.map_adj hxy with hsame | hadj
      · exact Or.inl (Subtype.ext hsame)
      · exact Or.inr hadj
    have hf_surjective : Function.Surjective f := by
      intro y
      obtain ⟨x, hx⟩ := C.surjective y.1
      have hxT : x ∉ T := by
        intro hxS
        exact y.2 (hx ▸ hxS)
      refine ⟨⟨x, hxT⟩, ?_⟩
      exact Subtype.ext hx
    exact hSdisc
      (SimpleGraph.Connected.map_of_adj_eq_or_adj
        hsource f hf_adj hf_surjective)
  obtain ⟨q, hqS, hqne⟩ :=
    Set.exists_ne_of_one_lt_ncard
      (s := S) (by omega) (C.map a)
  have hS_eq : S = ({C.map a, q} : Set C.Target) := by
    have hsubset : ({C.map a, q} : Set C.Target) ⊆ S := by
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact hcollapsed_mem
      · rw [Set.mem_singleton_iff] at hy
        simpa [hy] using hqS
    have hpaircard : ({C.map a, q} : Set C.Target).ncard = 2 := by
      simp [hqne.symm]
    symm
    apply Set.eq_of_subset_of_ncard_le hsubset
    rw [hScard, hpaircard]
  obtain ⟨z, hzmap⟩ := C.surjective q
  have hza : z ≠ a := by
    intro hza
    subst z
    exact hqne hzmap.symm
  have hzb : z ≠ b := by
    intro hzb
    subst z
    exact hqne (hzmap.symm.trans hab_map.symm)
  let U : Set V := {a, b, z}
  have pair_mem_U {x : V}
      (hx : x ∈ ({a, b} : Set V)) :
      x ∈ U := by
    have hx' : x = a ∨ x = b := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with rfl | rfl <;> simp [U]
  let rep : C.Target → V := fun y => Classical.choose (C.surjective y)
  have hrep (y : C.Target) : C.map (rep y) = y :=
    Classical.choose_spec (C.surjective y)
  have hmap_unique_outside :
      forall {x y : V}, x ∉ ({a, b} : Set V) →
        C.map y = C.map x → y = x := by
    intro x y hx hmap
    rcases
        (GraphContraction.collapseEdge_map_eq_iff
          (G := G) hab (v := y) (w := x)).mp
          (by simpa [C] using hmap) with
      hpair | houtside
    · exact False.elim (hx hpair.2)
    · exact houtside.1
  let e : G.induce Uᶜ ≃g C.graph.induce Sᶜ :=
    { toEquiv :=
        { toFun := fun x => by
            refine ⟨C.map x.1, ?_⟩
            rw [hS_eq]
            intro hxS
            rcases Set.mem_insert_iff.mp hxS with hxa | hxq
            · have hx_pair :
                  x.1 ∈ ({a, b} : Set V) := by
                  rcases
                      (GraphContraction.collapseEdge_map_eq_iff
                        (G := G) hab (v := x.1) (w := a)).mp
                        (by simpa [C] using hxa) with
                    hpair | houtside
                  · exact hpair.1
                  · simp [houtside.1]
              exact x.2 (by
                exact pair_mem_U hx_pair)
            · have hxq_eq : C.map x.1 = q :=
                Set.mem_singleton_iff.mp hxq
              have hxz : C.map x.1 = C.map z := by
                exact hxq_eq.trans hzmap.symm
              have hx_eq_z :
                  x.1 = z := by
                exact
                  (hmap_unique_outside
                    (x := x.1) (y := z)
                    (by
                      intro hxpair
                      exact x.2 (pair_mem_U hxpair))
                    hxz.symm).symm
              exact x.2 (by simp [U, hx_eq_z])
          invFun := fun y => by
            refine ⟨rep y.1, ?_⟩
            intro hrepU
            rcases Set.mem_insert_iff.mp hrepU with hra | hrbz
            · apply y.2
              rw [← hrep y.1, hra]
              exact hcollapsed_mem
            · rcases Set.mem_insert_iff.mp hrbz with hrb | hrz
              · apply y.2
                rw [← hrep y.1, hrb, ← hab_map]
                exact hcollapsed_mem
              · apply y.2
                rw [← hrep y.1, Set.mem_singleton_iff.mp hrz, hzmap]
                exact hqS
          left_inv := by
            intro x
            apply Subtype.ext
            exact
              hmap_unique_outside
                (x := x.1) (y := rep (C.map x.1))
                (by
                  intro hxpair
                  exact x.2 (pair_mem_U hxpair))
                (hrep (C.map x.1))
          right_inv := by
            intro y
            apply Subtype.ext
            exact hrep y.1 }
      map_rel_iff' := by
        intro x y
        constructor
        · intro hxy
          obtain ⟨u, v, hu, hv, huv⟩ := C.edge_lift hxy
          have hu_eq : u = x.1 :=
            hmap_unique_outside
              (x := x.1) (y := u)
              (by
                intro hxpair
                exact x.2 (pair_mem_U hxpair))
              hu
          have hv_eq : v = y.1 :=
            hmap_unique_outside
              (x := y.1) (y := v)
              (by
                intro hypair
                exact y.2 (pair_mem_U hypair))
              hv
          simpa [hu_eq, hv_eq] using huv
        · intro hxy
          rcases C.map_adj hxy with hsame | hadj
          · have hxy_val : x.1 = y.1 :=
              GraphContraction.collapseEdge_map_injective_on_set_of_not_pair_both
                G hab Uᶜ
                (by
                  rintro ⟨ha, _hb⟩
                  exact ha (by simp [U]))
                x.1 y.1 x.2 y.2
                (by simpa [C] using hsame)
            exact False.elim (hxy.ne (Subtype.ext hxy_val))
          · exact hadj }
  refine ⟨z, ?_⟩
  intro hconnected
  apply hSdisc
  have hsource : (G.induce Uᶜ).Connected := by
    simpa [U] using hconnected
  exact e.connected_iff.mp hsource

end Schematic.Math.GraphTheory
