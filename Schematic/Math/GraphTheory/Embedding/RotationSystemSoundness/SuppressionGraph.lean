import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.CarrierDegree

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness
/-- The surviving representatives of a collapsed edge, with the possible
new edge between the two neighbours of the deleted degree-two endpoint. -/
def suppressionGraph
    {V : Type u}
    (G : SimpleGraph V) (v : V)
    (w u : {z : V // z ≠ v}) :
    SimpleGraph {z : V // z ≠ v} :=
  G.induce {z : V | z ≠ v} ⊔ SimpleGraph.edge w u

theorem collapseEdge_preimage_survivor
    {V : Type u} {G : SimpleGraph V}
    {v w a : V}
    (hvw : G.Adj v w)
    (x : {z : V // z ≠ v})
    (ha :
      (GraphContraction.collapseEdge G hvw).map a =
        (GraphContraction.collapseEdge G hvw).map (x : V)) :
    a = (x : V) ∨ (a = v ∧ (x : V) = w) := by
  classical
  rcases
      (GraphContraction.collapseEdge_map_eq_iff
        (G := G) hvw (v := a) (w := (x : V))).mp ha with
    hpair | hout
  · have ha_pair : a = v ∨ a = w := by simpa using hpair.1
    have hx_pair : (x : V) = v ∨ (x : V) = w := by simpa using hpair.2
    rcases hx_pair with hxv | hxw
    · exact False.elim (x.2 hxv)
    · rcases ha_pair with hav | haw
      · exact Or.inr ⟨hav, hxw⟩
      · exact Or.inl (haw.trans hxw.symm)
  · exact Or.inl hout.1

theorem collapseEdge_induce_compl_pair_connected_of_isTwoConnected
    {V : Type u} {G : SimpleGraph V}
    {v w : V}
    (hvw : G.Adj v w)
    (hC : IsTwoConnected
      (GraphContraction.collapseEdge G hvw).graph) :
    (G.induce ({v, w} : Set V)ᶜ).Connected := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let c : C.Target := C.map v
  let H : C.graph.Subgraph :=
    (⊤ : C.graph.Subgraph).induce ({c} : Set C.Target)ᶜ
  have hH : H.coe.Connected := by
    change ((⊤ : C.graph.Subgraph).induce ({c} : Set C.Target)ᶜ).coe.Connected
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hC.2 ({c} : Set C.Target) (by simp)
  have hpre : (C.PreimageSubgraph H).coe.Connected :=
    GraphContraction.preimageSubgraph_connected hH
  have hverts : (C.PreimageSubgraph H).verts =
      ({v, w} : Set V)ᶜ := by
    ext z
    change C.map z ≠ C.map v ↔ ¬ (z = v ∨ z = w)
    have heq := not_congr
      (GraphContraction.collapseEdge_map_eq_iff
        (G := G) hvw (v := z) (w := v))
    simpa [C, hvw.ne] using heq
  let φ : (C.PreimageSubgraph H).coe ≃g
      G.induce ({v, w} : Set V)ᶜ := {
    toEquiv := {
      toFun := fun z => ⟨z.1, by rw [← hverts]; exact z.2⟩
      invFun := fun z => ⟨z.1, by rw [hverts]; exact z.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
    }
    map_rel_iff' := by
      intro a b
      change G.Adj a.1 b.1 ↔
        (C.PreimageSubgraph H).Adj a.1 b.1
      constructor
      · intro hab
        have haH : C.map a.1 ∈ H.verts := a.2
        have hbH : C.map b.1 ∈ H.verts := b.2
        refine ⟨hab, a.2, b.2, ?_⟩
        rcases C.map_adj hab with hsame | hadj
        · exact Or.inl hsame
        · exact Or.inr ⟨haH, hbH, hadj⟩
      · exact fun hab => hab.1
  }
  exact φ.connected_iff.mp hpre

theorem collapseEdge_induce_compl_singleton_connected_of_isTwoConnected
    {V : Type u} {G : SimpleGraph V}
    {v w z : V}
    (hvw : G.Adj v w)
    (hzv : z ≠ v)
    (hzw : z ≠ w)
    (hC : IsTwoConnected
      (GraphContraction.collapseEdge G hvw).graph) :
    (G.induce ({z} : Set V)ᶜ).Connected := by
  classical
  let C := GraphContraction.collapseEdge G hvw
  let c : C.Target := C.map z
  let H : C.graph.Subgraph :=
    (⊤ : C.graph.Subgraph).induce ({c} : Set C.Target)ᶜ
  have hH : H.coe.Connected := by
    change ((⊤ : C.graph.Subgraph).induce ({c} : Set C.Target)ᶜ).coe.Connected
    rw [← SimpleGraph.induce_eq_coe_induce_top]
    exact hC.2 ({c} : Set C.Target) (by simp)
  have hpre : (C.PreimageSubgraph H).coe.Connected :=
    GraphContraction.preimageSubgraph_connected hH
  have hverts : (C.PreimageSubgraph H).verts = ({z} : Set V)ᶜ := by
    ext a
    change C.map a ≠ C.map z ↔ a ≠ z
    apply not_congr
    constructor
    · intro hmap
      rcases
          (GraphContraction.collapseEdge_map_eq_iff
            (G := G) hvw (v := a) (w := z)).mp (by simpa [C] using hmap) with
        hpair | hout
      · have hzpair : z = v ∨ z = w := by simpa using hpair.2
        exact False.elim (hzpair.elim hzv hzw)
      · exact hout.1
    · intro haz
      subst a
      rfl
  let φ : (C.PreimageSubgraph H).coe ≃g G.induce ({z} : Set V)ᶜ := {
    toEquiv := {
      toFun := fun a => ⟨a.1, by rw [← hverts]; exact a.2⟩
      invFun := fun a => ⟨a.1, by rw [hverts]; exact a.2⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl
    }
    map_rel_iff' := by
      intro a b
      change G.Adj a.1 b.1 ↔ (C.PreimageSubgraph H).Adj a.1 b.1
      constructor
      · intro hab
        have haH : C.map a.1 ∈ H.verts := a.2
        have hbH : C.map b.1 ∈ H.verts := b.2
        refine ⟨hab, a.2, b.2, ?_⟩
        rcases C.map_adj hab with hsame | hadj
        · exact Or.inl hsame
        · exact Or.inr ⟨haH, hbH, hadj⟩
      · exact fun hab => hab.1
  }
  exact φ.connected_iff.mp hpre

theorem connected_induce_compl_singleton_of_pair_core
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {x y r : V}
    (hxy : x ≠ y)
    (hrx : r ≠ x)
    (hry : r ≠ y)
    (hyr : G.Adj y r)
    (hcore : (G.induce ({x, y} : Set V)ᶜ).Connected) :
    (G.induce ({x} : Set V)ᶜ).Connected := by
  classical
  let Core : Set V := ({x, y} : Set V)ᶜ
  let Del : Set V := ({x} : Set V)ᶜ
  let f : (G.induce Core) →g (G.induce Del) := {
    toFun := fun z => ⟨z.1, by
      change z.1 ≠ x
      exact fun h => z.2 (by simp [h])⟩
    map_rel' := by intro a b hab; exact hab
  }
  let rCore : Core := ⟨r, by
    dsimp [Core]
    simp [hrx, hry]⟩
  let rDel : Del := f rCore
  let yDel : Del := ⟨y, by
    dsimp [Del]
    simp [hxy.symm]⟩
  have hyrDel : (G.induce Del).Adj yDel rDel := by
    exact hyr
  refine { preconnected := ?_, nonempty := ⟨yDel⟩ }
  intro a b
  by_cases hay : (a : V) = y
  · have ha : a = yDel := Subtype.ext hay
    subst a
    by_cases hby : (b : V) = y
    · have hb : b = yDel := by
        apply Subtype.ext
        exact hby
      exact hb.symm ▸ SimpleGraph.Reachable.rfl
    · have hbx : (b : V) ≠ x := by
        exact b.2
      let bCore : Core := ⟨b.1, by
        simp [Core, hbx, hby]⟩
      have hrb : (G.induce Core).Reachable rCore bCore := hcore rCore bCore
      exact hyrDel.reachable.trans (hrb.map f)
  · have hax : (a : V) ≠ x := by
      exact a.2
    let aCore : Core := ⟨a.1, by
      simp [Core, hax, hay]⟩
    by_cases hby : (b : V) = y
    · have habCore : (G.induce Core).Reachable aCore rCore := hcore aCore rCore
      have hb : b = yDel := Subtype.ext hby
      subst b
      exact (habCore.map f).trans hyrDel.reachable.symm
    · have hbx : (b : V) ≠ x := by
        exact b.2
      let bCore : Core := ⟨b.1, by
        simp [Core, hbx, hby]⟩
      exact (hcore aCore bCore).map f

/-- Uncontract a degree-two vertex inside a two-connected graph.  The two
displayed core edges are the exact local data needed to keep each endpoint
attached after deleting the other; subdivision carriers provide them
canonically. -/
theorem IsTwoConnected.of_collapseEdge_of_degree_two_core
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    {v w u r : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (huw : u ≠ w)
    (hwr : G.Adj w r)
    (hrv : r ≠ v)
    (hrw : r ≠ w)
    (hC : IsTwoConnected
      (GraphContraction.collapseEdge G hvw).graph) :
    IsTwoConnected G := by
  classical
  have hcard : 2 < Nat.card V := by
    have hlt := GraphContraction.collapseEdge_target_card_lt G hvw
    have hCcard : 2 < Fintype.card
        (GraphContraction.collapseEdge G hvw).Target := by
      simpa [Nat.card_eq_fintype_card] using hC.1
    simpa [Nat.card_eq_fintype_card] using
      (show 2 < Fintype.card V by omega)
  have hcore : (G.induce ({v, w} : Set V)ᶜ).Connected :=
    collapseEdge_induce_compl_pair_connected_of_isTwoConnected hvw hC
  have hdelv : (G.induce ({v} : Set V)ᶜ).Connected :=
    connected_induce_compl_singleton_of_pair_core
      hvw.ne hrv hrw hwr hcore
  have hdelw : (G.induce ({w} : Set V)ᶜ).Connected :=
    connected_induce_compl_singleton_of_pair_core
      hvw.ne' huw hvu.ne' hvu (by
        have hpairs : ({w, v} : Set V) = {v, w} := by
          ext z
          simp [or_comm]
        rw [hpairs]
        exact hcore)
  have hconn : G.Connected :=
    connected_of_induce_compl_singleton_connected_of_adj hvu hdelv
  refine ⟨hcard, ?_⟩
  intro S hS
  have hSle : S.ncard ≤ 1 := by omega
  rcases (Set.ncard_le_one_iff_eq (s := S)).mp hSle with rfl | ⟨z, rfl⟩
  · have hempty : ((∅ : Set V)ᶜ) = Set.univ := by ext z; simp
    rw [hempty]
    exact connected_induce_univ_of_connected (G := G) hconn
  · by_cases hzv : z = v
    · subst z
      exact hdelv
    · by_cases hzw : z = w
      · subst z
        exact hdelw
      · exact
          collapseEdge_induce_compl_singleton_connected_of_isTwoConnected
            hvw hzv hzw hC

/-- Suppressing a degree-two endpoint is graph-isomorphic to its edge
contraction.  If the two surviving neighbours were already adjacent, the
displayed supremum simply contains that edge twice. -/
noncomputable def suppressionGraphIsoCollapse
    {V : Type u} {G : SimpleGraph V}
    {v w u : V}
    (hvw : G.Adj v w)
    (hvu : G.Adj v u)
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hneigh : forall z : V, G.Adj v z -> z = w ∨ z = u) :
    suppressionGraph G v ⟨w, hvw.ne'⟩ ⟨u, huv⟩ ≃g
      (GraphContraction.collapseEdge G hvw).graph where
  toEquiv :=
    Equiv.ofBijective
      (GraphContraction.collapseEdgeDeleteLeftHom G hvw)
      ⟨GraphContraction.collapseEdgeDeleteLeftHom_injective G hvw, by
        intro y
        change
          Option
            {z : V //
              z ∉ ((⊤ : G.Subgraph).induce ({v, w} : Set V)).verts} at y
        cases y with
        | none =>
            refine ⟨⟨w, hvw.ne'⟩, ?_⟩
            change (GraphContraction.collapseEdge G hvw).map w =
              (none : (GraphContraction.collapseEdge G hvw).Target)
            simp [GraphContraction.collapseEdge, GraphContraction.ofMap,
              GraphContraction.collapseSubgraph]
        | some z =>
            have hz_not_pair : (z : V) ∉ ({v, w} : Set V) := by
              simpa using z.2
            refine ⟨⟨z, ?_⟩, ?_⟩
            · intro hzv
              exact hz_not_pair (by simp [hzv])
            · change (GraphContraction.collapseEdge G hvw).map (z : V) =
                (some z : (GraphContraction.collapseEdge G hvw).Target)
              simp [GraphContraction.collapseEdge, GraphContraction.ofMap,
                GraphContraction.collapseSubgraph, hz_not_pair]⟩
  map_rel_iff' := by
    intro x y
    let C := GraphContraction.collapseEdge G hvw
    change
      C.graph.Adj (C.map (x : V)) (C.map (y : V)) ↔
        (suppressionGraph G v ⟨w, hvw.ne'⟩ ⟨u, huv⟩).Adj x y
    constructor
    · intro hxy
      rcases C.edge_lift hxy with ⟨a, b, ha, hb, hab⟩
      rcases collapseEdge_preimage_survivor hvw x ha with hax | ⟨hav, hxw⟩
      · rcases collapseEdge_preimage_survivor hvw y hb with hby | ⟨hbv, hyw⟩
        · exact (SimpleGraph.sup_adj _ _ x y).mpr (Or.inl (by
            simpa [hax, hby] using hab))
        · have hxa : (x : V) = u := by
            rcases hneigh (x : V) (by simpa [hax, hbv] using hab.symm) with hxw' | hxu
            · exact False.elim (hxy.ne (by simp [C, hxw', hyw]))
            · exact hxu
          have hx_u : x = (⟨u, huv⟩ : {z : V // z ≠ v}) :=
            Subtype.ext hxa
          have hy_w : y = (⟨w, hvw.ne'⟩ : {z : V // z ≠ v}) :=
            Subtype.ext hyw
          exact (SimpleGraph.sup_adj _ _ x y).mpr (Or.inr
            ((SimpleGraph.edge_adj ⟨w, hvw.ne'⟩ ⟨u, huv⟩ x y).mpr
              ⟨Or.inr ⟨hx_u, hy_w⟩,
              fun h => hxy.ne (congrArg
                (fun z : {z : V // z ≠ v} => C.map (z : V)) h)⟩))
      · rcases collapseEdge_preimage_survivor hvw y hb with hby | ⟨hbv, hyw⟩
        · have hyu : (y : V) = u := by
            rcases hneigh (y : V) (by simpa [hav, hby] using hab) with hyw' | hyu
            · exact False.elim (hxy.ne (by simp [C, hxw, hyw']))
            · exact hyu
          have hx_w : x = (⟨w, hvw.ne'⟩ : {z : V // z ≠ v}) :=
            Subtype.ext hxw
          have hy_u : y = (⟨u, huv⟩ : {z : V // z ≠ v}) :=
            Subtype.ext hyu
          exact (SimpleGraph.sup_adj _ _ x y).mpr (Or.inr
            ((SimpleGraph.edge_adj ⟨w, hvw.ne'⟩ ⟨u, huv⟩ x y).mpr
              ⟨Or.inl ⟨hx_w, hy_u⟩,
              fun h => hxy.ne (congrArg
                (fun z : {z : V // z ≠ v} => C.map (z : V)) h)⟩))
        · exact False.elim (hxy.ne (by simp [C, hxw, hyw]))
    · intro hxy
      rcases (SimpleGraph.sup_adj _ _ x y).mp hxy with hxyG | hxyEdge
      · exact (GraphContraction.collapseEdgeDeleteLeftHom G hvw).map_rel' hxyG
      · have hcases :
            ((x : V) = w ∧ (y : V) = u) ∨
              ((x : V) = u ∧ (y : V) = w) := by
          rcases
              (SimpleGraph.edge_adj ⟨w, hvw.ne'⟩ ⟨u, huv⟩ x y).mp hxyEdge with
            ⟨hends, _hne⟩
          rcases hends with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact Or.inl ⟨congrArg Subtype.val hx, congrArg Subtype.val hy⟩
          · exact Or.inr ⟨congrArg Subtype.val hx, congrArg Subtype.val hy⟩
        have hmap_ne : C.map v ≠ C.map u := by
          intro hmap
          rcases
              (GraphContraction.collapseEdge_map_eq_iff
                (G := G) hvw (v := v) (w := u)).mp hmap with
            hpair | hout
          · have hu_pair : u = v ∨ u = w := by simpa using hpair.2
            exact hu_pair.elim huv huw
          · exact huv hout.1.symm
        have hadj : C.graph.Adj (C.map v) (C.map u) :=
          (C.map_adj hvu).resolve_left hmap_ne
        have hmap_vw : C.map v = C.map w := by
          apply (GraphContraction.collapseEdge_map_eq_iff
            (G := G) hvw (v := v) (w := w)).mpr
          exact Or.inl ⟨by simp, by simp⟩
        have hadj_wu : C.graph.Adj (C.map w) (C.map u) := by
          rw [← hmap_vw]
          exact hadj
        rcases hcases with ⟨hxw, hyu⟩ | ⟨hxu, hyw⟩
        · simpa [hxw, hyu] using hadj_wu
        · simpa [hxu, hyw] using hadj_wu.symm


end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
