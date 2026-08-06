import Schematic.Math.GraphTheory.Contractions.Definitions

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GraphContraction

variable {G : SimpleGraph V}

/-- A set induced from the top subgraph is connected when one of its vertices
is adjacent to every other vertex.  Pair and triple contraction connectivity
are small specializations of this star-shaped criterion. -/
theorem connected_top_induce_of_forall_eq_or_adj
    (s : Set V) {c : V} (hc : c ∈ s)
    (hstar : ∀ x ∈ s, x = c ∨ G.Adj c x) :
    ((⊤ : G.Subgraph).induce s).coe.Connected := by
  let H : G.Subgraph := (⊤ : G.Subgraph).induce s
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨c, hc⟩, ?_⟩
  intro x
  rcases hstar x x.2 with hxc | hcx
  · have hx_eq : x = ⟨c, hc⟩ := Subtype.ext hxc
    subst x
    exact Reachable.rfl
  · apply Adj.reachable
    change H.Adj c (x : V)
    simpa [H, hc] using hcx

/-- Transport a property of a connected subgraph across subgraph equality.
The connectivity witness is proof-irrelevant, so clients need not manually
construct dependent equality recursors. -/
theorem connectedSubgraphProperty_congr
    (P : ∀ K : G.Subgraph, K.coe.Connected → Prop)
    {K K' : G.Subgraph}
    {hK : K.coe.Connected} {hK' : K'.coe.Connected}
    (hKK' : K = K') (hP : P K hK) :
    P K' hK' := by
  have hPall : ∀ h : K.coe.Connected, P K h := by
    intro h
    simpa only [Subsingleton.elim h hK] using hP
  exact Eq.ndrec (motive := fun J =>
    ∀ h : J.coe.Connected, P J h) hPall hKK' hK'

def Fiber (C : GraphContraction G) (y : C.Target) : Set V :=
  {v : V | C.map v = y}

def ContractsSubgraph (C : GraphContraction G) (H : G.Subgraph) : Prop :=
  Exists fun y : C.Target => H.verts = C.Fiber y

def ContractsEdgeSet (C : GraphContraction G) (E : Set (Sym2 V)) : Prop :=
  forall {v w : V}, s(v, w) ∈ E -> C.map v = C.map w

def ContractsConnectedSubgraph (C : GraphContraction G) (H : G.Subgraph) : Prop :=
  H.coe.Connected ∧ C.ContractsSubgraph H

def OnlyContractsSubgraphTo (C : GraphContraction G) (H : G.Subgraph) (y : C.Target) : Prop :=
  H.verts = C.Fiber y ∧ forall v : V, C.map v ≠ y -> C.Fiber (C.map v) = {v}

def OnlyContractsSubgraph (C : GraphContraction G) (H : G.Subgraph) : Prop :=
  Exists fun y : C.Target => C.OnlyContractsSubgraphTo H y

theorem collapseSubgraph_onlyContractsSubgraphTo
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    (GraphContraction.collapseSubgraph G H hH_connected).OnlyContractsSubgraphTo
      H (none : (GraphContraction.collapseSubgraph G H hH_connected).Target) := by
  classical
  let C := GraphContraction.collapseSubgraph G H hH_connected
  dsimp [OnlyContractsSubgraphTo]
  constructor
  · ext v
    constructor
    · intro hv
      simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap, Fiber, hv]
    · intro hv
      by_cases hvH : v ∈ H.verts
      · exact hvH
      · simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap, Fiber, hvH] at hv
  · intro v hv_ne
    have hvH : v ∉ H.verts := by
      intro hvH
      exact hv_ne (by
        simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap, hvH])
    ext w
    constructor
    · intro hw
      have hwH : w ∉ H.verts := by
        intro hwH
        simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap,
          Fiber, hwH, hvH] at hw
      have hsome :
          some (⟨w, hwH⟩ : {v : V // v ∉ H.verts}) =
            some (⟨v, hvH⟩ : {v : V // v ∉ H.verts}) := by
        simpa [GraphContraction.collapseSubgraph, GraphContraction.ofMap,
          Fiber, hwH, hvH] using hw
      injection hsome with hsub
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hsub)
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      exact rfl

theorem collapseSubgraph_map_eq_none_of_mem
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {v : V}
    (hv : v ∈ H.verts) :
    (GraphContraction.collapseSubgraph G H hH_connected).map v =
      (none : (GraphContraction.collapseSubgraph G H hH_connected).Target) := by
  classical
  simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap, hv]

theorem collapseSubgraph_map_eq_some_of_not_mem
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {v : V}
    (hv : v ∉ H.verts) :
    (GraphContraction.collapseSubgraph G H hH_connected).map v =
      some (⟨v, hv⟩ :
        {v : V // v ∉ H.verts}) := by
  classical
  simp [GraphContraction.collapseSubgraph, GraphContraction.ofMap, hv]

theorem collapseSubgraph_map_eq_iff
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {v w : V} :
    (GraphContraction.collapseSubgraph G H hH_connected).map v =
        (GraphContraction.collapseSubgraph G H hH_connected).map w ↔
      (v ∈ H.verts ∧ w ∈ H.verts) ∨
        (v = w ∧ v ∉ H.verts ∧ w ∉ H.verts) := by
  classical
  by_cases hv : v ∈ H.verts
  · by_cases hw : w ∈ H.verts
    · constructor
      · intro _h
        exact Or.inl ⟨hv, hw⟩
      · intro _h
        rw [collapseSubgraph_map_eq_none_of_mem G H hH_connected hv,
          collapseSubgraph_map_eq_none_of_mem G H hH_connected hw]
    · constructor
      · intro hmap
        rw [collapseSubgraph_map_eq_none_of_mem G H hH_connected hv,
          collapseSubgraph_map_eq_some_of_not_mem G H hH_connected hw] at hmap
        simp at hmap
      · intro h
        rcases h with hboth | hout
        · exact False.elim (hw hboth.2)
        · exact False.elim (hout.2.1 hv)
  · by_cases hw : w ∈ H.verts
    · constructor
      · intro hmap
        rw [collapseSubgraph_map_eq_some_of_not_mem G H hH_connected hv,
          collapseSubgraph_map_eq_none_of_mem G H hH_connected hw] at hmap
        simp at hmap
      · intro h
        rcases h with hboth | hout
        · exact False.elim (hv hboth.1)
        · exact False.elim (hout.2.2 hw)
    · constructor
      · intro hmap
        have hsome :
            some (⟨v, hv⟩ : {v : V // v ∉ H.verts}) =
              some (⟨w, hw⟩ : {v : V // v ∉ H.verts}) := by
          rw [collapseSubgraph_map_eq_some_of_not_mem G H hH_connected hv,
            collapseSubgraph_map_eq_some_of_not_mem G H hH_connected hw] at hmap
          exact hmap
        injection hsome with hsub
        exact Or.inr ⟨congrArg Subtype.val hsub, hv, hw⟩
      · intro h
        rcases h with hboth | hout
        · exact False.elim (hv hboth.1)
        · rw [hout.1]

/-- Injectivity of a map followed by a connected-subgraph collapse reduces to
injectivity before the collapse and uniqueness among the inputs landing in
the collapsed subgraph.  This is the reusable composition principle behind
successive-collapse arguments. -/
theorem collapseSubgraph_comp_injective
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {B : Type*}
    (f : B → V)
    (hf : Function.Injective f)
    (hcollapsed : ∀ r s : B, f r ∈ H.verts → f s ∈ H.verts → r = s) :
    Function.Injective (fun r : B =>
      (GraphContraction.collapseSubgraph G H hH_connected).map (f r)) := by
  classical
  intro r s hrs
  rcases
      (GraphContraction.collapseSubgraph_map_eq_iff
        G H hH_connected (v := f r) (w := f s)).mp hrs
    with hboth | hout
  · exact hcollapsed r s hboth.1 hboth.2
  · exact hf hout.1

/-- After collapsing a connected subgraph, the quotient induced away from the
new collapsed vertex embeds back into the original graph.  This is the formal
version of the obvious part of the source proof's uncontraction step: quotient
models that do not use the contracted vertex are already models in `G`. -/
noncomputable def collapseSubgraphOutsideEmbedding
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    ((GraphContraction.collapseSubgraph G H hH_connected).graph.induce
      {y : (GraphContraction.collapseSubgraph G H hH_connected).Target |
        y ≠ none}) →g G where
  toFun
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some v, _hnotnone⟩ => (v : V)
  map_rel' := by
    classical
    intro y z hyz
    cases y with
    | mk yval hyout =>
      cases yval with
      | none =>
          exact False.elim (hyout rfl)
      | some yv =>
        cases z with
        | mk zval hzout =>
          cases zval with
          | none =>
              exact False.elim (hzout rfl)
          | some zv =>
            change (GraphContraction.collapseSubgraph G H hH_connected).graph.Adj
              (some yv) (some zv) at hyz
            rcases hyz with ⟨_hne, a, b, ha, hb, hab⟩
            have ha_eq : a = (yv : V) := by
              by_cases haH : a ∈ H.verts
              · simp [haH] at ha
              · have hsome :
                    some (⟨a, haH⟩ : {v : V // v ∉ H.verts}) = some yv := by
                  simpa [GraphContraction.collapseSubgraph,
                    GraphContraction.ofMap, haH] using ha
                exact congrArg Subtype.val (Option.some.inj hsome)
            have hb_eq : b = (zv : V) := by
              by_cases hbH : b ∈ H.verts
              · simp [hbH] at hb
              · have hsome :
                    some (⟨b, hbH⟩ : {v : V // v ∉ H.verts}) = some zv := by
                  simpa [GraphContraction.collapseSubgraph,
                    GraphContraction.ofMap, hbH] using hb
                exact congrArg Subtype.val (Option.some.inj hsome)
            simpa [ha_eq, hb_eq] using hab

theorem collapseSubgraphOutsideEmbedding_injective
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    Function.Injective
      (GraphContraction.collapseSubgraphOutsideEmbedding G H hH_connected) := by
  classical
  intro y z hyz
  cases y with
  | mk yval hyout =>
    cases yval with
    | none =>
        exact False.elim (hyout rfl)
    | some yv =>
      cases z with
      | mk zval hzout =>
        cases zval with
        | none =>
            exact False.elim (hzout rfl)
        | some zv =>
            apply Subtype.ext
            exact congrArg some (Subtype.ext hyz)

/-- Lift a quotient walk whose support avoids the collapsed vertex back to the
original graph. -/
noncomputable def collapseSubgraphOutsideWalk
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {y z : (GraphContraction.collapseSubgraph G H hH_connected).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseSubgraph G H hH_connected).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support -> t ≠ none) :
    G.Walk
      (GraphContraction.collapseSubgraphOutsideEmbedding
        G H hH_connected ⟨y, hy⟩)
      (GraphContraction.collapseSubgraphOutsideEmbedding
        G H hH_connected ⟨z, hz⟩) := by
  let S : Set (GraphContraction.collapseSubgraph G H hH_connected).Target :=
    {t | t ≠ none}
  let pS :
      ((GraphContraction.collapseSubgraph G H hH_connected).graph.induce S).Walk
        ⟨y, hpavoid y p.start_mem_support⟩
        ⟨z, hpavoid z p.end_mem_support⟩ :=
    p.induce S hpavoid
  exact
    (pS.map
      (GraphContraction.collapseSubgraphOutsideEmbedding G H hH_connected)).copy
      (by
        apply congrArg
        exact Subtype.ext rfl)
      (by
        apply congrArg
        exact Subtype.ext rfl)

theorem collapseSubgraphOutsideWalk_isPath
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {y z : (GraphContraction.collapseSubgraph G H hH_connected).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseSubgraph G H hH_connected).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support -> t ≠ none)
    (hp : p.IsPath) :
    (GraphContraction.collapseSubgraphOutsideWalk
      G H hH_connected hy hz p hpavoid).IsPath := by
  classical
  let S : Set (GraphContraction.collapseSubgraph G H hH_connected).Target :=
    {t | t ≠ none}
  let pS :
      ((GraphContraction.collapseSubgraph G H hH_connected).graph.induce S).Walk
        ⟨y, hpavoid y p.start_mem_support⟩
        ⟨z, hpavoid z p.end_mem_support⟩ :=
    p.induce S hpavoid
  have hpS : pS.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map
      (f :=
        (SimpleGraph.Embedding.induce
          (G := (GraphContraction.collapseSubgraph G H hH_connected).graph)
          S).toHom)
    simpa [pS] using hp
  have hmap :
      (pS.map
        (GraphContraction.collapseSubgraphOutsideEmbedding
          G H hH_connected)).IsPath :=
    Walk.map_isPath_of_injective
      (GraphContraction.collapseSubgraphOutsideEmbedding_injective
        G H hH_connected)
      hpS
  simpa [GraphContraction.collapseSubgraphOutsideWalk, S, pS] using
    (SimpleGraph.Walk.isPath_copy
      (pS.map
        (GraphContraction.collapseSubgraphOutsideEmbedding G H hH_connected))
      (by
        apply congrArg
        exact Subtype.ext rfl)
      (by
        apply congrArg
        exact Subtype.ext rfl)).mpr hmap

theorem collapseSubgraphOutsideWalk_support_reflects
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {y z : (GraphContraction.collapseSubgraph G H hH_connected).Target}
    (hy : y ≠ none)
    (hz : z ≠ none)
    (p : (GraphContraction.collapseSubgraph G H hH_connected).graph.Walk y z)
    (hpavoid : forall t, t ∈ p.support -> t ≠ none)
    {t : V}
    (ht :
      t ∈
        (GraphContraction.collapseSubgraphOutsideWalk
          G H hH_connected hy hz p hpavoid).support) :
    Exists fun qv :
        (GraphContraction.collapseSubgraph G H hH_connected).Target =>
      Exists fun _ : qv ∈ p.support =>
        Exists fun hqv_ne : qv ≠ none =>
          GraphContraction.collapseSubgraphOutsideEmbedding
              G H hH_connected ⟨qv, hqv_ne⟩ = t := by
  classical
  let C : GraphContraction G :=
    GraphContraction.collapseSubgraph G H hH_connected
  let S : Set C.Target := {qv | qv ≠ none}
  let pS : (C.graph.induce S).Walk
      ⟨y, hpavoid y p.start_mem_support⟩
      ⟨z, hpavoid z p.end_mem_support⟩ :=
    p.induce S hpavoid
  have ht' :
      t ∈
        (pS.map
          (GraphContraction.collapseSubgraphOutsideEmbedding
            G H hH_connected)).support := by
    simpa [GraphContraction.collapseSubgraphOutsideWalk, C, S, pS] using ht
  rw [SimpleGraph.Walk.support_map] at ht'
  rcases List.mem_map.mp ht' with ⟨qvS, hqvS, hqv_eq⟩
  refine ⟨(qvS : C.Target), ?_, qvS.2, ?_⟩
  · exact Walk.mem_support_of_mem_induce_support p hpavoid hqvS
  · exact hqv_eq

theorem collapseSubgraph_none_mem_support_iff
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    (none : (GraphContraction.collapseSubgraph G H hH_connected).Target) ∈
        (GraphContraction.collapseSubgraph G H hH_connected).graph.support ↔
      Exists fun u : V =>
        Exists fun v : V => u ∈ H.verts ∧ v ∉ H.verts ∧ G.Adj u v := by
  classical
  constructor
  · intro hsupport
    change Exists fun y : Option {v : V // v ∉ H.verts} =>
      (GraphContraction.collapseSubgraph G H hH_connected).graph.Adj none y at hsupport
    rcases hsupport with ⟨y, hnone_y⟩
    cases hy : y with
    | none =>
        simp [hy] at hnone_y
    | some yv =>
        rcases hnone_y with ⟨_hne, a, b, ha, hb, hab⟩
        have haH : a ∈ H.verts := by
          by_contra haH
          simp [haH] at ha
        have hb_not_H : b ∉ H.verts := by
          by_contra hbH
          rw [hy] at hb
          simp [hbH] at hb
        exact ⟨a, b, haH, hb_not_H, hab⟩
  · rintro ⟨u, v, huH, hvH, huv⟩
    change Exists fun y : Option {v : V // v ∉ H.verts} =>
      (GraphContraction.collapseSubgraph G H hH_connected).graph.Adj none y
    refine ⟨some (⟨v, hvH⟩ : {v : V // v ∉ H.verts}), ?_⟩
    refine ⟨by simp, u, v, ?_, ?_, huv⟩
    · exact GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected huH
    · exact GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
        G H hH_connected hvH

noncomputable instance collapseSubgraphTargetFintype
    [Fintype V]
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    Fintype (GraphContraction.collapseSubgraph G H hH_connected).Target := by
  classical
  dsimp [GraphContraction.collapseSubgraph, GraphContraction.ofMap]
  infer_instance

theorem collapseSubgraph_target_card_lt
    [Fintype V]
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {a b : V}
    (haH : a ∈ H.verts)
    (hbH : b ∈ H.verts)
    (hab : a ≠ b) :
    Fintype.card (GraphContraction.collapseSubgraph G H hH_connected).Target <
      Fintype.card V := by
  classical
  let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
  let embedTarget : C.Target -> V
    | none => a
    | some x => x
  have hinj : Function.Injective embedTarget := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            have hy_eq : (y : V) = a := by
              simpa [embedTarget] using hxy.symm
            exact False.elim (y.2 (by simpa [hy_eq] using haH))
    | some x =>
        cases y with
        | none =>
            have hx_eq : (x : V) = a := by
              simpa [embedTarget] using hxy
            exact False.elim (x.2 (by simpa [hx_eq] using haH))
        | some y =>
            have hxy_val : (x : V) = y := by
              simpa [embedTarget] using hxy
            exact congrArg some (Subtype.ext hxy_val)
  have hnot_mem : b ∉ Set.range embedTarget := by
    rintro ⟨x, hx⟩
    cases x with
    | none =>
        exact hab (by simpa [embedTarget] using hx)
    | some x =>
        have hx_eq : (x : V) = b := by
          simpa [embedTarget] using hx
        exact x.2 (by simpa [hx_eq] using hbH)
  exact Fintype.card_lt_of_injective_of_notMem
    (b := b) embedTarget hinj hnot_mem

theorem collapseSubgraph_onlyContractsSubgraph
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    (GraphContraction.collapseSubgraph G H hH_connected).OnlyContractsSubgraph H := by
  exact ⟨none, collapseSubgraph_onlyContractsSubgraphTo G H hH_connected⟩

theorem collapseSubgraph_contractsConnectedSubgraph
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    (GraphContraction.collapseSubgraph G H hH_connected).ContractsConnectedSubgraph H := by
  refine ⟨hH_connected, ?_⟩
  exact ⟨none, (collapseSubgraph_onlyContractsSubgraphTo G H hH_connected).1⟩

theorem target_colorable_of_colorable_of_injective
    {c : Nat}
    (C : GraphContraction G)
    (hinj : Function.Injective C.map)
    (hcolor : G.Colorable c) :
    C.graph.Colorable c := by
  classical
  rcases hcolor with ⟨col⟩
  let rep : C.Target -> V := fun y => Classical.choose (C.surjective y)
  have hrep : forall y : C.Target, C.map (rep y) = y := fun y =>
    Classical.choose_spec (C.surjective y)
  refine ⟨Coloring.mk (fun y => col (rep y)) ?_⟩
  intro y z hyz hsame
  obtain ⟨v, w, hv, hw, hvw⟩ := C.edge_lift hyz
  have hrep_y : rep y = v := hinj ((hrep y).trans hv.symm)
  have hrep_z : rep z = w := hinj ((hrep z).trans hw.symm)
  exact col.valid hvw (by simpa [hrep_y, hrep_z] using hsame)

def ImageOfSet (C : GraphContraction G) (s : Set V) : Set C.Target :=
  C.map '' s

def PreimageSubgraph (C : GraphContraction G) (H : C.graph.Subgraph) : G.Subgraph where
  verts := C.map ⁻¹' H.verts
  Adj v w :=
    G.Adj v w ∧
      C.map v ∈ H.verts ∧
      C.map w ∈ H.verts ∧
      (C.map v = C.map w ∨ H.Adj (C.map v) (C.map w))
  adj_sub h := h.1
  edge_vert h := h.2.1
  symm := by
    intro v w h
    exact ⟨h.1.symm, h.2.2.1, h.2.1, by
      rcases h.2.2.2 with hsame | hadj
      · exact Or.inl hsame.symm
      · exact Or.inr (H.symm hadj)⟩

theorem fiber_nonempty (C : GraphContraction G) (y : C.Target) :
    (C.Fiber y).Nonempty := by
  obtain ⟨v, hv⟩ := C.surjective y
  exact ⟨v, hv⟩

theorem connected_induce_fiber (C : GraphContraction G) (y : C.Target) :
    (G.induce (C.Fiber y)).Connected := by
  simpa [Fiber] using C.connected_fiber y

theorem map_mem_imageOfSet {C : GraphContraction G} {s : Set V} {v : V}
    (hv : v ∈ s) :
    C.map v ∈ C.ImageOfSet s := by
  exact ⟨v, hv, rfl⟩

theorem mem_imageOfSet_iff {C : GraphContraction G} {s : Set V} {y : C.Target} :
    y ∈ C.ImageOfSet s ↔ Exists fun v : V => v ∈ s ∧ C.map v = y := by
  rfl

theorem eq_of_onlyContractsSubgraphTo_of_map_eq
    {C : GraphContraction G} {H : G.Subgraph} {y : C.Target}
    (hC : C.OnlyContractsSubgraphTo H y)
    {v w : V}
    (hv : C.map v ≠ y)
    (hw : C.map w = C.map v) :
    w = v := by
  have hw_fiber : w ∈ C.Fiber (C.map v) := hw
  have hsingle := hC.2 v hv
  simpa [Fiber] using (by
    have := congrArg (fun s : Set V => w ∈ s) hsingle
    simpa [hw_fiber] using this)

theorem mem_preimageSubgraph_verts {C : GraphContraction G} {H : C.graph.Subgraph} {v : V} :
    v ∈ (C.PreimageSubgraph H).verts ↔ C.map v ∈ H.verts := by
  rfl

theorem preimageSubgraph_adj_of_same_fiber
    {C : GraphContraction G} {H : C.graph.Subgraph} {v w : V}
    (hvw : G.Adj v w)
    (hv : C.map v ∈ H.verts)
    (hsame : C.map v = C.map w) :
    (C.PreimageSubgraph H).Adj v w := by
  exact ⟨hvw, hv, by simpa [hsame.symm] using hv, Or.inl hsame⟩

theorem preimageSubgraph_adj_of_quotient_edge
    {C : GraphContraction G} {H : C.graph.Subgraph} {v w : V}
    (hvw : G.Adj v w)
    (hvwH : H.Adj (C.map v) (C.map w)) :
    (C.PreimageSubgraph H).Adj v w := by
  exact ⟨hvw, H.edge_vert hvwH, H.edge_vert hvwH.symm, Or.inr hvwH⟩

def fiberToPreimageSubgraph
    (C : GraphContraction G) {H : C.graph.Subgraph} {y : C.Target}
    (hy : y ∈ H.verts) :
    (G.induce (C.Fiber y)) →g (C.PreimageSubgraph H).coe where
  toFun v := ⟨v, by
    rw [mem_preimageSubgraph_verts, v.2]
    exact hy⟩
  map_rel' := by
    intro v w hvw
    show (C.PreimageSubgraph H).Adj v w
    exact preimageSubgraph_adj_of_same_fiber hvw (by
      rw [v.2]
      exact hy) (by
      simpa [Fiber] using v.2.trans w.2.symm)

theorem fiber_reachable_in_preimageSubgraph
    {C : GraphContraction G} {H : C.graph.Subgraph} {y : C.Target}
    (hy : y ∈ H.verts)
    {v w : V}
    (hv : C.map v = y)
    (hw : C.map w = y) :
    (C.PreimageSubgraph H).coe.Reachable
      ⟨v, by rw [mem_preimageSubgraph_verts, hv]; exact hy⟩
      ⟨w, by rw [mem_preimageSubgraph_verts, hw]; exact hy⟩ := by
  let v' : (C.Fiber y) := ⟨v, hv⟩
  let w' : (C.Fiber y) := ⟨w, hw⟩
  have hreach : (G.induce (C.Fiber y)).Reachable v' w' :=
    C.connected_fiber y v' w'
  simpa [fiberToPreimageSubgraph, v', w'] using
    hreach.map (fiberToPreimageSubgraph C hy)

theorem preimageSubgraph_reachable_of_quotient_edge
    {C : GraphContraction G} {H : C.graph.Subgraph}
    {y z : C.Target}
    (hyz : H.Adj y z)
    {v w : V}
    (hv : C.map v = y)
    (hw : C.map w = z) :
    (C.PreimageSubgraph H).coe.Reachable
      ⟨v, by rw [mem_preimageSubgraph_verts, hv]; exact H.edge_vert hyz⟩
      ⟨w, by rw [mem_preimageSubgraph_verts, hw]; exact H.edge_vert hyz.symm⟩ := by
  obtain ⟨a, b, ha, hb, hab⟩ := C.edge_lift (H.adj_sub hyz)
  have hv_to_a :
      (C.PreimageSubgraph H).coe.Reachable
        ⟨v, by rw [mem_preimageSubgraph_verts, hv]; exact H.edge_vert hyz⟩
        ⟨a, by rw [mem_preimageSubgraph_verts, ha]; exact H.edge_vert hyz⟩ :=
    fiber_reachable_in_preimageSubgraph (C := C) (H := H) (H.edge_vert hyz) hv ha
  have ha_to_b :
      (C.PreimageSubgraph H).coe.Reachable
        ⟨a, by rw [mem_preimageSubgraph_verts, ha]; exact H.edge_vert hyz⟩
        ⟨b, by rw [mem_preimageSubgraph_verts, hb]; exact H.edge_vert hyz.symm⟩ := by
    have hyz' : H.Adj (C.map a) (C.map b) := by
      simpa [ha, hb] using hyz
    exact SimpleGraph.Adj.reachable (preimageSubgraph_adj_of_quotient_edge hab hyz')
  have hb_to_w :
      (C.PreimageSubgraph H).coe.Reachable
        ⟨b, by rw [mem_preimageSubgraph_verts, hb]; exact H.edge_vert hyz.symm⟩
        ⟨w, by rw [mem_preimageSubgraph_verts, hw]; exact H.edge_vert hyz.symm⟩ :=
    fiber_reachable_in_preimageSubgraph (C := C) (H := H) (H.edge_vert hyz.symm) hb hw
  exact hv_to_a.trans (ha_to_b.trans hb_to_w)

theorem preimageSubgraph_reachable_of_quotient_walk
    {C : GraphContraction G} {H : C.graph.Subgraph} :
    forall {y z : H.verts} (_p : H.coe.Walk y z) {v w : V},
      (hv : C.map v = (y : C.Target)) ->
      (hw : C.map w = (z : C.Target)) ->
      (C.PreimageSubgraph H).coe.Reachable
        ⟨v, by
          rw [mem_preimageSubgraph_verts, hv]
          exact y.2⟩
        ⟨w, by
          rw [mem_preimageSubgraph_verts, hw]
          exact z.2⟩
  | y, _, .nil, v, w, hv, hw =>
      fiber_reachable_in_preimageSubgraph (C := C) (H := H) y.2 hv hw
  | y, z, .cons hyx p, v, w, hv, hw => by
      obtain ⟨x, hx⟩ := C.surjective _
      have hfirst :
          (C.PreimageSubgraph H).coe.Reachable
            ⟨v, by rw [mem_preimageSubgraph_verts, hv]; exact y.2⟩
            ⟨x, by rw [mem_preimageSubgraph_verts, hx]; exact H.edge_vert hyx.symm⟩ :=
        preimageSubgraph_reachable_of_quotient_edge (C := C) (H := H) hyx hv hx
      have hrest :
          (C.PreimageSubgraph H).coe.Reachable
            ⟨x, by rw [mem_preimageSubgraph_verts, hx]; exact H.edge_vert hyx.symm⟩
            ⟨w, by rw [mem_preimageSubgraph_verts, hw]; exact z.2⟩ :=
        preimageSubgraph_reachable_of_quotient_walk (C := C) (H := H) p hx hw
      exact hfirst.trans hrest

theorem preimageSubgraph_connected
    {C : GraphContraction G} {H : C.graph.Subgraph}
    (hH : H.coe.Connected) :
    (C.PreimageSubgraph H).coe.Connected where
  preconnected := by
    intro v w
    let y : H.verts := ⟨C.map v, v.2⟩
    let z : H.verts := ⟨C.map w, w.2⟩
    obtain ⟨p⟩ := hH y z
    simpa [y, z] using
      preimageSubgraph_reachable_of_quotient_walk (C := C) (H := H) p rfl rfl
  nonempty := by
    obtain ⟨y⟩ := hH.nonempty
    obtain ⟨v, hv⟩ := C.surjective (y : C.Target)
    exact ⟨⟨v, by
      rw [mem_preimageSubgraph_verts, hv]
      exact y.2⟩⟩

/-!
MI integration extras: contraction helpers used by the completed rerouting and
main-induction proof.
-/

theorem collapseSubgraph_adj_of_mem_of_adjacent
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected)
    {u v : V}
    (huH : u ∈ H.verts)
    (hv_not_H : v ∉ H.verts)
    (hH_adj_v : Exists fun w : V => w ∈ H.verts ∧ G.Adj w v) :
    let C : GraphContraction G := GraphContraction.collapseSubgraph G H hH_connected
    C.graph.Adj (C.map u) (C.map v) := by
  classical
  intro C
  obtain ⟨w, hwH, hwv⟩ := hH_adj_v
  have hw_map : C.map w = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected hwH
  have hu_map : C.map u = (none : C.Target) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_none_of_mem
        G H hH_connected huH
  have hv_map :
      C.map v = some (⟨v, hv_not_H⟩ : {a : V // a ∉ H.verts}) := by
    simpa [C] using
      GraphContraction.collapseSubgraph_map_eq_some_of_not_mem
        G H hH_connected hv_not_H
  have hne : C.map w ≠ C.map v := by
    rw [hw_map, hv_map]
    simp
  rcases C.map_adj hwv with hsame | hadj
  · exact False.elim (hne hsame)
  · simpa [hu_map, hw_map] using hadj

theorem contractionTargetGraph_colorable_of_same_fibers
    {W Z : Type u}
    (f : V -> W) (g : V -> Z)
    (hsame_fibers : forall a b : V, f a = f b ↔ g a = g b)
    (hcolor : (contractionTargetGraph G g).Colorable 4) :
    (contractionTargetGraph G f).Colorable 4 := by
  classical
  rcases hcolor with ⟨col⟩
  let rep? : W -> Option V := fun y =>
    if h : Exists fun v : V => f v = y then some h.choose else none
  let color : W -> Fin 4 := fun y =>
    match rep? y with
    | some v => col (g v)
    | none => 0
  refine ⟨Coloring.mk color ?_⟩
  intro y z hyz hsame
  rcases hyz with ⟨hyz_ne, a, b, hfa, hfb, hab⟩
  let hy_exists : Exists fun v : V => f v = y := ⟨a, hfa⟩
  let hz_exists : Exists fun v : V => f v = z := ⟨b, hfb⟩
  let ay : V := Classical.choose hy_exists
  let bz : V := Classical.choose hz_exists
  have hay : f ay = y := Classical.choose_spec hy_exists
  have hbz : f bz = z := Classical.choose_spec hz_exists
  have hga : g ay = g a :=
    (hsame_fibers ay a).mp (hay.trans hfa.symm)
  have hgb : g bz = g b :=
    (hsame_fibers bz b).mp (hbz.trans hfb.symm)
  have hneq_g : g a ≠ g b := by
    intro hgab
    exact hyz_ne
      (hfa.symm.trans (((hsame_fibers a b).mpr hgab).trans hfb))
  have hg_adj : (contractionTargetGraph G g).Adj (g a) (g b) :=
    ⟨hneq_g, a, b, rfl, rfl, hab⟩
  have hy_color : color y = col (g a) := by
    have hy_color' : color y = col (g ay) := by
      simp [color, rep?, hy_exists, ay]
    exact hy_color'.trans (by rw [hga])
  have hz_color : color z = col (g b) := by
    have hz_color' : color z = col (g bz) := by
      simp [color, rep?, hz_exists, bz]
    exact hz_color'.trans (by rw [hgb])
  have hsame_ab : col (g a) = col (g b) := by
    exact hy_color.symm.trans (hsame.trans hz_color)
  exact col.valid hg_adj hsame_ab


end GraphContraction

end Schematic.Math.GraphTheory
