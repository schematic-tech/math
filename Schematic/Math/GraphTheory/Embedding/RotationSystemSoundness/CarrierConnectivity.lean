import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.CarrierWalks

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness
/-- A finite two-connected graph has no bridge.  The proof uses a second
neighbour of one endpoint and connectivity after deleting that endpoint. -/
theorem IsTwoConnected.connected_delete_edge
    {W : Type u} [Fintype W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (h2 : IsTwoConnected H)
    {x y : W} (hxy : H.Adj x y) :
    (H.deleteEdges {s(x, y)}).Connected := by
  classical
  apply (h2.connected (by decide)).connected_delete_edge_of_not_isBridge
  intro hbridge
  have hall : forall p : H.Walk x y, s(x, y) ∈ p.edges :=
    (SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges.mp hbridge).2
  have hdegree : 2 ≤ H.degree x := h2.degree_atLeast x
  have hneighbors : 1 < (H.neighborSet x).ncard := by
    rw [← Set.fintypeCard_eq_ncard,
      SimpleGraph.card_neighborSet_eq_degree]
    exact hdegree
  obtain ⟨r, hr, hry⟩ :=
    (H.neighborSet x).exists_ne_of_one_lt_ncard hneighbors y
  let X : Set W := ({x} : Set W)ᶜ
  let rX : X := ⟨r, by
    dsimp [X]
    exact hr.ne'⟩
  let yX : X := ⟨y, by
    dsimp [X]
    exact hxy.ne'⟩
  obtain ⟨p⟩ := h2.2 ({x} : Set W) (by simp) rX yX
  let f : H.induce X →g H :=
    (SimpleGraph.Embedding.induce (G := H) X).toHom
  let pH : H.Walk r y := (p.map f).copy rfl rfl
  let q : H.Walk x y := hr.toWalk.append pH
  have hqedge := hall q
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at hqedge
  rcases hqedge with hfirst | htail
  · have heq : s(x, y) = s(x, r) := by
      simpa [q, SimpleGraph.Adj.toWalk] using hfirst
    have : y = r := by
      rcases (Sym2.eq_iff.mp heq) with hsame | hswap
      · exact hsame.2
      · exact False.elim (hxy.ne hswap.2.symm)
    exact hry this.symm
  · have hxSupport : x ∈ pH.support :=
      pH.fst_mem_support_of_mem_edges htail
    have hxNot : x ∉ pH.support := by
      intro hx
      have hxMap : x ∈ (p.map f).support := by
        simpa [pH] using hx
      rw [SimpleGraph.Walk.support_map] at hxMap
      rcases List.mem_map.mp hxMap with ⟨z, _hz, hzx⟩
      exact z.2 hzx
    exact hxNot hxSupport

theorem Walk.IsPath.exists_walk_to_endpoint_avoiding_other
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {s t a z : V}
    {p : G.Walk s t}
    (hp : p.IsPath)
    (ha : a ∈ p.support)
    (haz : a ≠ z) :
    (Exists fun q : G.Walk a s =>
      q.toSubgraph ≤ p.toSubgraph ∧ z ∉ q.support) ∨
    Exists fun q : G.Walk a t =>
      q.toSubgraph ≤ p.toSubgraph ∧ z ∉ q.support := by
  classical
  by_cases hz : z ∈ p.support
  · rcases Walk.mem_support_takeUntil_or_mem_support_takeUntil
        ha hz with ha_before | hz_before
    · left
      let q : G.Walk a s := (p.takeUntil a ha).reverse
      refine ⟨q, ?_, ?_⟩
      · simpa [q, SimpleGraph.Walk.toSubgraph_reverse] using
          Walk.toSubgraph_takeUntil_le p ha
      · intro hzq
        have hzprefix : z ∈ (p.takeUntil a ha).support := by
          simpa [q, SimpleGraph.Walk.support_reverse] using hzq
        exact
          (SimpleGraph.Walk.notMem_support_takeUntil_support_takeUntil_subset
            haz hz ha_before) hzprefix
    · right
      let q : G.Walk a t := p.dropUntil a ha
      refine ⟨q, Walk.toSubgraph_dropUntil_le p ha, ?_⟩
      intro hzq
      exact Set.disjoint_left.mp
        (Walk.IsPath.punctured_takeUntil_support_disjoint_dropUntil_support
          hp ha)
        ⟨hz_before, haz.symm⟩ (by simpa [q] using hzq)
  · left
    let q : G.Walk a s := (p.takeUntil a ha).reverse
    refine ⟨q, ?_, ?_⟩
    · simpa [q, SimpleGraph.Walk.toSubgraph_reverse] using
        Walk.toSubgraph_takeUntil_le p ha
    · intro hzq
      apply hz
      exact SimpleGraph.Walk.support_takeUntil_subset p ha (by
        simpa [q, SimpleGraph.Walk.support_reverse] using hzq)

/-- Every surviving carrier vertex can be joined, inside the carrier and
without the deleted vertex, to an endpoint branch vertex of one selected
source edge. -/
theorem exists_carrier_walk_to_branchVertex_avoiding
    {W : Type u} {V : Type v}
    [LinearOrder W] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (a z : V)
    (ha : a ∈ (strictSubdivisionCarrierGraph
      (orderedStrictSubdivisionModel M)).support)
    (haz : a ≠ z) :
    Exists fun c : W => Exists fun q :
      (strictSubdivisionCarrierGraph
        (orderedStrictSubdivisionModel M)).Walk a
          ((orderedStrictSubdivisionModel M).branchVertex c) =>
      z ∉ q.support := by
  classical
  let N := orderedStrictSubdivisionModel M
  let C := strictSubdivisionCarrierGraph N
  rw [SimpleGraph.mem_support] at ha
  rcases ha with ⟨b, hab⟩
  rcases (strictSubdivisionCarrierGraph_adj_iff N).mp hab with
    ⟨x, y, hxy, habPath⟩
  have haPath : a ∈ (N.edgePath hxy).support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
    exact (N.edgePath hxy).toSubgraph.edge_vert habPath
  rcases
      Walk.IsPath.exists_walk_to_endpoint_avoiding_other
        (N.edgePath_isPath hxy) haPath haz with
    ⟨q, hqle, hzq⟩ | ⟨q, hqle, hzq⟩
  · refine ⟨x, ?_⟩
    let qC : C.Walk a (N.branchVertex x) :=
      q.transfer C (fun e he =>
        SimpleGraph.edgeSet_mono
          (le_trans
            (SimpleGraph.Subgraph.spanningCoe_le_of_le hqle)
            (edgePath_toSubgraph_spanningCoe_le_carrier N hxy))
          (by
            change e ∈ q.toSubgraph.edgeSet
            exact q.mem_edges_toSubgraph.mpr he))
    refine ⟨qC, ?_⟩
    dsimp [qC]
    rw [SimpleGraph.Walk.support_transfer]
    exact hzq
  · refine ⟨y, ?_⟩
    let qC : C.Walk a (N.branchVertex y) :=
      q.transfer C (fun e he =>
        SimpleGraph.edgeSet_mono
          (le_trans
            (SimpleGraph.Subgraph.spanningCoe_le_of_le hqle)
            (edgePath_toSubgraph_spanningCoe_le_carrier N hxy))
          (by
            change e ∈ q.toSubgraph.edgeSet
            exact q.mem_edges_toSubgraph.mpr he))
    refine ⟨qC, ?_⟩
    dsimp [qC]
    rw [SimpleGraph.Walk.support_transfer]
    exact hzq

theorem Walk.support_subset_graph_support_of_notNil
    {V : Type u}
    {G : SimpleGraph V}
    {a b : V} {p : G.Walk a b}
    (hp : ¬ p.Nil) :
    {z : V | z ∈ p.support} ⊆ G.support := by
  intro z hz
  rcases
      (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hp).mp hz with
    ⟨e, he, hze⟩
  have heG : e ∈ G.edgeSet := p.edges_subset_edgeSet he
  revert hze heG
  refine Sym2.ind ?_ e
  intro x y hz hxy
  rw [Sym2.mem_iff] at hz
  rw [SimpleGraph.mem_edgeSet] at hxy
  rw [SimpleGraph.mem_support]
  rcases hz with rfl | rfl
  · exact ⟨y, hxy⟩
  · exact ⟨x, hxy.symm⟩

theorem strictSubdivisionLiftWalk_support_subset_carrier_support
    {W : Type u} {V : Type v}
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hsource : forall x : W, Exists fun y : W => H.Adj x y)
    {a b : W} (p : H.Walk a b) :
    {z : V | z ∈
        (strictSubdivisionLiftWalk
          (edgeRestrictStrictSubdivisionCarrier M) p).support} ⊆
      (strictSubdivisionCarrierGraph M).support := by
  intro z hz
  cases p with
  | nil =>
      simp only [strictSubdivisionLiftWalk,
        SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      obtain ⟨y, hay⟩ := hsource a
      exact (edgeRestrictStrictSubdivisionCarrier M).branchVertex_mem_support_of_adj hay
  | cons hab p =>
      exact Walk.support_subset_graph_support_of_notNil
        (p := strictSubdivisionLiftWalk
          (edgeRestrictStrictSubdivisionCarrier M) (.cons hab p))
        (by
          rw [strictSubdivisionLiftWalk, SimpleGraph.Walk.nil_append_iff]
          intro hnil
          have hends := hnil.1.eq
          exact hab.ne
            ((edgeRestrictStrictSubdivisionCarrier M).branchVertex_injective hends))
        hz

/-- Lift a source walk between two chosen branch vertices while avoiding one
forbidden host vertex.  A forbidden branch vertex is handled by deleting its
source vertex; an internal forbidden vertex is handled by deleting its unique
source edge. -/
theorem exists_carrier_walk_between_branchVertices_avoiding
    {W : Type u} {V : Type v}
    [Fintype W] [LinearOrder W]
    [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (h2 : IsTwoConnected H)
    (a b : W) (z : V)
    (haz : (orderedStrictSubdivisionModel M).branchVertex a ≠ z)
    (hbz : (orderedStrictSubdivisionModel M).branchVertex b ≠ z) :
    Exists fun q :
      (strictSubdivisionCarrierGraph
        (orderedStrictSubdivisionModel M)).Walk
          ((orderedStrictSubdivisionModel M).branchVertex a)
          ((orderedStrictSubdivisionModel M).branchVertex b) =>
      z ∉ q.support := by
  classical
  let N := orderedStrictSubdivisionModel M
  let C := strictSubdivisionCarrierGraph N
  let L := edgeRestrictStrictSubdivisionCarrier N
  have hsource : forall x : W, Exists fun y : W => H.Adj x y := by
    intro x
    have hxdegree : 2 ≤ H.degree x := h2.degree_atLeast x
    have hxneighbors : 0 < (H.neighborSet x).ncard := by
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
      omega
    exact (Set.ncard_pos).mp hxneighbors
  by_cases hbranch : Exists fun c : W => z = N.branchVertex c
  · rcases hbranch with ⟨c, rfl⟩
    have hac : a ≠ c := by
      intro h
      subst a
      exact haz rfl
    have hbc : b ≠ c := by
      intro h
      subst b
      exact hbz rfl
    let X : Set W := ({c} : Set W)ᶜ
    let aX : X := ⟨a, by simpa [X] using hac⟩
    let bX : X := ⟨b, by simpa [X] using hbc⟩
    obtain ⟨p⟩ := h2.2 ({c} : Set W) (by simp) aX bX
    let f : H.induce X →g H :=
      (SimpleGraph.Embedding.induce (G := H) X).toHom
    let pH : H.Walk a b := (p.map f).copy rfl rfl
    let q : C.Walk (N.branchVertex a) (N.branchVertex b) :=
      strictSubdivisionLiftWalk L pH
    refine ⟨q, ?_⟩
    intro hcz
    have hcSource : c ∈ pH.support :=
      (branchVertex_mem_strictSubdivisionLiftWalk_support_iff
        L pH).mp (by simpa [q, L, N] using hcz)
    have hcMap : c ∈ (p.map f).support := by
      simpa [pH] using hcSource
    rw [SimpleGraph.Walk.support_map] at hcMap
    rcases List.mem_map.mp hcMap with ⟨d, _hd, hdc⟩
    exact d.2 hdc
  · by_cases hzCarrier : z ∈ C.support
    · rw [SimpleGraph.mem_support] at hzCarrier
      rcases hzCarrier with ⟨w, hzw⟩
      rcases (strictSubdivisionCarrierGraph_adj_iff N).mp hzw with
        ⟨x, y, hxy, hzwPath⟩
      have hzPath : z ∈ (N.edgePath hxy).support := by
        rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
        exact (N.edgePath hxy).toSubgraph.edge_vert hzwPath
      have hzInternal : z ∈ Walk.InternalVertices (N.edgePath hxy) := by
        refine ⟨hzPath, ?_, ?_⟩
        · intro hzx
          exact hbranch ⟨x, hzx⟩
        · intro hzy
          exact hbranch ⟨y, hzy⟩
      have hdeleted :=
        RotationSoundness.IsTwoConnected.connected_delete_edge h2 hxy
      have hreach :
          (H.deleteEdges {s(x, y)}).Reachable a b := hdeleted a b
      rcases
          SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach with
        ⟨p, hpEdge⟩
      let q : C.Walk (N.branchVertex a) (N.branchVertex b) :=
        strictSubdivisionLiftWalk L p
      refine ⟨q, ?_⟩
      intro hzq
      have hzInternalL :
          z ∈ Walk.InternalVertices (L.edgePath hxy) := by
        change z ∈ Walk.InternalVertices
          ((N.edgePath hxy).transfer C _)
        rw [Walk.internalVertices_transfer]
        exact hzInternal
      have hsourceEdge : s(x, y) ∈ p.edges :=
        source_edge_mem_of_internal_mem_strictSubdivisionLiftWalk_support
          L hxy hzInternalL p (by simpa [q] using hzq)
      exact hpEdge hsourceEdge
    · have hconn : H.Connected := h2.connected (by decide)
      obtain ⟨p⟩ := hconn a b
      let q : C.Walk (N.branchVertex a) (N.branchVertex b) :=
        strictSubdivisionLiftWalk L p
      refine ⟨q, ?_⟩
      intro hzq
      exact hzCarrier
        (strictSubdivisionLiftWalk_support_subset_carrier_support
          N hsource p (by simpa [q, L] using hzq))

/-- Deleting one used host vertex from the exact subdivision carrier leaves
the remaining carrier support connected. -/
theorem strictSubdivisionCarrier_delete_connected
    {W : Type u} {V : Type v}
    [Fintype W] [LinearOrder W]
    [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (h2 : IsTwoConnected H)
    (z : V) :
    let C := strictSubdivisionCarrierGraph
      (orderedStrictSubdivisionModel M)
    (C.induce (C.support \ {z})).Connected := by
  classical
  let N := orderedStrictSubdivisionModel M
  let C := strictSubdivisionCarrierGraph N
  let L := edgeRestrictStrictSubdivisionCarrier N
  have hsource : forall x : W, Exists fun y : W => H.Adj x y := by
    intro x
    have hxdegree : 2 ≤ H.degree x := h2.degree_atLeast x
    have hxneighbors : 0 < (H.neighborSet x).ncard := by
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
      omega
    exact (Set.ncard_pos).mp hxneighbors
  have hWpos : 0 < Fintype.card W := by
    have hWcard : 2 < Fintype.card W := by
      simpa [Nat.card_eq_fintype_card] using h2.1
    omega
  letI : Nonempty W := Fintype.card_pos_iff.mp hWpos
  let c : W := Classical.choice inferInstance
  obtain ⟨d, hcd⟩ := hsource c
  have hnonempty : Nonempty ↑(C.support \ {z}) := by
    by_cases hcz : N.branchVertex c = z
    · have hdz : N.branchVertex d ≠ z := by
        intro h
        exact hcd.ne (N.branchVertex_injective (hcz.trans h.symm))
      exact ⟨⟨N.branchVertex d,
        (L.branchVertex_mem_support_of_adj hcd.symm), by simpa using hdz⟩⟩
    · exact ⟨⟨N.branchVertex c,
        (L.branchVertex_mem_support_of_adj hcd), by simpa using hcz⟩⟩
  refine { preconnected := ?_, nonempty := hnonempty }
  intro a b
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  have haz : (a : V) ≠ z := by
    exact a.2.2
  have hbz : (b : V) ≠ z := by
    exact b.2.2
  obtain ⟨ca, qa, hzqa⟩ :=
    exists_carrier_walk_to_branchVertex_avoiding
      M a z a.2.1 haz
  obtain ⟨cb, qb, hzqb⟩ :=
    exists_carrier_walk_to_branchVertex_avoiding
      M b z b.2.1 hbz
  have hcaz : N.branchVertex ca ≠ z := by
    intro h
    apply hzqa
    simpa [N, h] using qa.end_mem_support
  have hcbz : N.branchVertex cb ≠ z := by
    intro h
    apply hzqb
    simpa [N, h] using qb.end_mem_support
  obtain ⟨qm, hzqm⟩ :=
    exists_carrier_walk_between_branchVertices_avoiding
      M h2 ca cb z (by simpa [N] using hcaz) (by simpa [N] using hcbz)
  let q : C.Walk (a : V) (b : V) :=
    qa.append (qm.append qb.reverse)
  have hzq : z ∉ q.support := by
    simp only [q, SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse]
    exact fun h => h.elim hzqa (fun h' => h'.elim hzqm hzqb)
  have hqNotNil : ¬ q.Nil := by
    intro hnil
    exact hab (Subtype.ext hnil.eq)
  have hqSupport : forall w : V, w ∈ q.support ->
      w ∈ C.support \ {z} := by
    intro w hw
    exact ⟨Walk.support_subset_graph_support_of_notNil hqNotNil hw,
      by
        intro hwz
        subst w
        exact hzq hw⟩
  have hreach := Walk.reachable_induce_of_support_subset q hqSupport
  exact hreach

/-- Deleting a vertex after inducing on graph support is the same as inducing
the original graph on its support minus that vertex. -/
def supportInduceDeleteIso
    {V : Type u}
    (C : SimpleGraph V) (z : C.support) :
    (C.induce C.support).induce ({z} : Set C.support)ᶜ ≃g
      C.induce (C.support \ {(z : V)}) where
  toEquiv := {
    toFun := fun x => ⟨x.1.1, x.1.2, by
      intro hxz
      apply x.2
      apply Subtype.ext
      exact hxz⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
      intro hxz
      apply x.2.2
      exact congrArg Subtype.val hxz⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  map_rel_iff' := by
    intro x y
    rfl

theorem connected_of_induce_compl_singleton_connected_of_adj
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {x r : V}
    (hxr : G.Adj x r)
    (hdel : (G.induce ({x} : Set V)ᶜ).Connected) :
    G.Connected := by
  classical
  let Del : Set V := ({x} : Set V)ᶜ
  let f : (G.induce Del) →g G :=
    (SimpleGraph.Embedding.induce (G := G) Del).toHom
  let rDel : Del := ⟨r, by
    dsimp [Del]
    exact hxr.ne'⟩
  refine { nonempty := ⟨x⟩, preconnected := ?_ }
  intro a b
  by_cases hax : a = x
  · subst a
    by_cases hbx : b = x
    · subst b
      exact SimpleGraph.Reachable.rfl
    · let bDel : Del := ⟨b, by
        dsimp [Del]
        exact hbx⟩
      have hrb : (G.induce Del).Reachable rDel bDel := hdel rDel bDel
      exact hxr.reachable.trans (SimpleGraph.Reachable.map f hrb)
  · let aDel : Del := ⟨a, by
      dsimp [Del]
      exact hax⟩
    by_cases hbx : b = x
    · subst b
      exact ((hdel aDel rDel).map f).trans hxr.reachable.symm
    · let bDel : Del := ⟨b, by
        dsimp [Del]
        exact hbx⟩
      exact (hdel aDel bDel).map f

/-- Subdividing every edge of a finite two-connected source graph and then
discarding unused ambient vertices again gives a two-connected graph. -/
theorem strictSubdivisionCarrierCore_isTwoConnected
    {W : Type u} {V : Type v}
    [Fintype W] [LinearOrder W]
    [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (h2 : IsTwoConnected H) :
    let C := strictSubdivisionCarrierGraph
      (orderedStrictSubdivisionModel M)
    IsTwoConnected (C.induce C.support) := by
  classical
  let N := orderedStrictSubdivisionModel M
  let C := strictSubdivisionCarrierGraph N
  let L := edgeRestrictStrictSubdivisionCarrier N
  have hsource : forall x : W, Exists fun y : W => H.Adj x y := by
    intro x
    have hxdegree : 2 ≤ H.degree x := h2.degree_atLeast x
    have hxneighbors : 0 < (H.neighborSet x).ncard := by
      rw [← Set.fintypeCard_eq_ncard,
        SimpleGraph.card_neighborSet_eq_degree]
      omega
    exact (Set.ncard_pos).mp hxneighbors
  let branchCore : W → C.support := fun x =>
    ⟨N.branchVertex x,
      L.branchVertex_mem_support_of_adj (Classical.choose_spec (hsource x))⟩
  have hbranchCore : Function.Injective branchCore := by
    intro x y hxy
    exact N.branchVertex_injective (congrArg Subtype.val hxy)
  have hcardLe : Fintype.card W ≤ Fintype.card C.support :=
    Fintype.card_le_of_injective branchCore hbranchCore
  have hcard : 2 < Nat.card C.support := by
    have hWcard : 2 < Fintype.card W := by
      simpa [Nat.card_eq_fintype_card] using h2.1
    simpa [Nat.card_eq_fintype_card] using
      (show 2 < Fintype.card C.support by omega)
  have hdelete : forall z : C.support,
      ((C.induce C.support).induce ({z} : Set C.support)ᶜ).Connected := by
    intro z
    apply (supportInduceDeleteIso C z).connected_iff.mpr
    exact strictSubdivisionCarrier_delete_connected M h2 z
  have hsupportNonempty : Nonempty C.support := by
    have hWpos : 0 < Fintype.card W := by
      have hWcard : 2 < Fintype.card W := by
        simpa [Nat.card_eq_fintype_card] using h2.1
      omega
    letI : Nonempty W := Fintype.card_pos_iff.mp hWpos
    exact ⟨branchCore (Classical.choice inferInstance)⟩
  let z₀ : C.support := Classical.choice hsupportNonempty
  have hz₀support := z₀.2
  rw [SimpleGraph.mem_support] at hz₀support
  obtain ⟨r, hzr⟩ := hz₀support
  let r₀ : C.support :=
    ⟨r, C.neighborSet_subset_support (z₀ : V) hzr⟩
  have hz₀r₀ : (C.induce C.support).Adj z₀ r₀ := hzr
  have hconnected : (C.induce C.support).Connected :=
    connected_of_induce_compl_singleton_connected_of_adj
      hz₀r₀ (hdelete z₀)
  refine ⟨hcard, ?_⟩
  intro S hS
  have hSle : S.ncard ≤ 1 := by omega
  rcases (Set.ncard_le_one_iff_eq (s := S)).mp hSle with rfl | ⟨z, rfl⟩
  · have hempty : ((∅ : Set C.support)ᶜ) = Set.univ := by
      ext x
      simp
    rw [hempty]
    exact connected_induce_univ_of_connected hconnected
  · exact hdelete z

end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
