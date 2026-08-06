import Schematic.Math.GraphTheory.Embedding.WagnerThree
import Schematic.Math.GraphTheory.Embedding.RotationSystemGluing
import Schematic.Math.GraphTheory.Embedding.RotationSystemEdgeGluing

/-!
The general separator induction in Coq `planar/wagner.v`.

This module sits above the completed three-connected reconstruction.  The
spanning side graphs below keep both sides of a separation on the original
vertex type; vertices outside a side are isolated.  Rotation systems only see
oriented edges, so this is the convenient representation for the checked
cut-vertex and common-cycle splices.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace WagnerGeneral

/-- The spanning graph containing exactly the edges of `G` with both ends in
`A`.  Vertices outside `A` are retained as isolated vertices. -/
def sideGraph {V : Type u} (G : SimpleGraph V) (A : Set V) :
    SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ A ∧ y ∈ A
  symm := by
    rintro x y ⟨hxy, hx, hy⟩
    exact ⟨hxy.symm, hy, hx⟩
  loopless := ⟨by
    intro x h
    exact G.irrefl h.1⟩

@[simp]
theorem sideGraph_adj_iff
    {V : Type u} {G : SimpleGraph V} {A : Set V} {x y : V} :
    (sideGraph G A).Adj x y ↔ G.Adj x y ∧ x ∈ A ∧ y ∈ A :=
  Iff.rfl

theorem sideGraph_le
    {V : Type u} (G : SimpleGraph V) (A : Set V) :
    sideGraph G A ≤ G := by
  intro x y hxy
  exact hxy.1

theorem sideGraph_support_subset
    {V : Type u} {G : SimpleGraph V} {A : Set V} :
    (sideGraph G A).support ⊆ A := by
  intro x hx
  rcases (SimpleGraph.mem_support (G := sideGraph G A)).mp hx with ⟨y, hxy⟩
  exact hxy.2.1

/-- A side graph with the temporary separator edge used by Wagner's
two-separator induction. -/
def markerSideGraph {V : Type u}
    (G : SimpleGraph V) (A : Set V) (x y : V) :
    SimpleGraph V :=
  sideGraph G A ⊔ SimpleGraph.edge x y

/-- The ambient graph in which a marker edge can be expanded along a path of
the original graph. -/
def markerAmbientGraph {V : Type u}
    (G : SimpleGraph V) (x y : V) :
    SimpleGraph V :=
  G ⊔ SimpleGraph.edge x y

@[simp]
theorem markerSideGraph_adj_iff
    {V : Type u} {G : SimpleGraph V} {A : Set V} {x y a b : V} :
    (markerSideGraph G A x y).Adj a b ↔
      (G.Adj a b ∧ a ∈ A ∧ b ∈ A) ∨
        ((a = x ∧ b = y ∨ a = y ∧ b = x) ∧ a ≠ b) := by
  simp [markerSideGraph, SimpleGraph.edge_adj]

theorem markerSideGraph_le_markerAmbientGraph
    {V : Type u} (G : SimpleGraph V) (A : Set V) (x y : V) :
    markerSideGraph G A x y ≤ markerAmbientGraph G x y := by
  apply sup_le
  · exact le_trans (sideGraph_le G A) le_sup_left
  · exact le_sup_right

theorem markerSideGraph_support_subset
    {V : Type u} {G : SimpleGraph V} {A : Set V} {x y : V}
    (hx : x ∈ A) (hy : y ∈ A) :
    (markerSideGraph G A x y).support ⊆ A := by
  intro z hz
  rcases (SimpleGraph.mem_support (G := markerSideGraph G A x y)).mp hz with
    ⟨w, hzw⟩
  rw [markerSideGraph_adj_iff] at hzw
  rcases hzw with hside | hmarker
  · exact hside.2.1
  · rcases hmarker.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx
    · exact hy

theorem markerSideGraph_edge_mem_original_or_marker
    {V : Type u} {G : SimpleGraph V} {A : Set V} {x y : V}
    {e : Sym2 V}
    (he : e ∈ (markerSideGraph G A x y).edgeSet) :
    e ∈ G.edgeSet ∨ e = s(x, y) := by
  rw [markerSideGraph, SimpleGraph.edgeSet_sup] at he
  rcases he with hside | hmarker
  · exact Or.inl
      (SimpleGraph.edgeSet_mono (sideGraph_le G A) hside)
  · right
    rw [SimpleGraph.edge, SimpleGraph.edgeSet_fromEdgeSet] at hmarker
    exact Set.mem_singleton_iff.mp hmarker.1

/-- A separation is the union of its two spanning side graphs. -/
theorem Separation.sideGraph_sup
    {V : Type u} {G : SimpleGraph V} (S : Separation G) :
    sideGraph G S.left ⊔ sideGraph G S.right = G := by
  ext x y
  constructor
  · intro hxy
    rcases hxy with hxy | hxy
    · exact hxy.1
    · exact hxy.1
  · intro hxy
    rcases S.mem_left_or_right x with hxL | hxR
    · rcases S.mem_left_or_right y with hyL | hyR
      · exact Or.inl ⟨hxy, hxL, hyL⟩
      · by_cases hxR : x ∈ S.right
        · exact Or.inr ⟨hxy, hxR, hyR⟩
        · by_cases hyL : y ∈ S.left
          · exact Or.inl ⟨hxy, hxL, hyL⟩
          · exact False.elim (S.no_cross hxL hxR hyR hyL hxy)
    · rcases S.mem_left_or_right y with hyL | hyR
      · by_cases hxL : x ∈ S.left
        · exact Or.inl ⟨hxy, hxL, hyL⟩
        · by_cases hyR : y ∈ S.right
          · exact Or.inr ⟨hxy, hxR, hyR⟩
          · exact False.elim (S.no_cross hyL hyR hxR hxL hxy.symm)
      · exact Or.inr ⟨hxy, hxR, hyR⟩

theorem Separation.markerSideGraph_sup
    {V : Type u} {G : SimpleGraph V}
    (S : Separation G) (x y : V) :
    markerSideGraph G S.left x y ⊔
        markerSideGraph G S.right x y =
      markerAmbientGraph G x y := by
  change
    (sideGraph G S.left ⊔ SimpleGraph.edge x y) ⊔
        (sideGraph G S.right ⊔ SimpleGraph.edge x y) =
      G ⊔ SimpleGraph.edge x y
  calc
    (sideGraph G S.left ⊔ SimpleGraph.edge x y) ⊔
          (sideGraph G S.right ⊔ SimpleGraph.edge x y) =
        (sideGraph G S.left ⊔ sideGraph G S.right) ⊔
          SimpleGraph.edge x y := by
      ac_rfl
    _ = G ⊔ SimpleGraph.edge x y := by
      rw [WagnerGeneral.Separation.sideGraph_sup S]

/-- Adding the marker edge makes either exact-two side connected. -/
theorem Separation.markerAmbient_induce_left_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    (hG : G.Connected)
    {x y : V} (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    ((markerAmbientGraph G x y).induce S.left).Connected := by
  classical
  have hxSep : x ∈ S.separator := by rw [hseparator]; simp
  have hySep : y ∈ S.separator := by rw [hseparator]; simp
  let H := markerAmbientGraph G x y
  let root : S.left := ⟨x, hxSep.1⟩
  have hreachRoot : forall u : S.left,
      (H.induce S.left).Reachable u root := by
    intro u
    by_contra hnot
    let C : Set V :=
      {z | Exists fun hz : z ∈ S.left =>
        (H.induce S.left).Reachable u ⟨z, hz⟩}
    have huC : (u : V) ∈ C :=
      ⟨u.2, SimpleGraph.Reachable.refl u⟩
    have hxNotC : x ∉ C := by
      rintro ⟨hxL, hux⟩
      exact hnot (by simpa [root] using hux)
    obtain ⟨a, haC, b, hbC, hab⟩ :=
      Connected.exists_adjacent_crossing (G := G) hG
        (S := C) ⟨u, huC⟩ ⟨x, hxNotC⟩
    have haCfull : a ∈ C := haC
    rcases haC with ⟨haL, hua⟩
    have haNotR : a ∉ S.right := by
      intro haR
      have haXY : a = x ∨ a = y := by
        have haSep : a ∈ S.separator := ⟨haL, haR⟩
        rw [hseparator] at haSep
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using haSep
      apply hnot
      exact hua.trans (by
        rcases haXY with hax | hay
        · have haroot : (⟨a, haL⟩ : S.left) = root := by
            apply Subtype.ext
            exact hax
          rw [haroot]
        · have hyx :
              (H.induce S.left).Adj
                (⟨y, hySep.1⟩ : S.left) root := by
            change H.Adj y x
            simp [H, markerAmbientGraph, SimpleGraph.edge_adj,
              hxy, hxy.symm]
          have haySub : (⟨a, haL⟩ : S.left) = ⟨y, hySep.1⟩ := by
            apply Subtype.ext
            exact hay
          rw [haySub]
          exact SimpleGraph.Adj.reachable hyx)
    rcases S.mem_left_or_right b with hbL | hbR
    · apply hbC
      refine ⟨hbL, hua.trans ?_⟩
      exact SimpleGraph.Adj.reachable (Or.inl hab)
    · by_cases hbL : b ∈ S.left
      · apply hbC
        refine ⟨hbL, hua.trans ?_⟩
        exact SimpleGraph.Adj.reachable (Or.inl hab)
      · exact S.no_cross haL haNotR hbR hbL hab
  refine {
    preconnected := ?_
    nonempty := ⟨root⟩ }
  intro u v
  exact (hreachRoot u).trans (hreachRoot v).symm

theorem Separation.markerAmbient_induce_right_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    (hG : G.Connected)
    {x y : V} (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    ((markerAmbientGraph G x y).induce S.right).Connected := by
  simpa [Separation.symm] using
    WagnerGeneral.Separation.markerAmbient_induce_left_connected S.symm hG hxy
      (by simpa [S.separator_symm] using hseparator)

theorem markerSideGraph_rotation_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Set V} {x y : V}
    [DecidableRel (markerSideGraph G A x y).Adj]
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hA : ((markerAmbientGraph G x y).induce A).Connected)
    (R : RotationSystem (markerSideGraph G A x y))
    (p : OrientedEdge (markerSideGraph G A x y)) :
    R.toHypermap.Connected := by
  letI : Nonempty (OrientedEdge (markerSideGraph G A x y)) := ⟨p⟩
  apply R.toHypermap_connected_of_tail_reachable
  intro e f
  have heA : e.tail ∈ A :=
    markerSideGraph_support_subset hxA hyA e.adj.left_mem_support
  have hfA : f.tail ∈ A :=
    markerSideGraph_support_subset hxA hyA f.adj.left_mem_support
  let eA : A := ⟨e.tail, heA⟩
  let fA : A := ⟨f.tail, hfA⟩
  let inclusion : ((markerAmbientGraph G x y).induce A) →g
      markerSideGraph G A x y := {
    toFun := fun z => z
    map_rel' := by
      intro a b hab
      rcases hab with hab | hab
      · exact Or.inl ⟨hab, a.2, b.2⟩
      · exact Or.inr hab }
  exact (hA eA fA).map inclusion

theorem Separation.markerSideGraph_support_meet
    {V : Type u} {G : SimpleGraph V}
    (S : Separation G) {x y v : V}
    (hxSep : x ∈ S.separator) (hySep : y ∈ S.separator)
    (hseparator : S.separator = ({x, y} : Set V))
    (hvL : v ∈ (markerSideGraph G S.left x y).support)
    (hvR : v ∈ (markerSideGraph G S.right x y).support) :
    v = x ∨ v = y := by
  have hvSep : v ∈ S.separator :=
    ⟨markerSideGraph_support_subset hxSep.1 hySep.1 hvL,
      markerSideGraph_support_subset hxSep.2 hySep.2 hvR⟩
  rw [hseparator] at hvSep
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hvSep

theorem Separation.markerSideGraph_common_edge
    {V : Type u} {G : SimpleGraph V}
    (S : Separation G) {x y a b : V}
    (hxSep : x ∈ S.separator) (hySep : y ∈ S.separator)
    (hseparator : S.separator = ({x, y} : Set V))
    (habL : (markerSideGraph G S.left x y).Adj a b)
    (habR : (markerSideGraph G S.right x y).Adj a b) :
    (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  have ha := WagnerGeneral.Separation.markerSideGraph_support_meet
    S hxSep hySep hseparator habL.left_mem_support habR.left_mem_support
  have hb := WagnerGeneral.Separation.markerSideGraph_support_meet
    S hxSep hySep hseparator habL.right_mem_support habR.right_mem_support
  rcases ha with hax | hay
  · rcases hb with hbx | hby
    · exact False.elim
        ((markerSideGraph G S.left x y).irrefl (hax ▸ hbx ▸ habL))
    · exact Or.inl ⟨hax, hby⟩
  · rcases hb with hbx | hby
    · exact Or.inr ⟨hay, hbx⟩
    · exact False.elim
        ((markerSideGraph G S.left x y).irrefl (hay ▸ hby ▸ habL))

/-- If a separation has the unique common vertex `a`, its two spanning side
graphs have disjoint edge sets. -/
theorem Separation.sideGraph_edge_disjoint_of_unique_separator
    {V : Type u} {G : SimpleGraph V} (S : Separation G) {a : V}
    (hunique :
      forall x : V, x ∈ S.left -> x ∈ S.right -> x = a) :
    forall ⦃x y : V⦄,
      (sideGraph G S.left).Adj x y ->
        Not ((sideGraph G S.right).Adj x y) := by
  intro x y hleft hright
  have hxa : x = a := hunique x hleft.2.1 hright.2.1
  have hya : y = a := hunique y hleft.2.2 hright.2.2
  exact G.irrefl (hxa ▸ hya ▸ hleft.1)

/-- The supports of the two side graphs meet only at the unique separator
vertex. -/
theorem Separation.sideGraph_support_meet_of_unique_separator
    {V : Type u} {G : SimpleGraph V} (S : Separation G) {a : V}
    (hunique :
      forall x : V, x ∈ S.left -> x ∈ S.right -> x = a) :
    forall ⦃v : V⦄,
      v ∈ (sideGraph G S.left).support ->
        v ∈ (sideGraph G S.right).support -> v = a := by
  intro v hvL hvR
  exact hunique v
    (sideGraph_support_subset hvL)
    (sideGraph_support_subset hvR)

/-- Connectivity of an induced side gives connectivity of every rotation
system on the corresponding spanning side graph.  The explicit dart supplies
the nonempty hypermap witness (isolated vertices outside `A` are invisible). -/
theorem sideGraph_rotation_connected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Set V} [DecidableRel (sideGraph G A).Adj]
    (hA : (G.induce A).Connected)
    (R : RotationSystem (sideGraph G A))
    (p : OrientedEdge (sideGraph G A)) :
    R.toHypermap.Connected := by
  letI : Nonempty (OrientedEdge (sideGraph G A)) := ⟨p⟩
  apply R.toHypermap_connected_of_tail_reachable
  intro e f
  let eA : A := ⟨e.tail, e.adj.2.1⟩
  let fA : A := ⟨f.tail, f.adj.2.1⟩
  let inclusion : (G.induce A) →g sideGraph G A := {
    toFun := fun x => x
    map_rel' := by
      intro x y hxy
      exact ⟨hxy, x.2, y.2⟩ }
  exact (hA eA fA).map inclusion

/-- Coq `vertex_plane_embedding`: glue recursively embedded sides of a
connected proper order-at-most-one separation at their unique common vertex. -/
theorem HasEulerRotationSystem.of_connected_separation_orderAtMost_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    [DecidableRel (sideGraph G S.left).Adj]
    [DecidableRel (sideGraph G S.right).Adj]
    (hG : G.Connected)
    (hproper : S.Proper)
    (horder : S.OrderAtMost 1)
    (hleft : HasEulerRotationSystem (sideGraph G S.left))
    (hright : HasEulerRotationSystem (sideGraph G S.right)) :
    HasEulerRotationSystem G := by
  classical
  rcases S.exists_unique_separator_of_connected_orderAtMost_one
      hG hproper horder with
    ⟨a, haL, haR, hunique⟩
  have hconnL : (G.induce S.left).Connected :=
    S.induce_left_connected_of_connected_unique_separator
      hG haL hunique
  have hconnR : (G.induce S.right).Connected :=
    S.induce_right_connected_of_connected_unique_separator
      hG haR hunique
  rcases hproper.1 with ⟨l, hlL, hl_not_R⟩
  rcases hproper.2 with ⟨r, hrR, hr_not_L⟩
  have hal : a ≠ l := by
    intro hal
    exact hl_not_R (hal ▸ haR)
  have har : a ≠ r := by
    intro har
    exact hr_not_L (har ▸ haL)
  let aL : S.left := ⟨a, haL⟩
  let lL : S.left := ⟨l, hlL⟩
  let aR : S.right := ⟨a, haR⟩
  let rR : S.right := ⟨r, hrR⟩
  obtain ⟨walkL⟩ := hconnL aL lL
  obtain ⟨walkR⟩ := hconnR aR rR
  have hwalkL : Not walkL.Nil := by
    exact SimpleGraph.Walk.not_nil_of_ne (by
      intro h
      exact hal (congrArg Subtype.val h))
  have hwalkR : Not walkR.Nil := by
    exact SimpleGraph.Walk.not_nil_of_ne (by
      intro h
      exact har (congrArg Subtype.val h))
  let p : OrientedEdge (sideGraph G S.left) :=
    ⟨(a, (walkL.snd : V)),
      ⟨walkL.adj_snd hwalkL, haL, walkL.snd.2⟩⟩
  let q : OrientedEdge (sideGraph G S.right) :=
    ⟨(a, (walkR.snd : V)),
      ⟨walkR.adj_snd hwalkR, haR, walkR.snd.2⟩⟩
  rcases hleft with ⟨RL, hRL⟩
  rcases hright with ⟨RR, hRR⟩
  have hRLconn : RL.toHypermap.Connected :=
    sideGraph_rotation_connected hconnL RL p
  have hRRconn : RR.toHypermap.Connected :=
    sideGraph_rotation_connected hconnR RR q
  let Rsum : RotationSystem
      (sideGraph G S.left ⊔ sideGraph G S.right) :=
    RotationSystemGluing.cutVertexSum
      (WagnerGeneral.Separation.sideGraph_edge_disjoint_of_unique_separator
        S hunique)
      (WagnerGeneral.Separation.sideGraph_support_meet_of_unique_separator
        S hunique)
      RL RR p q rfl rfl
  have hRsum : Rsum.toHypermap.dual.EulerPlanar :=
    RotationSystemGluing.cutVertexSum_dual_eulerPlanar
      (WagnerGeneral.Separation.sideGraph_edge_disjoint_of_unique_separator
        S hunique)
      (WagnerGeneral.Separation.sideGraph_support_meet_of_unique_separator
        S hunique)
      RL RR p q rfl rfl hRLconn hRRconn hRL hRR
  have hsum :
      HasEulerRotationSystem
        (sideGraph G S.left ⊔ sideGraph G S.right) :=
    ⟨Rsum, hRsum⟩
  exact HasEulerRotationSystem.of_iso
    (RotationSystemFan.graphIsoOfEq
      (WagnerGeneral.Separation.sideGraph_sup S)).symm
    hsum

/-- Each proper side of a connected separation omits an edge incident with a
vertex exclusive to the opposite side. -/
theorem Separation.sideGraph_left_lt_of_connected_proper
    {V : Type u} {G : SimpleGraph V}
    (S : Separation G)
    (hG : G.Connected)
    (hproper : S.Proper) :
    sideGraph G S.left < G := by
  rcases hproper.1 with ⟨l, hlL, hl_not_R⟩
  rcases hproper.2 with ⟨r, hrR, hr_not_L⟩
  have hrl : r ≠ l := by
    intro hrl
    exact hr_not_L (hrl ▸ hlL)
  obtain ⟨p⟩ := hG r l
  have hp : Not p.Nil := SimpleGraph.Walk.not_nil_of_ne hrl
  have hne : sideGraph G S.left ≠ G := by
    intro heq
    have hside : (sideGraph G S.left).Adj r p.snd := by
      rw [heq]
      exact p.adj_snd hp
    exact hr_not_L hside.2.1
  exact lt_of_le_of_ne (sideGraph_le G S.left) hne

theorem Separation.sideGraph_right_lt_of_connected_proper
    {V : Type u} {G : SimpleGraph V}
    (S : Separation G)
    (hG : G.Connected)
    (hproper : S.Proper) :
    sideGraph G S.right < G := by
  simpa [Separation.symm] using
    WagnerGeneral.Separation.sideGraph_left_lt_of_connected_proper
      S.symm hG ((S.proper_symm).mpr hproper)

theorem Separation.sideGraph_left_edgeFinset_card_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    [DecidableRel (sideGraph G S.left).Adj]
    (hG : G.Connected)
    (hproper : S.Proper) :
    (sideGraph G S.left).edgeFinset.card < G.edgeFinset.card := by
  exact Finset.card_lt_card
    (SimpleGraph.edgeFinset_strict_mono
      (WagnerGeneral.Separation.sideGraph_left_lt_of_connected_proper
        S hG hproper))

theorem Separation.sideGraph_right_edgeFinset_card_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    [DecidableRel (sideGraph G S.right).Adj]
    (hG : G.Connected)
    (hproper : S.Proper) :
    (sideGraph G S.right).edgeFinset.card < G.edgeFinset.card := by
  exact Finset.card_lt_card
    (SimpleGraph.edgeFinset_strict_mono
      (WagnerGeneral.Separation.sideGraph_right_lt_of_connected_proper
        S hG hproper))

/-- In a two-connected graph, each nontrivial side of a two-separation
contains a path between the two separator vertices whose internal vertices
are exclusive to that side.  This is the graph-theoretic path used to replace
the temporary marker edge in Wagner's induction. -/
theorem Separation.exists_right_only_path_between_separator_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    (hG : IsTwoConnected G)
    (hproper : S.Proper)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    Exists fun p : G.Walk x y =>
      p.IsPath ∧
        forall z : V, z ∈ p.support ->
          z = x ∨ z = y ∨ z ∈ S.right \ S.left := by
  classical
  let A : Set V := S.right \ S.left
  rcases hproper.2 with ⟨r, hr_right, hr_not_left⟩
  let rA : A := ⟨r, hr_right, hr_not_left⟩
  let C : (G.induce A).ConnectedComponent :=
    (G.induce A).connectedComponentMk rA
  let K : Set V := induceComponentSupport (G := G) C
  have hK_nonempty : K.Nonempty :=
    induceComponentSupport_nonempty (G := G) C
  have hK_subset : K ⊆ A :=
    induceComponentSupport_subset (G := G) C
  have hK_disjoint_separator : Disjoint K S.separator := by
    rw [Set.disjoint_left]
    intro z hzK hzseparator
    exact (hK_subset hzK).2 hzseparator.1
  have hseparator_large : 1 < S.separator.ncard := by
    rw [hseparator, Set.ncard_pair hxy]
    omega
  have hK_closed :
      forall a : V, a ∈ K -> forall b : V, G.Adj a b ->
        b ∈ K ∨ b ∈ S.separator := by
    intro a haK b hab
    have haA : a ∈ A := hK_subset haK
    by_cases hbA : b ∈ A
    · exact Or.inl
        (induceComponentSupport_mem_of_adj (G := G) C haK hbA hab)
    · have hb_right : b ∈ S.right :=
        S.adj_mem_right_of_mem_right_not_left haA.1 haA.2 hab
      have hb_left : b ∈ S.left := by
        by_contra hb_not_left
        exact hbA ⟨hb_right, hb_not_left⟩
      exact Or.inr ⟨hb_left, hb_right⟩
  let B : Set V := relativeVertexBoundary G K S.separator
  have hB_card : 2 <= B.ncard := by
    exact hG.boundary_ncard_ge_two hK_nonempty hK_disjoint_separator
      hseparator_large hK_closed
  have hB_subset : B ⊆ S.separator := by
    intro z hz
    exact hz.1
  have hseparator_card : S.separator.ncard = 2 := by
    rw [hseparator, Set.ncard_pair hxy]
  have hB_eq : B = S.separator := by
    apply Set.eq_of_subset_of_ncard_le hB_subset
    rw [hseparator_card]
    exact hB_card
  have hxB : x ∈ B := by
    rw [hB_eq, hseparator]
    simp
  have hyB : y ∈ B := by
    rw [hB_eq, hseparator]
    simp
  rcases hxB.2 with ⟨a, haK, hax⟩
  rcases hyB.2 with ⟨b, hbK, hby⟩
  have hK_connected : (G.induce K).Connected :=
    induceComponentSupport_connected (G := G) C
  obtain ⟨p, hp, hp_support⟩ :=
    connected_induce_exists_path_support_subset
      (G := G) hK_connected haK hbK
  let xa : G.Walk x a := hax.symm.toWalk
  let byEdge : G.Walk b y := hby.toWalk
  let q1 : G.Walk x b := xa.append p
  let q : G.Walk x y := q1.append byEdge
  have hx_not_K : x ∉ K := by
    intro hxK
    exact Set.disjoint_left.mp hK_disjoint_separator hxK hxB.1
  have hy_not_K : y ∉ K := by
    intro hyK
    exact Set.disjoint_left.mp hK_disjoint_separator hyK hyB.1
  have hq1 : q1.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      (SimpleGraph.Walk.IsPath.of_adj hax.symm) hp ?_
    intro z hz_xa hz_p
    have hzK : z ∈ K := hp_support z hz_p
    simp [xa] at hz_xa
    rcases hz_xa with hzx | hza
    · exact False.elim (hx_not_K (hzx ▸ hzK))
    · exact hza
  have hq : q.IsPath := by
    refine Walk.IsPath.append_of_support_inter_eq_endpoint
      hq1 (SimpleGraph.Walk.IsPath.of_adj hby) ?_
    intro z hz_q1 hz_byEdge
    simp [byEdge] at hz_byEdge
    rcases hz_byEdge with hzb | hzy
    · exact hzb
    · have hzy_q1 : y ∈ q1.support := by simpa [hzy] using hz_q1
      have hzy_xa_or_p : y ∈ xa.support ∨ y ∈ p.support := by
        simpa [q1, SimpleGraph.Walk.mem_support_append_iff] using hzy_q1
      rcases hzy_xa_or_p with hzy_xa | hzy_p
      · simp [xa] at hzy_xa
        rcases hzy_xa with hyx | hya
        · exact False.elim (hxy hyx.symm)
        · exact False.elim (hy_not_K (hya ▸ haK))
      · exact False.elim (hy_not_K (hp_support y hzy_p))
  refine ⟨q, hq, ?_⟩
  intro z hzq
  have hz_q1_or_by : z ∈ q1.support ∨ z ∈ byEdge.support := by
    simpa [q, SimpleGraph.Walk.mem_support_append_iff] using hzq
  rcases hz_q1_or_by with hz_q1 | hz_byEdge
  · have hz_xa_or_p : z ∈ xa.support ∨ z ∈ p.support := by
      simpa [q1, SimpleGraph.Walk.mem_support_append_iff] using hz_q1
    rcases hz_xa_or_p with hz_xa | hz_p
    · simp [xa] at hz_xa
      rcases hz_xa with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hK_subset haK))
    · exact Or.inr (Or.inr (hK_subset (hp_support z hz_p)))
  · simp [byEdge] at hz_byEdge
    rcases hz_byEdge with rfl | rfl
    · exact Or.inr (Or.inr (hK_subset hbK))
    · exact Or.inr (Or.inl rfl)

theorem Separation.exists_left_only_path_between_separator_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    (hG : IsTwoConnected G)
    (hproper : S.Proper)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    Exists fun p : G.Walk x y =>
      p.IsPath ∧
        forall z : V, z ∈ p.support ->
          z = x ∨ z = y ∨ z ∈ S.left \ S.right := by
  simpa [Separation.symm] using
    WagnerGeneral.Separation.exists_right_only_path_between_separator_pair
      S.symm hG ((S.proper_symm).mpr hproper) hxy
      (by simpa [S.separator_symm] using hseparator)

/-- The marked left side of a proper two-separation has fewer edges than the
ambient graph.  If the marker is new, the clean path through the opposite
side has at least two distinct edges, all omitted by the left side, whereas
the marker contributes only one edge. -/
theorem Separation.markerSideGraph_left_edgeFinset_card_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G) {x y : V}
    [DecidableRel (sideGraph G S.left).Adj]
    [DecidableRel (markerSideGraph G S.left x y).Adj]
    (hG : IsTwoConnected G)
    (hproper : S.Proper)
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    (markerSideGraph G S.left x y).edgeFinset.card <
      G.edgeFinset.card := by
  classical
  have hxseparator : x ∈ S.separator := by
    rw [hseparator]
    simp
  have hyseparator : y ∈ S.separator := by
    rw [hseparator]
    simp
  by_cases hxy_adj : G.Adj x y
  · have hedge_le : SimpleGraph.edge x y ≤ sideGraph G S.left := by
      intro a b hab
      rw [SimpleGraph.edge_adj] at hab
      rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hxy_adj, hxseparator.1, hyseparator.1⟩
      · exact ⟨hxy_adj.symm, hyseparator.1, hxseparator.1⟩
    have hmarker_eq : markerSideGraph G S.left x y = sideGraph G S.left := by
      exact sup_eq_left.mpr hedge_le
    have hside_lt : sideGraph G S.left < G :=
      WagnerGeneral.Separation.sideGraph_left_lt_of_connected_proper S
        (hG.connected (by decide)) hproper
    have hmarker_lt : markerSideGraph G S.left x y < G := by
      simpa only [hmarker_eq] using hside_lt
    exact Finset.card_lt_card
      (SimpleGraph.edgeFinset_strict_mono hmarker_lt)
  · obtain ⟨q, hq, hq_support⟩ :=
      WagnerGeneral.Separation.exists_right_only_path_between_separator_pair S
        hG hproper hxy hseparator
    let E : Finset (Sym2 V) := q.edges.toFinset
    have hEcard : E.card = q.length := by
      dsimp [E]
      rw [List.toFinset_card_of_nodup hq.isTrail.edges_nodup,
        SimpleGraph.Walk.length_edges]
    have hq_length : 2 ≤ q.length := by
      have hzero : q.length ≠ 0 := by
        intro hlen
        exact hxy (SimpleGraph.Walk.eq_of_length_eq_zero hlen)
      have hone : q.length ≠ 1 := by
        intro hlen
        exact hxy_adj (SimpleGraph.Walk.adj_of_length_eq_one hlen)
      omega
    have hEsubset :
        E ⊆ G.edgeFinset \ (sideGraph G S.left).edgeFinset := by
      intro e he
      have heq : e ∈ q.edges := by
        simpa [E] using he
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact SimpleGraph.mem_edgeFinset.mpr (q.edges_subset_edgeSet heq)
      · intro he_side
        induction e using Sym2.inductionOn with
        | _ a b =>
            have hab_side : (sideGraph G S.left).Adj a b := by
              simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he_side
            have ha_support : a ∈ q.support :=
              q.fst_mem_support_of_mem_edges heq
            have hb_support : b ∈ q.support :=
              q.snd_mem_support_of_mem_edges heq
            have ha_xy : a = x ∨ a = y := by
              rcases hq_support a ha_support with hax | hay | ha_right
              · exact Or.inl hax
              · exact Or.inr hay
              · exact False.elim (ha_right.2 hab_side.2.1)
            have hb_xy : b = x ∨ b = y := by
              rcases hq_support b hb_support with hbx | hby | hb_right
              · exact Or.inl hbx
              · exact Or.inr hby
              · exact False.elim (hb_right.2 hab_side.2.2)
            rcases ha_xy with rfl | rfl <;>
              rcases hb_xy with rfl | rfl
            · exact G.irrefl hab_side.1
            · exact hxy_adj hab_side.1
            · exact hxy_adj hab_side.1.symm
            · exact G.irrefl hab_side.1
    have hmissing :
        2 ≤ (G.edgeFinset \ (sideGraph G S.left).edgeFinset).card := by
      calc
        2 ≤ E.card := by simpa [hEcard] using hq_length
        _ ≤ (G.edgeFinset \ (sideGraph G S.left).edgeFinset).card :=
          Finset.card_le_card hEsubset
    have hside_subset :
        (sideGraph G S.left).edgeFinset ⊆ G.edgeFinset :=
      SimpleGraph.edgeFinset_mono (sideGraph_le G S.left)
    have hpartition :=
      Finset.card_sdiff_add_card_eq_card hside_subset
    have hside_gap :
        (sideGraph G S.left).edgeFinset.card + 1 < G.edgeFinset.card := by
      omega
    have hmarker_card :
        (markerSideGraph G S.left x y).edgeFinset.card =
          (sideGraph G S.left).edgeFinset.card + 1 := by
      simpa [markerSideGraph] using
        (SimpleGraph.card_edgeFinset_sup_edge
          (G := sideGraph G S.left)
          (fun hside => hxy_adj hside.1) hxy)
    rw [hmarker_card]
    exact hside_gap

theorem Separation.markerSideGraph_right_edgeFinset_card_lt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G) {x y : V}
    [DecidableRel (sideGraph G S.right).Adj]
    [DecidableRel (markerSideGraph G S.right x y).Adj]
    (hG : IsTwoConnected G)
    (hproper : S.Proper)
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    (markerSideGraph G S.right x y).edgeFinset.card <
      G.edgeFinset.card := by
  classical
  letI : DecidableRel (sideGraph G S.symm.left).Adj :=
    inferInstanceAs (DecidableRel (sideGraph G S.right).Adj)
  letI : DecidableRel (markerSideGraph G S.symm.left x y).Adj :=
    inferInstanceAs (DecidableRel (markerSideGraph G S.right x y).Adj)
  simpa [Separation.symm] using
    WagnerGeneral.Separation.markerSideGraph_left_edgeFinset_card_lt
      S.symm hG ((S.proper_symm).mpr hproper) hxy
      (by simpa [S.separator_symm] using hseparator)

/-- A strict subdivision in a side graph with a genuinely new marker edge can
be rerouted through a clean path of the original graph.  This is the
topological-model version of Coq's `add_edge_separation_excluded`. -/
theorem containsStrictSubdivision_of_markerSideGraph
    {W : Type*} {V : Type u}
    [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (A : Set V) (x y : V)
    (hxA : x ∈ A) (hyA : y ∈ A)
    (hsource : forall w : W, Exists fun t : W => H.Adj w t)
    (hxy_not : Not (G.Adj x y))
    (q : G.Walk x y)
    (hq : q.IsPath)
    (hq_clean :
      forall z : V, z ∈ q.support -> z ∈ A -> z = x ∨ z = y)
    (hmarker : ContainsStrictSubdivision H (markerSideGraph G A x y)) :
    ContainsStrictSubdivision H G := by
  classical
  rcases hmarker with ⟨M⟩
  let U : SimpleGraph V := markerAmbientGraph G x y
  let Mplus : StrictSubdivisionModel H U :=
    M.targetMono (markerSideGraph_le_markerAmbientGraph G A x y)
  let qU : U.Walk x y :=
    q.transfer U (fun e he =>
      SimpleGraph.edgeSet_mono (show G ≤ U from le_sup_left)
        (q.edges_subset_edgeSet he))
  have hqU : qU.IsPath := by
    exact hq.transfer _
  have hbranch : forall w : W, Mplus.branchVertex w ∈ A := by
    intro w
    rcases hsource w with ⟨t, hwt⟩
    have hw_support : M.branchVertex w ∈
        (markerSideGraph G A x y).support :=
      M.branchVertex_mem_support_of_adj hwt
    exact markerSideGraph_support_subset hxA hyA hw_support
  have hpath :
      forall {a b : W} (hab : H.Adj a b) {z : V},
        z ∈ (Mplus.edgePath hab).support -> z ∈ A := by
    intro a b hab z hz
    have hzM : z ∈ (M.edgePath hab).support := by
      simpa [Mplus, StrictSubdivisionModel.targetMono,
        SimpleGraph.Walk.support_transfer] using hz
    have hp_not_nil : Not (M.edgePath hab).Nil :=
      SimpleGraph.Walk.not_nil_of_ne (M.branchVertex_ne_of_adj hab)
    have hz_support : z ∈ (markerSideGraph G A x y).support :=
      SimpleGraph.mem_support_of_mem_walk_support
        (M.edgePath hab) hp_not_nil hzM
    exact markerSideGraph_support_subset hxA hyA hz_support
  have hqU_clean :
      forall z : V, z ∈ qU.support -> z ∈ A -> z = x ∨ z = y := by
    intro z hz hzA
    have hzq : z ∈ q.support := by
      simpa [qU, SimpleGraph.Walk.support_transfer] using hz
    exact hq_clean z hzq hzA
  let Mr : StrictSubdivisionModel H U :=
    Mplus.rerouteHostEdgeOutside A x y qU hqU hbranch hpath hqU_clean
  have hq_no_marker : s(x, y) ∉ q.edges := by
    intro he
    apply hxy_not
    rw [← SimpleGraph.mem_edgeSet]
    exact q.edges_subset_edgeSet he
  have hqU_no_marker : s(x, y) ∉ qU.edges := by
    simpa [qU, SimpleGraph.Walk.edges_transfer] using hq_no_marker
  refine ⟨Mr.edgeRestrict ?_⟩
  intro a b hab e he
  let hp : (Mplus.edgePath hab).IsPath := Mplus.edgePath_isPath hab
  have he_expanded :
      e ∈ (Walk.IsPath.expandEdge hp x y qU).edges := by
    simpa [Mr, StrictSubdivisionModel.rerouteHostEdgeOutside, hp] using he
  have hno_marker :
      s(x, y) ∉ (Walk.IsPath.expandEdge hp x y qU).edges :=
    Walk.IsPath.marker_not_mem_expandEdge_edges hp hqU_no_marker
  rcases Walk.IsPath.expandEdge_edges_subset hp qU e he_expanded with
    heold | heq
  · have heM : e ∈ (M.edgePath hab).edges := by
      simpa [Mplus, StrictSubdivisionModel.targetMono,
        SimpleGraph.Walk.edges_transfer, hp] using heold
    have heSide : e ∈ (markerSideGraph G A x y).edgeSet :=
      (M.edgePath hab).edges_subset_edgeSet heM
    rcases markerSideGraph_edge_mem_original_or_marker heSide with
      heG | heMarker
    · exact heG
    · exact False.elim (hno_marker (by simpa [heMarker] using he_expanded))
  · have heqG : e ∈ q.edges := by
      simpa [qU, SimpleGraph.Walk.edges_transfer] using heq
    exact q.edges_subset_edgeSet heqG

theorem markerSideGraph_le_of_adj
    {V : Type u} {G : SimpleGraph V} {A : Set V} {x y : V}
    (hxy : G.Adj x y) :
    markerSideGraph G A x y ≤ G := by
  intro a b hab
  rw [markerSideGraph_adj_iff] at hab
  rcases hab with hside | hmarker
  · exact hside.1
  · rcases hmarker.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy
    · exact hxy.symm

/-- Adding the separator marker edge to the left side of a proper
two-separation preserves the repository's strict-Kuratowski planarity
predicate. -/
theorem IsPlanar.markerSideGraph_left
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hplanar : IsPlanar G)
    (S : Separation G)
    (hG : IsTwoConnected G)
    (hproper : S.Proper)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    IsPlanar (markerSideGraph G S.left x y) := by
  classical
  have hxseparator : x ∈ S.separator := by
    rw [hseparator]
    simp
  have hyseparator : y ∈ S.separator := by
    rw [hseparator]
    simp
  by_cases hxy_adj : G.Adj x y
  · exact hplanar.mono (markerSideGraph_le_of_adj hxy_adj)
  obtain ⟨q, hq, hq_support⟩ :=
    WagnerGeneral.Separation.exists_right_only_path_between_separator_pair
      S hG hproper hxy hseparator
  have hq_clean :
      forall z : V, z ∈ q.support -> z ∈ S.left -> z = x ∨ z = y := by
    intro z hzq hzleft
    rcases hq_support z hzq with hzx | hzy | hzright_only
    · exact Or.inl hzx
    · exact Or.inr hzy
    · exact False.elim (hzright_only.2 hzleft)
  refine ⟨?_, ?_⟩
  · intro hK5
    exact hplanar.no_K5_subdivision
      (containsStrictSubdivision_of_markerSideGraph
        S.left x y hxseparator.1 hyseparator.1 K5Graph_exists_adj
        hxy_adj q hq hq_clean hK5)
  · intro hK33
    exact hplanar.no_K33_subdivision
      (containsStrictSubdivision_of_markerSideGraph
        S.left x y hxseparator.1 hyseparator.1 K33Graph_exists_adj
        hxy_adj q hq hq_clean hK33)

theorem IsPlanar.markerSideGraph_right
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hplanar : IsPlanar G)
    (S : Separation G)
    (hG : IsTwoConnected G)
    (hproper : S.Proper)
    {x y : V}
    (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V)) :
    IsPlanar (markerSideGraph G S.right x y) := by
  simpa [Separation.symm] using
    WagnerGeneral.IsPlanar.markerSideGraph_left
      hplanar S.symm hG ((S.proper_symm).mpr hproper) hxy
      (by simpa [S.separator_symm] using hseparator)

/-- Coq `edge_plane_embedding`, specialized to the marked spanning side
graphs used by Wagner induction. -/
theorem HasEulerRotationSystem.of_exact_two_separation_markers
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (S : Separation G)
    {x y : V} (hxy : x ≠ y)
    (hseparator : S.separator = ({x, y} : Set V))
    [DecidableRel (markerSideGraph G S.left x y).Adj]
    [DecidableRel (markerSideGraph G S.right x y).Adj]
    [DecidableRel (markerAmbientGraph G x y).Adj]
    (hG : IsTwoConnected G)
    (hleft : HasEulerRotationSystem
      (markerSideGraph G S.left x y))
    (hright : HasEulerRotationSystem
      (markerSideGraph G S.right x y)) :
    HasEulerRotationSystem (markerAmbientGraph G x y) := by
  classical
  have hxSep : x ∈ S.separator := by rw [hseparator]; simp
  have hySep : y ∈ S.separator := by rw [hseparator]; simp
  have hxyL : (markerSideGraph G S.left x y).Adj x y := by
    rw [markerSideGraph_adj_iff]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  have hxyR : (markerSideGraph G S.right x y).Adj x y := by
    rw [markerSideGraph_adj_iff]
    exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩
  rcases hleft with ⟨RL, hRL⟩
  rcases hright with ⟨RR, hRR⟩
  have hconnG : G.Connected := hG.connected (by decide)
  have hconnL :
      ((markerAmbientGraph G x y).induce S.left).Connected :=
    WagnerGeneral.Separation.markerAmbient_induce_left_connected
      S hconnG hxy hseparator
  have hconnR :
      ((markerAmbientGraph G x y).induce S.right).Connected :=
    WagnerGeneral.Separation.markerAmbient_induce_right_connected
      S hconnG hxy hseparator
  let pL : OrientedEdge (markerSideGraph G S.left x y) :=
    EdgeDeletion.forwardDart hxyL
  let pR : OrientedEdge (markerSideGraph G S.right x y) :=
    EdgeDeletion.forwardDart hxyR
  have hRLconn : RL.toHypermap.Connected :=
    markerSideGraph_rotation_connected hxSep.1 hySep.1 hconnL RL pL
  have hRRconn : RR.toHypermap.Connected :=
    markerSideGraph_rotation_connected hxSep.2 hySep.2 hconnR RR pR
  have hcommon : forall ⦃a b : V⦄,
      (markerSideGraph G S.left x y).Adj a b ->
      (markerSideGraph G S.right x y).Adj a b ->
        (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    intro a b habL habR
    exact WagnerGeneral.Separation.markerSideGraph_common_edge
      S hxSep hySep hseparator habL habR
  have hattach : forall ⦃v : V⦄,
      v ∈ (markerSideGraph G S.left x y).support ->
      v ∈ (markerSideGraph G S.right x y).support ->
        v = x ∨ v = y := by
    intro v hvL hvR
    exact WagnerGeneral.Separation.markerSideGraph_support_meet
      S hxSep hySep hseparator hvL hvR
  let Rsum : RotationSystem
      (markerSideGraph G S.left x y ⊔
        markerSideGraph G S.right x y) :=
    RotationSystemEdgeGluing.edgeSumRotationSystem
      RL RR hxyL hxyR hcommon hattach
  have hRsum : Rsum.toHypermap.dual.EulerPlanar :=
    RotationSystemEdgeGluing.edgeSumRotationSystem_dual_eulerPlanar
      RL RR hxyL hxyR hcommon hattach hRLconn hRRconn hRL hRR
  have hsum : HasEulerRotationSystem
      (markerSideGraph G S.left x y ⊔
        markerSideGraph G S.right x y) :=
    ⟨Rsum, hRsum⟩
  exact HasEulerRotationSystem.of_iso
    (RotationSystemFan.graphIsoOfEq
      (WagnerGeneral.Separation.markerSideGraph_sup S x y)).symm hsum

/-- Complete Coq `wagner`: the strict Kuratowski predicate constructs an
Euler-planar rotation system.  The outer strong induction is on vertices
(components and contractions); the inner strong induction is on edges
(ordinary and marker-augmented separation sides). -/
theorem hasEulerRotationSystem_of_isPlanar :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      {G : SimpleGraph V} [DecidableRel G.Adj],
        IsPlanar G → HasEulerRotationSystem G := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      Fintype.card V = n →
        ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
          IsPlanar G → HasEulerRotationSystem G
  have hP : ∀ n : Nat, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IHv =>
        intro V _ _ hV G _ hplanar
        let Q : Nat → Prop := fun m =>
          ∀ {G : SimpleGraph V} [DecidableRel G.Adj],
            G.edgeFinset.card = m →
              IsPlanar G → HasEulerRotationSystem G
        have hQ : ∀ m : Nat, Q m := by
          intro m
          induction m using Nat.strong_induction_on with
          | h m IHe =>
              intro G _ hE hplanar
              by_cases hsmall : Fintype.card V ≤ 4
              · exact HasEulerRotationSystem.of_card_le_four (G := G) hsmall
              have hlarge : 4 < Fintype.card V := by omega
              by_cases hpre : G.Preconnected
              · letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
                have hconn : G.Connected := ⟨hpre⟩
                by_cases htwo : IsTwoConnected G
                · by_cases hthree : IsThreeConnected G
                  · apply
                      WagnerThree.IsThreeConnected.hasEulerRotationSystem_of_contractibleEdge
                        hthree hplanar
                        (by simpa [Nat.card_eq_fintype_card] using hlarge)
                    intro a b hab
                    letI : Fintype
                        (GraphContraction.collapseEdge G hab).Target :=
                      GraphContraction.collapseEdgeTargetFintype G hab
                    letI : DecidableEq
                        (GraphContraction.collapseEdge G hab).Target :=
                      GraphContraction.collapseEdgeTargetDecidableEq G hab
                    letI : DecidableRel
                        (GraphContraction.collapseEdge G hab).graph.Adj :=
                      Classical.decRel _
                    have hlt :
                        Fintype.card
                            (GraphContraction.collapseEdge G hab).Target < n := by
                      have hraw :=
                        GraphContraction.collapseEdge_target_card_lt G hab
                      omega
                    have hIH :
                        P (Fintype.card
                          (GraphContraction.collapseEdge G hab).Target) :=
                      IHv _ hlt
                    exact hIH
                      (V := (GraphContraction.collapseEdge G hab).Target) rfl
                      (G := (GraphContraction.collapseEdge G hab).graph)
                      (IsPlanar.collapseEdge hplanar hab)
                  · obtain ⟨S, hproper, horder⟩ :=
                      not_kplusone_connected_has_proper_small_separation
                        (G := G) 2
                        (by simpa [Nat.card_eq_fintype_card] using
                          (show 3 < Fintype.card V by omega))
                        hthree
                    have hnot_order_one : ¬ S.OrderAtMost 1 := by
                      intro horder_one
                      exact isKConnected_no_proper_separation_orderAtMost
                        (G := G) (k := 1) htwo S hproper horder_one
                    obtain ⟨x, y, hxy, hseparator⟩ :=
                      S.exists_separator_pair_of_orderAtMost_two_not_orderAtMost_one
                        horder hnot_order_one
                    letI : DecidableRel
                        (sideGraph G S.left).Adj := Classical.decRel _
                    letI : DecidableRel
                        (sideGraph G S.right).Adj := Classical.decRel _
                    letI : DecidableRel
                        (markerSideGraph G S.left x y).Adj := Classical.decRel _
                    letI : DecidableRel
                        (markerSideGraph G S.right x y).Adj := Classical.decRel _
                    letI : DecidableRel
                        (markerAmbientGraph G x y).Adj := Classical.decRel _
                    have hleft_planar :
                        IsPlanar (markerSideGraph G S.left x y) :=
                      WagnerGeneral.IsPlanar.markerSideGraph_left
                        hplanar S htwo hproper hxy hseparator
                    have hright_planar :
                        IsPlanar (markerSideGraph G S.right x y) :=
                      WagnerGeneral.IsPlanar.markerSideGraph_right
                        hplanar S htwo hproper hxy hseparator
                    have hleft_lt :
                        (markerSideGraph G S.left x y).edgeFinset.card < m := by
                      have hraw :=
                        WagnerGeneral.Separation.markerSideGraph_left_edgeFinset_card_lt S
                          htwo hproper hxy hseparator
                      omega
                    have hright_lt :
                        (markerSideGraph G S.right x y).edgeFinset.card < m := by
                      have hraw :=
                        WagnerGeneral.Separation.markerSideGraph_right_edgeFinset_card_lt S
                          htwo hproper hxy hseparator
                      omega
                    have hleft : HasEulerRotationSystem
                        (markerSideGraph G S.left x y) :=
                      by
                        have hIE : Q
                            (markerSideGraph G S.left x y).edgeFinset.card :=
                          IHe _ hleft_lt
                        exact hIE (G := markerSideGraph G S.left x y)
                          rfl hleft_planar
                    have hright : HasEulerRotationSystem
                        (markerSideGraph G S.right x y) :=
                      by
                        have hIE : Q
                            (markerSideGraph G S.right x y).edgeFinset.card :=
                          IHe _ hright_lt
                        exact hIE (G := markerSideGraph G S.right x y)
                          rfl hright_planar
                    have hambient : HasEulerRotationSystem
                        (markerAmbientGraph G x y) :=
                      HasEulerRotationSystem.of_exact_two_separation_markers
                        S hxy hseparator htwo hleft hright
                    exact hambient.mono le_sup_left
                · obtain ⟨S, hproper, horder⟩ :=
                    not_kplusone_connected_has_proper_small_separation
                      (G := G) 1
                      (by simpa [Nat.card_eq_fintype_card] using
                        (show 2 < Fintype.card V by omega))
                      htwo
                  letI : DecidableRel
                      (sideGraph G S.left).Adj := Classical.decRel _
                  letI : DecidableRel
                      (sideGraph G S.right).Adj := Classical.decRel _
                  have hleft_lt :
                      (sideGraph G S.left).edgeFinset.card < m := by
                    have hraw :=
                      WagnerGeneral.Separation.sideGraph_left_edgeFinset_card_lt
                        S hconn hproper
                    omega
                  have hright_lt :
                      (sideGraph G S.right).edgeFinset.card < m := by
                    have hraw :=
                      WagnerGeneral.Separation.sideGraph_right_edgeFinset_card_lt
                        S hconn hproper
                    omega
                  have hleft : HasEulerRotationSystem
                      (sideGraph G S.left) :=
                    by
                      have hIE : Q (sideGraph G S.left).edgeFinset.card :=
                        IHe _ hleft_lt
                      exact hIE (G := sideGraph G S.left) rfl
                        (hplanar.mono (sideGraph_le G S.left))
                  have hright : HasEulerRotationSystem
                      (sideGraph G S.right) :=
                    by
                      have hIE : Q (sideGraph G S.right).edgeFinset.card :=
                        IHe _ hright_lt
                      exact hIE (G := sideGraph G S.right) rfl
                        (hplanar.mono (sideGraph_le G S.right))
                  exact
                    HasEulerRotationSystem.of_connected_separation_orderAtMost_one
                      S hconn hproper horder hleft hright
              · exact
                  HasEulerRotationSystem.of_isPlanar_connectedComponents
                    (G := G) hplanar (by
                      intro C hCplanar
                      letI : Fintype C := C.supp.toFinite.fintype
                      letI : DecidableEq C := Classical.decEq C
                      letI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
                      have hltC : Fintype.card C < n := by
                        have hraw : Fintype.card C < Fintype.card V :=
                          connectedComponent_card_lt_of_not_preconnected
                            (G := G) hpre C
                        omega
                      have hIH : P (Fintype.card C) := IHv _ hltC
                      exact hIH (V := C) rfl
                        (G := C.toSimpleGraph) hCplanar)
        have hQG : Q G.edgeFinset.card := hQ G.edgeFinset.card
        exact hQG (G := G) rfl hplanar
  intro V _ _ G _ hplanar
  have hPV : P (Fintype.card V) := hP (Fintype.card V)
  exact hPV (V := V) rfl (G := G) hplanar

end WagnerGeneral

end FourColor

end Schematic.Math.GraphTheory
