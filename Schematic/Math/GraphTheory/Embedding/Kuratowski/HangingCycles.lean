import Schematic.Math.GraphTheory.Embedding.Kuratowski.CutComponents
import Schematic.Math.GraphTheory.Embedding.Kuratowski.TheoremInterfaces

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Source-independent block/cactus output.  A connected finite theta-free
graph of minimum degree at least two has a simple cycle whose outside contacts
all pass through one distinguished vertex. -/
theorem exists_hanging_cycle_of_connected_no_homeomorphicTheta_min_degree_two
    {W : Type u} [Fintype W] [DecidableEq W]
    {D : SimpleGraph W} [DecidableRel D.Adj]
    (hconn : D.Connected)
    (hno : Not (ContainsHomeomorphicTheta D))
    (hdegree : forall w : W, 2 <= D.degree w) :
    Exists fun r : W =>
      Exists fun C : D.Walk r r =>
        C.IsCycle ∧
          Exists fun v : W =>
            v ∈ C.support ∧
              (forall {t c : W},
                t ∉ C.support -> c ∈ C.support -> D.Adj t c -> c = v) := by
  classical
  rcases
      isTwoConnected_or_exists_cutComponent_twoConnected_of_connected_min_degree_two
        (G := D) hconn hdegree with
    h2 | hend
  · letI : Nonempty W := hconn.nonempty
    rcases exists_isCycle_of_nonempty_min_degree_two (G := D) hdegree with
      ⟨r, C, hC⟩
    have hspans : forall t : W, t ∈ C.support :=
      cycle_support_univ_of_twoConnected_no_homeomorphicTheta
        (G := D) h2 C hC hno
    exact
      ⟨r, C, hC, r, C.start_mem_support, by
        intro t _c ht _hc _htc
        exact False.elim (ht (hspans t))⟩
  · rcases hend with ⟨root, K, h2K⟩
    rcases
        induceComponentSupport_exists_adj_root_of_connected_compl_singleton
          (G := D) hconn K with
      ⟨u, huK, hur⟩
    rcases
        exists_ambient_spanning_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
          (G := D) K huK hur h2K hno hdegree with
      ⟨r, C, hC, hroot, hsupport_subset, hsupport_cover⟩
    exact
      ⟨r, C, hC, root, hroot,
        cycle_contact_eq_root_of_cutComponent_support
          (G := D) K C hroot hsupport_subset hsupport_cover⟩

/-- Componentwise deleted-end block production.  This handles disconnected
two-end deletions by applying the source-independent hanging-cycle theorem to
one connected component and mapping the resulting cycle back to the whole
deleted graph. -/
theorem deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_connectedComponent_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    (K : (deleteEdgeEndsGraph G p q).ConnectedComponent)
    (hno : Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hdegree_ge :
      forall z : {w : V | w ∉ ({p, q} : Set V)},
        2 <= (deleteEdgeEndsGraph G p q).degree z) :
    Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
      Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
        C.IsCycle ∧
          Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
            v ∈ C.support ∧
              (forall t : {w : V | w ∉ ({p, q} : Set V)},
                t ∈ C.support -> t ≠ v ->
                  G.Adj (t : V) p ∨ G.Adj (t : V) q) := by
  classical
  let D : SimpleGraph {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph G p q
  letI : Fintype K := K.supp.toFinite.fintype
  haveI : DecidableEq K := Classical.decEq K
  haveI : DecidableRel K.toSimpleGraph.Adj := Classical.decRel _
  have hnoK : Not (ContainsHomeomorphicTheta K.toSimpleGraph) := by
    intro htheta
    exact hno
      (ContainsHomeomorphicTheta.map
        K.toSimpleGraph_hom
        (by
          intro a b hab
          exact Subtype.ext hab)
        htheta)
  have hdegreeK : forall z : K, 2 <= K.toSimpleGraph.degree z := by
    intro z
    have hdeg_eq :
        D.degree (z : {w : V | w ∉ ({p, q} : Set V)}) =
          K.toSimpleGraph.degree z := by
      simpa [D] using
        connectedComponent_degree_eq (G := D) K z
    have hzdeg : 2 <= D.degree (z : {w : V | w ∉ ({p, q} : Set V)}) := by
      simpa [D] using hdegree_ge (z : {w : V | w ∉ ({p, q} : Set V)})
    omega
  rcases
      exists_hanging_cycle_of_connected_no_homeomorphicTheta_min_degree_two
        (D := K.toSimpleGraph) K.connected_toSimpleGraph hnoK hdegreeK with
    ⟨rK, CK, hCK, vK, hvK, hcontactK⟩
  let φ : K.toSimpleGraph →g D := K.toSimpleGraph_hom
  let CD : D.Walk (rK : {w : V | w ∉ ({p, q} : Set V)})
      (rK : {w : V | w ∉ ({p, q} : Set V)}) := CK.map φ
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    exact Subtype.ext hab
  have hCD : CD.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map (p := CK) (f := φ) hφ_inj hCK
  have hvD : (vK : {w : V | w ∉ ({p, q} : Set V)}) ∈ CD.support := by
    change (vK : {w : V | w ∉ ({p, q} : Set V)}) ∈ (CK.map φ).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨vK, hvK, rfl⟩
  have hcontactD :
      forall {t c : {w : V | w ∉ ({p, q} : Set V)}},
        t ∉ CD.support -> c ∈ CD.support -> D.Adj t c ->
          c = (vK : {w : V | w ∉ ({p, q} : Set V)}) := by
    intro t c ht hc htc
    change c ∈ (CK.map φ).support at hc
    rw [SimpleGraph.Walk.support_map] at hc
    rcases List.mem_map.mp hc with ⟨cK, hcK, rfl⟩
    have htK_supp : t ∈ K.supp :=
      K.mem_supp_of_adj_mem_supp cK.2 (by
        simpa [D] using htc.symm)
    let tK : K := ⟨t, htK_supp⟩
    have htK_not : tK ∉ CK.support := by
      intro htK
      exact ht (by
        change (tK : {w : V | w ∉ ({p, q} : Set V)}) ∈ (CK.map φ).support
        rw [SimpleGraph.Walk.support_map]
        exact List.mem_map.mpr ⟨tK, htK, rfl⟩)
    have htcK : K.toSimpleGraph.Adj tK cK := by
      simpa [D, tK] using htc
    exact congrArg Subtype.val (hcontactK htK_not hcK htcK)
  rcases
      deleteEdgeEndsGraph_noncut_attach_of_hanging_cycle_contact
        (G := G) hmin CD hCD hno hvD (by
          intro t c ht hc htc
          exact hcontactD ht hc (by simpa [D] using htc)) with
    ⟨v, hv, hattach⟩
  exact ⟨(rK : {w : V | w ∉ ({p, q} : Set V)}), CD, hCD, v, hv, hattach⟩

/-- Deleted-end block/cactus production with no connectedness hypothesis.
Every two-end deletion is nonempty under source minimum degree three; applying
the componentwise hanging-cycle theorem to any connected component supplies
the required non-cut-attachment cycle. -/
theorem deleteEdgeEndsGraph_exists_noncut_attach_cycle_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    (hno : Not (ContainsHomeomorphicTheta (deleteEdgeEndsGraph G p q)))
    (hdegree_ge :
      forall z : {w : V | w ∉ ({p, q} : Set V)},
        2 <= (deleteEdgeEndsGraph G p q).degree z) :
    Exists fun r : {w : V | w ∉ ({p, q} : Set V)} =>
      Exists fun C : (deleteEdgeEndsGraph G p q).Walk r r =>
        C.IsCycle ∧
          Exists fun v : {w : V | w ∉ ({p, q} : Set V)} =>
            v ∈ C.support ∧
              (forall t : {w : V | w ∉ ({p, q} : Set V)},
                t ∈ C.support -> t ≠ v ->
                  G.Adj (t : V) p ∨ G.Adj (t : V) q) := by
  classical
  let D : SimpleGraph {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph G p q
  letI : Nonempty {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin p q
  let z : {w : V | w ∉ ({p, q} : Set V)} :=
    Classical.choice inferInstance
  let K : D.ConnectedComponent := D.connectedComponentMk z
  exact
    deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_connectedComponent_no_homeomorphicTheta
      (G := G) hmin K (by simpa [D] using hno) (by
        intro t
        simpa [D] using hdegree_ge t)

/-- The proved Makarychev/Skopenkov block/cactus production theorem in the
reference-faithful non-cut-attachment form. -/
theorem deleteEdgeEnds_noncutAttachCycles_obstruction :
    DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u} := by
  intro V _ _ G _ _hG _hlarge hmin hno hdegree_ge p q hpq
  exact
    deleteEdgeEndsGraph_exists_noncut_attach_cycle_no_homeomorphicTheta
      (G := G) hmin (hno hpq) (hdegree_ge hpq)

/-- Under the standing no-theta hypotheses, the spanning-cycle target also
implies the non-cut-attachment cycle target.  A spanning cycle in a theta-free
deleted-end graph is chordless, hence exactly two-regular; minimum degree
three in the source then forces every cycle vertex except the chosen basepoint
to attach to one of the deleted endpoints. -/
theorem DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.of_spanningCycles
    (hcycles : DeleteEdgeEndsSpanningCyclesObstructionTheorem.{u}) :
    DeleteEdgeEndsNoncutAttachCyclesObstructionTheorem.{u} := by
  intro V _ _ G _ hG hlarge hmin hno hdegree_ge p q hpq
  classical
  rcases hcycles hG hlarge hmin hno hdegree_ge hpq with
    ⟨r, C, hC, hspanning⟩
  rcases
      deleteEdgeEndsGraph_noncut_attach_of_spanning_cycle_no_homeomorphicTheta
        (G := G) hmin C hC hspanning (hno hpq) with
    ⟨v, hv, hattach⟩
  exact ⟨r, C, hC, v, hv, hattach⟩
end FourColor

end Schematic.Math.GraphTheory
