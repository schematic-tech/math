import Schematic.Math.GraphTheory.Embedding.Kuratowski.CycleAttachments

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Two-connected branch of the block/cactus production.  If the deleted-end
graph `G - p - q` is already two-connected, then a cycle exists by the
minimum deleted-degree condition and spans by the theta-free block theorem;
the connected-cycle exit supplies the Makarychev/Skopenkov non-cut attachment
witness. -/
theorem deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    (h2 : IsTwoConnected (deleteEdgeEndsGraph G p q))
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
  letI : Nonempty {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin p q
  rcases
      exists_isCycle_of_nonempty_min_degree_two
        (G := deleteEdgeEndsGraph G p q) hdegree_ge with
    ⟨r, C, hC⟩
  have hspanning :
      C.toSubgraph.verts = Set.univ :=
    cycle_toSubgraph_verts_eq_univ_of_twoConnected_no_homeomorphicTheta
      (G := deleteEdgeEndsGraph G p q) h2 C hC hno
  rcases
      deleteEdgeEndsGraph_noncut_attach_of_spanning_cycle_no_homeomorphicTheta
        (G := G) hmin C hC hspanning hno with
    ⟨v, hv, hattach⟩
  exact ⟨r, C, hC, v, hv, hattach⟩

/-- Connected non-two-connected branch of the block/cut split for a two-end
deletion.  Minimum deleted degree at least two rules out the small-cardinality
failure of two-connectedness, so the failure supplies an actual cut vertex. -/
theorem deleteEdgeEndsGraph_exists_cutVertex_of_preconnected_not_twoConnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    (hconn : (deleteEdgeEndsGraph G p q).Preconnected)
    (hnot2 : ¬ IsTwoConnected (deleteEdgeEndsGraph G p q))
    (hdegree_ge :
      forall z : {w : V | w ∉ ({p, q} : Set V)},
        2 <= (deleteEdgeEndsGraph G p q).degree z) :
    Exists fun c : {w : V | w ∉ ({p, q} : Set V)} =>
      Not (((deleteEdgeEndsGraph G p q).induce
        ({c} : Set {w : V | w ∉ ({p, q} : Set V)})ᶜ).Connected) := by
  classical
  let D : SimpleGraph {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph G p q
  letI : Nonempty {w : V | w ∉ ({p, q} : Set V)} :=
    deleteEdgeEndsGraph_nonempty_of_min_degree_three (G := G) hmin p q
  have hD_connected : D.Connected := {
    preconnected := by
      simpa [D] using hconn
    nonempty := inferInstance
  }
  have hD_card : 2 < Nat.card {w : V | w ∉ ({p, q} : Set V)} :=
    natCard_gt_two_of_nonempty_min_degree_two
      (G := D) (by
        intro z
        simpa [D] using hdegree_ge z)
  exact
    not_isTwoConnected_exists_cutVertex_of_connected
      (G := D) hD_connected hD_card (by
        simpa [D] using hnot2)

/-- End-block branch before the full block tree is built.  If a component of
`G - root`, together with the cut vertex `root`, is already two-connected,
then the no-theta block theorem makes any cycle in it spanning.  The cycle
exists because every non-root vertex still has degree at least two inside this
induced subgraph. -/
theorem exists_spanning_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {root u : V}
    (K : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    (huK : u ∈ induceComponentSupport (G := G) K)
    (hur : G.Adj u root)
    (h2 :
      IsTwoConnected
        (G.induce (insert root (induceComponentSupport (G := G) K))))
    (hno : Not (ContainsHomeomorphicTheta G))
    (hdegree : forall v : V, 2 <= G.degree v) :
    Exists fun r :
        (insert root (induceComponentSupport (G := G) K) : Set V) =>
      Exists fun C :
          (G.induce (insert root (induceComponentSupport (G := G) K))).Walk r r =>
        C.IsCycle ∧ forall t :
          (insert root (induceComponentSupport (G := G) K) : Set V),
            t ∈ C.support := by
  classical
  let S : Set V := insert root (induceComponentSupport (G := G) K)
  letI : Fintype S := Subtype.fintype (fun x : V => x ∈ S)
  let rootH : S := ⟨root, by simp [S]⟩
  have hH_connected : (G.induce S).Connected := by
    simpa [S] using
      induceComponentSupport_insert_connected_of_adj
        (G := G) K huK hur
  have hne_root : Exists fun v : S => v ≠ rootH := by
    refine ⟨⟨u, ?_⟩, ?_⟩
    · exact Or.inr huK
    · intro h
      exact hur.ne (congrArg Subtype.val h)
  have hdegree_H :
      forall v : S, v ≠ rootH -> 2 <= (G.induce S).degree v := by
    intro v hvroot
    have hvK : (v : V) ∈ induceComponentSupport (G := G) K := by
      rcases v.2 with hroot | hK
      · exact False.elim (hvroot (Subtype.ext hroot))
      · exact hK
    have hneighbor_sub : G.neighborSet (v : V) ⊆ S := by
      intro w hvw
      by_cases hwroot : w = root
      · exact Or.inl hwroot
      · have hwA : w ∈ (({root} : Set V)ᶜ) := by
          simp [hwroot]
        exact Or.inr
          (induceComponentSupport_mem_of_adj
            (G := G) K hvK hwA hvw)
    have hdeg_eq : (G.induce S).degree v = G.degree (v : V) := by
      simpa [S] using
        SimpleGraph.degree_induce_of_neighborSet_subset
          (G := G) (s := S) (v := v) hneighbor_sub
    have hvdeg : 2 <= G.degree (v : V) := hdegree (v : V)
    omega
  rcases
      exists_isCycle_of_connected_min_degree_two_away_from_root
        (G := G.induce S) hH_connected hne_root hdegree_H with
    ⟨r, C, hC⟩
  have hnoH : Not (ContainsHomeomorphicTheta (G.induce S)) := by
    simpa [S] using
      not_containsHomeomorphicTheta_induce (G := G) S hno
  have h2H : IsTwoConnected (G.induce S) := by
    simpa [S] using h2
  have hspans : forall t : S, t ∈ C.support :=
    cycle_support_univ_of_twoConnected_no_homeomorphicTheta
      (G := G.induce S) h2H C hC hnoH
  exact ⟨r, C, hC, hspans⟩

/-- Ambient-graph form of
`exists_spanning_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta`.
The cycle is mapped out of the induced end component, and its support is
recorded exactly as the component support plus the root. -/
theorem exists_ambient_spanning_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {root u : V}
    (K : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    (huK : u ∈ induceComponentSupport (G := G) K)
    (hur : G.Adj u root)
    (h2 :
      IsTwoConnected
        (G.induce (insert root (induceComponentSupport (G := G) K))))
    (hno : Not (ContainsHomeomorphicTheta G))
    (hdegree : forall v : V, 2 <= G.degree v) :
    Exists fun r : V =>
      Exists fun C : G.Walk r r =>
        C.IsCycle ∧
          root ∈ C.support ∧
          (forall t : V,
            t ∈ C.support ->
              t ∈ insert root (induceComponentSupport (G := G) K)) ∧
          (forall t : V,
            t ∈ insert root (induceComponentSupport (G := G) K) ->
              t ∈ C.support) := by
  classical
  let S : Set V := insert root (induceComponentSupport (G := G) K)
  rcases
      exists_spanning_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
        (G := G) K huK hur h2 hno hdegree with
    ⟨rS, C₀, hC₀, hspan₀⟩
  let φ := (SimpleGraph.Embedding.induce (G := G) S).toHom
  let C : G.Walk (rS : V) (rS : V) := C₀.map φ
  have hφ_inj : Function.Injective φ :=
    (SimpleGraph.Embedding.induce (G := G) S).injective
  have hC : C.IsCycle := by
    exact SimpleGraph.Walk.IsCycle.map (p := C₀) (f := φ) hφ_inj hC₀
  have hsupport_subset :
      forall t : V, t ∈ C.support -> t ∈ S := by
    intro t ht
    change t ∈ (C₀.map φ).support at ht
    rw [SimpleGraph.Walk.support_map] at ht
    rcases List.mem_map.mp ht with ⟨z, _hz, rfl⟩
    exact z.2
  have hsupport_cover :
      forall t : V, t ∈ S -> t ∈ C.support := by
    intro t htS
    change t ∈ (C₀.map φ).support
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr
      ⟨(⟨t, htS⟩ : S), hspan₀ ⟨t, htS⟩, by simp [φ]⟩
  have hroot : root ∈ C.support :=
    hsupport_cover root (by simp [S])
  exact
    ⟨(rS : V), C, hC, hroot,
      (by
        intro t ht
        simpa [S] using hsupport_subset t ht),
      (by
        intro t ht
        exact hsupport_cover t (by simpa [S] using ht))⟩

/-- Component-separation contact lemma for an ambient end-component cycle.
If a cycle has exactly the support of one component of `G - root` together
with `root`, then any vertex outside the cycle can meet it only at `root`. -/
theorem cycle_contact_eq_root_of_cutComponent_support
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {root r : V}
    (K : (G.induce (({root} : Set V)ᶜ)).ConnectedComponent)
    (C : G.Walk r r)
    (hroot : root ∈ C.support)
    (hsupport_subset :
      forall t : V,
        t ∈ C.support ->
          t ∈ insert root (induceComponentSupport (G := G) K))
    (hsupport_cover :
      forall t : V,
        t ∈ insert root (induceComponentSupport (G := G) K) ->
          t ∈ C.support) :
    forall {t c : V}, t ∉ C.support -> c ∈ C.support ->
      G.Adj t c -> c = root := by
  classical
  intro t c ht_out hc htc
  by_cases hcroot : c = root
  · exact hcroot
  have hcK : c ∈ induceComponentSupport (G := G) K := by
    have hcS := hsupport_subset c hc
    rcases hcS with hcroot' | hcK
    · exact False.elim (hcroot hcroot')
    · exact hcK
  have htroot : t ≠ root := by
    intro htroot_eq
    exact ht_out (by simpa [htroot_eq] using hroot)
  have htA : t ∈ (({root} : Set V)ᶜ) := by
    simp [htroot]
  have htK : t ∈ induceComponentSupport (G := G) K :=
    induceComponentSupport_mem_of_adj
      (G := G) K hcK htA htc.symm
  exact False.elim (ht_out (hsupport_cover t (Or.inr htK)))

/-- Deleted-end end-component branch in the non-cut-attachment target form.
If a component of `(G - p - q) - root` plus `root` is two-connected, then the
ambient spanning cycle from that end component satisfies the hanging-cycle
contact predicate by component separation, hence supplies the
Makarychev/Skopenkov non-cut attachment witness. -/
theorem deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    {root u : {w : V | w ∉ ({p, q} : Set V)}}
    (K :
      ((deleteEdgeEndsGraph G p q).induce
        (({root} : Set {w : V | w ∉ ({p, q} : Set V)})ᶜ)).ConnectedComponent)
    (huK :
      u ∈ induceComponentSupport
        (G := deleteEdgeEndsGraph G p q) K)
    (hur : (deleteEdgeEndsGraph G p q).Adj u root)
    (h2 :
      IsTwoConnected
        ((deleteEdgeEndsGraph G p q).induce
          (insert root
            (induceComponentSupport
              (G := deleteEdgeEndsGraph G p q) K))))
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
  rcases
      exists_ambient_spanning_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
        (G := D) K huK hur h2 hno (by
          intro z
          simpa [D] using hdegree_ge z) with
    ⟨r, C, hC, hroot, hsupport_subset, hsupport_cover⟩
  have hcontact :
      forall {t c : {w : V | w ∉ ({p, q} : Set V)}},
        t ∉ C.support -> c ∈ C.support ->
          (deleteEdgeEndsGraph G p q).Adj t c -> c = root := by
    intro t c ht hc htc
    exact
      cycle_contact_eq_root_of_cutComponent_support
        (G := D) K C hroot
        (by
          intro z hz
          simpa [D] using hsupport_subset z hz)
        (by
          intro z hz
          exact hsupport_cover z (by simpa [D] using hz))
        ht hc (by simpa [D] using htc)
  rcases
      deleteEdgeEndsGraph_noncut_attach_of_hanging_cycle_contact
        (G := G) hmin C hC hno hroot hcontact with
    ⟨v, hv, hattach⟩
  exact ⟨r, C, hC, v, hv, hattach⟩

/-- Connected deleted-end wrapper for the two-connected end-component branch:
in a connected deleted graph, every component after removing `root` has an
edge back to `root`, so the previous theorem needs only the component and the
two-connectedness of that component plus `root`. -/
theorem deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_connected_cutComponent_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    (hconn : (deleteEdgeEndsGraph G p q).Connected)
    {root : {w : V | w ∉ ({p, q} : Set V)}}
    (K :
      ((deleteEdgeEndsGraph G p q).induce
        (({root} : Set {w : V | w ∉ ({p, q} : Set V)})ᶜ)).ConnectedComponent)
    (h2 :
      IsTwoConnected
        ((deleteEdgeEndsGraph G p q).induce
          (insert root
            (induceComponentSupport
              (G := deleteEdgeEndsGraph G p q) K))))
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
  rcases
      induceComponentSupport_exists_adj_root_of_connected_compl_singleton
        (G := D) (by simpa [D] using hconn) K with
    ⟨u, huK, hur⟩
  exact
    deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_cutComponent_twoConnected_no_homeomorphicTheta
      (G := G) hmin K huK (by simpa [D] using hur) h2 hno hdegree_ge

/-- Packaged block/cactus exit once the finite block descent supplies either
the whole deleted graph as a two-connected block or a two-connected end
component. -/
theorem deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_twoConnected_or_cutComponent_twoConnected_no_homeomorphicTheta
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {p q : V}
    (hconn : (deleteEdgeEndsGraph G p q).Connected)
    (halt :
      IsTwoConnected (deleteEdgeEndsGraph G p q) ∨
        Exists fun root : {w : V | w ∉ ({p, q} : Set V)} =>
          Exists fun K :
            ((deleteEdgeEndsGraph G p q).induce
              (({root} : Set {w : V | w ∉ ({p, q} : Set V)})ᶜ)).ConnectedComponent =>
            IsTwoConnected
              ((deleteEdgeEndsGraph G p q).induce
                (insert root
                  (induceComponentSupport
                    (G := deleteEdgeEndsGraph G p q) K))))
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
  rcases halt with h2 | hend
  · exact
      deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_twoConnected_no_homeomorphicTheta
        (G := G) hmin h2 hno hdegree_ge
  · rcases hend with ⟨root, K, h2K⟩
    exact
      deleteEdgeEndsGraph_exists_noncut_attach_cycle_of_connected_cutComponent_twoConnected_no_homeomorphicTheta
        (G := G) hmin hconn K h2K hno hdegree_ge
end FourColor

end Schematic.Math.GraphTheory
