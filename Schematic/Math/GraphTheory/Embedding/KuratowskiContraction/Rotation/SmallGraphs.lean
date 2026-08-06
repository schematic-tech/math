import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The rotation system on an edgeless graph.  Its dart type is empty, so the
node permutation and its orbit condition are vacuous. -/
noncomputable def edgelessRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ x y : V, ¬ G.Adj x y) :
    RotationSystem G where
  node := Equiv.refl (OrientedEdge G)
  node_tail := by
    intro _e
    rfl
  node_orbit_of_same_tail := by
    intro e _f _hef
    exact False.elim (h e.tail e.head e.adj)

theorem orientedEdge_isEmpty_of_edgeless
    {V : Type u} {G : SimpleGraph V}
    (h : ∀ x y : V, ¬ G.Adj x y) :
    IsEmpty (OrientedEdge G) :=
  ⟨fun e => h e.tail e.head e.adj⟩

/-- The edgeless case of the Kuratowski-to-rotation-system bridge. -/
theorem exists_eulerRotationSystem_of_edgeless
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ x y : V, ¬ G.Adj x y) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R := edgelessRotationSystem (G := G) h
  have hempty : IsEmpty (R.toHypermap).dual.Dart := by
    change IsEmpty (OrientedEdge G)
    exact orientedEdge_isEmpty_of_edgeless h
  letI : IsEmpty (R.toHypermap).dual.Dart := hempty
  exact ⟨R, Hypermap.eulerPlanar_of_isEmpty (R.toHypermap).dual⟩

/-- The first finite-size base case for the Kuratowski bridge. -/
theorem exists_eulerRotationSystem_of_card_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 1) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  haveI : Subsingleton V :=
    Fintype.card_le_one_iff_subsingleton.mp hcard
  exact exists_eulerRotationSystem_of_edgeless (G := G) (by
    intro x y hxy
    exact hxy.ne (Subsingleton.elim x y))

/-- The identity rotation system on a graph with at most one outgoing dart at
each vertex. -/
noncomputable def matchingRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (huniq : ∀ e f : OrientedEdge G, e.tail = f.tail -> e = f) :
    RotationSystem G where
  node := Equiv.refl (OrientedEdge G)
  node_tail := by
    intro _e
    rfl
  node_orbit_of_same_tail := by
    intro e f hef
    rw [huniq e f hef]
    exact PermReachable.refl (Equiv.refl (OrientedEdge G)) f

theorem unique_orientedEdge_of_neighbor_unique
    {V : Type u} {G : SimpleGraph V}
    (huniq : ∀ x y z : V, G.Adj x y -> G.Adj x z -> y = z) :
    ∀ e f : OrientedEdge G, e.tail = f.tail -> e = f := by
  intro e f htail
  apply Subtype.ext
  rcases e with ⟨⟨et, eh⟩, he⟩
  rcases f with ⟨⟨ft, fh⟩, hf⟩
  simp [OrientedEdge.tail] at htail ⊢
  subst ft
  have hhead : eh = fh := huniq et eh fh he hf
  subst fh
  simp

/-- The matching/maximum-degree-one case of the Kuratowski bridge. -/
theorem exists_eulerRotationSystem_of_neighbor_unique
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (huniq : ∀ x y z : V, G.Adj x y -> G.Adj x z -> y = z) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let R := matchingRotationSystem (G := G)
    (unique_orientedEdge_of_neighbor_unique huniq)
  have hplain : (R.toHypermap).dual.Plain := R.toHypermap_dual_plain
  have hnode : (R.toHypermap).dual.node = (R.toHypermap).dual.edge := by
    rfl
  have hface : (R.toHypermap).dual.face =
      Equiv.refl (R.toHypermap).dual.Dart := by
    rfl
  exact ⟨R, Hypermap.eulerPlanar_of_plain_node_eq_edge_face_eq_refl
    (G := (R.toHypermap).dual) hplain hnode hface⟩

theorem neighbor_unique_of_degree_le_one
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 1) :
    ∀ x y z : V, G.Adj x y -> G.Adj x z -> y = z := by
  classical
  intro x y z hxy hxz
  by_contra hyz
  have hpair_sub :
      ({y, z} : Set V) ⊆ G.neighborSet x := by
    intro w hw
    rcases hw with rfl | hw
    · exact hxy
    · have hwz : w = z := Set.mem_singleton_iff.mp hw
      simpa [hwz] using hxz
  have hpair_ncard : ({y, z} : Set V).ncard = 2 := by
    simp [hyz]
  have hle :
      ({y, z} : Set V).ncard <= (G.neighborSet x).ncard :=
    Set.ncard_le_ncard hpair_sub
  have hdegree_ncard :
      (G.neighborSet x).ncard = G.degree x := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := x))
  have hdegx : G.degree x <= 1 := hdegree x
  rw [hpair_ncard, hdegree_ncard] at hle
  omega

/-- Local uniqueness at a degree-at-most-one vertex. -/
theorem neighbor_eq_of_degree_le_one_of_adj
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w x : V}
    (hdegree : G.degree v <= 1)
    (hvw : G.Adj v w)
    (hvx : G.Adj v x) :
    x = w := by
  classical
  have hpos : 0 < G.degree v :=
    (G.degree_pos_iff_exists_adj v).mpr ⟨w, hvw⟩
  have hdeg : G.degree v = 1 := by omega
  rcases (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hdeg with
    ⟨y, _hvy, hyuniq⟩
  exact (hyuniq x hvx).trans (hyuniq w hvw).symm

/-- Rotation-system base case for graphs of maximum degree at most one.  This
packages the low-degree branch of the Makarychev/Skopenkov induction at the
actual Euler-rotation-system boundary. -/
theorem exists_eulerRotationSystem_of_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 1) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_neighbor_unique
    (G := G) (neighbor_unique_of_degree_le_one hdegree)

theorem neighbor_unique_of_card_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V}
    (hcard : Fintype.card V ≤ 2) :
    ∀ x y z : V, G.Adj x y -> G.Adj x z -> y = z := by
  intro x y z hxy hxz
  by_contra hyz
  let f : Fin 3 → V
    | 0 => x
    | 1 => y
    | 2 => z
  have hfinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
    · exact False.elim (hxy.ne hab)
    · exact False.elim (hxz.ne hab)
    · exact False.elim (hxy.ne hab.symm)
    · exact False.elim (hyz hab)
    · exact False.elim (hxz.ne hab.symm)
    · exact False.elim (hyz hab.symm)
  have hle : Fintype.card (Fin 3) ≤ Fintype.card V :=
    Fintype.card_le_of_injective f hfinj
  simp at hle
  omega

/-- The two-vertex base case of the Kuratowski bridge. -/
theorem exists_eulerRotationSystem_of_card_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 2) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_neighbor_unique
    (G := G) (neighbor_unique_of_card_le_two hcard)

/-- A graph on at most three vertices has maximum degree at most two. -/
theorem degree_le_two_of_card_le_three
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V ≤ 3) :
    forall v : V, G.degree v <= 2 := by
  classical
  intro v
  let C : G.ConnectedComponent := G.connectedComponentMk v
  have hvC : v ∈ C.supp := by
    simp [C]
  have hCcard : C.supp.ncard <= 3 := by
    have hsub : C.supp ⊆ Set.univ := by
      intro x _hx
      exact Set.mem_univ x
    have hle : C.supp.ncard <= (Set.univ : Set V).ncard :=
      Set.ncard_le_ncard hsub
    have huniv : (Set.univ : Set V).ncard = Fintype.card V := by
      simp
    omega
  exact
    degree_le_two_of_mem_component_ncard_le_three
      (G := G) C hvC hCcard

/-- If a finite type has at most four vertices, the complement of a distinct
pair has at most two vertices. -/
theorem pair_compl_ncard_le_two_of_card_le_four
    {V : Type u} [Fintype V] {u v : V}
    (hcard : Fintype.card V <= 4)
    (huv : u ≠ v) :
    ({u, v} : Set V)ᶜ.ncard <= 2 := by
  classical
  let S : Set V := ({u, v} : Set V)
  have hpair : S.ncard = 2 := by
    simpa [S] using Set.ncard_pair huv
  have hsum :
      S.ncard + Sᶜ.ncard = Fintype.card V := by
    simpa [S, Set.ncard_univ] using Set.ncard_add_ncard_compl S
  have hsum_pair :
      2 + ({u, v} : Set V)ᶜ.ncard = Fintype.card V := by
    simpa [S, hpair] using hsum
  omega

/-- A non-complete graph on at most four vertices has a vertex of degree at
most two.  This is the graph-side reduction for the first small non-complete
branch; the complete four-vertex graph is the only remaining cyclic small
endpoint. -/
theorem exists_degree_le_two_of_card_le_four_of_not_complete
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 4)
    (hnot_complete : Not (forall u v : V, u ≠ v -> G.Adj u v)) :
    Exists fun v : V => G.degree v <= 2 := by
  classical
  by_contra hno
  push Not at hno
  have hcomplete : forall u v : V, u ≠ v -> G.Adj u v := by
    intro u v huv
    by_contra huv_not_adj
    have hsub : G.neighborSet u ⊆ ({u, v} : Set V)ᶜ := by
      intro w hw
      simp only [Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
      constructor
      · intro hwu
        have hloop : G.Adj u u := by
          subst w
          exact hw
        exact G.loopless.irrefl u hloop
      · intro hwv
        exact huv_not_adj (by simpa [hwv] using hw)
    have hneigh_le :
        (G.neighborSet u).ncard <= ({u, v} : Set V)ᶜ.ncard :=
      Set.ncard_le_ncard hsub
    have hcompl_le :
        ({u, v} : Set V)ᶜ.ncard <= 2 :=
      pair_compl_ncard_le_two_of_card_le_four
        (V := V) hcard huv
    have hdegree_ncard :
        (G.neighborSet u).ncard = G.degree u := by
      simpa [Set.ncard_eq_toFinset_card'] using
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := u))
    have hdegree_le : G.degree u <= 2 := by
      rw [← hdegree_ncard]
      exact hneigh_le.trans hcompl_le
    have hgt : 2 < G.degree u := hno u
    omega
  exact hnot_complete hcomplete
end FourColor

end Schematic.Math.GraphTheory
