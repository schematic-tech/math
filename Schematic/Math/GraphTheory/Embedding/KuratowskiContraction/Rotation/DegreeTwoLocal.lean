import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.SmallGraphs

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem edgeFinset_card_le_support_card_of_degree_le_two
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2) :
    G.edgeFinset.card <= Fintype.card G.support := by
  classical
  have hsum_le :
      (∑ v ∈ G.support, G.degree v) <=
        (∑ v ∈ G.support, (2 : ℕ)) := by
    exact Finset.sum_le_sum (by
      intro v hv
      exact hdegree v)
  rw [G.sum_degrees_support_eq_twice_card_edges] at hsum_le
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum_le
  have hle_toFinset : G.edgeFinset.card <= G.support.toFinset.card := by
    have htwice :
        2 * G.edgeFinset.card <= 2 * G.support.toFinset.card := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_le
    exact le_of_mul_le_mul_left htwice (by decide : 0 < 2)
  simpa [Set.toFinset_card] using hle_toFinset

/-- A sharpened handshaking estimate for a maximum-degree-two graph with at
least one supported endpoint.  It is the Euler-count input for path components:
one degree-at-most-one support vertex removes one edge from the cycle bound. -/
theorem edgeFinset_card_add_one_le_support_card_of_degree_le_two_of_exists_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hexists : Exists fun x : G.support => G.degree (x : V) <= 1) :
    G.edgeFinset.card + 1 <= Fintype.card G.support := by
  classical
  rcases hexists with ⟨x, hxdegree⟩
  let S : Finset V := G.support.toFinset
  have hxS : (x : V) ∈ S := by
    simp [S, x.property]
  have hsum_le :
      (∑ v ∈ S, G.degree v) <=
        1 + ∑ v ∈ (S.erase (x : V)), (2 : ℕ) := by
    rw [← Finset.add_sum_erase S (fun v => G.degree v) hxS]
    exact Nat.add_le_add hxdegree (Finset.sum_le_sum (by
      intro v _hv
      exact hdegree v))
  have hsum_graph :
      (∑ v ∈ S, G.degree v) = 2 * G.edgeFinset.card := by
    simpa [S] using G.sum_degrees_support_eq_twice_card_edges
  rw [hsum_graph] at hsum_le
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum_le
  have hsum_le' :
      2 * G.edgeFinset.card <= 1 + 2 * (S.erase (x : V)).card := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum_le
  have hm_le_erase : G.edgeFinset.card <= (S.erase (x : V)).card := by
    omega
  have hcard : S.card = (S.erase (x : V)).card + 1 := by
    have h := Finset.card_erase_add_one hxS
    omega
  have hle_toFinset : G.edgeFinset.card + 1 <= S.card := by
    omega
  simpa [S, Set.toFinset_card] using hle_toFinset

/-- If a vertex has degree at least two and one neighbour is fixed, it has a
second, distinct neighbour.  This is the branch point for the degree-two
uncontraction/subdivision lift. -/
theorem exists_neighbor_ne_of_two_le_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hdegree : 2 <= G.degree v) :
    Exists fun u : V => G.Adj v u ∧ u ≠ w := by
  classical
  by_contra hno
  have hsub : G.neighborSet v ⊆ ({w} : Set V) := by
    intro u hu
    by_contra huw
    exact hno ⟨u, hu, huw⟩
  have hle :
      (G.neighborSet v).ncard <= ({w} : Set V).ncard :=
    Set.ncard_le_ncard hsub
  have hdegree_ncard :
      (G.neighborSet v).ncard = G.degree v := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v))
  rw [hdegree_ncard] at hle
  simp at hle
  omega

/-- At a vertex of degree at most two, once one neighbour is fixed, there is at
most one other neighbour.  This is the local combinatorial fact needed to make
the degree-two rotation at a vertex an involution. -/
theorem neighbor_other_unique_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {x y z t : V}
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hxt : G.Adj x t)
    (hyz : y ≠ z) (hyt : y ≠ t) :
    z = t := by
  classical
  by_contra hzt
  have htriple_sub :
      ({y, z, t} : Set V) ⊆ G.neighborSet x := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxy
    · exact hxz
    · exact hxt
  have htriple_ncard : ({y, z, t} : Set V).ncard = 3 := by
    simp [hyz, hyt, hzt]
  have hle :
      ({y, z, t} : Set V).ncard <= (G.neighborSet x).ncard :=
    Set.ncard_le_ncard htriple_sub
  have hdegree_ncard :
      (G.neighborSet x).ncard = G.degree x := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := x))
  have hdegx : G.degree x <= 2 := hdegree x
  rw [htriple_ncard, hdegree_ncard] at hle
  omega

/-- Local degree-two data at a vertex: if `v` is not degree at most one and
has a fixed neighbour `w`, then it has a second neighbour `u`, and every
neighbour of `v` is one of `w,u`. -/
theorem exists_second_neighbor_and_neighbor_eq_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hupper : G.degree v <= 2)
    (hlower : ¬ G.degree v <= 1)
    (hvw : G.Adj v w) :
    Exists fun u : V =>
      G.Adj v u ∧ u ≠ w ∧
        forall t : V, G.Adj v t -> t = w ∨ t = u := by
  classical
  have htwo : 2 <= G.degree v := by omega
  rcases exists_neighbor_ne_of_two_le_degree
      (G := G) (v := v) (w := w) htwo with
    ⟨u, hvu, huw⟩
  refine ⟨u, hvu, huw, ?_⟩
  intro t hvt
  by_cases htw : t = w
  · exact Or.inl htw
  · right
    by_contra htu
    have hsub : ({w, u, t} : Set V) ⊆ G.neighborSet v := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact hvw
      · exact hvu
      · exact hvt
    have htriple_ncard : ({w, u, t} : Set V).ncard = 3 := by
      have hwu : w ≠ u := huw.symm
      have hwt : w ≠ t := by
        intro h
        exact htw h.symm
      have hut : u ≠ t := by
        intro h
        exact htu h.symm
      simp [hwu, hwt, hut]
    have hle :
        ({w, u, t} : Set V).ncard <= (G.neighborSet v).ncard :=
      Set.ncard_le_ncard hsub
    have hdegree_ncard :
        (G.neighborSet v).ncard = G.degree v := by
      simpa [Set.ncard_eq_toFinset_card'] using
        (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v))
    rw [htriple_ncard, hdegree_ncard] at hle
    omega

theorem orientedEdge_eq_of_tail_head
    {V : Type u} {G : SimpleGraph V}
    {e f : OrientedEdge G}
    (htail : e.tail = f.tail)
    (hhead : e.head = f.head) :
    e = f := by
  cases e with
  | mk e he =>
      cases f with
      | mk f hf =>
          cases e
          cases f
          simp [OrientedEdge.tail, OrientedEdge.head] at htail hhead ⊢
          exact ⟨htail, hhead⟩

theorem orientedEdge_head_ne_of_ne_same_tail
    {V : Type u} {G : SimpleGraph V}
    {e f : OrientedEdge G}
    (htail : e.tail = f.tail)
    (hne : e ≠ f) :
    e.head ≠ f.head := by
  intro hhead
  exact hne (orientedEdge_eq_of_tail_head htail hhead)

/-- At a vertex of degree at most three, a rotation-system node orbit links
any two distinct outgoing darts in one forward or backward node step. -/
theorem RotationSystem.node_permLink_of_same_tail_degree_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    {x : V}
    (hdeg : G.degree x <= 3)
    {e f : OrientedEdge G}
    (he : e.tail = x)
    (hf : f.tail = x)
    (hne : e ≠ f) :
    PermLink R.node e f := by
  classical
  have hef_tail : e.tail = f.tail := he.trans hf.symm
  by_cases hnode_eq_f : R.node e = f
  · simpa [hnode_eq_f] using (PermLink.forward (σ := R.node) e)
  have hnode_ne_e : R.node e ≠ e := by
    intro hfix
    have hreach : PermReachable R.node e f :=
      R.node_orbit_of_same_tail e f hef_tail
    have hf_eq_e : f = e :=
      permReachable_eq_of_apply_eq_self hfix hreach
    exact hne hf_eq_e.symm
  have hef_head : e.head ≠ f.head :=
    orientedEdge_head_ne_of_ne_same_tail hef_tail hne
  have hnode_tail_f : (R.node e).tail = f.tail :=
    (R.node_tail e).trans hef_tail
  have hnode_head_ne_e : (R.node e).head ≠ e.head :=
    orientedEdge_head_ne_of_ne_same_tail (R.node_tail e) hnode_ne_e
  have hnode_head_ne_f : (R.node e).head ≠ f.head := by
    intro hhead
    exact hnode_eq_f
      (orientedEdge_eq_of_tail_head hnode_tail_f hhead)
  have hnode_tail_x : (R.node e).tail = x :=
    (R.node_tail e).trans he
  have hsub :
      G.neighborSet x ⊆ ({e.head, f.head, (R.node e).head} : Set V) := by
    exact
      neighborSet_subset_triple_of_degree_le_three
        (G := G) (u := x) (a := e.head) (b := f.head)
        (c := (R.node e).head) hdeg
        (by simpa [he] using e.adj)
        (by simpa [hf] using f.adj)
        (by simpa [hnode_tail_x] using (R.node e).adj)
        hef_head hnode_head_ne_e.symm hnode_head_ne_f.symm
  have hnodef_tail_x : (R.node f).tail = x :=
    (R.node_tail f).trans hf
  have hnodef_mem :
      (R.node f).head ∈ ({e.head, f.head, (R.node e).head} : Set V) := by
    exact hsub (by simpa [hnodef_tail_x] using (R.node f).adj)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnodef_mem
  rcases hnodef_mem with hhead_e | hhead_f | hhead_nodee
  · have hnodef_eq_e : R.node f = e :=
      orientedEdge_eq_of_tail_head
        ((R.node_tail f).trans (hf.trans he.symm)) hhead_e
    have hsymm : R.node.symm e = f := by
      rw [← hnodef_eq_e]
      simp
    simpa [hsymm] using (PermLink.backward (σ := R.node) e)
  · have hnodef_eq_f : R.node f = f :=
      orientedEdge_eq_of_tail_head (R.node_tail f) hhead_f
    have hreach : PermReachable R.node f e :=
      R.node_orbit_of_same_tail f e hef_tail.symm
    have he_eq_f : e = f :=
      permReachable_eq_of_apply_eq_self hnodef_eq_f hreach
    exact False.elim (hne he_eq_f)
  · have hnodef_eq_nodee : R.node f = R.node e :=
      orientedEdge_eq_of_tail_head
        ((R.node_tail f).trans (hf.trans hnode_tail_x.symm))
        hhead_nodee
    have hf_eq_e : f = e := R.node.injective hnodef_eq_nodee
    exact False.elim (hne hf_eq_e.symm)

/-- If the rotation at the common head sends `e.symm` forward to `f.symm`,
then the face containing the corresponding side of the two-edge wedge has
one dart based at `e.tail` and one dart based at `f.tail`. -/
theorem RotationSystem.exists_faceReachable_endpointDarts_of_node_apply_symm_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hnode : R.node e.symm = f.symm) :
    Exists fun p : OrientedEdge G =>
      Exists fun q : OrientedEdge G =>
        p.tail = e.tail ∧ q.tail = f.tail ∧
          PermReachable (R.toHypermap).face p q := by
  classical
  let p : OrientedEdge G := (R.toHypermap).face e.symm
  have hp : p.tail = e.tail := by
    simp [p]
  have hface_f : (R.toHypermap).face f = e.symm := by
    change R.node.symm f.symm = e.symm
    rw [← hnode]
    simp
  have hreach_f_p : PermReachable (R.toHypermap).face f p := by
    have h₁ : PermReachable (R.toHypermap).face f e.symm := by
      rw [← hface_f]
      exact PermReachable.forward (R.toHypermap).face f
    have h₂ : PermReachable (R.toHypermap).face e.symm p := by
      exact PermReachable.forward (R.toHypermap).face e.symm
    exact PermReachable.trans (R.toHypermap).face h₁ h₂
  exact ⟨p, f, hp, rfl,
    PermReachable.symm (R.toHypermap).face hreach_f_p⟩

/-- Backward version of
`exists_faceReachable_endpointDarts_of_node_apply_symm_eq`. -/
theorem RotationSystem.exists_faceReachable_endpointDarts_of_node_apply_symm_eq'
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hnode : R.node f.symm = e.symm) :
    Exists fun p : OrientedEdge G =>
      Exists fun q : OrientedEdge G =>
        p.tail = e.tail ∧ q.tail = f.tail ∧
          PermReachable (R.toHypermap).face p q := by
  rcases
      R.exists_faceReachable_endpointDarts_of_node_apply_symm_eq
        (e := f) (f := e) hnode with
    ⟨p, q, hp, hq, hpq⟩
  exact ⟨q, p, hq, hp, PermReachable.symm (R.toHypermap).face hpq⟩

/-- A one-step node link between incoming darts at a common head produces
cofacial endpoint darts based at the two original tails. -/
theorem RotationSystem.exists_faceReachable_endpointDarts_of_node_permLink_symm
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    {e f : OrientedEdge G}
    (hlink : PermLink R.node e.symm f.symm) :
    Exists fun p : OrientedEdge G =>
      Exists fun q : OrientedEdge G =>
        p.tail = e.tail ∧ q.tail = f.tail ∧
          PermReachable (R.toHypermap).face p q := by
  rcases permLink_eq_or_eq_symm hlink with hforward | hbackward
  · exact
      R.exists_faceReachable_endpointDarts_of_node_apply_symm_eq
        (e := e) (f := f) hforward.symm
  · have hnode : R.node f.symm = e.symm := by
      rw [hbackward]
      simp
    exact
      R.exists_faceReachable_endpointDarts_of_node_apply_symm_eq'
        (e := e) (f := f) hnode

/-- Degree-at-most-three version of the local wedge/face fact. -/
theorem RotationSystem.exists_faceReachable_endpointDarts_of_same_head_degree_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G)
    {x : V}
    (hdeg : G.degree x <= 3)
    {e f : OrientedEdge G}
    (he : e.head = x)
    (hf : f.head = x)
    (hne : e ≠ f) :
    Exists fun p : OrientedEdge G =>
      Exists fun q : OrientedEdge G =>
        p.tail = e.tail ∧ q.tail = f.tail ∧
          PermReachable (R.toHypermap).face p q := by
  have hne_symm : e.symm ≠ f.symm := by
    intro h
    apply hne
    have h' := congrArg OrientedEdge.symm h
    simpa using h'
  have hlink :
      PermLink R.node e.symm f.symm :=
    R.node_permLink_of_same_tail_degree_le_three
      (x := x) hdeg (by simpa using he) (by simpa using hf) hne_symm
  exact R.exists_faceReachable_endpointDarts_of_node_permLink_symm hlink

/-- Oriented-edge version of
`neighbor_other_unique_of_degree_le_two`: at a degree-at-most-two vertex there
is at most one outgoing dart other than a fixed outgoing dart. -/
theorem orientedEdge_other_unique_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e f g : OrientedEdge G}
    (hef : f.tail = e.tail)
    (heg : g.tail = e.tail)
    (hfe : f ≠ e)
    (hge : g ≠ e) :
    f = g := by
  have htail : f.tail = g.tail := hef.trans heg.symm
  have hfe_head : e.head ≠ f.head :=
    orientedEdge_head_ne_of_ne_same_tail hef.symm (by
      intro h
      exact hfe h.symm)
  have hge_head : e.head ≠ g.head :=
    orientedEdge_head_ne_of_ne_same_tail heg.symm (by
      intro h
      exact hge h.symm)
  have hhead : f.head = g.head :=
    neighbor_other_unique_of_degree_le_two (G := G) hdegree
      (x := e.tail) (y := e.head) (z := f.head) (t := g.head)
      e.adj
      (by
        exact hef ▸ f.adj)
      (by
        exact heg ▸ g.adj)
      hfe_head hge_head
  exact orientedEdge_eq_of_tail_head htail hhead

/-- At a degree-at-most-two vertex, send an outgoing dart to the unique other
outgoing dart when it exists, and otherwise fix it. -/
noncomputable def orientedEdgeOtherOrSelfOfDegreeLeTwo
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (_hdegree : forall x : V, G.degree x <= 2)
    (e : OrientedEdge G) :
    OrientedEdge G :=
  if h : Exists fun f : OrientedEdge G => f.tail = e.tail ∧ f ≠ e then
    h.choose
  else
    e

theorem orientedEdgeOtherOrSelfOfDegreeLeTwo_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (e : OrientedEdge G) :
    (orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e).tail = e.tail := by
  classical
  unfold orientedEdgeOtherOrSelfOfDegreeLeTwo
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

theorem orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_of_same_tail_ne
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e f : OrientedEdge G}
    (hef : f.tail = e.tail)
    (hne : f ≠ e) :
    orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e = f := by
  classical
  unfold orientedEdgeOtherOrSelfOfDegreeLeTwo
  split_ifs with h
  · exact orientedEdge_other_unique_of_degree_le_two hdegree
      h.choose_spec.1 hef h.choose_spec.2 hne
  · exact False.elim (h ⟨f, hef, hne⟩)

theorem orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_self_of_no_other
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e : OrientedEdge G}
    (hno : Not (Exists fun f : OrientedEdge G => f.tail = e.tail ∧ f ≠ e)) :
    orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e = e := by
  classical
  unfold orientedEdgeOtherOrSelfOfDegreeLeTwo
  simp [hno]

theorem orientedEdgeOtherOrSelfOfDegreeLeTwo_involutive
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (e : OrientedEdge G) :
    orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree
      (orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e) = e := by
  classical
  by_cases h :
      Exists fun f : OrientedEdge G => f.tail = e.tail ∧ f ≠ e
  · have hother_tail :
        (orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e).tail = e.tail :=
      orientedEdgeOtherOrSelfOfDegreeLeTwo_tail hdegree e
    have hother_ne :
        orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e ≠ e := by
      unfold orientedEdgeOtherOrSelfOfDegreeLeTwo
      simp [h, h.choose_spec.2]
    exact orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_of_same_tail_ne hdegree
      hother_tail.symm hother_ne.symm
  · rw [orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_self_of_no_other hdegree h]
    exact orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_self_of_no_other hdegree h

/-- The degree-at-most-two node permutation: each vertex's two outgoing darts
are swapped, and a lone outgoing dart is fixed. -/
noncomputable def degreeLeTwoNode
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2) :
    Equiv.Perm (OrientedEdge G) where
  toFun := orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree
  invFun := orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree
  left_inv := orientedEdgeOtherOrSelfOfDegreeLeTwo_involutive hdegree
  right_inv := orientedEdgeOtherOrSelfOfDegreeLeTwo_involutive hdegree

@[simp]
theorem degreeLeTwoNode_apply
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (e : OrientedEdge G) :
    degreeLeTwoNode hdegree e =
      orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e :=
  rfl

theorem degreeLeTwoNode_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (e : OrientedEdge G) :
    (degreeLeTwoNode hdegree e).tail = e.tail :=
  orientedEdgeOtherOrSelfOfDegreeLeTwo_tail hdegree e

/-- The canonical rotation system for a graph of maximum degree at most two.
This is the constructive rotation object for paths and cycles; the remaining
bridge work is to prove the corresponding Euler-planarity count and to use the
same local two-dart swap in the degree-two uncontraction step. -/
noncomputable def degreeLeTwoRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2) :
    RotationSystem G where
  node := degreeLeTwoNode hdegree
  node_tail := degreeLeTwoNode_tail hdegree
  node_orbit_of_same_tail := by
    intro e f hef
    by_cases hfe : f = e
    · subst f
      exact PermReachable.refl (degreeLeTwoNode hdegree) e
    · have hnode :
          degreeLeTwoNode hdegree e = f := by
        exact orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_of_same_tail_ne
          hdegree hef.symm hfe
      rw [← hnode]
      exact PermReachable.forward (degreeLeTwoNode hdegree) e

@[simp]
theorem degreeLeTwoNode_symm
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2) :
    (degreeLeTwoNode hdegree).symm = degreeLeTwoNode hdegree := by
  apply Equiv.ext
  intro e
  rfl

theorem degreeLeTwoRotationSystem_toHypermap_face
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (e : OrientedEdge G) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face e =
      orientedEdgeOtherOrSelfOfDegreeLeTwo hdegree e.symm := by
  rfl

theorem degreeLeTwoRotationSystem_toHypermap_face_eq_symm_of_no_other_at_head
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e : OrientedEdge G}
    (hno :
      Not (Exists fun f : OrientedEdge G =>
        f.tail = e.head ∧ f ≠ e.symm)) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face e = e.symm := by
  rw [degreeLeTwoRotationSystem_toHypermap_face]
  exact orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_self_of_no_other
    hdegree hno

theorem no_other_orientedEdge_of_tail_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {e : OrientedEdge G}
    (hdegree : G.degree e.tail <= 1) :
    Not (Exists fun f : OrientedEdge G => f.tail = e.tail ∧ f ≠ e) := by
  classical
  rintro ⟨f, hf_tail, hf_ne⟩
  have hhead_ne : e.head ≠ f.head :=
    orientedEdge_head_ne_of_ne_same_tail hf_tail.symm (by
      intro h
      exact hf_ne h.symm)
  have hpair_sub :
      ({e.head, f.head} : Set V) ⊆ G.neighborSet e.tail := by
    intro z hz
    rcases hz with rfl | hz
    · exact e.adj
    · have hz' : z = f.head := Set.mem_singleton_iff.mp hz
      simpa [hz', hf_tail] using f.adj
  have hpair_ncard : ({e.head, f.head} : Set V).ncard = 2 := by
    simp [hhead_ne]
  have hle :
      ({e.head, f.head} : Set V).ncard <=
        (G.neighborSet e.tail).ncard :=
    Set.ncard_le_ncard hpair_sub
  have hdegree_ncard :
      (G.neighborSet e.tail).ncard = G.degree e.tail := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := e.tail))
  rw [hpair_ncard, hdegree_ncard] at hle
  omega

theorem degreeLeTwoRotationSystem_toHypermap_face_eq_symm_of_head_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e : OrientedEdge G}
    (hhead_degree : G.degree e.head <= 1) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face e = e.symm := by
  exact degreeLeTwoRotationSystem_toHypermap_face_eq_symm_of_no_other_at_head
    hdegree (no_other_orientedEdge_of_tail_degree_le_one
      (e := e.symm) hhead_degree)

theorem degreeLeTwoRotationSystem_face_reachable_symm_of_head_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e : OrientedEdge G}
    (hhead_degree : G.degree e.head <= 1) :
    PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      e e.symm := by
  rw [← degreeLeTwoRotationSystem_toHypermap_face_eq_symm_of_head_degree_le_one
    hdegree hhead_degree]
  exact PermReachable.forward
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face e

theorem degreeLeTwoRotationSystem_toHypermap_face_eq_of_other_at_head
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e f : OrientedEdge G}
    (hf_tail : f.tail = e.head)
    (hf_ne : f ≠ e.symm) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face e = f := by
  rw [degreeLeTwoRotationSystem_toHypermap_face]
  exact orientedEdgeOtherOrSelfOfDegreeLeTwo_eq_of_same_tail_ne
    hdegree hf_tail hf_ne

theorem degreeLeTwoRotationSystem_toHypermap_face_eq_path_step
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w)
    (huw : u ≠ w) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (⟨(u, v), huv⟩ : OrientedEdge G) =
      (⟨(v, w), hvw⟩ : OrientedEdge G) := by
  exact degreeLeTwoRotationSystem_toHypermap_face_eq_of_other_at_head
    hdegree (e := (⟨(u, v), huv⟩ : OrientedEdge G))
    (f := (⟨(v, w), hvw⟩ : OrientedEdge G)) rfl (by
      intro h
      have hhead : w = u := by
        have hpair := congrArg Subtype.val h
        exact Prod.ext_iff.mp hpair |>.2
      exact huw hhead.symm)

theorem degreeLeTwoRotationSystem_face_reachable_path_step
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w)
    (huw : u ≠ w) :
    PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      (⟨(u, v), huv⟩ : OrientedEdge G)
      (⟨(v, w), hvw⟩ : OrientedEdge G) := by
  rw [← degreeLeTwoRotationSystem_toHypermap_face_eq_path_step
    hdegree huv hvw huw]
  exact PermReachable.forward
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face
    (⟨(u, v), huv⟩ : OrientedEdge G)

theorem degreeLeTwoRotationSystem_toHypermap_face_eq_getVert_step
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    {i : ℕ} (hi : i + 2 <= p.length) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (⟨(p.getVert i, p.getVert (i + 1)),
          p.adj_getVert_succ (by omega)⟩ : OrientedEdge G) =
      (⟨(p.getVert (i + 1), p.getVert (i + 2)),
          p.adj_getVert_succ (i := i + 1) (by omega)⟩ :
        OrientedEdge G) := by
  refine degreeLeTwoRotationSystem_toHypermap_face_eq_path_step
    hdegree _ _ ?_
  intro hbad
  have hi0 : i < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hi2 : i + 2 < p.support.length := by
    rw [SimpleGraph.Walk.length_support]
    omega
  have hget :
      p.support[i]'hi0 = p.support[i + 2]'hi2 := by
    rw [SimpleGraph.Walk.support_getElem_eq_getVert,
      SimpleGraph.Walk.support_getElem_eq_getVert]
    exact hbad
  have hidx : i = i + 2 :=
    (List.Nodup.getElem_inj_iff hp.support_nodup).mp hget
  omega

theorem degreeLeTwoRotationSystem_face_reachable_getVert_step
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    {i : ℕ} (hi : i + 2 <= p.length) :
    PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      (⟨(p.getVert i, p.getVert (i + 1)),
        p.adj_getVert_succ (by omega)⟩ : OrientedEdge G)
      (⟨(p.getVert (i + 1), p.getVert (i + 2)),
        p.adj_getVert_succ (i := i + 1) (by omega)⟩ :
        OrientedEdge G) := by
  rw [← degreeLeTwoRotationSystem_toHypermap_face_eq_getVert_step
    hdegree p hp hi]
  exact PermReachable.forward
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face
    (⟨(p.getVert i, p.getVert (i + 1)),
      p.adj_getVert_succ (by omega)⟩ : OrientedEdge G)

theorem degreeLeTwoRotationSystem_face_reachable_getVert_of_le
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    {i j : ℕ} (hij : i <= j) (hj : j + 1 <= p.length) :
    PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      (⟨(p.getVert i, p.getVert (i + 1)),
        p.adj_getVert_succ (by omega)⟩ : OrientedEdge G)
      (⟨(p.getVert j, p.getVert (j + 1)),
        p.adj_getVert_succ (by omega)⟩ : OrientedEdge G) := by
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      exact PermReachable.refl
        ((degreeLeTwoRotationSystem hdegree).toHypermap).face _
  | succ j ih =>
      by_cases hij_eq : i = j + 1
      · subst i
        exact PermReachable.refl
          ((degreeLeTwoRotationSystem hdegree).toHypermap).face _
      · have hij_prev : i <= j := by omega
        have hj_prev : j + 1 <= p.length := by omega
        have hprev :=
          ih (i := i) hij_prev hj_prev
        have hlast :
            PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
              (⟨(p.getVert j, p.getVert (j + 1)),
                p.adj_getVert_succ (by omega)⟩ : OrientedEdge G)
              (⟨(p.getVert (j + 1), p.getVert ((j + 1) + 1)),
                p.adj_getVert_succ (i := j + 1) (by omega)⟩ :
        OrientedEdge G) :=
          degreeLeTwoRotationSystem_face_reachable_getVert_step
            hdegree p hp (i := j) (by omega)
        exact PermReachable.trans
          ((degreeLeTwoRotationSystem hdegree).toHypermap).face hprev hlast

theorem degreeLeTwoRotationSystem_face_reachable_first_to_reverse_last
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 0 < p.length)
    (hend_degree : G.degree v <= 1) :
    PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      (⟨(p.getVert 0, p.getVert 1),
        p.adj_getVert_succ hlen⟩ : OrientedEdge G)
      (OrientedEdge.symm
        (⟨(p.getVert (p.length - 1), p.getVert ((p.length - 1) + 1)),
        p.adj_getVert_succ (i := p.length - 1) (by omega)⟩ :
        OrientedEdge G)) := by
  let last : OrientedEdge G :=
    ⟨(p.getVert (p.length - 1), p.getVert ((p.length - 1) + 1)),
      p.adj_getVert_succ (i := p.length - 1) (by omega)⟩
  have hto_last :
      PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (⟨(p.getVert 0, p.getVert 1),
          p.adj_getVert_succ hlen⟩ : OrientedEdge G)
        last := by
    exact degreeLeTwoRotationSystem_face_reachable_getVert_of_le
      hdegree p hp (i := 0) (j := p.length - 1) (by omega) (by omega)
  have hlast_back :
      PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        last last.symm := by
    have hhead_degree : G.degree last.head <= 1 := by
      change G.degree (p.getVert ((p.length - 1) + 1)) <= 1
      have hidx : (p.length - 1) + 1 = p.length := by omega
      rw [hidx, SimpleGraph.Walk.getVert_length]
      exact hend_degree
    exact degreeLeTwoRotationSystem_face_reachable_symm_of_head_degree_le_one
      hdegree hhead_degree
  exact PermReachable.trans
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face hto_last hlast_back

/-- On a path component of the degree-at-most-two rotation system, the two
orientations of the first edge lie in the same face orbit.  This is the local
path-component face fact in the Kuratowski/rotation-system bridge: follow one
side of the path to the far end, turn around at the degree-one end, then follow
the reverse direction back to the initial edge. -/
theorem degreeLeTwoRotationSystem_face_reachable_first_to_reverse_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v : V}
    (p : G.Walk u v) (hp : p.IsPath)
    (hlen : 0 < p.length)
    (hend_degree : G.degree v <= 1) :
    PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      (⟨(p.getVert 0, p.getVert 1),
        p.adj_getVert_succ hlen⟩ : OrientedEdge G)
      (OrientedEdge.symm
        (⟨(p.getVert 0, p.getVert 1),
          p.adj_getVert_succ hlen⟩ : OrientedEdge G)) := by
  let first : OrientedEdge G :=
    ⟨(p.getVert 0, p.getVert 1), p.adj_getVert_succ hlen⟩
  let last : OrientedEdge G :=
    ⟨(p.getVert (p.length - 1), p.getVert ((p.length - 1) + 1)),
      p.adj_getVert_succ (i := p.length - 1) (by omega)⟩
  have hto_far :
      PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        first last.symm := by
    simpa [first, last] using
      degreeLeTwoRotationSystem_face_reachable_first_to_reverse_last
        hdegree p hp hlen hend_degree
  have hback_raw :
      PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (⟨(p.reverse.getVert 0, p.reverse.getVert 1),
          p.reverse.adj_getVert_succ (by
            rw [SimpleGraph.Walk.length_reverse]
            omega)⟩ : OrientedEdge G)
        (⟨(p.reverse.getVert (p.length - 1),
            p.reverse.getVert ((p.length - 1) + 1)),
          p.reverse.adj_getVert_succ (i := p.length - 1) (by
            rw [SimpleGraph.Walk.length_reverse]
            omega)⟩ : OrientedEdge G) := by
    exact degreeLeTwoRotationSystem_face_reachable_getVert_of_le
      hdegree p.reverse hp.reverse (i := 0) (j := p.length - 1)
      (by omega) (by rw [SimpleGraph.Walk.length_reverse]; omega)
  have hsource :
      (⟨(p.reverse.getVert 0, p.reverse.getVert 1),
          p.reverse.adj_getVert_succ (by
            rw [SimpleGraph.Walk.length_reverse]
            omega)⟩ : OrientedEdge G) = last.symm := by
    apply Subtype.ext
    have hlast_idx : (p.length - 1) + 1 = p.length := by omega
    simp [last, OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head,
      SimpleGraph.Walk.getVert_reverse, hlast_idx,
      SimpleGraph.Walk.getVert_length]
  have htarget :
      (⟨(p.reverse.getVert (p.length - 1),
          p.reverse.getVert ((p.length - 1) + 1)),
          p.reverse.adj_getVert_succ (i := p.length - 1) (by
            rw [SimpleGraph.Walk.length_reverse]
            omega)⟩ : OrientedEdge G) = first.symm := by
    apply Subtype.ext
    have hsub_one : p.length - (p.length - 1) = 1 := by omega
    have hsub_zero : p.length - ((p.length - 1) + 1) = 0 := by omega
    simp [first, OrientedEdge.symm, OrientedEdge.tail, OrientedEdge.head,
      SimpleGraph.Walk.getVert_reverse, hsub_one, hsub_zero]
  have hback :
      PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        last.symm first.symm := by
    rw [hsource, htarget] at hback_raw
    exact hback_raw
  simpa [first] using
    PermReachable.trans
      ((degreeLeTwoRotationSystem hdegree).toHypermap).face hto_far hback
end FourColor

end Schematic.Math.GraphTheory
