import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.EdgeInsertion
import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.FaceSplit


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- Choose an outgoing dart at a deleted-edge endpoint, when one exists.  This
is the graph-side splice point for the add-edge node insertion. -/
noncomputable def endpointPivot
    {V : Type u} (D : SimpleGraph V) (x : V) :
    Option (OrientedEdge D) := by
  classical
  exact
    if h : Exists fun e : OrientedEdge D => e.tail = x then
      some h.choose
    else
      none

theorem endpointPivot_spec_of_eq_some
    {V : Type u} {D : SimpleGraph V} {x : V} {e : OrientedEdge D}
    (h : endpointPivot D x = some e) :
    e.tail = x := by
  classical
  unfold endpointPivot at h
  by_cases h_exists : Exists fun e : OrientedEdge D => e.tail = x
  · simp [h_exists] at h
    simpa [h] using h_exists.choose_spec
  · simp [h_exists] at h

theorem endpointPivot_eq_none_iff
    {V : Type u} {D : SimpleGraph V} {x : V} :
    endpointPivot D x = none ↔
      ¬ Exists fun e : OrientedEdge D => e.tail = x := by
  classical
  unfold endpointPivot
  by_cases h : Exists fun e : OrientedEdge D => e.tail = x
  · simp [h]
  · simp [h]

theorem no_orientedEdge_tail_of_endpointPivot_eq_none
    {V : Type u} {D : SimpleGraph V} {x : V}
    (h : endpointPivot D x = none)
    (e : OrientedEdge D) :
    e.tail ≠ x := by
  intro he
  exact (endpointPivot_eq_none_iff.mp h) ⟨e, he⟩

noncomputable def addEdgePivotA
    {V : Type u} (G : SimpleGraph V) (a b : V) :
    Option (OrientedEdge (deletedGraph G a b)) :=
  endpointPivot (deletedGraph G a b) a

noncomputable def addEdgePivotB
    {V : Type u} (G : SimpleGraph V) (a b : V) :
    Option (OrientedEdge (deletedGraph G a b)) :=
  endpointPivot (deletedGraph G a b) b

theorem addEdgePivotA_spec_of_eq_some
    {V : Type u} {G : SimpleGraph V} {a b : V}
    {p : OrientedEdge (deletedGraph G a b)}
    (hp : addEdgePivotA G a b = some p) :
    p.tail = a :=
  endpointPivot_spec_of_eq_some hp

theorem addEdgePivotB_spec_of_eq_some
    {V : Type u} {G : SimpleGraph V} {a b : V}
    {p : OrientedEdge (deletedGraph G a b)}
    (hp : addEdgePivotB G a b = some p) :
    p.tail = b :=
  endpointPivot_spec_of_eq_some hp

theorem no_old_tail_a_of_addEdgePivotA_eq_none
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hp : addEdgePivotA G a b = none)
    (e : OrientedEdge (deletedGraph G a b)) :
    e.tail ≠ a :=
  no_orientedEdge_tail_of_endpointPivot_eq_none hp e

theorem no_old_tail_b_of_addEdgePivotB_eq_none
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hp : addEdgePivotB G a b = none)
    (e : OrientedEdge (deletedGraph G a b)) :
    e.tail ≠ b :=
  no_orientedEdge_tail_of_endpointPivot_eq_none hp e

theorem addEdgePivotA_exists_of_adj_ne_right
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b c : V}
    (hac : G.Adj a c)
    (hcb : c ≠ b) :
    Exists fun p : OrientedEdge (deletedGraph G a b) =>
      addEdgePivotA G a b = some p := by
  classical
  have hexists :
      Exists fun e : OrientedEdge (deletedGraph G a b) => e.tail = a := by
    refine ⟨⟨(a, c), ?_⟩, rfl⟩
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨hac, ?_⟩
    intro hmem
    have hs : s(a, c) = s(a, b) := by
      simpa using hmem
    have hcases :
        (a = a ∧ c = b) ∨ (a = b ∧ c = a) := by
      simpa [Sym2.eq_iff] using hs
    rcases hcases with ⟨_, hcb_eq⟩ | ⟨_, hca⟩
    · exact hcb hcb_eq
    · exact hac.ne hca.symm
  unfold addEdgePivotA endpointPivot
  simp [hexists]

theorem addEdgePivotB_exists_of_adj_ne_left
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b c : V}
    (hbc : G.Adj b c)
    (hca : c ≠ a) :
    Exists fun q : OrientedEdge (deletedGraph G a b) =>
      addEdgePivotB G a b = some q := by
  classical
  have hexists :
      Exists fun e : OrientedEdge (deletedGraph G a b) => e.tail = b := by
    refine ⟨⟨(b, c), ?_⟩, rfl⟩
    rw [deletedGraph, SimpleGraph.deleteEdges_adj]
    refine ⟨hbc, ?_⟩
    intro hmem
    have hs : s(b, c) = s(a, b) := by
      simpa using hmem
    have hcases :
        (b = a ∧ c = b) ∨ (b = b ∧ c = a) := by
      simpa [Sym2.eq_iff] using hs
    rcases hcases with ⟨_, hcb⟩ | ⟨_, hca_eq⟩
    · exact hbc.ne hcb.symm
    · exact hca hca_eq
  unfold addEdgePivotB endpointPivot
  simp [hexists]

theorem exists_adj_ne_right_of_two_le_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hdeg : 2 <= G.degree a) :
    Exists fun c : V => G.Adj a c ∧ c ≠ b := by
  classical
  by_contra hnot
  push Not at hnot
  have hsub : G.neighborFinset a ⊆ {b} := by
    intro c hc
    have hac : G.Adj a c := by
      simpa [SimpleGraph.mem_neighborFinset] using hc
    have hcb : c = b := hnot c hac
    simp [hcb]
  have hcard : G.degree a <= 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hsub).trans (by simp)
  omega

theorem addEdgePivotA_exists_of_two_le_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hdeg : 2 <= G.degree a) :
    Exists fun p : OrientedEdge (deletedGraph G a b) =>
      addEdgePivotA G a b = some p := by
  classical
  rcases exists_adj_ne_right_of_two_le_degree
      (G := G) (a := a) (b := b) hdeg with
    ⟨c, hac, hcb⟩
  exact addEdgePivotA_exists_of_adj_ne_right (G := G) (a := a) (b := b) hac hcb

theorem addEdgePivotB_exists_of_two_le_degree
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hdeg : 2 <= G.degree b) :
    Exists fun q : OrientedEdge (deletedGraph G a b) =>
      addEdgePivotB G a b = some q := by
  classical
  rcases exists_adj_ne_right_of_two_le_degree
      (G := G) (a := b) (b := a) hdeg with
    ⟨c, hbc, hca⟩
  exact addEdgePivotB_exists_of_adj_ne_left (G := G) (a := a) (b := b) hbc hca

/-- In the minimum-degree-three source branch, deleting any ordered pair leaves
both endpoint insertion pivots. For an existing edge, the remaining source
obligation is only the face/cofacial relation between these two pivots. -/
theorem addEdgePivots_exist_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    (a b : V) :
    Exists fun p : OrientedEdge (deletedGraph G a b) =>
      Exists fun q : OrientedEdge (deletedGraph G a b) =>
        addEdgePivotA G a b = some p ∧ addEdgePivotB G a b = some q := by
  classical
  rcases addEdgePivotA_exists_of_two_le_degree
      (G := G) (a := a) (b := b) (by
        have ha := hmin a
        omega) with
    ⟨p, hp⟩
  rcases addEdgePivotB_exists_of_two_le_degree
      (G := G) (a := a) (b := b) (by
        have hb := hmin b
        omega) with
    ⟨q, hq⟩
  exact ⟨p, q, hp, hq⟩

/-- Source-selected endpoint darts exist for every deleted vertex pair in the
minimum-degree-three branch. This is the pivot-choice-free form used by the
remaining cofacial source theorem. -/
theorem addEdgeEndpointDarts_exist_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    (a b : V) :
    Exists fun p : OrientedEdge (deletedGraph G a b) =>
      Exists fun q : OrientedEdge (deletedGraph G a b) =>
        p.tail = a ∧ q.tail = b := by
  classical
  rcases addEdgePivots_exist_of_min_degree_three
      (G := G) hmin a b with
    ⟨p, q, hp, hq⟩
  exact ⟨p, q, addEdgePivotA_spec_of_eq_some hp,
    addEdgePivotB_spec_of_eq_some hq⟩

theorem addEdgePivot_disjoint
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b) :
    forall p : OrientedEdge (deletedGraph G a b),
      addEdgePivotA G a b = some p ->
        addEdgePivotB G a b ≠ some p := by
  intro p hpA hpB
  have hpa : p.tail = a := addEdgePivotA_spec_of_eq_some hpA
  have hpb : p.tail = b := addEdgePivotB_spec_of_eq_some hpB
  have hab_eq : a = b := hpa.symm.trans hpb
  exact hab.ne hab_eq

noncomputable def addEdgeNode
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b)) :
    Equiv.Perm (ExtDart (OrientedEdge (deletedGraph G a b))) :=
  insertedEdgeNode R.node
    (addEdgePivotA G a b)
    (addEdgePivotB G a b)
    (addEdgePivot_disjoint hab)

theorem addEdgeNode_extTail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (x : ExtDart (OrientedEdge (deletedGraph G a b))) :
    extTail (G := G) a b (addEdgeNode (G := G) (a := a) (b := b) hab R x) =
      extTail (G := G) a b x := by
  classical
  cases x with
  | new =>
      cases hpA : addEdgePivotA G a b with
      | none =>
          simp [addEdgeNode, hpA, extTail]
      | some p =>
          simpa [addEdgeNode, hpA, extTail] using
            (R.node_tail p).trans (addEdgePivotA_spec_of_eq_some hpA)
  | newEdge =>
      cases hpB : addEdgePivotB G a b with
      | none =>
          simp [addEdgeNode, hpB, extTail]
      | some q =>
          simpa [addEdgeNode, hpB, extTail] using
            (R.node_tail q).trans (addEdgePivotB_spec_of_eq_some hpB)
  | old e =>
      cases hpA : addEdgePivotA G a b with
      | none =>
          cases hpB : addEdgePivotB G a b with
          | none =>
              simpa [addEdgeNode, hpA, hpB, extTail] using R.node_tail e
          | some q =>
              by_cases heq : e = q
              · subst e
                simp [addEdgeNode, hpA, hpB, extTail,
                  addEdgePivotB_spec_of_eq_some hpB]
              · simpa [addEdgeNode, hpA, hpB, heq, extTail] using
                  R.node_tail e
      | some p =>
          cases hpB : addEdgePivotB G a b with
          | none =>
              by_cases hep : e = p
              · subst e
                simp [addEdgeNode, hpA, hpB, extTail,
                  addEdgePivotA_spec_of_eq_some hpA]
              · simpa [addEdgeNode, hpA, hpB, hep, extTail] using
                  R.node_tail e
          | some q =>
              by_cases hep : e = p
              · subst e
                simp [addEdgeNode, hpA, hpB, extTail,
                  addEdgePivotA_spec_of_eq_some hpA]
              · by_cases heq : e = q
                · subst e
                  simp [addEdgeNode, hpA, hpB, hep, extTail,
                    addEdgePivotB_spec_of_eq_some hpB]
                · simpa [addEdgeNode, hpA, hpB, hep, heq, extTail] using
                    R.node_tail e

theorem addEdgeNode_reachable_of_same_extTail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    {x y : ExtDart (OrientedEdge (deletedGraph G a b))}
    (hxy : extTail (G := G) a b x = extTail (G := G) a b y) :
    PermReachable (addEdgeNode (G := G) (a := a) (b := b) hab R) x y := by
  classical
  cases x with
  | new =>
      cases y with
      | new =>
          exact PermReachable.refl _ ExtDart.new
      | newEdge =>
          have hab_eq : a = b := by simpa [extTail] using hxy
          exact False.elim (hab.ne hab_eq)
      | old f =>
          have haf : a = f.tail := by simpa [extTail] using hxy
          cases hpA : addEdgePivotA G a b with
          | none =>
              exact False.elim
                ((no_old_tail_a_of_addEdgePivotA_eq_none hpA f) haf.symm)
          | some p =>
              have hpf : p.tail = f.tail :=
                (addEdgePivotA_spec_of_eq_some hpA).trans haf
              have hR : PermReachable R.node p f :=
                R.node_orbit_of_same_tail p f hpf
              simpa [addEdgeNode] using
                insertedEdgeNode_new_reachable_old_of_permReachable_of_eq_some
                  R.node (addEdgePivotA G a b) (addEdgePivotB G a b)
                  (addEdgePivot_disjoint hab) hpA hR
  | newEdge =>
      cases y with
      | new =>
          have hba : b = a := by simpa [extTail] using hxy
          exact False.elim (hab.ne' hba)
      | newEdge =>
          exact PermReachable.refl _ ExtDart.newEdge
      | old f =>
          have hbf : b = f.tail := by simpa [extTail] using hxy
          cases hpB : addEdgePivotB G a b with
          | none =>
              exact False.elim
                ((no_old_tail_b_of_addEdgePivotB_eq_none hpB f) hbf.symm)
          | some q =>
              have hqf : q.tail = f.tail :=
                (addEdgePivotB_spec_of_eq_some hpB).trans hbf
              have hR : PermReachable R.node q f :=
                R.node_orbit_of_same_tail q f hqf
              simpa [addEdgeNode] using
                insertedEdgeNode_newEdge_reachable_old_of_permReachable_of_eq_some
                  R.node (addEdgePivotA G a b) (addEdgePivotB G a b)
                  (addEdgePivot_disjoint hab) hpB hR
  | old e =>
      cases y with
      | new =>
          have hea : e.tail = a := by simpa [extTail] using hxy
          cases hpA : addEdgePivotA G a b with
          | none =>
              exact False.elim
                ((no_old_tail_a_of_addEdgePivotA_eq_none hpA e) hea)
          | some p =>
              have hpe : p.tail = e.tail :=
                (addEdgePivotA_spec_of_eq_some hpA).trans hea.symm
              have hR : PermReachable R.node p e :=
                R.node_orbit_of_same_tail p e hpe
              exact
                PermReachable.symm
                  (addEdgeNode (G := G) (a := a) (b := b) hab R)
                  (by
                    simpa [addEdgeNode] using
                      insertedEdgeNode_new_reachable_old_of_permReachable_of_eq_some
                        R.node (addEdgePivotA G a b) (addEdgePivotB G a b)
                        (addEdgePivot_disjoint hab) hpA hR)
      | newEdge =>
          have heb : e.tail = b := by simpa [extTail] using hxy
          cases hpB : addEdgePivotB G a b with
          | none =>
              exact False.elim
                ((no_old_tail_b_of_addEdgePivotB_eq_none hpB e) heb)
          | some q =>
              have hqe : q.tail = e.tail :=
                (addEdgePivotB_spec_of_eq_some hpB).trans heb.symm
              have hR : PermReachable R.node q e :=
                R.node_orbit_of_same_tail q e hqe
              exact
                PermReachable.symm
                  (addEdgeNode (G := G) (a := a) (b := b) hab R)
                  (by
                    simpa [addEdgeNode] using
                      insertedEdgeNode_newEdge_reachable_old_of_permReachable_of_eq_some
                        R.node (addEdgePivotA G a b) (addEdgePivotB G a b)
                        (addEdgePivot_disjoint hab) hpB hR)
      | old f =>
          have hef : e.tail = f.tail := by simpa [extTail] using hxy
          have hR : PermReachable R.node e f :=
            R.node_orbit_of_same_tail e f hef
          simpa [addEdgeNode] using
            insertedEdgeNode_old_reachable_of_permReachable
              R.node (addEdgePivotA G a b) (addEdgePivotB G a b)
              (addEdgePivot_disjoint hab) hR

/-- Add a deleted edge back to any rotation system on the deleted graph.  This
only constructs the graph rotation system; the planar/Euler part still needs
the usual cofacial add-edge hypothesis. -/
noncomputable def addEdgeRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b)) :
    RotationSystem G :=
  rotationSystemOfExtNode (G := G) (a := a) (b := b) hab
    (addEdgeNode (G := G) (a := a) (b := b) hab R)
    (addEdgeNode_extTail (G := G) (a := a) (b := b) hab R)
    (fun _ _ hxy =>
      addEdgeNode_reachable_of_same_extTail
        (G := G) (a := a) (b := b) hab R hxy)

/-- Pure hypermap form of the deleted-edge add-back node insertion.  The
Euler-planarity theorem for the deletion branch will be proved on this
hypermap, then transported to `addEdgeRotationSystem`. -/
def addEdgeHypermap
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart)
    (hAB : forall p : H.Dart, pivotA = some p -> pivotB ≠ some p) :
    Hypermap.{u} where
  Dart := ExtDart H.Dart
  edge := ExtDart.Perm.edge H.edge
  node := insertedEdgeNode H.node pivotA pivotB hAB
  face := (ExtDart.Perm.edge H.edge).symm.trans
    (insertedEdgeNode H.node pivotA pivotB hAB).symm
  node_face_edge := by
    intro x
    simp [Equiv.trans_apply]

@[simp]
theorem addEdgeHypermap_edge
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart)
    (hAB : forall p : H.Dart, pivotA = some p -> pivotB ≠ some p)
    (x : (addEdgeHypermap H pivotA pivotB hAB).Dart) :
    (addEdgeHypermap H pivotA pivotB hAB).edge x =
      ExtDart.Perm.edge H.edge x :=
  rfl

@[simp]
theorem addEdgeHypermap_node
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart)
    (hAB : forall p : H.Dart, pivotA = some p -> pivotB ≠ some p)
    (x : (addEdgeHypermap H pivotA pivotB hAB).Dart) :
    (addEdgeHypermap H pivotA pivotB hAB).node x =
      insertedEdgeNode H.node pivotA pivotB hAB x :=
  rfl

@[simp]
theorem addEdgeHypermap_face
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart)
    (hAB : forall p : H.Dart, pivotA = some p -> pivotB ≠ some p)
    (x : (addEdgeHypermap H pivotA pivotB hAB).Dart) :
    (addEdgeHypermap H pivotA pivotB hAB).face x =
      (insertedEdgeNode H.node pivotA pivotB hAB).symm
        ((ExtDart.Perm.edge H.edge).symm x) :=
  rfl

theorem hypermap_edge_symm_eq_node_iff_eq_face_symm
    (H : Hypermap.{u}) (x p : H.Dart) :
    H.edge.symm x = H.node p ↔ x = H.face.symm p := by
  constructor
  · intro h
    calc
      x = H.edge (H.edge.symm x) := by simp
      _ = H.edge (H.node p) := by rw [h]
      _ = H.face.symm p := H.edge_node_eq_face_symm p
  · intro h
    rw [h, ← H.edge_node_eq_face_symm p]
    simp

theorem hypermap_node_symm_edge_symm_eq_face
    (H : Hypermap.{u}) (x : H.Dart) :
    H.node.symm (H.edge.symm x) = H.face x := by
  apply H.node.injective
  simpa using (H.node_face_edge (H.edge.symm x)).symm

theorem addEdgeHypermap_face_some_some_eq_splitFacePerm
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hpq : p ≠ q) :
    (addEdgeHypermap H (some p) (some q) hAB).face =
      splitFacePerm H.face p q hpq := by
  ext x
  cases x with
  | new =>
      change
        (insertedEdgeNode H.node (some p) (some q) hAB).symm
          ExtDart.newEdge = ExtDart.old q
      rfl
  | newEdge =>
      change
        (insertedEdgeNode H.node (some p) (some q) hAB).symm
          ExtDart.new = ExtDart.old p
      rfl
  | old x =>
      change
        (insertedEdgeNode H.node (some p) (some q) hAB).symm
          (ExtDart.old (H.edge.symm x)) =
          (if x = H.face.symm p then ExtDart.new
          else if x = H.face.symm q then ExtDart.newEdge
          else ExtDart.old (H.face x))
      by_cases hxp : x = H.face.symm p
      · subst x
        rw [← H.edge_node_eq_face_symm p]
        simp [insertedEdgeNode]
      · by_cases hxq : x = H.face.symm q
        · subst x
          have hnode_qp : H.node q ≠ H.node p := by
            intro h
            exact hpq ((H.node.injective h).symm)
          have hface_qp : H.edge (H.node q) ≠ H.face.symm p := by
            intro h
            exact hxp (by
              rw [← H.edge_node_eq_face_symm q]
              exact h)
          rw [← H.edge_node_eq_face_symm q]
          simp [insertedEdgeNode, hnode_qp, hface_qp]
        · have hpnode : H.edge.symm x ≠ H.node p := by
            intro h
            exact hxp
              ((hypermap_edge_symm_eq_node_iff_eq_face_symm H x p).mp h)
          have hqnode : H.edge.symm x ≠ H.node q := by
            intro h
            exact hxq
              ((hypermap_edge_symm_eq_node_iff_eq_face_symm H x q).mp h)
          simp [insertedEdgeNode, hxp, hxq, hpnode, hqnode,
            hypermap_node_symm_edge_symm_eq_face]

theorem addEdgeHypermap_face_apply_some_some
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hpq : p ≠ q)
    (x : (addEdgeHypermap H (some p) (some q) hAB).Dart) :
    (addEdgeHypermap H (some p) (some q) hAB).face x =
      splitFacePerm H.face p q hpq x := by
  rw [addEdgeHypermap_face_some_some_eq_splitFacePerm H p q hAB hpq]
  rfl

@[simp]
theorem addEdgeHypermap_card
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart)
    (hAB : forall p : H.Dart, pivotA = some p -> pivotB ≠ some p) :
    Fintype.card (addEdgeHypermap H pivotA pivotB hAB).Dart =
      Fintype.card H.Dart + 2 :=
  ExtDart.card

/-- Adding one graph edge contributes exactly one edge orbit to the pure
add-edge hypermap. -/
theorem addEdgeHypermap_edgeOrbitCount_of_basepoint
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart)
    (hAB : forall p : H.Dart, pivotA = some p -> pivotB ≠ some p)
    (x0 : H.Dart) :
    (addEdgeHypermap H pivotA pivotB hAB).edgeOrbitCount =
      H.edgeOrbitCount + 1 := by
  simpa [addEdgeHypermap, Hypermap.edgeOrbitCount, Hypermap.EdgeOrbit] using
    Hypermap.extensionN_edgeOrbitCount (G := H) x0

theorem addEdgeHypermap_nodeOrbitCount_some_some
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r) :
    (addEdgeHypermap H (some p) (some q) hAB).nodeOrbitCount =
      H.nodeOrbitCount := by
  unfold Hypermap.nodeOrbitCount
  change Nat.card (PermOrbit (insertedEdgeNode H.node (some p) (some q) hAB)) =
    Nat.card (PermOrbit H.node)
  exact insertedEdgeNodeSomeSome_nodeOrbitCount H.node p q hAB

theorem addEdgeHypermap_faceOrbitCount_some_some_of_reachable
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hreach : PermReachable H.face p q) :
    (addEdgeHypermap H (some p) (some q) hAB).faceOrbitCount =
      H.faceOrbitCount + 1 := by
  have hpq : p ≠ q := by
    intro hpq
    exact hAB p rfl (by simp [hpq])
  unfold Hypermap.faceOrbitCount
  change
    Nat.card (PermOrbit (addEdgeHypermap H (some p) (some q) hAB).face) =
      Nat.card (PermOrbit H.face) + 1
  rw [addEdgeHypermap_face_some_some_eq_splitFacePerm H p q hAB hpq]
  exact splitFacePerm_orbitCount_of_reachable H.face p q hreach hpq

/-- Cofacial add-edge hypothesis for the pure add-edge hypermap.  In the
minimum-degree deletion branch both endpoint pivots will be present; the
`none` cases are kept vacuous because those are leaf-like degeneracies handled
by separate low-degree branches. -/
def addEdgeCofacial
    (H : Hypermap.{u}) (pivotA pivotB : Option H.Dart) : Prop :=
  match pivotA, pivotB with
  | some p, some q => PermReachable H.face p q
  | _, _ => True

@[simp]
theorem addEdgeCofacial_none_left
    (H : Hypermap.{u}) (pivotB : Option H.Dart) :
    addEdgeCofacial H none pivotB := by
  cases pivotB <;> trivial

@[simp]
theorem addEdgeCofacial_none_right
    (H : Hypermap.{u}) (pivotA : Option H.Dart) :
    addEdgeCofacial H pivotA none := by
  cases pivotA <;> trivial

@[simp]
theorem addEdgeCofacial_some_some
    (H : Hypermap.{u}) (p q : H.Dart) :
    addEdgeCofacial H (some p) (some q) ↔
      PermReachable H.face p q :=
  Iff.rfl

theorem addEdgeHypermap_faceOrbitCount_some_some_of_cofacial
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hcofacial : addEdgeCofacial H (some p) (some q)) :
    (addEdgeHypermap H (some p) (some q) hAB).faceOrbitCount =
      H.faceOrbitCount + 1 :=
  addEdgeHypermap_faceOrbitCount_some_some_of_reachable H p q hAB
    ((addEdgeCofacial_some_some H p q).mp hcofacial)

theorem addEdgeHypermap_old_face_reachable_some_some
    (H : Hypermap.{u}) (p q x : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r) :
    (addEdgeHypermap H (some p) (some q) hAB).Reachable
      (ExtDart.old x) (ExtDart.old (H.face x)) := by
  let A := addEdgeHypermap H (some p) (some q) hAB
  have hpq : p ≠ q := by
    intro hpq
    exact hAB p rfl (by simp [hpq])
  by_cases hxp : x = H.face.symm p
  · subst x
    have h1 : A.Reachable (ExtDart.old (H.face.symm p)) ExtDart.new := by
      have h := A.reachable_face (ExtDart.old (H.face.symm p))
      change A.Reachable (ExtDart.old (H.face.symm p))
        (A.face (ExtDart.old (H.face.symm p))) at h
      rw [addEdgeHypermap_face_apply_some_some H p q hAB hpq] at h
      simpa [A, splitFacePerm_old] using h
    have h2 : A.Reachable ExtDart.new ExtDart.newEdge := by
      simpa [A, ExtDart.Perm.edge] using A.reachable_edge ExtDart.new
    have h3 : A.Reachable ExtDart.newEdge (ExtDart.old p) := by
      have h := A.reachable_face ExtDart.newEdge
      change A.Reachable ExtDart.newEdge (A.face ExtDart.newEdge) at h
      rw [addEdgeHypermap_face_apply_some_some H p q hAB hpq] at h
      simpa [A, splitFacePerm_newEdge] using h
    simpa using h1.trans (h2.trans h3)
  · by_cases hxq : x = H.face.symm q
    · subst x
      have h1 : A.Reachable (ExtDart.old (H.face.symm q)) ExtDart.newEdge := by
        have h := A.reachable_face (ExtDart.old (H.face.symm q))
        change A.Reachable (ExtDart.old (H.face.symm q))
          (A.face (ExtDart.old (H.face.symm q))) at h
        rw [addEdgeHypermap_face_apply_some_some H p q hAB hpq] at h
        have hqp : H.face.symm q ≠ H.face.symm p := by
          intro h
          exact hpq (H.face.symm.injective h).symm
        simpa [A, splitFacePerm_old, hqp] using h
      have h2 : A.Reachable ExtDart.newEdge ExtDart.new := by
        simpa [A, ExtDart.Perm.edge] using A.reachable_edge ExtDart.newEdge
      have h3 : A.Reachable ExtDart.new (ExtDart.old q) := by
        have h := A.reachable_face ExtDart.new
        change A.Reachable ExtDart.new (A.face ExtDart.new) at h
        rw [addEdgeHypermap_face_apply_some_some H p q hAB hpq] at h
        simpa [A, splitFacePerm_new] using h
      simpa using h1.trans (h2.trans h3)
    · have h := A.reachable_face (ExtDart.old x)
      change A.Reachable (ExtDart.old x) (A.face (ExtDart.old x)) at h
      rw [addEdgeHypermap_face_apply_some_some H p q hAB hpq] at h
      simpa [A, splitFacePerm_old, hxp, hxq] using h

theorem addEdgeHypermap_old_reachable_of_link_some_some
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    {x y : H.Dart}
    (hxy : H.Link x y) :
    (addEdgeHypermap H (some p) (some q) hAB).Reachable
      (ExtDart.old x) (ExtDart.old y) := by
  let A := addEdgeHypermap H (some p) (some q) hAB
  rcases hxy with hxy | hxy | hxy
  · subst y
    have h := A.reachable_edge (ExtDart.old x)
    simpa [A, ExtDart.Perm.edge] using h
  · subst y
    have hnode :
        PermReachable A.node (ExtDart.old x) (ExtDart.old (H.node x)) := by
      simpa [A] using
        (insertedEdgeNode_old_forward_reachable H.node (some p) (some q) hAB x)
    exact A.nodePermReachable_reachable hnode
  · subst y
    exact addEdgeHypermap_old_face_reachable_some_some H p q x hAB

theorem addEdgeHypermap_old_reachable_of_reachable_some_some
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    {x y : H.Dart}
    (hxy : H.Reachable x y) :
    (addEdgeHypermap H (some p) (some q) hAB).Reachable
      (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun _ _ h =>
    addEdgeHypermap_old_reachable_of_link_some_some H p q hAB h

def addEdgeHypermap_componentCode_some_some
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r) :
    (addEdgeHypermap H (some p) (some q) hAB).Dart -> H.Component
  | ExtDart.new => H.componentOf p
  | ExtDart.newEdge => H.componentOf q
  | ExtDart.old x => H.componentOf x

theorem addEdgeHypermap_componentCode_some_some_of_link
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hreach : PermReachable H.face p q)
    {x y : (addEdgeHypermap H (some p) (some q) hAB).Dart}
    (hxy : (addEdgeHypermap H (some p) (some q) hAB).Link x y) :
    addEdgeHypermap_componentCode_some_some H p q hAB x =
      addEdgeHypermap_componentCode_some_some H p q hAB y := by
  let A := addEdgeHypermap H (some p) (some q) hAB
  have hpq : p ≠ q := by
    intro hpq
    exact hAB p rfl (by simp [hpq])
  have hpq_comp : H.componentOf p = H.componentOf q :=
    H.componentOf_eq_componentOf (H.facePermReachable_reachable hreach)
  rcases hxy with hxy | hxy | hxy
  · subst y
    cases x with
    | new =>
        simp [addEdgeHypermap_componentCode_some_some, hpq_comp]
    | newEdge =>
        simp [addEdgeHypermap_componentCode_some_some, hpq_comp]
    | old x =>
        simp [addEdgeHypermap_componentCode_some_some]
        exact (H.componentOf_edge x).symm
  · subst y
    cases x with
    | new =>
        simp [addEdgeHypermap_componentCode_some_some]
        exact (H.componentOf_node p).symm
    | newEdge =>
        simp [addEdgeHypermap_componentCode_some_some]
        exact (H.componentOf_node q).symm
    | old x =>
        by_cases hxp : x = p
        · subst x
          simp [addEdgeHypermap_componentCode_some_some, insertedEdgeNode_apply]
        · by_cases hxq : x = q
          · subst x
            have hqp : q ≠ p := hpq.symm
            simp [addEdgeHypermap_componentCode_some_some,
              insertedEdgeNode_apply, hqp]
          · simp [addEdgeHypermap_componentCode_some_some,
              insertedEdgeNode_apply, hxp, hxq]
            exact (H.componentOf_node x).symm
  · subst y
    rw [addEdgeHypermap_face_apply_some_some H p q hAB hpq]
    cases x with
    | new =>
        simp [addEdgeHypermap_componentCode_some_some, splitFacePerm_new,
          hpq_comp]
    | newEdge =>
        simp [addEdgeHypermap_componentCode_some_some, splitFacePerm_newEdge,
          hpq_comp]
    | old x =>
        by_cases hxp : x = H.face.symm p
        · subst x
          simp [addEdgeHypermap_componentCode_some_some, splitFacePerm_old]
          simpa using (H.componentOf_face (H.face.symm p)).symm
        · by_cases hxq : x = H.face.symm q
          · subst x
            have hqp : H.face.symm q ≠ H.face.symm p := by
              intro h
              exact hpq (H.face.symm.injective h).symm
            simp [addEdgeHypermap_componentCode_some_some, splitFacePerm_old,
              hqp]
            simpa using (H.componentOf_face (H.face.symm q)).symm
          · simp [addEdgeHypermap_componentCode_some_some, splitFacePerm_old,
              hxp, hxq]
            exact (H.componentOf_face x).symm

theorem addEdgeHypermap_componentCode_some_some_of_reachable
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hreach : PermReachable H.face p q)
    {x y : (addEdgeHypermap H (some p) (some q) hAB).Dart}
    (hxy : (addEdgeHypermap H (some p) (some q) hAB).Reachable x y) :
    addEdgeHypermap_componentCode_some_some H p q hAB x =
      addEdgeHypermap_componentCode_some_some H p q hAB y :=
  hxy.apply_eq (addEdgeHypermap_componentCode_some_some H p q hAB)
    (fun {_ _} h =>
      addEdgeHypermap_componentCode_some_some_of_link H p q hAB hreach h)

noncomputable def addEdgeHypermap_componentEquiv_some_some
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hreach : PermReachable H.face p q) :
    (addEdgeHypermap H (some p) (some q) hAB).Component ≃ H.Component where
  toFun :=
    Quotient.lift
      (addEdgeHypermap_componentCode_some_some H p q hAB)
      (by
        intro x y hxy
        exact addEdgeHypermap_componentCode_some_some_of_reachable
          H p q hAB hreach hxy)
  invFun :=
    Quotient.lift
      (fun x => (addEdgeHypermap H (some p) (some q) hAB).componentOf
        (ExtDart.old x))
      (by
        intro x y hxy
        exact (addEdgeHypermap H (some p) (some q) hAB).componentOf_eq_componentOf
          (addEdgeHypermap_old_reachable_of_reachable_some_some
            H p q hAB hxy))
  left_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            apply (addEdgeHypermap H (some p) (some q) hAB).componentOf_eq_componentOf
            have hnode :
                PermReachable
                  (addEdgeHypermap H (some p) (some q) hAB).node
                  ExtDart.new (ExtDart.old p) := by
              simpa [addEdgeHypermap] using
                (insertedEdgeNode_new_reachable_old_of_permReachable
                  H.node p (some q) hAB (PermReachable.refl H.node p))
            exact (addEdgeHypermap H (some p) (some q) hAB).reachable_symm
              ((addEdgeHypermap H (some p) (some q) hAB).nodePermReachable_reachable
                hnode)
        | newEdge =>
            apply (addEdgeHypermap H (some p) (some q) hAB).componentOf_eq_componentOf
            have hnode :
                PermReachable
                  (addEdgeHypermap H (some p) (some q) hAB).node
                  ExtDart.newEdge (ExtDart.old q) := by
              simpa [addEdgeHypermap] using
                (insertedEdgeNode_newEdge_reachable_old_of_permReachable
                  H.node (some p) q hAB (PermReachable.refl H.node q))
            exact (addEdgeHypermap H (some p) (some q) hAB).reachable_symm
              ((addEdgeHypermap H (some p) (some q) hAB).nodePermReachable_reachable
                hnode)
        | old x => rfl
  right_inv := by
    intro c
    induction c using Quotient.inductionOn with
    | h x => rfl

theorem addEdgeHypermap_componentCount_some_some_of_reachable
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hreach : PermReachable H.face p q) :
    (addEdgeHypermap H (some p) (some q) hAB).componentCount =
      H.componentCount := by
  unfold Hypermap.componentCount
  exact Nat.card_congr
    (addEdgeHypermap_componentEquiv_some_some H p q hAB hreach)

theorem addEdgeHypermap_componentCount_some_some_of_cofacial
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hcofacial : addEdgeCofacial H (some p) (some q)) :
    (addEdgeHypermap H (some p) (some q) hAB).componentCount =
      H.componentCount :=
  addEdgeHypermap_componentCount_some_some_of_reachable H p q hAB
    ((addEdgeCofacial_some_some H p q).mp hcofacial)

theorem addEdgeHypermap_eulerLeft_some_some_of_cofacial
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hcofacial : addEdgeCofacial H (some p) (some q)) :
    (addEdgeHypermap H (some p) (some q) hAB).eulerLeft =
      H.eulerLeft + 2 := by
  unfold Hypermap.eulerLeft
  rw [addEdgeHypermap_componentCount_some_some_of_cofacial H p q hAB hcofacial,
    addEdgeHypermap_card]
  omega

theorem addEdgeHypermap_eulerRight_some_some_of_cofacial
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hcofacial : addEdgeCofacial H (some p) (some q)) :
    (addEdgeHypermap H (some p) (some q) hAB).eulerRight =
      H.eulerRight + 2 := by
  unfold Hypermap.eulerRight
  rw [addEdgeHypermap_edgeOrbitCount_of_basepoint H (some p) (some q) hAB p,
    addEdgeHypermap_nodeOrbitCount_some_some H p q hAB,
    addEdgeHypermap_faceOrbitCount_some_some_of_cofacial H p q hAB hcofacial]
  omega

theorem addEdgeHypermap_genus_some_some_of_cofacial
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hcofacial : addEdgeCofacial H (some p) (some q)) :
    (addEdgeHypermap H (some p) (some q) hAB).genus = H.genus := by
  unfold Hypermap.genus
  rw [addEdgeHypermap_eulerLeft_some_some_of_cofacial H p q hAB hcofacial,
    addEdgeHypermap_eulerRight_some_some_of_cofacial H p q hAB hcofacial,
    Nat.add_sub_add_right]

theorem addEdgeHypermap_eulerPlanar_iff_some_some_of_cofacial
    (H : Hypermap.{u}) (p q : H.Dart)
    (hAB : forall r : H.Dart, (some p : Option H.Dart) = some r ->
      (some q : Option H.Dart) ≠ some r)
    (hcofacial : addEdgeCofacial H (some p) (some q)) :
    (addEdgeHypermap H (some p) (some q) hAB).EulerPlanar ↔
      H.EulerPlanar := by
  simp [Hypermap.EulerPlanar,
    addEdgeHypermap_genus_some_some_of_cofacial H p q hAB hcofacial]

@[simp]
theorem addEdgeExt_edge_symm_eq_edge
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (x : ExtDart (OrientedEdge (deletedGraph G a b))) :
    (ExtDart.Perm.edge
        (OrientedEdge.edgePerm (deletedGraph G a b))).symm x =
      ExtDart.Perm.edge
        (OrientedEdge.edgePerm (deletedGraph G a b)) x := by
  cases x <;> simp [ExtDart.Perm.edge, OrientedEdge.edgePerm]

@[simp]
theorem addEdgeRotationSystem_node_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (e : OrientedEdge G) :
    (dartEquivExt (G := G) (a := a) (b := b) hab)
      ((addEdgeRotationSystem (G := G) (a := a) (b := b) hab R).node e) =
    addEdgeNode (G := G) (a := a) (b := b) hab R
      ((dartEquivExt (G := G) (a := a) (b := b) hab) e) := by
  let E := dartEquivExt (G := G) (a := a) (b := b) hab
  let N := addEdgeNode (G := G) (a := a) (b := b) hab R
  change E (E.symm (N (E e))) = N (E e)
  exact E.apply_symm_apply (N (E e))

/-- The graph-facing add-edge rotation system induces exactly the pure
add-edge hypermap under the deleted-edge dart split. -/
noncomputable def addEdgeRotationSystem_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b)) :
    Hypermap.Iso
      ((addEdgeRotationSystem
        (G := G) (a := a) (b := b) hab R).toHypermap)
      (addEdgeHypermap R.toHypermap
        (addEdgePivotA G a b)
        (addEdgePivotB G a b)
        (addEdgePivot_disjoint hab)) where
  toEquiv := dartEquivExt (G := G) (a := a) (b := b) hab
  map_edge := by
    intro e
    exact dartEquivExt_symm (G := G) (a := a) (b := b) hab e
  map_node := by
    intro e
    exact addEdgeRotationSystem_node_conj
      (G := G) (a := a) (b := b) hab R e
  map_face := by
    intro e
    let E := dartEquivExt (G := G) (a := a) (b := b) hab
    let S := addEdgeRotationSystem (G := G) (a := a) (b := b) hab R
    let N := addEdgeNode (G := G) (a := a) (b := b) hab R
    let τ := ExtDart.Perm.edge
      (OrientedEdge.edgePerm (deletedGraph G a b))
    have hnode : forall x : OrientedEdge G, E (S.node x) = N (E x) := by
      intro x
      exact addEdgeRotationSystem_node_conj
        (G := G) (a := a) (b := b) hab R x
    change E (S.node.symm e.symm) = N.symm (τ.symm (E e))
    calc
      E (S.node.symm e.symm) = N.symm (E e.symm) :=
        perm_conj_symm_apply E S.node N hnode e.symm
      _ = N.symm (τ (E e)) := by
        rw [dartEquivExt_symm (G := G) (a := a) (b := b) hab e]
      _ = N.symm (τ.symm (E e)) := by
        rw [addEdgeExt_edge_symm_eq_edge
          (G := G) (a := a) (b := b) (E e)]

theorem addEdgeRotationSystem_eulerPlanar_iff_some_some_of_cofacial
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    {p q : OrientedEdge (deletedGraph G a b)}
    (hpA : addEdgePivotA G a b = some p)
    (hpB : addEdgePivotB G a b = some q)
    (hcofacial : addEdgeCofacial R.toHypermap (some p) (some q)) :
    ((addEdgeRotationSystem
      (G := G) (a := a) (b := b) hab R).toHypermap).EulerPlanar ↔
      R.toHypermap.EulerPlanar := by
  have hIso :=
    (addEdgeRotationSystem_toHypermapIso
      (G := G) (a := a) (b := b) hab R).eulerPlanar_iff
  have hABpq :
      forall r : R.toHypermap.Dart, (some p : Option R.toHypermap.Dart) = some r ->
        (some q : Option R.toHypermap.Dart) ≠ some r := by
    intro r hpr hqr
    exact (addEdgePivot_disjoint hab r (by simpa [hpA] using hpr))
      (by simpa [hpB] using hqr)
  have hpure :
      (addEdgeHypermap R.toHypermap
        (addEdgePivotA G a b)
        (addEdgePivotB G a b)
        (addEdgePivot_disjoint hab)).EulerPlanar ↔
        R.toHypermap.EulerPlanar := by
    simpa [hpA, hpB] using
      (addEdgeHypermap_eulerPlanar_iff_some_some_of_cofacial
        R.toHypermap p q hABpq hcofacial)
  exact hIso.trans hpure

theorem addEdgePivotOptions_disjoint_of_tail
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    {p q : OrientedEdge (deletedGraph G a b)}
    (hpA : p.tail = a)
    (hpB : q.tail = b) :
    forall r : OrientedEdge (deletedGraph G a b),
      (some p : Option (OrientedEdge (deletedGraph G a b))) = some r ->
        (some q : Option (OrientedEdge (deletedGraph G a b))) ≠ some r := by
  intro r hpr hqr
  have hpq : p = q := by
    simpa using hpr.trans hqr.symm
  have hab_eq : a = b := hpA.symm.trans (by simpa [hpq] using hpB)
  exact hab.ne hab_eq

/-- Add back the deleted edge using explicitly supplied endpoint pivots rather
than the arbitrary `endpointPivot` choices.  This is the source-facing form:
the embedding theorem may choose the two darts that border the common face. -/
noncomputable def addEdgeNodeAt
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (p q : OrientedEdge (deletedGraph G a b))
    (hpA : p.tail = a)
    (hpB : q.tail = b) :
    Equiv.Perm (ExtDart (OrientedEdge (deletedGraph G a b))) :=
  insertedEdgeNode R.node (some p) (some q)
    (addEdgePivotOptions_disjoint_of_tail (G := G) (a := a) (b := b)
      hab hpA hpB)

theorem addEdgeNodeAt_extTail
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (p q : OrientedEdge (deletedGraph G a b))
    (hpA : p.tail = a)
    (hpB : q.tail = b)
    (x : ExtDart (OrientedEdge (deletedGraph G a b))) :
    extTail (G := G) a b (addEdgeNodeAt
        (G := G) (a := a) (b := b) hab R p q hpA hpB x) =
      extTail (G := G) a b x := by
  classical
  cases x with
  | new =>
      simpa [addEdgeNodeAt, extTail] using (R.node_tail p).trans hpA
  | newEdge =>
      simpa [addEdgeNodeAt, extTail] using (R.node_tail q).trans hpB
  | old e =>
      by_cases hep : e = p
      · subst e
        simp [addEdgeNodeAt, extTail, hpA]
      · by_cases heq : e = q
        · subst e
          simp [addEdgeNodeAt, extTail, hep, hpB]
        · simpa [addEdgeNodeAt, insertedEdgeNode_old_some_some,
            extTail, hep, heq] using R.node_tail e

theorem addEdgeNodeAt_reachable_of_same_extTail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (p q : OrientedEdge (deletedGraph G a b))
    (hpA : p.tail = a)
    (hpB : q.tail = b)
    {x y : ExtDart (OrientedEdge (deletedGraph G a b))}
    (hxy : extTail (G := G) a b x = extTail (G := G) a b y) :
    PermReachable (addEdgeNodeAt
      (G := G) (a := a) (b := b) hab R p q hpA hpB) x y := by
  classical
  let hAB :=
    addEdgePivotOptions_disjoint_of_tail
      (G := G) (a := a) (b := b) hab hpA hpB
  cases x with
  | new =>
      cases y with
      | new =>
          exact PermReachable.refl _ ExtDart.new
      | newEdge =>
          have hba : a = b := by simpa [extTail] using hxy
          exact False.elim (hab.ne hba)
      | old f =>
          have haf : a = f.tail := by simpa [extTail] using hxy
          have hpf : p.tail = f.tail := hpA.trans haf
          have hR : PermReachable R.node p f :=
            R.node_orbit_of_same_tail p f hpf
          simpa [addEdgeNodeAt, hAB] using
            insertedEdgeNode_new_reachable_old_of_permReachable
              R.node p (some q) hAB hR
  | newEdge =>
      cases y with
      | new =>
          have hba : b = a := by simpa [extTail] using hxy
          exact False.elim (hab.ne' hba)
      | newEdge =>
          exact PermReachable.refl _ ExtDart.newEdge
      | old f =>
          have hbf : b = f.tail := by simpa [extTail] using hxy
          have hqf : q.tail = f.tail := hpB.trans hbf
          have hR : PermReachable R.node q f :=
            R.node_orbit_of_same_tail q f hqf
          simpa [addEdgeNodeAt, hAB] using
            insertedEdgeNode_newEdge_reachable_old_of_permReachable
              R.node (some p) q hAB hR
  | old e =>
      cases y with
      | new =>
          have hea : e.tail = a := by simpa [extTail] using hxy
          have hpe : p.tail = e.tail := hpA.trans hea.symm
          have hR : PermReachable R.node p e :=
            R.node_orbit_of_same_tail p e hpe
          exact
            PermReachable.symm
              (addEdgeNodeAt
                (G := G) (a := a) (b := b) hab R p q hpA hpB)
              (by
                simpa [addEdgeNodeAt, hAB] using
                  insertedEdgeNode_new_reachable_old_of_permReachable
                    R.node p (some q) hAB hR)
      | newEdge =>
          have heb : e.tail = b := by simpa [extTail] using hxy
          have hqe : q.tail = e.tail := hpB.trans heb.symm
          have hR : PermReachable R.node q e :=
            R.node_orbit_of_same_tail q e hqe
          exact
            PermReachable.symm
              (addEdgeNodeAt
                (G := G) (a := a) (b := b) hab R p q hpA hpB)
              (by
                simpa [addEdgeNodeAt, hAB] using
                  insertedEdgeNode_newEdge_reachable_old_of_permReachable
                    R.node (some p) q hAB hR)
      | old f =>
          have hef : e.tail = f.tail := by simpa [extTail] using hxy
          have hR : PermReachable R.node e f :=
            R.node_orbit_of_same_tail e f hef
          simpa [addEdgeNodeAt, hAB] using
            insertedEdgeNode_old_reachable_of_permReachable
              R.node (some p) (some q) hAB hR

noncomputable def addEdgeRotationSystemAt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (p q : OrientedEdge (deletedGraph G a b))
    (hpA : p.tail = a)
    (hpB : q.tail = b) :
    RotationSystem G :=
  rotationSystemOfExtNode (G := G) (a := a) (b := b) hab
    (addEdgeNodeAt (G := G) (a := a) (b := b) hab R p q hpA hpB)
    (addEdgeNodeAt_extTail (G := G) (a := a) (b := b)
      hab R p q hpA hpB)
    (fun _ _ hxy =>
      addEdgeNodeAt_reachable_of_same_extTail
        (G := G) (a := a) (b := b) hab R p q hpA hpB hxy)

@[simp]
theorem addEdgeRotationSystemAt_node_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (p q : OrientedEdge (deletedGraph G a b))
    (hpA : p.tail = a)
    (hpB : q.tail = b)
    (e : OrientedEdge G) :
    (dartEquivExt (G := G) (a := a) (b := b) hab)
      ((addEdgeRotationSystemAt
        (G := G) (a := a) (b := b) hab R p q hpA hpB).node e) =
    addEdgeNodeAt (G := G) (a := a) (b := b) hab R p q hpA hpB
      ((dartEquivExt (G := G) (a := a) (b := b) hab) e) := by
  let E := dartEquivExt (G := G) (a := a) (b := b) hab
  let N := addEdgeNodeAt (G := G) (a := a) (b := b) hab R p q hpA hpB
  change E (E.symm (N (E e))) = N (E e)
  exact E.apply_symm_apply (N (E e))

noncomputable def addEdgeRotationSystemAt_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    (p q : OrientedEdge (deletedGraph G a b))
    (hpA : p.tail = a)
    (hpB : q.tail = b) :
    Hypermap.Iso
      ((addEdgeRotationSystemAt
        (G := G) (a := a) (b := b) hab R p q hpA hpB).toHypermap)
      (addEdgeHypermap R.toHypermap (some p) (some q)
        (addEdgePivotOptions_disjoint_of_tail
          (G := G) (a := a) (b := b) hab hpA hpB)) where
  toEquiv := dartEquivExt (G := G) (a := a) (b := b) hab
  map_edge := by
    intro e
    exact dartEquivExt_symm (G := G) (a := a) (b := b) hab e
  map_node := by
    intro e
    exact addEdgeRotationSystemAt_node_conj
      (G := G) (a := a) (b := b) hab R p q hpA hpB e
  map_face := by
    intro e
    let E := dartEquivExt (G := G) (a := a) (b := b) hab
    let S := addEdgeRotationSystemAt
      (G := G) (a := a) (b := b) hab R p q hpA hpB
    let N := addEdgeNodeAt (G := G) (a := a) (b := b) hab R p q hpA hpB
    let τ := ExtDart.Perm.edge
      (OrientedEdge.edgePerm (deletedGraph G a b))
    have hnode : forall x : OrientedEdge G, E (S.node x) = N (E x) := by
      intro x
      exact addEdgeRotationSystemAt_node_conj
        (G := G) (a := a) (b := b) hab R p q hpA hpB x
    change E (S.node.symm e.symm) = N.symm (τ.symm (E e))
    calc
      E (S.node.symm e.symm) = N.symm (E e.symm) :=
        perm_conj_symm_apply E S.node N hnode e.symm
      _ = N.symm (τ (E e)) := by
        rw [dartEquivExt_symm (G := G) (a := a) (b := b) hab e]
      _ = N.symm (τ.symm (E e)) := by
        rw [addEdgeExt_edge_symm_eq_edge
          (G := G) (a := a) (b := b) (E e)]

theorem addEdgeRotationSystemAt_eulerPlanar_iff_of_cofacial
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (deletedGraph G a b))
    {p q : OrientedEdge (deletedGraph G a b)}
    (hpA : p.tail = a)
    (hpB : q.tail = b)
    (hcofacial : addEdgeCofacial R.toHypermap (some p) (some q)) :
    ((addEdgeRotationSystemAt
      (G := G) (a := a) (b := b) hab R p q hpA hpB).toHypermap).EulerPlanar ↔
      R.toHypermap.EulerPlanar := by
  have hABpq :
      forall r : R.toHypermap.Dart, (some p : Option R.toHypermap.Dart) = some r ->
        (some q : Option R.toHypermap.Dart) ≠ some r :=
    addEdgePivotOptions_disjoint_of_tail
      (G := G) (a := a) (b := b) hab hpA hpB
  have hIso :=
    (addEdgeRotationSystemAt_toHypermapIso
      (G := G) (a := a) (b := b) hab R p q hpA hpB).eulerPlanar_iff
  have hpure :
      (addEdgeHypermap R.toHypermap (some p) (some q) hABpq).EulerPlanar ↔
        R.toHypermap.EulerPlanar :=
    addEdgeHypermap_eulerPlanar_iff_some_some_of_cofacial
      R.toHypermap p q hABpq hcofacial
  exact hIso.trans hpure

end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
