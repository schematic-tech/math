import Schematic.Math.GraphTheory.Embedding.Kuratowski

/-!
Rotation-system form of Coq `embedding.v`'s `add_node` construction.

The new vertex is represented by `none`; old vertices are represented by
`some v`.  This module builds the operation from the checked leaf and
cofacial-edge extensions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- Forward membership expressed directly in the oriented-edge list of a
walk. -/
theorem cycleForwardDart_iff_mem_orientedDarts
    {V : Type u} {G : SimpleGraph V} {r : V}
    (c : G.Walk r r) (e : OrientedEdge G) :
    CycleForwardDart c e ↔
      e ∈ c.darts.map (orientedEdgeDartEquiv (G := G)).symm := by
  rw [cycleForwardDart_iff_mem_darts]
  constructor
  · intro he
    exact List.mem_map.mpr ⟨orientedEdgeDartEquiv e, he,
      (orientedEdgeDartEquiv (G := G)).symm_apply_apply e⟩
  · intro he
    rcases List.mem_map.mp he with ⟨d, hd, hde⟩
    have hdEq : d = orientedEdgeDartEquiv e := by
      apply (orientedEdgeDartEquiv (G := G)).symm.injective
      simpa using hde
    simpa [hdEq] using hd

theorem cycleForwardDart_map_iso_symm_iff
    {V W : Type u}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (phi : G ≃g H)
    {r : W} (c : H.Walk r r)
    (e : OrientedEdge G) :
    CycleForwardDart (c.map phi.symm.toHom) e ↔
      CycleForwardDart c (orientedEdgeEquivOfGraphIso phi e) := by
  constructor
  · rintro ⟨i, hi, htail, hhead⟩
    refine ⟨i, by simpa using hi, ?_, ?_⟩
    · calc
        (orientedEdgeEquivOfGraphIso phi e).tail = phi e.tail := rfl
        _ = phi ((c.map phi.symm.toHom).getVert i) := by rw [htail]
        _ = c.getVert i := by simp [SimpleGraph.Walk.getVert_map]
    · calc
        (orientedEdgeEquivOfGraphIso phi e).head = phi e.head := rfl
        _ = phi ((c.map phi.symm.toHom).getVert (i + 1)) := by rw [hhead]
        _ = c.getVert (i + 1) := by simp [SimpleGraph.Walk.getVert_map]
  · rintro ⟨i, hi, htail, hhead⟩
    refine ⟨i, by simpa using hi, ?_, ?_⟩
    · apply phi.injective
      rw [SimpleGraph.Walk.getVert_map]
      simpa using htail
    · apply phi.injective
      rw [SimpleGraph.Walk.getVert_map]
      simpa using hhead

/-- Pulling a rotation system and its directed facial cycle back through a
graph isomorphism preserves the complete face-orbit invariant. -/
theorem isFacialCycle_ofIso
    {V W : Type u} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (phi : G ≃g H)
    (R : RotationSystem H)
    {r : W} (c : H.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc) :
    let c' := c.map phi.symm.toHom
    let hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.map
      (p := c) (f := phi.symm.toHom) phi.symm.toEquiv.injective hc
    RotationSystemGluing.IsFacialCycle
      (RotationSystem.ofIso phi R) c' hc' := by
  let c' := c.map phi.symm.toHom
  let hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.map
    (p := c) (f := phi.symm.toHom) phi.symm.toEquiv.injective hc
  let psi := orientedEdgeEquivOfGraphIso phi
  have hfirstForward :
      CycleForwardDart c (psi (cycleFirstDart c' hc')) := by
    exact (cycleForwardDart_map_iso_symm_iff phi c
      (cycleFirstDart c' hc')).mp (cycleForwardDart_first c' hc')
  have hfirstEq :
      psi (cycleFirstDart c' hc') = cycleFirstDart c hc := by
    apply cycleForwardDart_eq_of_tail_eq hc hfirstForward
      (cycleForwardDart_first c hc)
    change phi (c'.getVert 0) = c.getVert 0
    simp [c']
  change RotationSystemGluing.IsFacialCycle
    (RotationSystem.ofIso phi R) c' hc'
  intro e
  rw [cycleForwardDart_map_iso_symm_iff phi c e, hfacial]
  rw [← hfirstEq]
  exact
    (RotationSystem.ofIso_toHypermapIso phi R).faceReachable_iff.symm

/-- Changing the basepoint of a directed facial cycle preserves the same
complete face orbit. -/
theorem isFacialCycle_rotate
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (x : V) (hx : x ∈ c.support) :
    let c' := c.rotate x hx
    let hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate hx hc
    RotationSystemGluing.IsFacialCycle R c' hc' := by
  let c' := c.rotate x hx
  let hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate hx hc
  have hforward : forall e : OrientedEdge G,
      CycleForwardDart c' e ↔ CycleForwardDart c e := by
    intro e
    rw [cycleForwardDart_iff_mem_darts, cycleForwardDart_iff_mem_darts]
    exact (SimpleGraph.Walk.rotate_darts c x hx).mem_iff
  have hnewFirst :
      CycleForwardDart c (cycleFirstDart c' hc') :=
    (hforward (cycleFirstDart c' hc')).mp
      (cycleForwardDart_first c' hc')
  have hbase : PermReachable R.toHypermap.face
      (cycleFirstDart c hc) (cycleFirstDart c' hc') :=
    (hfacial (cycleFirstDart c' hc')).mp hnewFirst
  change RotationSystemGluing.IsFacialCycle R c' hc'
  intro e
  rw [hforward, hfacial]
  constructor
  · intro hold
    exact PermReachable.trans R.toHypermap.face
      (PermReachable.symm R.toHypermap.face hbase) hold
  · intro hnew
    exact PermReachable.trans R.toHypermap.face hbase hnew

/-- Faciality depends on the directed cyclic vertex order, not on the chosen
basepoint or ambient walk proof.  Two simple closed walks with cyclically
rotated tail supports therefore bound the same face. -/
theorem isFacialCycle_of_tailSupport_isRotated
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r x : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (d : G.Walk x x) (hd : d.IsCycle)
    (hrot : d.support.tail ~r c.support.tail) :
    RotationSystemGluing.IsFacialCycle R d hd := by
  have hxDtail : x ∈ d.support.tail :=
    d.end_mem_tail_support hd.not_nil
  have hxCtail : x ∈ c.support.tail := hrot.mem_iff.mp hxDtail
  have hxC : x ∈ c.support := List.mem_of_mem_tail hxCtail
  let c' : G.Walk x x := c.rotate x hxC
  have hc' : c'.IsCycle := SimpleGraph.Walk.IsCycle.rotate hxC hc
  have hfacial' : RotationSystemGluing.IsFacialCycle R c' hc' := by
    simpa [c', hc'] using isFacialCycle_rotate R c hc hfacial x hxC
  have hrot' : d.support.tail ~r c'.support.tail :=
    hrot.trans (SimpleGraph.Walk.support_rotate c x hxC).symm
  have hdTailNe : d.support.tail ≠ [] := List.ne_nil_of_mem hxDtail
  have hc'TailNe : c'.support.tail ≠ [] := by
    exact List.ne_nil_of_mem (c'.end_mem_tail_support hc'.not_nil)
  have hlast :
      d.support.tail.getLast hdTailNe =
        c'.support.tail.getLast hc'TailNe := by
    rw [List.getLast_tail, List.getLast_tail,
      d.getLast_support, c'.getLast_support]
  have htailEq : d.support.tail = c'.support.tail :=
    List.IsRotated.eq_of_nodup_getLast_eq hrot'
      hd.support_nodup hdTailNe hc'TailNe hlast
  have hsupportEq : d.support = c'.support := by
    rw [← d.cons_tail_support, ← c'.cons_tail_support, htailEq]
  have hdc : d = c' := SimpleGraph.Walk.ext_support hsupportEq
  subst d
  simpa using hfacial'

/-- A directed cycle with a cyclic rotation of the same dart list bounds the
same face.  This is the basepoint-independent form of
`isFacialCycle_rotate`. -/
theorem isFacialCycle_of_darts_isRotated
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) {r x : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hfacial : RotationSystemGluing.IsFacialCycle R c hc)
    (d : G.Walk x x) (hd : d.IsCycle)
    (hrot : d.darts.IsRotated c.darts) :
    RotationSystemGluing.IsFacialCycle R d hd := by
  have hforward : forall e : OrientedEdge G,
      CycleForwardDart d e ↔ CycleForwardDart c e := by
    intro e
    rw [cycleForwardDart_iff_mem_darts, cycleForwardDart_iff_mem_darts]
    exact hrot.mem_iff
  have hnewFirst :
      CycleForwardDart c (cycleFirstDart d hd) :=
    (hforward (cycleFirstDart d hd)).mp
      (cycleForwardDart_first d hd)
  have hbase : PermReachable R.toHypermap.face
      (cycleFirstDart c hc) (cycleFirstDart d hd) :=
    (hfacial (cycleFirstDart d hd)).mp hnewFirst
  intro e
  rw [hforward, hfacial]
  constructor
  · intro hold
    exact PermReachable.trans R.toHypermap.face
      (PermReachable.symm R.toHypermap.face hbase) hold
  · intro hnew
    exact PermReachable.trans R.toHypermap.face hbase hnew

/-- Inserting the old-end dart of a leaf after a specified outgoing pivot
preserves the extended tail map. -/
theorem insertedLeafNodeAt_leafExtTail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (p : OrientedEdge (G.induce {z : V | z ≠ v}))
    (hp : ((p.tail : {z : V // z ≠ v}) : V) = w)
    (x : ExtDart (OrientedEdge (G.induce {z : V | z ≠ v}))) :
    LeafExtension.leafExtTail (G := G) (v := v) (w := w)
        (LeafExtension.insertedLeafNode R.node (some p) x) =
      LeafExtension.leafExtTail (G := G) (v := v) (w := w) x := by
  cases x with
  | new => rfl
  | newEdge =>
      change (((R.node p).tail : {z : V // z ≠ v}) : V) = w
      exact (congrArg Subtype.val (R.node_tail p)).trans hp
  | old e =>
      by_cases he : e = p
      · subst e
        change
          LeafExtension.leafExtTail (G := G) (v := v) (w := w)
              (if p = p then ExtDart.newEdge else ExtDart.old (R.node p)) =
            ((p.tail : {z : V // z ≠ v}) : V)
        rw [if_pos rfl]
        exact hp.symm
      · change
          LeafExtension.leafExtTail (G := G) (v := v) (w := w)
              (if e = p then ExtDart.newEdge else ExtDart.old (R.node e)) =
            ((e.tail : {z : V // z ≠ v}) : V)
        rw [if_neg he]
        exact congrArg Subtype.val (R.node_tail e)

/-- The specified-pivot leaf node permutation has exactly one node orbit over
each extended tail. -/
theorem insertedLeafNodeAt_reachable_of_same_leafExtTail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (p : OrientedEdge (G.induce {z : V | z ≠ v}))
    (hp : ((p.tail : {z : V // z ≠ v}) : V) = w)
    {x y : ExtDart (OrientedEdge (G.induce {z : V | z ≠ v}))}
    (hxy :
      LeafExtension.leafExtTail (G := G) (v := v) (w := w) x =
        LeafExtension.leafExtTail (G := G) (v := v) (w := w) y) :
    PermReachable (LeafExtension.insertedLeafNode R.node (some p)) x y := by
  cases x with
  | new =>
      cases y with
      | new => exact PermReachable.refl _ ExtDart.new
      | newEdge =>
          exact False.elim (hvw.ne (by simpa using hxy))
      | old f =>
          exact False.elim (f.tail.property (by simpa using hxy.symm))
  | newEdge =>
      cases y with
      | new => exact False.elim (hvw.ne' (by simpa using hxy))
      | newEdge => exact PermReachable.refl _ ExtDart.newEdge
      | old f =>
          have hpf : p.tail = f.tail := by
            ext
            exact hp.trans (by simpa using hxy)
          exact
            LeafExtension.insertedLeafNode_newEdge_reachable_old_of_permReachable
              R.node (R.node_orbit_of_same_tail p f hpf)
  | old e =>
      cases y with
      | new => exact False.elim (e.tail.property (by simpa using hxy))
      | newEdge =>
          have hpe : p.tail = e.tail := by
            ext
            exact hp.trans (by simpa using hxy.symm)
          exact PermReachable.symm _
            (LeafExtension.insertedLeafNode_newEdge_reachable_old_of_permReachable
              R.node (R.node_orbit_of_same_tail p e hpe))
      | old f =>
          have hef : e.tail = f.tail := by
            ext
            simpa using hxy
          exact LeafExtension.insertedLeafNode_old_reachable_of_permReachable
            R.node (some p) (R.node_orbit_of_same_tail e f hef)

/-- Reattach a deleted leaf at a specified corner of the old endpoint. -/
noncomputable def leafReattachRotationSystemAt
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (p : OrientedEdge (G.induce {z : V | z ≠ v}))
    (hp : ((p.tail : {z : V // z ≠ v}) : V) = w) :
    RotationSystem G where
  node :=
    let E := LeafExtension.orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let N := LeafExtension.insertedLeafNode R.node (some p)
    (E.trans N).trans E.symm
  node_tail := by
    intro e
    let E := LeafExtension.orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let N := LeafExtension.insertedLeafNode R.node (some p)
    change (E.symm (N (E e))).tail = e.tail
    calc
      (E.symm (N (E e))).tail =
          LeafExtension.leafExtTail (G := G) (v := v) (w := w)
            (N (E e)) :=
        LeafExtension.orientedEdgeDeleteLeafEquiv_symm_tail
          (G := G) (v := v) (w := w) hvw hdegree (N (E e))
      _ = LeafExtension.leafExtTail (G := G) (v := v) (w := w)
            (E e) := insertedLeafNodeAt_leafExtTail R p hp (E e)
      _ = e.tail :=
        LeafExtension.orientedEdgeDeleteLeafEquiv_tail
          (G := G) (v := v) (w := w) hvw hdegree e
  node_orbit_of_same_tail := by
    intro e f hef
    let E := LeafExtension.orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let N := LeafExtension.insertedLeafNode R.node (some p)
    change PermReachable ((E.trans N).trans E.symm) e f
    have htail :
        LeafExtension.leafExtTail (G := G) (v := v) (w := w) (E e) =
          LeafExtension.leafExtTail (G := G) (v := v) (w := w) (E f) := by
      rw [LeafExtension.orientedEdgeDeleteLeafEquiv_tail
          (G := G) (v := v) (w := w) hvw hdegree e,
        LeafExtension.orientedEdgeDeleteLeafEquiv_tail
          (G := G) (v := v) (w := w) hvw hdegree f, hef]
    have hN : PermReachable N (E e) (E f) :=
      insertedLeafNodeAt_reachable_of_same_leafExtTail hvw R p hp htail
    have hconj : forall x : OrientedEdge G,
        E (((E.trans N).trans E.symm) x) = N (E x) := by
      intro x
      exact E.apply_symm_apply (N (E x))
    exact (permReachable_conj_iff E ((E.trans N).trans E.symm) N hconj).mpr hN

@[simp]
theorem leafReattachRotationSystemAt_node_conj
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (p : OrientedEdge (G.induce {z : V | z ≠ v}))
    (hp : ((p.tail : {z : V // z ≠ v}) : V) = w)
    (e : OrientedEdge G) :
    (LeafExtension.orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree)
      ((leafReattachRotationSystemAt hvw hdegree R p hp).node e) =
    LeafExtension.insertedLeafNode R.node (some p)
      ((LeafExtension.orientedEdgeDeleteLeafEquiv
        (G := G) (v := v) (w := w) hvw hdegree) e) := by
  let E := LeafExtension.orientedEdgeDeleteLeafEquiv
    (G := G) (v := v) (w := w) hvw hdegree
  let N := LeafExtension.insertedLeafNode R.node (some p)
  exact E.apply_symm_apply (N (E e))

/-- The specified-corner graph lift induces the pure specified-pivot leaf
hypermap. -/
noncomputable def leafReattachRotationSystemAt_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (p : OrientedEdge (G.induce {z : V | z ≠ v}))
    (hp : ((p.tail : {z : V // z ≠ v}) : V) = w) :
    Hypermap.Iso
      ((leafReattachRotationSystemAt hvw hdegree R p hp).toHypermap)
      (LeafExtension.leafHypermap R.toHypermap (some p)) where
  toEquiv := LeafExtension.orientedEdgeDeleteLeafEquiv
    (G := G) (v := v) (w := w) hvw hdegree
  map_edge := by
    intro e
    exact LeafExtension.orientedEdgeDeleteLeafEquiv_edge
      (G := G) (v := v) (w := w) hvw hdegree e
  map_node := by
    intro e
    exact leafReattachRotationSystemAt_node_conj hvw hdegree R p hp e
  map_face := by
    intro e
    let E := LeafExtension.orientedEdgeDeleteLeafEquiv
      (G := G) (v := v) (w := w) hvw hdegree
    let S := leafReattachRotationSystemAt hvw hdegree R p hp
    let N := LeafExtension.insertedLeafNode R.node (some p)
    let tau := ExtDart.Perm.edge
      (OrientedEdge.edgePerm (G.induce {z : V | z ≠ v}))
    have hnode : forall x : OrientedEdge G, E (S.node x) = N (E x) := by
      intro x
      exact leafReattachRotationSystemAt_node_conj hvw hdegree R p hp x
    change E (S.node.symm e.symm) = N.symm (tau.symm (E e))
    calc
      E (S.node.symm e.symm) = N.symm (E e.symm) :=
        perm_conj_symm_apply E S.node N hnode e.symm
      _ = N.symm (tau (E e)) := by
        rw [LeafExtension.orientedEdgeDeleteLeafEquiv_edge
          (G := G) (v := v) (w := w) hvw hdegree e]
      _ = N.symm (tau.symm (E e)) := by
        rw [LeafExtension.leafHypermap_edge_symm_eq_edge_for_orientedEdge
          (G := G.induce {z : V | z ≠ v}) (E e)]

theorem leafReattachRotationSystemAt_dual_eulerPlanar
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {v w : V}
    (hvw : G.Adj v w)
    (hdegree : G.degree v <= 1)
    (R : RotationSystem (G.induce {z : V | z ≠ v}))
    (p : OrientedEdge (G.induce {z : V | z ≠ v}))
    (hp : ((p.tail : {z : V // z ≠ v}) : V) = w)
    (hR : (R.toHypermap).dual.EulerPlanar) :
    ((leafReattachRotationSystemAt hvw hdegree R p hp).toHypermap).dual.EulerPlanar := by
  let S := leafReattachRotationSystemAt hvw hdegree R p hp
  have hold : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hleaf : (LeafExtension.leafHypermap R.toHypermap (some p)).EulerPlanar :=
    (LeafExtension.leafHypermap_eulerPlanar_iff R.toHypermap (some p)).mpr hold
  have hsource : S.toHypermap.EulerPlanar := by
    let phi := leafReattachRotationSystemAt_toHypermapIso hvw hdegree R p hp
    exact (phi.eulerPlanar_iff).mpr hleaf
  exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hsource


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
