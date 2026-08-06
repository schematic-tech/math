import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.FaceBoundaries

/-! Retained and complementary faces after inserting an edge. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- Graph-indexed version of one `plane_add_fan` step.  The new edge is
inserted between the first boundary dart's tail and a later boundary dart's
tail; the retained suffix is transported back from the pure split hypermap. -/
theorem exists_addEdgeRetained
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (EdgeDeletion.deletedGraph G a b))
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge (EdgeDeletion.deletedGraph G a b))
    (pre post : List (OrientedEdge (EdgeDeletion.deletedGraph G a b)))
    (hrest : B.rest = pre ++ q :: post)
    (hpA : B.first.tail = a)
    (hqB : q.tail = b) :
    Exists fun S : RotationSystem G =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun C : FaceBoundary S.toHypermap =>
          C.first.tail = a ∧
            Exists fun lift :
                OrientedEdge (EdgeDeletion.deletedGraph G a b) ->
                  OrientedEdge G =>
              (forall d, (lift d).tail = d.tail) ∧
                C.rest = lift q :: post.map lift := by
  classical
  have hreach : PermReachable R.toHypermap.face B.first q := by
    exact Hypermap.FacePath.mem_faceReachable (G := R.toHypermap) B.path (by
      right
      rw [hrest]
      exact List.mem_append_right pre (List.mem_cons_self))
  have hcofacial :
      EdgeDeletion.addEdgeCofacial R.toHypermap (some B.first) (some q) :=
    (EdgeDeletion.addEdgeCofacial_some_some R.toHypermap B.first q).mpr hreach
  let S : RotationSystem G :=
    EdgeDeletion.addEdgeRotationSystemAt hab R B.first q hpA hqB
  have hS : (S.toHypermap).dual.EulerPlanar := by
    have hold : R.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
    have hnew : S.toHypermap.EulerPlanar := by
      exact
        (EdgeDeletion.addEdgeRotationSystemAt_eulerPlanar_iff_of_cofacial
          hab R hpA hqB hcofacial).mpr hold
    exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hnew
  let pureBoundary := B.addEdgeRetained q pre post hrest
  let phi := EdgeDeletion.addEdgeRotationSystemAt_toHypermapIso
    hab R B.first q hpA hqB
  let C : FaceBoundary S.toHypermap := pureBoundary.mapIso phi.symm
  let lift : OrientedEdge (EdgeDeletion.deletedGraph G a b) -> OrientedEdge G :=
    fun d => phi.toEquiv.symm (ExtDart.old d)
  refine ⟨S, hS, C, ?_, lift, ?_, ?_⟩
  · change (phi.toEquiv.symm ExtDart.new).tail = a
    rfl
  · intro d
    rfl
  · change
      ((q :: post).map ExtDart.old).map phi.toEquiv.symm =
        lift q :: post.map lift
    change phi.toEquiv.symm (ExtDart.old q) ::
        (post.map ExtDart.old).map phi.toEquiv.symm =
      lift q :: post.map lift
    congr 1
    have hmap : forall l : List (OrientedEdge (EdgeDeletion.deletedGraph G a b)),
        (l.map ExtDart.old).map phi.toEquiv.symm = l.map lift := by
      intro l
      induction l with
      | nil => rfl
      | cons d l ih =>
          change phi.toEquiv.symm (ExtDart.old d) ::
              (l.map ExtDart.old).map phi.toEquiv.symm =
            lift d :: l.map lift
          rw [ih]
          change phi.toEquiv.symm (ExtDart.old d) :: l.map lift =
            phi.toEquiv.symm (ExtDart.old d) :: l.map lift
          rfl
    exact hmap post

/-- Graph-indexed face split exposing both faces created by inserting a
chord.  The first boundary follows the old suffix after `q`; the second
follows the old prefix from the original base dart.  Both use the same
endpoint-preserving lift of old darts into the restored graph. -/
theorem exists_addEdgeSplitBoundaries
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (EdgeDeletion.deletedGraph G a b))
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge (EdgeDeletion.deletedGraph G a b))
    (pre post : List (OrientedEdge (EdgeDeletion.deletedGraph G a b)))
    (hrest : B.rest = pre ++ q :: post)
    (hpA : B.first.tail = a)
    (hqB : q.tail = b) :
    Exists fun S : RotationSystem G =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun retained : FaceBoundary S.toHypermap =>
          Exists fun complementary : FaceBoundary S.toHypermap =>
            retained.first.tail = a ∧
              complementary.first.tail = b ∧
                Exists fun lift :
                    OrientedEdge (EdgeDeletion.deletedGraph G a b) ->
                      OrientedEdge G =>
                  (forall d, (lift d).tail = d.tail) ∧
                    (forall d, (lift d).head = d.head) ∧
                      retained.rest = lift q :: post.map lift ∧
                        complementary.rest =
                          lift B.first :: pre.map lift := by
  classical
  have hreach : PermReachable R.toHypermap.face B.first q := by
    exact Hypermap.FacePath.mem_faceReachable (G := R.toHypermap) B.path (by
      right
      rw [hrest]
      exact List.mem_append_right pre (List.mem_cons_self))
  have hcofacial :
      EdgeDeletion.addEdgeCofacial R.toHypermap (some B.first) (some q) :=
    (EdgeDeletion.addEdgeCofacial_some_some R.toHypermap B.first q).mpr hreach
  let S : RotationSystem G :=
    EdgeDeletion.addEdgeRotationSystemAt hab R B.first q hpA hqB
  have hS : (S.toHypermap).dual.EulerPlanar := by
    have hold : R.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
    have hnew : S.toHypermap.EulerPlanar :=
      (EdgeDeletion.addEdgeRotationSystemAt_eulerPlanar_iff_of_cofacial
        hab R hpA hqB hcofacial).mpr hold
    exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hnew
  let pureRetained := B.addEdgeRetained q pre post hrest
  let pureComplementary := B.addEdgeComplementary q pre post hrest
  let phi := EdgeDeletion.addEdgeRotationSystemAt_toHypermapIso
    hab R B.first q hpA hqB
  let retained : FaceBoundary S.toHypermap := pureRetained.mapIso phi.symm
  let complementary : FaceBoundary S.toHypermap :=
    pureComplementary.mapIso phi.symm
  let lift : OrientedEdge (EdgeDeletion.deletedGraph G a b) -> OrientedEdge G :=
    fun d => phi.toEquiv.symm (ExtDart.old d)
  refine ⟨S, hS, retained, complementary, ?_, ?_, lift, ?_, ?_, ?_, ?_⟩
  · change (phi.toEquiv.symm ExtDart.new).tail = a
    rfl
  · change (phi.toEquiv.symm ExtDart.newEdge).tail = b
    rfl
  · intro d
    rfl
  · intro d
    rfl
  · change
      ((q :: post).map ExtDart.old).map phi.toEquiv.symm =
        lift q :: post.map lift
    change phi.toEquiv.symm (ExtDart.old q) ::
        (post.map ExtDart.old).map phi.toEquiv.symm =
      lift q :: post.map lift
    congr 1
    have hmap : forall l : List (OrientedEdge (EdgeDeletion.deletedGraph G a b)),
        (l.map ExtDart.old).map phi.toEquiv.symm = l.map lift := by
      intro l
      induction l with
      | nil => rfl
      | cons d l ih =>
          change phi.toEquiv.symm (ExtDart.old d) ::
              (l.map ExtDart.old).map phi.toEquiv.symm =
            lift d :: l.map lift
          rw [ih]
          change phi.toEquiv.symm (ExtDart.old d) :: l.map lift =
            phi.toEquiv.symm (ExtDart.old d) :: l.map lift
          rfl
    exact hmap post
  · change
      ((B.first :: pre).map ExtDart.old).map phi.toEquiv.symm =
        lift B.first :: pre.map lift
    change phi.toEquiv.symm (ExtDart.old B.first) ::
        (pre.map ExtDart.old).map phi.toEquiv.symm =
      lift B.first :: pre.map lift
    congr 1
    have hmap : forall l : List (OrientedEdge (EdgeDeletion.deletedGraph G a b)),
        (l.map ExtDart.old).map phi.toEquiv.symm = l.map lift := by
      intro l
      induction l with
      | nil => rfl
      | cons d l ih =>
          change phi.toEquiv.symm (ExtDart.old d) ::
              (l.map ExtDart.old).map phi.toEquiv.symm =
            lift d :: l.map lift
          rw [ih]
          change phi.toEquiv.symm (ExtDart.old d) :: l.map lift =
            phi.toEquiv.symm (ExtDart.old d) :: l.map lift
          rfl
    exact hmap pre

/-- Transported form of `exists_addEdgeSplitBoundaries`.  The old rotation
may be indexed by any graph propositionally equal to the graph obtained by
deleting the inserted edge.  The returned old-dart lift is expressed from the
original graph and still preserves both endpoints exactly. -/
theorem exists_addEdgeSplitBoundaries_of_deletedGraph_eq
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    {a b : V}
    (hab : H.Adj a b)
    (hdel : EdgeDeletion.deletedGraph H a b = G)
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge G)
    (pre post : List (OrientedEdge G))
    (hrest : B.rest = pre ++ q :: post)
    (hpA : B.first.tail = a)
    (hqB : q.tail = b) :
    Exists fun S : RotationSystem H =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun retained : FaceBoundary S.toHypermap =>
          Exists fun complementary : FaceBoundary S.toHypermap =>
            retained.first.tail = a ∧
              complementary.first.tail = b ∧
                Exists fun lift : OrientedEdge G -> OrientedEdge H =>
                  (forall d, (lift d).tail = d.tail) ∧
                    (forall d, (lift d).head = d.head) ∧
                      retained.rest = lift q :: post.map lift ∧
                        complementary.rest =
                          lift B.first :: pre.map lift := by
  classical
  let D := EdgeDeletion.deletedGraph H a b
  letI : DecidableRel D.Adj := inferInstance
  let phi : D ≃g G := {
    toEquiv := Equiv.refl V
    map_rel_iff' := by
      intro x y
      change G.Adj x y ↔
        (EdgeDeletion.deletedGraph H a b).Adj x y
      rw [hdel]
  }
  let RD : RotationSystem D := RotationSystem.ofIso phi R
  let psi : Hypermap.Iso RD.toHypermap R.toHypermap :=
    RotationSystem.ofIso_toHypermapIso phi R
  have hRD : (RD.toHypermap).dual.EulerPlanar := by
    have hprimal : R.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
    have hsource : RD.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hprimal
    exact (Hypermap.dual_eulerPlanar_iff (G := RD.toHypermap)).mpr hsource
  let BD : FaceBoundary RD.toHypermap := B.mapIso psi.symm
  let dartPhi := orientedEdgeEquivOfGraphIso phi
  let qD : OrientedEdge D := dartPhi.symm q
  let preD : List (OrientedEdge D) := pre.map dartPhi.symm
  let postD : List (OrientedEdge D) := post.map dartPhi.symm
  have hrestD : BD.rest = preD ++ qD :: postD := by
    change B.rest.map dartPhi.symm =
      pre.map dartPhi.symm ++ dartPhi.symm q :: post.map dartPhi.symm
    rw [hrest, List.map_append, List.map_cons]
  have hfirstD : BD.first.tail = a := by
    change (dartPhi.symm B.first).tail = a
    simpa [dartPhi, phi] using hpA
  have hqD : qD.tail = b := by
    change (dartPhi.symm q).tail = b
    simpa [dartPhi, phi] using hqB
  rcases exists_addEdgeSplitBoundaries hab RD hRD BD qD preD postD
      hrestD hfirstD hqD with
    ⟨S, hS, retained, complementary, hretained, hcomplementary,
      liftD, hliftDtail, hliftDhead, hretainedRest, hcomplementaryRest⟩
  let lift : OrientedEdge G -> OrientedEdge H :=
    fun d => liftD (dartPhi.symm d)
  refine ⟨S, hS, retained, complementary, hretained, hcomplementary,
    lift, ?_, ?_, ?_, ?_⟩
  · intro d
    calc
      (lift d).tail = (dartPhi.symm d).tail := hliftDtail _
      _ = d.tail := by
        simp [dartPhi, phi, orientedEdgeEquivOfGraphIso,
          OrientedEdge.tail]
  · intro d
    calc
      (lift d).head = (dartPhi.symm d).head := hliftDhead _
      _ = d.head := by
        simp [dartPhi, phi, orientedEdgeEquivOfGraphIso,
          OrientedEdge.head]
  · rw [hretainedRest]
    change liftD (dartPhi.symm q) ::
        (post.map dartPhi.symm).map liftD =
      lift q :: post.map lift
    simp [lift, List.map_map]
  · rw [hcomplementaryRest]
    change liftD (dartPhi.symm B.first) ::
        (pre.map dartPhi.symm).map liftD =
      lift B.first :: pre.map lift
    simp [lift, List.map_map]


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
