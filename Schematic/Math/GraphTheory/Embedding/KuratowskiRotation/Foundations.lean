import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v
namespace RotationSystem

/-- Pull a rotation system back along a graph isomorphism. -/
noncomputable def ofIso
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (R : RotationSystem H) :
    RotationSystem G where
  node :=
    ((orientedEdgeEquivOfGraphIso φ).trans R.node).trans
      (orientedEdgeEquivOfGraphIso φ).symm
  node_tail := by
    intro e
    let ψ := orientedEdgeEquivOfGraphIso φ
    change (ψ.symm (R.node (ψ e))).tail = e.tail
    apply φ.injective
    calc
      φ ((ψ.symm (R.node (ψ e))).tail) =
          (R.node (ψ e)).tail := by
        change (ψ (ψ.symm (R.node (ψ e)))).tail = (R.node (ψ e)).tail
        simp [ψ]
      _ = (ψ e).tail := R.node_tail (ψ e)
      _ = φ e.tail := rfl
  node_orbit_of_same_tail := by
    intro e f hef
    let ψ := orientedEdgeEquivOfGraphIso φ
    have htail : (ψ e).tail = (ψ f).tail := by
      simp [ψ, hef]
    have hR : PermReachable R.node (ψ e) (ψ f) :=
      R.node_orbit_of_same_tail (ψ e) (ψ f) htail
    have hconj :
        forall x : OrientedEdge G,
          ψ ((((ψ.trans R.node).trans ψ.symm) x)) = R.node (ψ x) := by
      intro x
      simp [ψ]
    exact
      (permReachable_conj_iff ψ (((ψ.trans R.node).trans ψ.symm))
        R.node hconj).mpr hR

@[simp]
theorem ofIso_node
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (R : RotationSystem H) (e : OrientedEdge G) :
    (orientedEdgeEquivOfGraphIso φ) ((ofIso φ R).node e) =
      R.node ((orientedEdgeEquivOfGraphIso φ) e) := by
  simp [ofIso]

/-- The hypermap of an isomorphism-pulled rotation system is isomorphic to the
original hypermap. -/
noncomputable def ofIso_toHypermapIso
    {V : Type u} {W : Type u}
    {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel (SimpleGraph.Adj G)]
    [Fintype W] [DecidableEq W] [DecidableRel (SimpleGraph.Adj H)]
    (φ : G ≃g H) (R : RotationSystem H) :
    Hypermap.Iso ((ofIso φ R).toHypermap) R.toHypermap where
  toEquiv := orientedEdgeEquivOfGraphIso φ
  map_edge := by
    intro e
    rfl
  map_node := by
    intro e
    exact ofIso_node φ R e
  map_face := by
    intro e
    let ψ := orientedEdgeEquivOfGraphIso φ
    have hnode :
        forall x : OrientedEdge G,
          ψ (((ofIso φ R).node) x) = R.node (ψ x) := by
      intro x
      exact ofIso_node φ R x
    change
      ψ (((ofIso φ R).node.symm) e.symm) =
        R.node.symm ((ψ e).symm)
    calc
      ψ (((ofIso φ R).node.symm) e.symm) =
          R.node.symm (ψ e.symm) :=
        perm_conj_symm_apply ψ (ofIso φ R).node R.node hnode e.symm
      _ = R.node.symm ((ψ e).symm) := by
        rw [orientedEdgeEquivOfGraphIso_symm]

/-- Pull a node permutation on an equivalent dart type back to a graph
rotation system.  The two hypotheses are exactly the local tail preservation
and orbit completeness obligations of a rotation system. -/
noncomputable def pullbackDartEquiv
    {V : Type u} {D : Type v} {G : SimpleGraph V}
    (E : OrientedEdge G ≃ D) (N : Equiv.Perm D)
    (hnode_tail : forall e : OrientedEdge G,
      (E.symm (N (E e))).tail = e.tail)
    (hnode_orbit : forall e f : OrientedEdge G, e.tail = f.tail ->
      PermReachable N (E e) (E f)) :
    RotationSystem G where
  node := (E.trans N).trans E.symm
  node_tail := hnode_tail
  node_orbit_of_same_tail := by
    intro e f hef
    have hconj : forall x : OrientedEdge G,
        E (((E.trans N).trans E.symm) x) = N (E x) := by
      intro x
      exact E.apply_symm_apply (N (E x))
    exact
      (permReachable_conj_iff E ((E.trans N).trans E.symm) N hconj).mpr
        (hnode_orbit e f hef)

@[simp]
theorem pullbackDartEquiv_node
    {V : Type u} {D : Type v} {G : SimpleGraph V}
    (E : OrientedEdge G ≃ D) (N : Equiv.Perm D)
    (hnode_tail : forall e : OrientedEdge G,
      (E.symm (N (E e))).tail = e.tail)
    (hnode_orbit : forall e f : OrientedEdge G, e.tail = f.tail ->
      PermReachable N (E e) (E f))
    (e : OrientedEdge G) :
    E ((pullbackDartEquiv E N hnode_tail hnode_orbit).node e) = N (E e) :=
  E.apply_symm_apply (N (E e))

/-- The hypermap induced by `pullbackDartEquiv` is isomorphic to the target
plain hypermap when the dart equivalence also intertwines edge reversal. -/
noncomputable def pullbackDartEquivToHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (H : Hypermap)
    (E : OrientedEdge G ≃ H.Dart) (hplain : H.Plain)
    (hnode_tail : forall e : OrientedEdge G,
      (E.symm (H.node (E e))).tail = e.tail)
    (hnode_orbit : forall e f : OrientedEdge G, e.tail = f.tail ->
      PermReachable H.node (E e) (E f))
    (hedge : forall e : OrientedEdge G, E e.symm = H.edge (E e)) :
    Hypermap.Iso
      ((pullbackDartEquiv E H.node hnode_tail hnode_orbit).toHypermap) H where
  toEquiv := E
  map_edge := hedge
  map_node := pullbackDartEquiv_node E H.node hnode_tail hnode_orbit
  map_face := by
    intro e
    let S := pullbackDartEquiv E H.node hnode_tail hnode_orbit
    have hnode : forall x : OrientedEdge G, E (S.node x) = H.node (E x) :=
      pullbackDartEquiv_node E H.node hnode_tail hnode_orbit
    have hface : H.node.symm (H.edge.symm (E e)) = H.face (E e) := by
      apply H.node.injective
      simpa using (H.node_face_edge (H.edge.symm (E e))).symm
    change E (S.node.symm e.symm) = H.face (E e)
    calc
      E (S.node.symm e.symm) = H.node.symm (E e.symm) :=
        perm_conj_symm_apply E S.node H.node hnode e.symm
      _ = H.node.symm (H.edge (E e)) := by rw [hedge]
      _ = H.node.symm (H.edge.symm (E e)) := by
        rw [Hypermap.Plain.edge_symm_eq (G := H) hplain]
      _ = H.face (E e) := hface

end RotationSystem

/-- The actual graph-embedding target for the Kuratowski/FCT bridge: the graph
admits a finite rotation system whose dual hypermap has Euler genus zero.

This is deliberately separate from `Schematic.Math.GraphTheory.IsPlanar`, which is the repository's
strict-Kuratowski predicate (`no K5/K3,3 subdivision`).  The bridge theorem has
to prove `HasEulerRotationSystem` from `IsPlanar`; using `IsPlanar` as the
source proof's embedding target would be circular. -/
def HasEulerRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Exists fun R : RotationSystem G =>
    (R.toHypermap).dual.EulerPlanar

theorem hasEulerRotationSystem_iff
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    HasEulerRotationSystem G ↔
      Exists fun R : RotationSystem G =>
        (R.toHypermap).dual.EulerPlanar :=
  Iff.rfl

/-- Euler-planar graph rotation systems restrict to spanning subgraphs. The
construction is the reference Coq `subgraph_embedding` operation, implemented
as finite graph-edge deletion by `WalkupF` followed by `WalkupE`. -/
theorem HasEulerRotationSystem.mono
    {V : Type u} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : HasEulerRotationSystem G) (hHG : H ≤ G) :
    HasEulerRotationSystem H := by
  let dAmbient : DecidableRel H.Adj := inferInstance
  rcases hG with ⟨R, hR⟩
  let P : EdgeDeletion.PlanarRotationSystem G :=
    ⟨R, ⟨inferInstance, hR⟩⟩
  let Q : EdgeDeletion.PlanarRotationSystem H := P.mono hHG
  let dH : DecidableRel H.Adj :=
    Classical.choose Q.dualEulerPlanar
  have hQ :
      letI : DecidableRel H.Adj := dH
      (Q.rotation.toHypermap).dual.EulerPlanar :=
    Classical.choose_spec Q.dualEulerPlanar
  have hd :
      dH = dAmbient :=
    Subsingleton.elim _ _
  have hQambient :
      letI : DecidableRel H.Adj := dAmbient
      (Q.rotation.toHypermap).dual.EulerPlanar := by
    rw [hd] at hQ
    exact hQ
  exact ⟨Q.rotation, hQambient⟩

/-- Transport the Euler-rotation-system target across a graph isomorphism. -/
theorem HasEulerRotationSystem.of_iso
    {V : Type u} {W : Type u}
    {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (φ : G ≃g H)
    (hH : HasEulerRotationSystem H) :
    HasEulerRotationSystem G := by
  classical
  rcases hH with ⟨R, hR⟩
  let RG : RotationSystem G := RotationSystem.ofIso φ R
  refine ⟨RG, ?_⟩
  have htarget : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hsource : (RG.toHypermap).EulerPlanar := by
    let ψ : Hypermap.Iso RG.toHypermap R.toHypermap :=
      RotationSystem.ofIso_toHypermapIso φ R
    exact (ψ.eulerPlanar_iff).mpr htarget
  exact (Hypermap.dual_eulerPlanar_iff (G := RG.toHypermap)).mpr hsource

/-- Consume the recursive contraction embedding hypothesis and expose the
selected Makarychev/Skopenkov split data for the contraction drawing. -/
theorem HasEulerRotationSystem.exists_selected_boundary_corner_and_theta_dart_not_boundary_of_faceOrbitNoTheta
    (hface : EdgeDeletion.FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (hcontract :
      HasEulerRotationSystem
        (GraphContraction.collapseEdge G hab).graph)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun R : RotationSystem (GraphContraction.collapseEdge G hab).graph =>
      (R.toHypermap).dual.EulerPlanar ∧
        Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
          e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
            (Exists fun dLeave : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
                (dLeave.tail = a ∨ dLeave.tail = b) ∧
                  Exists fun dPrev : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                    EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dPrev =
                        (R.toHypermap).face.symm e ∧
                      (dPrev.head = a ∨ dPrev.head = b) ∧
                        Exists fun dNext : OrientedEdge
                            (EdgeDeletion.deletedGraph G a b) =>
                          EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dNext =
                              (R.toHypermap).face e ∧
                            dNext.tail ∉ ({a, b} : Set V) ∧
                              (R.toHypermap).face.symm e ∈
                                  EdgeDeletion.contractionFaceBoundary hab R e ∧
                                (R.toHypermap).face e ∈
                                  EdgeDeletion.contractionFaceBoundary hab R e) ∧
              Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
                Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
                  Exists fun dTheta : OrientedEdge
                      (EdgeDeletion.deletedGraph G a b) =>
                    (deleteEdgeEndsGraph G a b).Adj x y ∧
                      dTheta.tail = (x : V) ∧
                        dTheta.head = (y : V) ∧
                          (EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta).tail =
                              EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                            (EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta).head =
                              EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                              Not
                                ((EdgeDeletion.contractionFaceBoundaryDeleteEndsSubgraph
                                    hab R e).Adj x y) := by
  rcases hcontract with ⟨R, hRdual⟩
  have hR : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hRdual
  rcases
      EdgeDeletion.exists_selected_boundary_corner_and_theta_dart_not_boundary_of_faceOrbitNoTheta
        hface hmin hab R hR htheta with
    ⟨e, htail, hcorner, x, y, dTheta, hxy, hdTheta_tail,
      hdTheta_head, hdTheta_collapse_tail, hdTheta_collapse_head,
      hnotBoundary⟩
  exact
    ⟨R, hRdual, e, htail, hcorner, x, y, dTheta, hxy,
      hdTheta_tail, hdTheta_head, hdTheta_collapse_tail,
      hdTheta_collapse_head, hnotBoundary⟩

/-- Recursive-contraction wrapper for the strengthened split datum: besides
the pulled-back non-boundary fact, the selected theta dart's quotient image is
not an edge of the selected contraction face boundary. -/
theorem HasEulerRotationSystem.exists_selected_boundary_corner_and_theta_dart_not_boundary_and_not_outsideBoundary_of_faceOrbitNoTheta
    (hface : EdgeDeletion.FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (hcontract :
      HasEulerRotationSystem
        (GraphContraction.collapseEdge G hab).graph)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun R : RotationSystem (GraphContraction.collapseEdge G hab).graph =>
      (R.toHypermap).dual.EulerPlanar ∧
        Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
          e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
            (Exists fun dLeave : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
                (dLeave.tail = a ∨ dLeave.tail = b) ∧
                  Exists fun dPrev : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                    EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dPrev =
                        (R.toHypermap).face.symm e ∧
                      (dPrev.head = a ∨ dPrev.head = b) ∧
                        Exists fun dNext : OrientedEdge
                            (EdgeDeletion.deletedGraph G a b) =>
                          EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dNext =
                              (R.toHypermap).face e ∧
                            dNext.tail ∉ ({a, b} : Set V) ∧
                              (R.toHypermap).face.symm e ∈
                                  EdgeDeletion.contractionFaceBoundary hab R e ∧
                                (R.toHypermap).face e ∈
                                  EdgeDeletion.contractionFaceBoundary hab R e) ∧
              Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
                Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
                  Exists fun dTheta : OrientedEdge
                      (EdgeDeletion.deletedGraph G a b) =>
                    (deleteEdgeEndsGraph G a b).Adj x y ∧
                      dTheta.tail = (x : V) ∧
                        dTheta.head = (y : V) ∧
                          (EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta).tail =
                              EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                            (EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta).head =
                              EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                              Not
                                ((EdgeDeletion.contractionFaceBoundaryDeleteEndsSubgraph
                                    hab R e).Adj x y) ∧
                                Not
                                  ((EdgeDeletion.contractionFaceBoundaryOutsideSubgraph
                                      hab R e).Adj
                                    (EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom
                                      G hab x)
                                    (EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom
                                      G hab y)) := by
  rcases hcontract with ⟨R, hRdual⟩
  have hR : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hRdual
  rcases
      EdgeDeletion.exists_selected_boundary_corner_and_theta_dart_not_boundary_and_not_outsideBoundary_of_faceOrbitNoTheta
        hface hmin hab R hR htheta with
    ⟨e, htail, hcorner, x, y, dTheta, hxy, hdTheta_tail,
      hdTheta_head, hdTheta_collapse_tail, hdTheta_collapse_head,
      hnotBoundary, hnotOutsideBoundary⟩
  exact
    ⟨R, hRdual, e, htail, hcorner, x, y, dTheta, hxy,
      hdTheta_tail, hdTheta_head, hdTheta_collapse_tail,
      hdTheta_collapse_head, hnotBoundary, hnotOutsideBoundary⟩

/-- Recursive-contraction wrapper for the fully strengthened split datum:
the selected theta dart is outside the pulled-back boundary, outside the
outside-boundary edge set, and not a member of the selected contraction face
orbit. -/
theorem HasEulerRotationSystem.exists_selected_boundary_corner_and_theta_dart_not_boundary_and_not_faceBoundary_of_faceOrbitNoTheta
    (hface : EdgeDeletion.FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (hcontract :
      HasEulerRotationSystem
        (GraphContraction.collapseEdge G hab).graph)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun R : RotationSystem (GraphContraction.collapseEdge G hab).graph =>
      (R.toHypermap).dual.EulerPlanar ∧
        Exists fun e : OrientedEdge (GraphContraction.collapseEdge G hab).graph =>
          e.tail = (none : (GraphContraction.collapseEdge G hab).Target) ∧
            (Exists fun dLeave : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dLeave = e ∧
                (dLeave.tail = a ∨ dLeave.tail = b) ∧
                  Exists fun dPrev : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                    EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dPrev =
                        (R.toHypermap).face.symm e ∧
                      (dPrev.head = a ∨ dPrev.head = b) ∧
                        Exists fun dNext : OrientedEdge
                            (EdgeDeletion.deletedGraph G a b) =>
                          EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dNext =
                              (R.toHypermap).face e ∧
                            dNext.tail ∉ ({a, b} : Set V) ∧
                              (R.toHypermap).face.symm e ∈
                                  EdgeDeletion.contractionFaceBoundary hab R e ∧
                                (R.toHypermap).face e ∈
                                  EdgeDeletion.contractionFaceBoundary hab R e) ∧
              Exists fun x : {z : V | z ∉ ({a, b} : Set V)} =>
                Exists fun y : {z : V | z ∉ ({a, b} : Set V)} =>
                  Exists fun dTheta : OrientedEdge
                      (EdgeDeletion.deletedGraph G a b) =>
                    (deleteEdgeEndsGraph G a b).Adj x y ∧
                      dTheta.tail = (x : V) ∧
                        dTheta.head = (y : V) ∧
                          (EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta).tail =
                              EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom G hab x ∧
                            (EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta).head =
                              EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom G hab y ∧
                              Not
                                ((EdgeDeletion.contractionFaceBoundaryDeleteEndsSubgraph
                                    hab R e).Adj x y) ∧
                                Not
                                  ((EdgeDeletion.contractionFaceBoundaryOutsideSubgraph
                                      hab R e).Adj
                                    (EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom
                                      G hab x)
                                    (EdgeDeletion.deleteEdgeEndsGraphToCollapseEdgeHom
                                      G hab y)) ∧
                                  EdgeDeletion.deletedGraphToCollapseEdgeDart G hab dTheta ∉
                                    EdgeDeletion.contractionFaceBoundary hab R e := by
  rcases hcontract with ⟨R, hRdual⟩
  have hR : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hRdual
  rcases
      EdgeDeletion.exists_selected_boundary_corner_and_theta_dart_not_boundary_and_not_faceBoundary_of_faceOrbitNoTheta
        hface hmin hab R hR htheta with
    ⟨e, htail, hcorner, x, y, dTheta, hxy, hdTheta_tail,
      hdTheta_head, hdTheta_collapse_tail, hdTheta_collapse_head,
      hnotBoundary, hnotOutsideBoundary, hnotFaceBoundary⟩
  exact
    ⟨R, hRdual, e, htail, hcorner, x, y, dTheta, hxy,
      hdTheta_tail, hdTheta_head, hdTheta_collapse_tail,
      hdTheta_collapse_head, hnotBoundary, hnotOutsideBoundary,
      hnotFaceBoundary⟩

/-- Recursive-contraction wrapper exposing the named selected split datum. -/
theorem HasEulerRotationSystem.exists_selectedSplitDatum_of_faceOrbitNoTheta
    (hface : EdgeDeletion.FaceOrbitNoThetaTheorem.{u})
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (hcontract :
      HasEulerRotationSystem
        (GraphContraction.collapseEdge G hab).graph)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun R : RotationSystem (GraphContraction.collapseEdge G hab).graph =>
      (R.toHypermap).dual.EulerPlanar ∧
        Nonempty (EdgeDeletion.SelectedSplitDatum hab R) := by
  rcases hcontract with ⟨R, hRdual⟩
  have hR : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hRdual
  exact
    ⟨R, hRdual,
      EdgeDeletion.exists_selectedSplitDatum_of_faceOrbitNoTheta
        hface hmin hab R hR htheta⟩

/-- The reference proof's two recursive embeddings, packaged at the exact
outside edge selected from the contraction face.  The outside theta dart is
an edge of `G - ab`, hence its source dart is an edge of `G` and the recursive
edge-deletion family supplies the second Euler-planar rotation system. -/
theorem HasEulerRotationSystem.exists_selectedSplitDatum_and_outsideEdgeEmbedding
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : forall v : V, 3 <= G.degree v)
    (hdeleted :
      ∀ {x y : V} (_hxy : G.Adj x y),
        HasEulerRotationSystem (EdgeDeletion.deletedGraph G x y))
    (hab : G.Adj a b)
    [Fintype (GraphContraction.collapseEdge G hab).Target]
    [DecidableEq (GraphContraction.collapseEdge G hab).Target]
    [DecidableRel (GraphContraction.collapseEdge G hab).graph.Adj]
    (hcontract :
      HasEulerRotationSystem
        (GraphContraction.collapseEdge G hab).graph)
    (htheta : ContainsHomeomorphicTheta (deleteEdgeEndsGraph G a b)) :
    Exists fun R : RotationSystem (GraphContraction.collapseEdge G hab).graph =>
      (R.toHypermap).dual.EulerPlanar ∧
        Exists fun D : EdgeDeletion.SelectedSplitDatum hab R =>
          HasEulerRotationSystem
            (EdgeDeletion.deletedGraph G
              D.theta.dTheta.tail D.theta.dTheta.head) := by
  rcases hcontract.exists_selectedSplitDatum_of_faceOrbitNoTheta
      EdgeDeletion.faceOrbitNoTheta_proved hmin hab htheta with
    ⟨R, hR, ⟨D⟩⟩
  have hthetaAdj :
      G.Adj D.theta.dTheta.tail D.theta.dTheta.head :=
    (EdgeDeletion.sourceDart D.theta.dTheta).adj
  exact ⟨R, hR, D, hdeleted hthetaAdj⟩

/-- Edge-deletion add-back branch for the non-circular embedding target.  If
`G - ab` has an Euler-planar rotation system in which the two endpoint splice
pivots are present and cofacial, then inserting `ab` gives an Euler-planar
rotation system on `G`. -/
theorem HasEulerRotationSystem.of_deleteEdge_of_cofacial
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (EdgeDeletion.deletedGraph G a b))
    {p q : OrientedEdge (EdgeDeletion.deletedGraph G a b)}
    (hR : (R.toHypermap).dual.EulerPlanar)
    (hpA : EdgeDeletion.addEdgePivotA G a b = some p)
    (hpB : EdgeDeletion.addEdgePivotB G a b = some q)
    (hcofacial : EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  let S : RotationSystem G :=
    EdgeDeletion.addEdgeRotationSystem (G := G) (a := a) (b := b) hab R
  refine ⟨S, ?_⟩
  have hold : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hnew : (S.toHypermap).EulerPlanar := by
    exact
      (EdgeDeletion.addEdgeRotationSystem_eulerPlanar_iff_some_some_of_cofacial
        (G := G) (a := a) (b := b) hab R hpA hpB hcofacial).mpr hold
  exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hnew

/-- Source-facing add-back branch with explicitly chosen endpoint pivots.
Unlike `of_deleteEdge_of_cofacial`, this does not depend on the arbitrary
`endpointPivot` choices; the source proof supplies the two darts that border
the common face. -/
theorem HasEulerRotationSystem.of_deleteEdge_of_cofacial_pivots
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (R : RotationSystem (EdgeDeletion.deletedGraph G a b))
    {p q : OrientedEdge (EdgeDeletion.deletedGraph G a b)}
    (hR : (R.toHypermap).dual.EulerPlanar)
    (hpA : p.tail = a)
    (hpB : q.tail = b)
    (hcofacial : EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  let S : RotationSystem G :=
    EdgeDeletion.addEdgeRotationSystemAt
      (G := G) (a := a) (b := b) hab R p q hpA hpB
  refine ⟨S, ?_⟩
  have hold : (R.toHypermap).EulerPlanar :=
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
  have hnew : (S.toHypermap).EulerPlanar := by
    exact
      (EdgeDeletion.addEdgeRotationSystemAt_eulerPlanar_iff_of_cofacial
        (G := G) (a := a) (b := b) hab R hpA hpB hcofacial).mpr hold
  exact (Hypermap.dual_eulerPlanar_iff (G := S.toHypermap)).mpr hnew

/-- Induction-facing edge-deletion branch.  This packages the previous theorem
so a source/minimal-counterexample argument only has to produce a suitable
rotation system on the deleted graph together with the cofacial endpoint
witnesses. -/
theorem HasEulerRotationSystem.of_deleteEdge_of_exists_cofacial
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (hdel :
      Exists fun R : RotationSystem (EdgeDeletion.deletedGraph G a b) =>
        (R.toHypermap).dual.EulerPlanar ∧
          Exists fun p : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
            Exists fun q : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              EdgeDeletion.addEdgePivotA G a b = some p ∧
                EdgeDeletion.addEdgePivotB G a b = some q ∧
                  EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  rcases hdel with ⟨R, hR, p, q, hpA, hpB, hcofacial⟩
  exact
    HasEulerRotationSystem.of_deleteEdge_of_cofacial
      (G := G) (a := a) (b := b) hab R hR hpA hpB hcofacial

/-- Induction-facing edge-deletion branch with explicit endpoint pivots. -/
theorem HasEulerRotationSystem.of_deleteEdge_of_exists_cofacial_pivots
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (hdel :
      Exists fun R : RotationSystem (EdgeDeletion.deletedGraph G a b) =>
        (R.toHypermap).dual.EulerPlanar ∧
          Exists fun p : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
            Exists fun q : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              p.tail = a ∧ q.tail = b ∧
                EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  rcases hdel with ⟨R, hR, p, q, hpA, hpB, hcofacial⟩
  exact
    HasEulerRotationSystem.of_deleteEdge_of_cofacial_pivots
      (G := G) (a := a) (b := b) hab R hR hpA hpB hcofacial

/-- Induction-ready planar deletion branch.  Planarity of the deleted graph is
obtained from the source graph by monotonicity; the remaining source theorem
only has to choose an Euler-planar deleted-edge rotation system whose endpoint
pivots are cofacial. -/
theorem HasEulerRotationSystem.of_isPlanar_deleteEdge_of_exists_cofacial
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (hdel :
      IsPlanar (EdgeDeletion.deletedGraph G a b) →
        Exists fun R : RotationSystem (EdgeDeletion.deletedGraph G a b) =>
          (R.toHypermap).dual.EulerPlanar ∧
            Exists fun p : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              Exists fun q : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                EdgeDeletion.addEdgePivotA G a b = some p ∧
                  EdgeDeletion.addEdgePivotB G a b = some q ∧
                    EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  exact
    HasEulerRotationSystem.of_deleteEdge_of_exists_cofacial
      (G := G) (a := a) (b := b) hab
      (hdel (h_planar.deleteEdges ({s(a, b)} : Set (Sym2 V))))

/-- Induction-ready planar deletion branch with explicit source-selected
endpoint pivots. -/
theorem HasEulerRotationSystem.of_isPlanar_deleteEdge_of_exists_cofacial_pivots
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_planar : IsPlanar G)
    {a b : V}
    (hab : G.Adj a b)
    (hdel :
      IsPlanar (EdgeDeletion.deletedGraph G a b) →
        Exists fun R : RotationSystem (EdgeDeletion.deletedGraph G a b) =>
          (R.toHypermap).dual.EulerPlanar ∧
            Exists fun p : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
              Exists fun q : OrientedEdge (EdgeDeletion.deletedGraph G a b) =>
                p.tail = a ∧ q.tail = b ∧
                  EdgeDeletion.addEdgeCofacial R.toHypermap (some p) (some q)) :
    HasEulerRotationSystem G := by
  classical
  exact
    HasEulerRotationSystem.of_deleteEdge_of_exists_cofacial_pivots
      (G := G) (a := a) (b := b) hab
      (hdel (h_planar.deleteEdges ({s(a, b)} : Set (Sym2 V))))

namespace EdgeDeletion

/-- Source-facing deleted-edge embedding witness.  For a selected source edge
`ab`, this packages exactly the data needed to add the edge back: an
Euler-planar rotation system on `G - ab` and two endpoint darts, one based at
`a` and one based at `b`, lying on a common face. -/
def HasCofacialDeletedEmbedding
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (a b : V) : Prop :=
  Exists fun R : RotationSystem (deletedGraph G a b) =>
    (R.toHypermap).dual.EulerPlanar ∧
      Exists fun p : OrientedEdge (deletedGraph G a b) =>
        Exists fun q : OrientedEdge (deletedGraph G a b) =>
          p.tail = a ∧ q.tail = b ∧
            addEdgeCofacial R.toHypermap (some p) (some q)

theorem HasCofacialDeletedEmbedding.hasEulerRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (h : HasCofacialDeletedEmbedding (G := G) a b) :
    HasEulerRotationSystem (deletedGraph G a b) := by
  rcases h with ⟨R, hR, _p, _q, _hp, _hq, _hcofacial⟩
  exact ⟨R, hR⟩

theorem not_addEdgeCofacial_of_not_hasCofacialDeletedEmbedding
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hno : ¬ HasCofacialDeletedEmbedding (G := G) a b)
    {R : RotationSystem (deletedGraph G a b)}
    (hR : (R.toHypermap).dual.EulerPlanar)
    {p q : OrientedEdge (deletedGraph G a b)}
    (hp : p.tail = a)
    (hq : q.tail = b) :
    ¬ addEdgeCofacial R.toHypermap (some p) (some q) := by
  intro hcofacial
  exact hno ⟨R, hR, p, q, hp, hq, hcofacial⟩

theorem exists_endpointDarts_not_addEdgeCofacial_of_min_degree_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hmin : forall v : V, 3 <= G.degree v)
    {a b : V}
    (hno : ¬ HasCofacialDeletedEmbedding (G := G) a b)
    {R : RotationSystem (deletedGraph G a b)}
    (hR : (R.toHypermap).dual.EulerPlanar) :
    Exists fun p : OrientedEdge (deletedGraph G a b) =>
      Exists fun q : OrientedEdge (deletedGraph G a b) =>
        p.tail = a ∧ q.tail = b ∧
          ¬ addEdgeCofacial R.toHypermap (some p) (some q) := by
  classical
  rcases addEdgeEndpointDarts_exist_of_min_degree_three
      (G := G) hmin a b with
    ⟨p, q, hp, hq⟩
  exact ⟨p, q, hp, hq,
    not_addEdgeCofacial_of_not_hasCofacialDeletedEmbedding
      (G := G) hno hR hp hq⟩

/-- Local cofacial endpoint-dart criterion.  If after deleting only the source
edge `ab` the two endpoints share a neighbour `z` of degree at most three, then
some outgoing dart at `a` and some outgoing dart at `b` lie on a common face of
any rotation system. -/
theorem exists_cofacial_endpointDarts_of_common_neighbor_degree_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b z : V}
    (hab : G.Adj a b)
    (haz : G.Adj a z)
    (hbz : G.Adj b z)
    (R : RotationSystem (deletedGraph G a b))
    (hzdeg : (deletedGraph G a b).degree z <= 3) :
    Exists fun p : OrientedEdge (deletedGraph G a b) =>
      Exists fun q : OrientedEdge (deletedGraph G a b) =>
        p.tail = a ∧ q.tail = b ∧
          addEdgeCofacial R.toHypermap (some p) (some q) := by
  classical
  let epG : OrientedEdge G := ⟨(a, z), haz⟩
  have hep_not_deleted : s(epG.tail, epG.head) ≠ s(a, b) := by
    intro hs
    have hcases :
        (a = a ∧ z = b) ∨ (a = b ∧ z = a) := by
      simpa [epG, OrientedEdge.tail, OrientedEdge.head, Sym2.eq_iff] using hs
    rcases hcases with ⟨_, hzb⟩ | ⟨hab_eq, _⟩
    · exact hbz.ne hzb.symm
    · exact hab.ne hab_eq
  let eqG : OrientedEdge G := ⟨(b, z), hbz⟩
  have heq_not_deleted : s(eqG.tail, eqG.head) ≠ s(a, b) := by
    intro hs
    have hcases :
        (b = a ∧ z = b) ∨ (b = b ∧ z = a) := by
      simpa [eqG, OrientedEdge.tail, OrientedEdge.head, Sym2.eq_iff] using hs
    rcases hcases with ⟨hba_eq, _⟩ | ⟨_, hza⟩
    · exact hab.ne hba_eq.symm
    · exact haz.ne hza.symm
  let ep : OrientedEdge (deletedGraph G a b) :=
    oldDart (G := G) (a := a) (b := b) epG hep_not_deleted
  let eq : OrientedEdge (deletedGraph G a b) :=
    oldDart (G := G) (a := a) (b := b) eqG heq_not_deleted
  have hep_head : ep.head = z := by
    rfl
  have heq_head : eq.head = z := by
    rfl
  have hep_ne_eq : ep ≠ eq := by
    intro h
    have ha_eq_b : a = b := by
      simpa [ep, eq, epG, eqG, OrientedEdge.tail] using
        congrArg OrientedEdge.tail h
    exact hab.ne ha_eq_b
  rcases
      R.exists_faceReachable_endpointDarts_of_same_head_degree_le_three
        (x := z) hzdeg (e := ep) (f := eq) hep_head heq_head
        hep_ne_eq with
    ⟨pD, qD, hpD, hqD, hreach⟩
  exact ⟨pD, qD, hpD, hqD,
    (addEdgeCofacial_some_some R.toHypermap pD qD).mpr hreach⟩

end EdgeDeletion

/-- Add back a selected source edge from a packaged cofacial deleted
embedding. -/
theorem HasEulerRotationSystem.of_deletedCofacialEmbedding
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (hdel : EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b) :
    HasEulerRotationSystem G :=
  HasEulerRotationSystem.of_deleteEdge_of_exists_cofacial_pivots
    (G := G) (a := a) (b := b) hab hdel

/-- Minimal-counterexample contrapositive for the deleted-edge source branch:
if adding `ab` back from any cofacial deleted embedding would contradict the
assumed counterexample, then no such deleted embedding can exist. -/
theorem not_hasCofacialDeletedEmbedding_of_not_hasEulerRotationSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V}
    (hab : G.Adj a b)
    (hnot : ¬ HasEulerRotationSystem G) :
    ¬ EdgeDeletion.HasCofacialDeletedEmbedding (G := G) a b := by
  intro hdel
  exact hnot
    (HasEulerRotationSystem.of_deletedCofacialEmbedding
      (G := G) (a := a) (b := b) hab hdel)

end FourColor

end Schematic.Math.GraphTheory
