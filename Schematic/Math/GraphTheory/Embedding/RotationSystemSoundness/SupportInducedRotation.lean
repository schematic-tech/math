import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.FaceCounting
import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.CarrierConnectivity
import Schematic.Math.GraphTheory.Embedding.KuratowskiTheta.LowDegreeStructure

namespace Schematic.Math.GraphTheory.FourColor

open SimpleGraph

namespace RotationSoundness
/-- Oriented edges are unchanged when isolated vertices are discarded. -/
noncomputable def orientedEdgeSupportInduceEquiv
    {V : Type u}
    (G : SimpleGraph V) :
    OrientedEdge (G.induce G.support) ≃ OrientedEdge G where
  toFun e := ⟨((e.tail : V), (e.head : V)), e.adj⟩
  invFun e := ⟨
    (⟨e.tail, by
      rw [SimpleGraph.mem_support]
      exact ⟨e.head, e.adj⟩⟩,
     ⟨e.head, by
      rw [SimpleGraph.mem_support]
      exact ⟨e.tail, e.adj.symm⟩⟩),
    e.adj⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  right_inv := by
    intro e
    apply Subtype.ext
    rfl

@[simp]
theorem orientedEdgeSupportInduceEquiv_symm
    {V : Type u}
    (G : SimpleGraph V)
    (e : OrientedEdge (G.induce G.support)) :
    orientedEdgeSupportInduceEquiv G e.symm =
      (orientedEdgeSupportInduceEquiv G e).symm := by
  rfl

namespace RotationSystem

/-- Restrict a rotation system to the support-induced graph. -/
noncomputable def supportInduce
    {V : Type u}
    {G : SimpleGraph V}
    (R : RotationSystem G) :
    RotationSystem (G.induce G.support) where
  node :=
    ((orientedEdgeSupportInduceEquiv G).trans R.node).trans
      (orientedEdgeSupportInduceEquiv G).symm
  node_tail := by
    intro e
    apply Subtype.ext
    exact R.node_tail (orientedEdgeSupportInduceEquiv G e)
  node_orbit_of_same_tail := by
    intro e f hef
    let E := orientedEdgeSupportInduceEquiv G
    have htail : (E e).tail = (E f).tail := by
      exact congrArg Subtype.val hef
    have hR : PermReachable R.node (E e) (E f) :=
      R.node_orbit_of_same_tail (E e) (E f) htail
    have hconj : forall x : OrientedEdge (G.induce G.support),
        E ((((E.trans R.node).trans E.symm) x)) = R.node (E x) := by
      intro x
      simp [E]
    exact
      (permReachable_conj_iff E (((E.trans R.node).trans E.symm))
        R.node hconj).mpr hR

@[simp]
theorem supportInduce_node
    {V : Type u}
    {G : SimpleGraph V}
    (R : RotationSystem G)
    (e : OrientedEdge (G.induce G.support)) :
    orientedEdgeSupportInduceEquiv G ((supportInduce R).node e) =
      R.node (orientedEdgeSupportInduceEquiv G e) := by
  simp [supportInduce]

noncomputable def supportInduce_toHypermapIso
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) :
    Hypermap.Iso (supportInduce R).toHypermap R.toHypermap :=
  Hypermap.Iso.ofEdgeNode
    (orientedEdgeSupportInduceEquiv G)
    (by intro e; rfl)
    (supportInduce_node R)

end RotationSystem

theorem HasEulerRotationSystem.induceSupport
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : HasEulerRotationSystem G) :
    HasEulerRotationSystem (G.induce G.support) := by
  classical
  rcases hG with ⟨R, hR⟩
  let S := RotationSystem.supportInduce R
  let φ : Hypermap.Iso S.toHypermap R.toHypermap :=
    RotationSystem.supportInduce_toHypermapIso R
  refine ⟨S, ?_⟩
  have hprimal : R.toHypermap.EulerPlanar :=
    R.toHypermap.dual_eulerPlanar_iff.mp hR
  have hsource : S.toHypermap.EulerPlanar :=
    (φ.eulerPlanar_iff).mpr hprimal
  exact S.toHypermap.dual_eulerPlanar_iff.mpr hsource

/-- Once every used carrier vertex is a branch vertex, the exact carrier is
isomorphic to the source graph. -/
noncomputable def strictSubdivisionCarrierCoreIso
    {W : Type u} {V : Type v}
    [LinearOrder W] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (M : StrictSubdivisionModel H G)
    (hsource : forall x : W, Exists fun y : W => H.Adj x y)
    (hsurj : Function.Surjective
      ((edgeRestrictStrictSubdivisionCarrier
        (orderedStrictSubdivisionModel M)).targetRestrictSupport
          hsource).branchVertex) :
    H ≃g
      (strictSubdivisionCarrierGraph
        (orderedStrictSubdivisionModel M)).induce
          (strictSubdivisionCarrierGraph
            (orderedStrictSubdivisionModel M)).support := by
  classical
  let N := orderedStrictSubdivisionModel M
  let C := strictSubdivisionCarrierGraph N
  let L := edgeRestrictStrictSubdivisionCarrier N
  let K := L.targetRestrictSupport hsource
  let f : W → C.support := K.branchVertex
  have hfInjective : Function.Injective f := K.branchVertex_injective
  have hfSurjective : Function.Surjective f := hsurj
  exact {
    toEquiv := Equiv.ofBijective f ⟨hfInjective, hfSurjective⟩
    map_rel_iff' := by
      intro a b
      constructor
      · intro hab
        have habC : C.Adj (N.branchVertex a) (N.branchVertex b) := hab
        rcases (strictSubdivisionCarrierGraph_adj_iff N).mp habC with
          ⟨x, y, hxy, hpath⟩
        have haPath : N.branchVertex a ∈ (N.edgePath hxy).support := by
          rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
          exact (N.edgePath hxy).toSubgraph.edge_vert hpath
        have hbPath : N.branchVertex b ∈ (N.edgePath hxy).support := by
          rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
          exact (N.edgePath hxy).toSubgraph.edge_vert hpath.symm
        have haEnds := (N.branchVertex_mem_edgePath_support_iff hxy).mp haPath
        have hbEnds := (N.branchVertex_mem_edgePath_support_iff hxy).mp hbPath
        rcases haEnds with rfl | rfl <;> rcases hbEnds with rfl | rfl
        · exact False.elim (hab.ne rfl)
        · exact hxy
        · exact hxy.symm
        · exact False.elim (hab.ne rfl)
      · intro hab
        exact
          Schematic.Math.GraphTheory.FourColor.StrictSubdivisionModel.adj_of_branchVertex_surjective
            K hsurj hab
  }

private noncomputable def rotationSystemOfIsoToHypermapIso
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    (φ : G ≃g H) (R : RotationSystem H) :
    Hypermap.Iso (RotationSystem.ofIso φ R).toHypermap R.toHypermap where
  toEquiv := orientedEdgeEquivOfGraphIso φ
  map_edge := by
    intro e
    rfl
  map_node := by
    intro e
    exact RotationSystem.ofIso_node φ R e
  map_face := by
    intro e
    let ψ := orientedEdgeEquivOfGraphIso φ
    have hnode : forall x : OrientedEdge G,
        ψ ((RotationSystem.ofIso φ R).node x) = R.node (ψ x) := by
      intro x
      exact RotationSystem.ofIso_node φ R x
    change ψ ((RotationSystem.ofIso φ R).node.symm e.symm) =
      R.node.symm ((ψ e).symm)
    calc
      ψ ((RotationSystem.ofIso φ R).node.symm e.symm) =
          R.node.symm (ψ e.symm) :=
        perm_conj_symm_apply ψ (RotationSystem.ofIso φ R).node
          R.node hnode e.symm
      _ = R.node.symm ((ψ e).symm) := by
        rw [orientedEdgeEquivOfGraphIso_symm]

theorem HasEulerRotationSystem.of_iso_univ
    {V : Type u} {W : Type v}
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
  have htarget : R.toHypermap.EulerPlanar :=
    R.toHypermap.dual_eulerPlanar_iff.mp hR
  have hsource : RG.toHypermap.EulerPlanar := by
    let ψ : Hypermap.Iso RG.toHypermap R.toHypermap :=
      rotationSystemOfIsoToHypermapIso φ R
    exact (ψ.eulerPlanar_iff).mpr htarget
  exact RG.toHypermap.dual_eulerPlanar_iff.mpr hsource

theorem K5Graph_isTwoConnected : IsTwoConnected K5Graph := by
  classical
  have hconnected : K5Graph.Connected := by
    letI : Nonempty (Fin 5) := inferInstance
    exact ⟨K5Graph_preconnected⟩
  refine ⟨by simp [Nat.card_eq_fintype_card], ?_⟩
  intro S hS
  have hSle : S.ncard ≤ 1 := by omega
  rcases (Set.ncard_le_one_iff_eq (s := S)).mp hSle with rfl | ⟨z, rfl⟩
  · have hempty : ((∅ : Set (Fin 5))ᶜ) = Set.univ := by ext x; simp
    rw [hempty]
    exact connected_induce_univ_of_connected hconnected
  · let A : Set (Fin 5) := ({z} : Set (Fin 5))ᶜ
    obtain ⟨w, hw⟩ := exists_ne z
    have hAnonempty : Nonempty A := ⟨⟨w, by simp [A, hw]⟩⟩
    refine { nonempty := hAnonempty, preconnected := ?_ }
    intro a b
    by_cases hab : a = b
    · subst b
      exact SimpleGraph.Reachable.rfl
    · exact (show (K5Graph.induce A).Adj a b by
        simpa [K5Graph, CompleteGraphOn] using hab).reachable

theorem K33Graph_isTwoConnected : IsTwoConnected K33Graph := by
  classical
  have hconnected : K33Graph.Connected := by
    letI : Nonempty K33Vertex := ⟨Sum.inl 0⟩
    exact ⟨K33Graph_preconnected⟩
  refine ⟨by simp [Nat.card_eq_fintype_card], ?_⟩
  intro S hS
  have hSle : S.ncard ≤ 1 := by omega
  rcases (Set.ncard_le_one_iff_eq (s := S)).mp hSle with rfl | ⟨z, rfl⟩
  · have hempty : ((∅ : Set K33Vertex)ᶜ) = Set.univ := by ext x; simp
    rw [hempty]
    exact connected_induce_univ_of_connected hconnected
  · let A : Set K33Vertex := ({z} : Set K33Vertex)ᶜ
    have hAnonempty : Nonempty A := by
      cases z with
      | inl i => exact ⟨⟨Sum.inr 0, by simp [A]⟩⟩
      | inr i => exact ⟨⟨Sum.inl 0, by simp [A]⟩⟩
    refine { nonempty := hAnonempty, preconnected := ?_ }
    intro a b
    cases ha : (a : K33Vertex) with
    | inl i =>
        cases hb : (b : K33Vertex) with
        | inl j =>
            obtain ⟨k, hkz⟩ : Exists fun k : Fin 3 => Sum.inr k ≠ z := by
              cases z with
              | inl t => exact ⟨0, by simp⟩
              | inr t =>
                  fin_cases t
                  · exact ⟨1, by simp⟩
                  · exact ⟨0, by simp⟩
                  · exact ⟨0, by simp⟩
            let kA : A := ⟨Sum.inr k, by simpa [A] using hkz⟩
            exact
              (show (K33Graph.induce A).Adj a kA by
                simpa [K33Graph, ha] using
                  (show K33Graph.Adj (Sum.inl i) (Sum.inr k) by
                    simp [K33Graph])).reachable.trans
              (show (K33Graph.induce A).Adj kA b by
                simpa [K33Graph, hb] using
                  (show K33Graph.Adj (Sum.inr k) (Sum.inl j) by
                    simp [K33Graph])).reachable
        | inr j =>
            exact (show (K33Graph.induce A).Adj a b by
              simp [K33Graph, ha, hb]).reachable
    | inr i =>
        cases hb : (b : K33Vertex) with
        | inl j =>
            exact (show (K33Graph.induce A).Adj a b by
              simp [K33Graph, ha, hb]).reachable
        | inr j =>
            obtain ⟨k, hkz⟩ : Exists fun k : Fin 3 => Sum.inl k ≠ z := by
              cases z with
              | inr t => exact ⟨0, by simp⟩
              | inl t =>
                  fin_cases t
                  · exact ⟨1, by simp⟩
                  · exact ⟨0, by simp⟩
                  · exact ⟨0, by simp⟩
            let kA : A := ⟨Sum.inl k, by simpa [A] using hkz⟩
            exact
              (show (K33Graph.induce A).Adj a kA by
                simpa [K33Graph, ha] using
                  (show K33Graph.Adj (Sum.inr i) (Sum.inl k) by
                    simp [K33Graph])).reachable.trans
              (show (K33Graph.induce A).Adj kA b by
                simpa [K33Graph, hb] using
                  (show K33Graph.Adj (Sum.inl k) (Sum.inr j) by
                    simp [K33Graph])).reachable


end RotationSoundness

end Schematic.Math.GraphTheory.FourColor
