import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.Forest

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- Full maximum-degree-two endpoint for the Kuratowski/rotation-system
bridge.  The finite support components are split into those with an explicit
simple cycle and those without one; the latter are trees and supply two
leaf-endpoints for the mixed path/cycle count. -/
theorem exists_eulerRotationSystem_of_degree_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  let Comp := (G.induce G.support).ConnectedComponent
  let Cyc : Finset Comp :=
    Finset.univ.filter fun C : Comp =>
      Exists fun u : V =>
        Exists fun hu : u ∈ G.support =>
          (⟨u, hu⟩ : G.support) ∈ C.supp ∧
            Exists fun c : G.Walk u u => c.IsCycle
  have hcycle :
      forall C : Comp, C ∈ Cyc ->
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  have hendpoints :
      forall C : Comp, C ∉ Cyc ->
        Exists fun a : G.support =>
          Exists fun b : G.support =>
            a ∈ C.supp ∧ b ∈ C.supp ∧ a ≠ b ∧
              G.degree (a : V) <= 1 ∧ G.degree (b : V) <= 1 := by
    intro C hC
    exact
      support_connectedComponent_exists_two_degree_le_one_of_no_cycle
        (G := G) C
        (by
          intro hcyclic
          exact hC (Finset.mem_filter.mpr ⟨Finset.mem_univ C, hcyclic⟩))
  exact
    exists_eulerRotationSystem_of_degree_le_two_of_component_cycle_endpoint_data
      (G := G) hdegree Cyc hcycle hendpoints

/-- The three-vertex base case of the Kuratowski bridge. -/
theorem exists_eulerRotationSystem_of_card_le_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcard : Fintype.card V <= 3) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_degree_le_two
    (G := G) (degree_le_two_of_card_le_three (G := G) hcard)

/-- Disconnected two-regular support endpoint for the rotation-system bridge.
If every non-isolated vertex has degree exactly two, then each support
component is cyclic, and the componentwise two-face count proves the canonical
rotation system Euler-planar. -/
theorem exists_eulerRotationSystem_of_support_degree_eq_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree_eq : forall x : G.support, G.degree (x : V) = 2) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  have hdegree_le : forall x : V, G.degree x <= 2 := by
    intro x
    by_cases hx : x ∈ G.support
    · have hxdeg : G.degree x = 2 := hdegree_eq ⟨x, hx⟩
      omega
    · have hxdeg : G.degree x = 0 := by
        exact (SimpleGraph.degree_eq_zero_iff_notMem_support
          (G := G) (v := x)).mpr hx
      omega
  have hno_endpoint :
      ¬ Exists fun x : G.support => G.degree (x : V) <= 1 := by
    rintro ⟨x, hx⟩
    have hxdeg : G.degree (x : V) = 2 := hdegree_eq x
    omega
  have hcycles : G.IsCycles :=
    isCycles_of_degree_le_two_of_no_support_degree_le_one
      (G := G) hdegree_le hno_endpoint
  have hcomponent_cycles :
      forall C : (G.induce G.support).ConnectedComponent,
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle := by
    intro C
    obtain ⟨x, hxC⟩ := C.nonempty_supp
    have hx_neighbor : (G.neighborSet (x : V)).Nonempty := by
      rcases (SimpleGraph.mem_support (G := G)).mp x.property with
        ⟨w, hxw⟩
      exact ⟨w, hxw⟩
    let CG : G.ConnectedComponent := G.connectedComponentMk (x : V)
    have hxCG : (x : V) ∈ CG.supp := by
      simp [CG]
    rcases
        SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
          (G := G) (v := (x : V)) (c := CG) hcycles hxCG
          hx_neighbor with
      ⟨p, hpcycle, _hpverts⟩
    exact ⟨x, x.property, hxC, p, hpcycle⟩
  exact
    exists_eulerRotationSystem_of_degree_le_two_of_component_cycles
      (G := G) hdegree_le hcomponent_cycles

/-- Endpoint-free maximum-degree-two graphs are exactly the disconnected
cycle-union case for the canonical rotation-system bridge.  This is the
global form of the connected source split used in
`exists_eulerRotationSystem_of_degree_le_two_support_preconnected_nonempty`:
if no non-isolated vertex has degree at most one, every supported vertex has
degree two, so each support component contributes the two cycle faces already
constructed above. -/
theorem exists_eulerRotationSystem_of_degree_le_two_of_no_support_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hno : ¬ Exists fun x : G.support => G.degree (x : V) <= 1) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  exact exists_eulerRotationSystem_of_support_degree_eq_two
    (G := G)
    (by
      intro x
      have hxle : G.degree (x : V) <= 2 := hdegree x
      have hxnot : ¬ G.degree (x : V) <= 1 := by
        intro hxone
        exact hno ⟨x, hxone⟩
      omega)

/-- Everywhere-two-regular finite simple graphs admit the canonical
Euler-planar rotation system, component by component. -/
theorem exists_eulerRotationSystem_of_degree_eq_two
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x = 2) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_support_degree_eq_two
    (G := G) (fun x => hdegree x)

/-- Connected graph form of the maximum-degree-two rotation endpoint. -/
theorem exists_eulerRotationSystem_of_degree_le_two_preconnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hG : G.Preconnected) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  exists_eulerRotationSystem_of_degree_le_two_support_preconnected
    (G := G) hdegree (support_preconnected_of_preconnected (G := G) hG)

/-- Oriented edges are transported by a graph isomorphism. -/
noncomputable def orientedEdgeEquivOfGraphIso
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) :
    OrientedEdge G ≃ OrientedEdge H where
  toFun e :=
    ⟨(φ e.tail, φ e.head), (φ.map_rel_iff).2 e.adj⟩
  invFun e :=
    ⟨(φ.symm e.tail, φ.symm e.head), (φ.symm.map_rel_iff).2 e.adj⟩
  left_inv := by
    intro e
    apply Subtype.ext
    simp [OrientedEdge.tail, OrientedEdge.head]
  right_inv := by
    intro e
    apply Subtype.ext
    simp [OrientedEdge.tail, OrientedEdge.head]

@[simp]
theorem orientedEdgeEquivOfGraphIso_tail
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (e : OrientedEdge G) :
    ((orientedEdgeEquivOfGraphIso φ e).tail) = φ e.tail :=
  rfl

@[simp]
theorem orientedEdgeEquivOfGraphIso_head
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (e : OrientedEdge G) :
    ((orientedEdgeEquivOfGraphIso φ e).head) = φ e.head :=
  rfl

@[simp]
theorem orientedEdgeEquivOfGraphIso_symm
    {V : Type u} {W : Type v}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (e : OrientedEdge G) :
    orientedEdgeEquivOfGraphIso φ e.symm =
      (orientedEdgeEquivOfGraphIso φ e).symm := by
  rfl
end FourColor

end Schematic.Math.GraphTheory
