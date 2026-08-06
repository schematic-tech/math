import Schematic.Math.GraphTheory.Minors.Society.Basic.Foundations.SocietyStructure
import Schematic.Math.GraphTheory.Minors.GMIX21

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- `A` catches a graph region if every component of the induced region meets
`A`.  This is the vertex-set version of the GM IX definition. -/
def Catches (G : SimpleGraph V) (A X : Set V) : Prop :=
  A ⊆ X ∧
    forall C : (G.induce X).ConnectedComponent,
      Exists fun a : V =>
        Exists fun haX : a ∈ X =>
          a ∈ A ∧ (⟨a, haX⟩ : X) ∈ C.supp

/-- The union of components of `G.induce X` that meet `A`.  In GM IX (2.4),
`X` is `G \ V(P)` and `A` is one of the two boundary arcs. -/
def ComponentUnionMeeting (G : SimpleGraph V) (A X : Set V) : Set V :=
  {v | Exists fun hvX : v ∈ X =>
    Exists fun C : (G.induce X).ConnectedComponent =>
      (⟨v, hvX⟩ : X) ∈ C.supp ∧
        Exists fun a : V =>
          Exists fun haX : a ∈ X =>
            a ∈ A ∧ (⟨a, haX⟩ : X) ∈ C.supp}

theorem ComponentUnionMeeting_subset (G : SimpleGraph V) (A X : Set V) :
    ComponentUnionMeeting G A X ⊆ X := by
  intro v hv
  exact hv.choose

theorem subset_ComponentUnionMeeting_of_subset
    (G : SimpleGraph V) {A X : Set V}
    (hAX : A ⊆ X) :
    A ⊆ ComponentUnionMeeting G A X := by
  intro a ha
  let haX : a ∈ X := hAX ha
  let C : (G.induce X).ConnectedComponent :=
    (G.induce X).connectedComponentMk ⟨a, haX⟩
  exact ⟨haX, C, SimpleGraph.ConnectedComponent.connectedComponentMk_mem,
    a, haX, ha, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

theorem ComponentUnionMeeting_catches
    (G : SimpleGraph V) {A X : Set V}
    (hAX : A ⊆ X) :
    Catches G A (ComponentUnionMeeting G A X) := by
  classical
  constructor
  · exact subset_ComponentUnionMeeting_of_subset G hAX
  · intro D
    obtain ⟨vSide, hvD⟩ := D.nonempty_supp
    rcases vSide.property with
      ⟨hvX, C, hvC, a, haX, haA, haC⟩
    have haSide : a ∈ ComponentUnionMeeting G A X :=
      ⟨haX, C, haC, a, haX, haA, haC⟩
    have hreachX :
        (G.induce X).Reachable
          (⟨(vSide : V), hvX⟩ : X) (⟨a, haX⟩ : X) :=
      C.reachable_of_mem_supp hvC haC
    obtain ⟨wX⟩ := hreachX
    let wG : G.Walk (vSide : V) a :=
      wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom
    have hwG_side :
        forall z : V, z ∈ wG.support ->
          z ∈ ComponentUnionMeeting G A X := by
      intro z hz
      change z ∈
        (wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨zX, hzX, hz_eq⟩
      subst z
      have hreach_start_z :
          (G.induce X).Reachable
            (⟨(vSide : V), hvX⟩ : X) zX :=
        (wX.takeUntil zX hzX).reachable
      have hstart_comp :
          (G.induce X).connectedComponentMk
              (⟨(vSide : V), hvX⟩ : X) = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C
          (⟨(vSide : V), hvX⟩ : X)).mp hvC
      have hz_comp :
          (G.induce X).connectedComponentMk zX = C := by
        exact (SimpleGraph.ConnectedComponent.sound hreach_start_z).symm.trans
          hstart_comp
      have hzC : zX ∈ C.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C zX).mpr hz_comp
      exact ⟨zX.property, C, hzC, a, haX, haA, haC⟩
    have hreachSide :
        (G.induce (ComponentUnionMeeting G A X)).Reachable
          vSide (⟨a, haSide⟩ :
            ComponentUnionMeeting G A X) := by
      simpa [wG] using
        Walk.reachable_induce_of_support_subset wG hwG_side
    have hD_eq :
        (G.induce (ComponentUnionMeeting G A X)).connectedComponentMk
            vSide = D :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff D vSide).mp hvD
    have haD :
        (⟨a, haSide⟩ : ComponentUnionMeeting G A X) ∈ D.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hreachSide).symm.trans hD_eq
    exact ⟨a, haSide, haA, haD⟩

/-- Convert the subgraph form of GM IX `(2.1)` catching into the vertex-set
catching predicate used by the GM IX `(2.4)` cut-path split, once the caught
subgraph has exactly the desired vertex set. -/
theorem Catches.of_GMIX21_catchesSubgraph_of_verts_eq
    {G : SimpleGraph V} {Z X : Set V} {H : G.Subgraph}
    (hcatch : GMIX21.CatchesSubgraph (G := G) Z H)
    (hverts : H.verts = X) :
    Catches G Z X := by
  classical
  constructor
  · intro z hz
    simpa [← hverts] using hcatch.subset_verts hz
  · intro C
    obtain ⟨uX, huC⟩ := C.nonempty_supp
    have huH : (uX : V) ∈ H.verts := by
      simp [hverts, uX.2]
    let CH : H.coe.ConnectedComponent :=
      H.coe.connectedComponentMk ⟨(uX : V), huH⟩
    obtain ⟨z, hzZ, hzCH⟩ := hcatch.component_meets CH
    obtain ⟨hzH, hzCH_supp⟩ := hzCH
    have hzX : z ∈ X := by
      simpa [← hverts] using hzH
    let f : H.coe →g G.induce X := {
      toFun := fun v => ⟨(v : V), by
        simp [← hverts, v.2]⟩
      map_rel' := by
        intro a b hab
        exact H.adj_sub hab
    }
    have hreachH :
        H.coe.Reachable
          (⟨(uX : V), huH⟩ : H.verts) (⟨z, hzH⟩ : H.verts) :=
      CH.reachable_of_mem_supp
        (by exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem)
        hzCH_supp
    have hreachX :
        (G.induce X).Reachable uX (⟨z, hzX⟩ : X) := by
      simpa [f] using hreachH.map f
    have hC_u :
        (G.induce X).connectedComponentMk uX = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C uX).mp huC
    have hzC : (⟨z, hzX⟩ : X) ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hreachX).symm.trans hC_u
    exact ⟨z, hzX, hzZ, hzC⟩

/-- A caught component supplies a path from any prescribed vertex of that
component to a witness in the catching set, and the whole path remains in the
same component.

The component conclusion is stronger than merely saying that the path stays
in `X`.  It is needed in the final GM IX `(2.4)` side-tripod argument, where
paths in two distinct components of `G - V(P)` must be proved disjoint. -/
theorem Catches.exists_path_to_witness_in_component
    (G : SimpleGraph V) {A X : Set V}
    (hcatch : Catches G A X)
    (C : (G.induce X).ConnectedComponent)
    {v : V} (hvX : v ∈ X) (hvC : (⟨v, hvX⟩ : X) ∈ C.supp) :
    Exists fun a : V =>
      Exists fun q : G.Walk v a =>
        a ∈ A ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support ->
            z ∈ induceComponentSupport (G := G) C) := by
  classical
  obtain ⟨a, haX, haA, haC⟩ := hcatch.2 C
  have hreach :
      (G.induce X).Reachable
        (⟨v, hvX⟩ : X) (⟨a, haX⟩ : X) :=
    C.reachable_of_mem_supp hvC haC
  obtain ⟨wX⟩ := hreach
  let wG : G.Walk v a :=
    wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom
  let q : G.Walk v a := wG.toPath
  have hwG_component :
      forall z : V, z ∈ wG.support ->
        z ∈ induceComponentSupport (G := G) C := by
    intro z hz
    change z ∈
      (wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨zX, hzX, hz_eq⟩
    subst z
    have hreach_start_z :
        (G.induce X).Reachable (⟨v, hvX⟩ : X) zX :=
      (wX.takeUntil zX hzX).reachable
    have hstart_component :
        (G.induce X).connectedComponentMk (⟨v, hvX⟩ : X) = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C
        (⟨v, hvX⟩ : X)).mp hvC
    have hzC : zX ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hreach_start_z).symm.trans
        hstart_component
    exact ⟨zX.property, hzC⟩
  refine ⟨a, q, haA, wG.toPath.property, ?_⟩
  intro z hz
  exact hwG_component z (SimpleGraph.Walk.support_toPath_subset wG hz)

/-- Two vertices represented in the same component of an induced graph are
joined by a simple ambient path whose support remains in that exact component.

Keeping the component, rather than only the ambient inducing set, in the
conclusion makes paths chosen in distinct components definitionally suitable
for disjointness arguments. -/
theorem exists_path_in_induceComponentSupport
    (G : SimpleGraph V) {X : Set V}
    (C : (G.induce X).ConnectedComponent)
    {u v : V} (huX : u ∈ X) (hvX : v ∈ X)
    (huC : (⟨u, huX⟩ : X) ∈ C.supp)
    (hvC : (⟨v, hvX⟩ : X) ∈ C.supp) :
    Exists fun q : G.Walk u v =>
      q.IsPath ∧
        forall z : V, z ∈ q.support ->
          z ∈ induceComponentSupport (G := G) C := by
  classical
  have hreach :
      (G.induce X).Reachable (⟨u, huX⟩ : X) (⟨v, hvX⟩ : X) :=
    C.reachable_of_mem_supp huC hvC
  obtain ⟨wX⟩ := hreach
  let wG : G.Walk u v :=
    wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom
  let q : G.Walk u v := wG.toPath
  have hwG_component :
      forall z : V, z ∈ wG.support ->
        z ∈ induceComponentSupport (G := G) C := by
    intro z hz
    change z ∈
      (wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨zX, hzX, hz_eq⟩
    subst z
    have hreach_start_z :
        (G.induce X).Reachable (⟨u, huX⟩ : X) zX :=
      (wX.takeUntil zX hzX).reachable
    have hstart_component :
        (G.induce X).connectedComponentMk (⟨u, huX⟩ : X) = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C
        (⟨u, huX⟩ : X)).mp huC
    have hzC : zX ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.sound hreach_start_z).symm.trans
        hstart_component
    exact ⟨zX.property, hzC⟩
  refine ⟨q, wG.toPath.property, ?_⟩
  intro z hz
  exact hwG_component z (SimpleGraph.Walk.support_toPath_subset wG hz)

/-- A walk that starts in a fixed induced component and never leaves the
inducing set stays in that component. -/
theorem SimpleGraph.Walk.support_subset_induceComponentSupport_of_start_mem
    {G : SimpleGraph V} {X : Set V}
    (C : (G.induce X).ConnectedComponent)
    {u v : V} (q : G.Walk u v)
    (hqX : forall z : V, z ∈ q.support -> z ∈ X)
    (huC : u ∈ induceComponentSupport (G := G) C) :
    forall z : V, z ∈ q.support ->
      z ∈ induceComponentSupport (G := G) C := by
  classical
  intro z hz
  rcases huC with ⟨huX, huC⟩
  have hzX : z ∈ X := hqX z hz
  have hreach :
      (G.induce X).Reachable (⟨u, huX⟩ : X) (⟨z, hzX⟩ : X) := by
    let qPrefix : G.Walk u z := q.takeUntil z hz
    have hprefixX : forall w : V, w ∈ qPrefix.support -> w ∈ X := by
      intro w hw
      exact hqX w (SimpleGraph.Walk.support_takeUntil_subset q hz hw)
    simpa [qPrefix] using
      Walk.reachable_induce_of_support_subset qPrefix hprefixX
  have huComponent :
      (G.induce X).connectedComponentMk (⟨u, huX⟩ : X) = C :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff C
      (⟨u, huX⟩ : X)).mp huC
  refine ⟨hzX, ?_⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact (SimpleGraph.ConnectedComponent.sound hreach).symm.trans huComponent

theorem exists_path_between_component_unions
    (G : SimpleGraph V) {A B X : Set V} {v : V}
    (hvA : v ∈ ComponentUnionMeeting G A X)
    (hvB : v ∈ ComponentUnionMeeting G B X) :
    Exists fun a : V =>
      Exists fun b : V =>
        Exists fun q : G.Walk a b =>
          a ∈ A ∧ b ∈ B ∧ q.IsPath ∧
            forall z : V, z ∈ q.support -> z ∈ X := by
  classical
  rcases hvA with ⟨hvX, CA, hvCA, a, haX, haA, haCA⟩
  rcases hvB with ⟨hvX', CB, hvCB, b, hbX, hbB, hbCB⟩
  have hreach_a_v :
      (G.induce X).Reachable
        (⟨a, haX⟩ : X) (⟨v, hvX⟩ : X) :=
    CA.reachable_of_mem_supp haCA hvCA
  have hreach_v_b :
      (G.induce X).Reachable
        (⟨v, hvX'⟩ : X) (⟨b, hbX⟩ : X) :=
    CB.reachable_of_mem_supp hvCB hbCB
  obtain ⟨wa⟩ := hreach_a_v
  obtain ⟨wb⟩ := hreach_v_b
  let waG : G.Walk a v :=
    wa.map (SimpleGraph.Embedding.induce (G := G) X).toHom
  let wbG : G.Walk v b :=
    wb.map (SimpleGraph.Embedding.induce (G := G) X).toHom
  let q0 : G.Walk a b := waG.append wbG
  let q : G.Walk a b := q0.toPath
  have hq0_support :
      forall z : V, z ∈ q0.support -> z ∈ X := by
    intro z hz
    change z ∈ (waG.append wbG).support at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · change z ∈
        (wa.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨zX, _hzX, hz_eq⟩
      subst z
      exact zX.property
    · change z ∈
        (wb.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      rcases List.mem_map.mp hz with ⟨zX, _hzX, hz_eq⟩
      subst z
      exact zX.property
  refine ⟨a, b, q, haA, hbB, q0.toPath.property, ?_⟩
  intro z hz
  exact hq0_support z (SimpleGraph.Walk.support_toPath_subset q0 hz)

theorem exists_path_to_component_union_witness
    (G : SimpleGraph V) {A X : Set V} {v : V}
    (hvA : v ∈ ComponentUnionMeeting G A X) :
    Exists fun a : V =>
      Exists fun q : G.Walk v a =>
        a ∈ A ∧ q.IsPath ∧
          forall z : V, z ∈ q.support -> z ∈ X := by
  classical
  rcases hvA with ⟨hvX, C, hvC, a, haX, haA, haC⟩
  have hreach :
      (G.induce X).Reachable
        (⟨v, hvX⟩ : X) (⟨a, haX⟩ : X) :=
    C.reachable_of_mem_supp hvC haC
  obtain ⟨wX⟩ := hreach
  let wG : G.Walk v a :=
    wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom
  let q : G.Walk v a := wG.toPath
  have hwG_support :
      forall z : V, z ∈ wG.support -> z ∈ X := by
    intro z hz
    change z ∈
      (wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨zX, _hzX, hz_eq⟩
    subst z
    exact zX.property
  refine ⟨a, q, haA, wG.toPath.property, ?_⟩
  intro z hz
  exact hwG_support z (SimpleGraph.Walk.support_toPath_subset wG hz)

theorem exists_path_to_component_union_witness_inside
    (G : SimpleGraph V) {A X : Set V} {v : V}
    (hvA : v ∈ ComponentUnionMeeting G A X) :
    Exists fun a : V =>
      Exists fun q : G.Walk v a =>
        a ∈ A ∧ q.IsPath ∧
          (forall z : V, z ∈ q.support -> z ∈ ComponentUnionMeeting G A X) ∧
            forall z : V, z ∈ q.support -> z ∈ X := by
  classical
  rcases hvA with ⟨hvX, C, hvC, a, haX, haA, haC⟩
  have hreach :
      (G.induce X).Reachable
        (⟨v, hvX⟩ : X) (⟨a, haX⟩ : X) :=
    C.reachable_of_mem_supp hvC haC
  obtain ⟨wX⟩ := hreach
  let wG : G.Walk v a :=
    wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom
  let q : G.Walk v a := wG.toPath
  have hwG_side :
      forall z : V, z ∈ wG.support -> z ∈ ComponentUnionMeeting G A X := by
    intro z hz
    change z ∈
      (wX.map (SimpleGraph.Embedding.induce (G := G) X).toHom).support at hz
    rw [SimpleGraph.Walk.support_map] at hz
    rcases List.mem_map.mp hz with ⟨zX, hzX, hz_eq⟩
    subst z
    have hreach_start_z :
        (G.induce X).Reachable (⟨v, hvX⟩ : X) zX :=
      (wX.takeUntil zX hzX).reachable
    have hstart_comp :
        (G.induce X).connectedComponentMk (⟨v, hvX⟩ : X) = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C (⟨v, hvX⟩ : X)).mp hvC
    have hz_comp :
        (G.induce X).connectedComponentMk zX = C :=
      (SimpleGraph.ConnectedComponent.sound hreach_start_z).symm.trans hstart_comp
    have hzC : zX ∈ C.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C zX).mpr hz_comp
    exact ⟨zX.property, C, hzC, a, haX, haA, haC⟩
  have hwG_outside :
      forall z : V, z ∈ wG.support -> z ∈ X := by
    intro z hz
    exact ComponentUnionMeeting_subset G A X (hwG_side z hz)
  refine ⟨a, q, haA, wG.toPath.property, ?_, ?_⟩
  · intro z hz
    exact hwG_side z (SimpleGraph.Walk.support_toPath_subset wG hz)
  · intro z hz
    exact hwG_outside z (SimpleGraph.Walk.support_toPath_subset wG hz)


end GeneralSociety

end Schematic.Math.GraphTheory
