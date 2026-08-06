import Schematic.Math.GraphTheory.Minors.Society.Basic.BoundaryPathTrimming
import Schematic.Math.GraphTheory.Minors.Rerouting.TargetSetMenger

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- A graph component containing a supported nonboundary vertex meets the
society boundary in at least three vertices.  Otherwise that component, with
all boundary vertices placed on the opposite shore, gives a society
separation of order at most two. -/
theorem ThreeConnected.connectedComponent_boundarySet_ncard_ge_three_of_nonboundary
    [Fintype V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (C : S.graph.ConnectedComponent)
    {v : V}
    (hvC : v ∈ C.supp)
    (hvBoundary : v ∉ S.boundarySet)
    (hvSupport : v ∈ S.graph.support) :
    3 <= (C.supp ∩ S.boundarySet).ncard := by
  classical
  by_contra hnot
  have hboundary_le : (C.supp ∩ S.boundarySet).ncard <= 2 := by omega
  let T : Separation S.graph := {
    left := C.suppᶜ ∪ S.boundarySet
    right := C.supp
    covers := by
      ext x
      constructor
      · intro _hx
        exact Set.mem_univ x
      · intro _hx
        by_cases hxC : x ∈ C.supp
        · exact Or.inr hxC
        · exact Or.inl (Or.inl hxC)
    no_cross := by
      intro a b ha haNotRight hb _hbNotLeft hab
      have hcomp_a_b :
          S.graph.connectedComponentMk a = S.graph.connectedComponentMk b :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab
      have hcomp_b : S.graph.connectedComponentMk b = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C b).mp hb
      have haC : a ∈ C.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact hcomp_a_b.trans hcomp_b
      exact haNotRight haC
  }
  have hboundary_left : S.boundarySet ⊆ T.left := by
    intro x hx
    exact Or.inr hx
  have hright : ((T.right \ T.left) ∩ S.activeSet).Nonempty := by
    refine ⟨v, ?_⟩
    refine ⟨?_, Or.inl hvSupport⟩
    refine ⟨hvC, ?_⟩
    intro hvLeft
    rcases hvLeft with hvNotC | hvBoundary'
    · exact hvNotC hvC
    · exact hvBoundary hvBoundary'
  have horder : T.OrderAtMost 2 := by
    refine ⟨(C.supp ∩ S.boundarySet).toFinite.toFinset, ?_, ?_⟩
    · rw [(C.supp ∩ S.boundarySet).toFinite.coe_toFinset]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        SimpleGraph.ConnectedComponent.mem_supp_iff, T, Separation.separator]
      constructor
      · intro hx
        exact ⟨Or.inr hx.2, hx.1⟩
      · intro hx
        refine ⟨hx.2, ?_⟩
        rcases hx.1 with hx_notC | hx_boundary
        · exact False.elim (hx_notC hx.2)
        · exact hx_boundary
    · rw [← Set.ncard_eq_toFinset_card
          (C.supp ∩ S.boundarySet)
          (C.supp ∩ S.boundarySet).toFinite]
      exact hboundary_le
  exact hthree T hboundary_left hright horder

/-- In a three-connected society, every graph component with at least three
vertices contains at least three society boundary vertices.

Otherwise the component with all boundary vertices added to the opposite shore
is a separation of order at most two and has a non-boundary active vertex on the
right-only side. -/
theorem ThreeConnected.connectedComponent_boundarySet_ncard_ge_three
    [Fintype V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (C : S.graph.ConnectedComponent)
    (hC_large : 3 <= C.supp.ncard) :
    3 <= (C.supp ∩ S.boundarySet).ncard := by
  classical
  by_contra hnot
  have hboundary_le : (C.supp ∩ S.boundarySet).ncard <= 2 := by omega
  have hC_not_subset_boundary : Not (C.supp ⊆ S.boundarySet) := by
    intro hsubset
    have h_eq : C.supp ∩ S.boundarySet = C.supp := by
      exact Set.inter_eq_left.mpr hsubset
    have hC_le_two : C.supp.ncard <= 2 := by
      simpa [h_eq] using hboundary_le
    omega
  have hnonboundary :
      Exists fun v : V => v ∈ C.supp ∧ v ∉ S.boundarySet := by
    by_contra hnone
    apply hC_not_subset_boundary
    intro v hvC
    by_contra hvBoundary
    exact hnone ⟨v, hvC, hvBoundary⟩
  obtain ⟨v, hvC, hvBoundary⟩ := hnonboundary
  have hvSupport : v ∈ S.graph.support := by
    have hC_one_lt : 1 < C.supp.ncard := by omega
    obtain ⟨w, hwC, hw_ne_v⟩ :=
      Set.exists_ne_of_one_lt_ncard hC_one_lt v
    have hreach : S.graph.Reachable v w :=
      C.reachable_of_mem_supp hvC hwC
    exact SimpleGraph.mem_support_of_reachable hw_ne_v.symm hreach
  let T : Separation S.graph := {
    left := C.suppᶜ ∪ S.boundarySet
    right := C.supp
    covers := by
      ext x
      constructor
      · intro _hx
        exact Set.mem_univ x
      · intro _hx
        by_cases hxC : x ∈ C.supp
        · exact Or.inr hxC
        · exact Or.inl (Or.inl hxC)
    no_cross := by
      intro a b ha haNotRight hb _hbNotLeft hab
      have hcomp_a_b :
          S.graph.connectedComponentMk a = S.graph.connectedComponentMk b :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab
      have hcomp_b : S.graph.connectedComponentMk b = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C b).mp hb
      have haC : a ∈ C.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact hcomp_a_b.trans hcomp_b
      exact haNotRight haC
  }
  have hboundary_left : S.boundarySet ⊆ T.left := by
    intro x hx
    exact Or.inr hx
  have hright : ((T.right \ T.left) ∩ S.activeSet).Nonempty := by
    refine ⟨v, ?_⟩
    refine ⟨?_, Or.inl hvSupport⟩
    refine ⟨hvC, ?_⟩
    intro hvLeft
    rcases hvLeft with hvNotC | hvBoundary'
    · exact hvNotC hvC
    · exact hvBoundary hvBoundary'
  have horder : T.OrderAtMost 2 := by
    refine ⟨(C.supp ∩ S.boundarySet).toFinite.toFinset, ?_, ?_⟩
    · rw [(C.supp ∩ S.boundarySet).toFinite.coe_toFinset]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
        SimpleGraph.ConnectedComponent.mem_supp_iff, T, Separation.separator]
      constructor
      · intro hx
        exact ⟨Or.inr hx.2, hx.1⟩
      · intro hx
        refine ⟨hx.2, ?_⟩
        rcases hx.1 with hx_notC | hx_boundary
        · exact False.elim (hx_notC hx.2)
        · exact hx_boundary
    · rw [← Set.ncard_eq_toFinset_card
          (C.supp ∩ S.boundarySet)
          (C.supp ∩ S.boundarySet).toFinite]
      exact hboundary_le
  exact hthree T hboundary_left hright horder

/-- In a three-connected society, adjoining the canonical boundary polygon
connects every non-isolated graph vertex to one connected support.  Each
component of the society graph containing an edge either already contains a
boundary vertex, or contains a supported nonboundary vertex and hence meets
the boundary by `connectedComponent_boundarySet_ncard_ge_three_of_nonboundary`.
The boundary polygon then joins the resulting component contacts. -/
theorem ThreeConnected.boundaryAugmentedGraph_support_preconnected
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (n : Nat) (hlength : S.boundary.length = n + 3) :
    let A := S.boundaryAugmentedGraphOfLength (n + 3) hlength
    (A.induce A.support).Preconnected := by
  classical
  let C : SimpleGraph V :=
    S.boundary.cycleGraphOfLength (n + 3) hlength
  let A : SimpleGraph V :=
    S.boundaryAugmentedGraphOfLength (n + 3) hlength
  have hA : A = S.graph ⊔ C := rfl
  have hcycleSupportBoundary : C.support ⊆ S.boundarySet := by
    intro z hz
    rcases (SimpleGraph.mem_support C).mp hz with ⟨w, hzw⟩
    let f : Fin (n + 3) ↪ V :=
      S.boundary.embeddingOfLength (n + 3) hlength
    have hzw' :
        ((SimpleGraph.cycleGraph (n + 3)).map f).Adj z w := by
      simpa [C, CyclicBoundary.cycleGraphOfLength, f] using hzw
    rcases (SimpleGraph.map_adj f (SimpleGraph.cycleGraph (n + 3)) z w).mp
        hzw' with ⟨i, _j, _hij, hi, _hj⟩
    rw [← hi]
    change f i ∈ S.boundary.vertexSet
    simp [f, CyclicBoundary.embeddingOfLength, CyclicBoundary.embedding,
      CyclicBoundary.vertexSet]
  have hcycleBoundarySupport : S.boundarySet ⊆ C.support := by
    intro z hz
    have hzWalk : z ∈ (S.boundary.cycleWalkOfLength n hlength).support :=
      S.boundary.mem_cycleWalkOfLength_support n hlength (by
        simpa [GeneralSociety.boundarySet] using hz)
    exact SimpleGraph.mem_support_of_mem_walk_support
      (S.boundary.cycleWalkOfLength n hlength)
      (S.boundary.cycleWalkOfLength_isCycle n hlength).not_nil hzWalk
  have htoBoundary :
      forall z : A.support,
        Exists fun b : V =>
          b ∈ S.boundarySet ∧ A.Reachable (z : V) b := by
    intro z
    rcases (SimpleGraph.mem_support A).mp z.property with ⟨w, hzw⟩
    have hzw' : S.graph.Adj (z : V) w ∨ C.Adj (z : V) w := by
      simpa [A, GeneralSociety.boundaryAugmentedGraphOfLength, C] using hzw
    rcases hzw' with hzGraph | hzCycle
    · by_cases hzBoundary : (z : V) ∈ S.boundarySet
      · exact ⟨z, hzBoundary,
          SimpleGraph.Reachable.refl (G := A) (z : V)⟩
      · let K : S.graph.ConnectedComponent :=
          S.graph.connectedComponentMk (z : V)
        have hzK : (z : V) ∈ K.supp := by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        have hcard : 3 <= (K.supp ∩ S.boundarySet).ncard :=
          hthree.connectedComponent_boundarySet_ncard_ge_three_of_nonboundary
            K hzK hzBoundary hzGraph.left_mem_support
        have hnonempty : (K.supp ∩ S.boundarySet).Nonempty :=
          (Set.ncard_pos).mp (by omega)
        rcases hnonempty with ⟨b, hbK, hbBoundary⟩
        have hreachGraph : S.graph.Reachable (z : V) b :=
          K.reachable_of_mem_supp hzK hbK
        exact ⟨b, hbBoundary,
          hreachGraph.mono (by
            rw [hA]
            exact le_sup_left)⟩
    · have hzBoundary : (z : V) ∈ S.boundarySet :=
        hcycleSupportBoundary hzCycle.left_mem_support
      exact ⟨z, hzBoundary,
        SimpleGraph.Reachable.refl (G := A) (z : V)⟩
  have hcyclePreconnected : (C.induce C.support).Preconnected := by
    simpa [C] using
      S.boundary.cycleGraphOfLength_support_preconnected n hlength
  have hcycleReach :
      forall {x y : V}, x ∈ S.boundarySet -> y ∈ S.boundarySet ->
        A.Reachable x y := by
    intro x y hx hy
    have hxyInduced :
        (C.induce C.support).Reachable
          ⟨x, hcycleBoundarySupport hx⟩
          ⟨y, hcycleBoundarySupport hy⟩ :=
      hcyclePreconnected _ _
    have hxyCycle : C.Reachable x y :=
      hxyInduced.map
        (SimpleGraph.Embedding.induce (G := C) C.support).toHom
    exact hxyCycle.mono (by
      rw [hA]
      exact le_sup_right)
  change (A.induce A.support).Preconnected
  intro x y
  rcases htoBoundary x with ⟨a, haBoundary, hxa⟩
  rcases htoBoundary y with ⟨b, hbBoundary, hyb⟩
  have hxy : A.Reachable (x : V) (y : V) :=
    hxa.trans ((hcycleReach haBoundary hbBoundary).trans hyb.symm)
  rcases hxy with ⟨p⟩
  have hpSupport : forall z : V, z ∈ p.support -> z ∈ A.support := by
    intro z hz
    by_cases hzx : z = (x : V)
    · subst z
      exact x.property
    · have hpNotNil : Not p.Nil := by
        intro hpNil
        have hsupp : p.support = [(x : V)] :=
          SimpleGraph.Walk.nil_iff_support_eq.mp hpNil
        rw [hsupp] at hz
        simp at hz
        exact hzx hz
      exact SimpleGraph.mem_support_of_mem_walk_support p hpNotNil hz
  exact ⟨p.induce A.support hpSupport⟩

/-- Deleting at most two vertices cannot leave an active component that is
disjoint from the society boundary.

This is the separator principle used in the GM IX `(2.2)` branch.  If such a
component existed in `G - D`, then `D` would be the separator of a society
separation of order at most two with all boundary vertices on the other side,
contradicting `ThreeConnected`. -/
theorem ThreeConnected.no_active_boundary_free_induced_component_after_small_deletion
    [Fintype V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    {D : Set V}
    (hD : D.ncard <= 2)
    (C : (S.graph.induce Dᶜ).ConnectedComponent)
    (hboundary :
      forall v : V,
        (Exists fun hv : v ∈ Dᶜ =>
          (⟨v, hv⟩ : {x : V // x ∈ Dᶜ}) ∈ C.supp) ->
          v ∉ S.boundarySet)
    (hactive :
      Exists fun v : V =>
        (Exists fun hv : v ∈ Dᶜ =>
          (⟨v, hv⟩ : {x : V // x ∈ Dᶜ}) ∈ C.supp) ∧
          v ∈ S.activeSet) :
    False := by
  classical
  let Cset : Set V :=
    {v : V |
      Exists fun hv : v ∈ Dᶜ =>
        (⟨v, hv⟩ : {x : V // x ∈ Dᶜ}) ∈ C.supp}
  have hCset_disjoint_D : Disjoint Cset D := by
    rw [Set.disjoint_left]
    intro v hvC hvD
    rcases hvC with ⟨hvDcomp, _hvC⟩
    exact hvDcomp hvD
  let T : Separation S.graph := {
    left := Csetᶜ
    right := Cset ∪ D
    covers := by
      ext v
      constructor
      · intro _hv
        exact Set.mem_univ v
      · intro _hv
        by_cases hvC : v ∈ Cset
        · exact Or.inr (Or.inl hvC)
        · exact Or.inl hvC
    no_cross := by
      intro a b ha haNotRight hb hbNotLeft hab
      have ha_notC : a ∉ Cset := ha
      have ha_notD : a ∉ D := by
        intro haD
        exact haNotRight (Or.inr haD)
      have hbC : b ∈ Cset := by
        by_contra hb_notC
        exact hbNotLeft hb_notC
      rcases hbC with ⟨hb_notD, hbSupp⟩
      let a' : {x : V // x ∈ Dᶜ} := ⟨a, ha_notD⟩
      let b' : {x : V // x ∈ Dᶜ} := ⟨b, hb_notD⟩
      have hab' : (S.graph.induce Dᶜ).Adj a' b' := by
        simpa [a', b'] using hab
      have hcomp_ab :
          (S.graph.induce Dᶜ).connectedComponentMk a' =
            (S.graph.induce Dᶜ).connectedComponentMk b' :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab'
      have hcomp_b :
          (S.graph.induce Dᶜ).connectedComponentMk b' = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C b').mp (by
          simpa [b'] using hbSupp)
      have haSupp : a' ∈ C.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact hcomp_ab.trans hcomp_b
      exact ha_notC ⟨ha_notD, by simpa [a'] using haSupp⟩
  }
  have hboundary_left : S.boundarySet ⊆ T.left := by
    intro v hvBoundary hvC
    exact hboundary v (by simpa [Cset] using hvC) hvBoundary
  have hright : ((T.right \ T.left) ∩ S.activeSet).Nonempty := by
    rcases hactive with ⟨v, hvC, hvActive⟩
    refine ⟨v, ?_⟩
    refine ⟨?_, hvActive⟩
    refine ⟨Or.inl (by simpa [Cset] using hvC), ?_⟩
    intro hvLeft
    exact hvLeft (by simpa [Cset] using hvC)
  have horder : T.OrderAtMost 2 := by
    refine ⟨D.toFinite.toFinset, ?_, ?_⟩
    · rw [Set.Finite.coe_toFinset]
      ext v
      constructor
      · intro hvD
        change v ∈ Csetᶜ ∩ (Cset ∪ D)
        refine ⟨?_, Or.inr hvD⟩
        intro hvC
        exact Set.disjoint_left.mp hCset_disjoint_D hvC hvD
      · intro hv
        change v ∈ Csetᶜ ∩ (Cset ∪ D) at hv
        rcases hv.2 with hvC | hvD
        · exact False.elim (hv.1 hvC)
        · exact hvD
    · rw [← Set.ncard_eq_toFinset_card D D.toFinite]
      exact hD
  exact hthree T hboundary_left hright horder

/-- The set-target form of the linkage consequence of society
three-connectivity.

Every injective triple of active vertices can be linked by three mutually
vertex-disjoint paths to three (automatically distinct) society-boundary
vertices.  This is the GM IX `(2.2)` input used in the side-tripod paragraph:
if a deletion set of size less than three separated the triple from the
boundary, a surviving source would lie in an active boundary-free component
of the deleted graph, contrary to `ThreeConnected`. -/
theorem ThreeConnected.hasThreeVertexLinkageToBoundary
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    {left : Fin 3 -> V}
    (hleft_injective : Function.Injective left)
    (hleft_active : forall i : Fin 3, left i ∈ S.activeSet) :
    HasThreeVertexLinkageToSet S.graph left S.boundarySet := by
  classical
  apply
    finite_menger_three_vertex_linkage_to_set_of_not_separates_from_set
      hleft_injective
  intro D hD hseparates
  have hexists_surviving : Exists fun i : Fin 3 => left i ∉ D := by
    by_contra hnone
    push Not at hnone
    have hrange_subset : Set.range left ⊆ D := by
      rintro _ ⟨i, rfl⟩
      exact hnone i
    have hrange_card : (Set.range left).ncard = 3 := by
      rw [Set.ncard_range_of_injective hleft_injective]
      simp
    have hrange_le : (Set.range left).ncard <= D.ncard :=
      Set.ncard_le_ncard hrange_subset
    omega
  rcases hexists_surviving with ⟨i, hiD⟩
  let iD : {v : V // v ∈ Dᶜ} := ⟨left i, hiD⟩
  let C : (S.graph.induce Dᶜ).ConnectedComponent :=
    (S.graph.induce Dᶜ).connectedComponentMk iD
  have hboundary_free :
      forall v : V,
        (Exists fun hv : v ∈ Dᶜ =>
          (⟨v, hv⟩ : {x : V // x ∈ Dᶜ}) ∈ C.supp) ->
          v ∉ S.boundarySet := by
    intro v hvC hvBoundary
    rcases hvC with ⟨hvD, hvC⟩
    have hiC : iD ∈ C.supp := by
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    have hreach :
        (S.graph.induce Dᶜ).Reachable
          iD (⟨v, hvD⟩ : {x : V // x ∈ Dᶜ}) :=
      C.reachable_of_mem_supp hiC hvC
    exact hseparates i v hiD hvBoundary hvD hreach
  have hactive_component :
      Exists fun v : V =>
        (Exists fun hv : v ∈ Dᶜ =>
          (⟨v, hv⟩ : {x : V // x ∈ Dᶜ}) ∈ C.supp) ∧
          v ∈ S.activeSet := by
    exact
      ⟨left i, ⟨hiD, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩,
        hleft_active i⟩
  exact
    hthree.no_active_boundary_free_induced_component_after_small_deletion
      (D := D) (by omega) C hboundary_free hactive_component


end GeneralSociety

end Schematic.Math.GraphTheory
