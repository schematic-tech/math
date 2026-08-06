import Schematic.Math.GraphTheory.Embedding.Walkup.EdgeRegularity

/-! Edge-orbit domains affected by Walkup deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

/-- Coq `cross_edge`: the edge cycle of `z` contains `node z`. -/
def CrossEdge (z : G.Dart) : Prop :=
  PermReachable G.edge z (G.node z)

/-- Coq `skip_edge_domain`: the original edge cycles touched by deleting
`z` in `WalkupE`.  In orbit language this is the union of the edge orbit of
`z` and the edge orbit of `node z`. -/
def EdgeDomain (z x : G.Dart) : Prop :=
  PermReachable G.edge x z ∨ PermReachable G.edge x (G.node z)

theorem edgeDomain_of_left {z x : G.Dart}
    (hx : PermReachable G.edge x z) :
    G.EdgeDomain z x :=
  Or.inl hx

theorem edgeDomain_of_right {z x : G.Dart}
    (hx : PermReachable G.edge x (G.node z)) :
    G.EdgeDomain z x :=
  Or.inr hx

theorem edgeDomain_self (z : G.Dart) :
    G.EdgeDomain z z :=
  Or.inl (PermReachable.refl G.edge z)

theorem edgeDomain_node (z : G.Dart) :
    G.EdgeDomain z (G.node z) :=
  Or.inr (PermReachable.refl G.edge (G.node z))

theorem edgeDomain_edge {z x : G.Dart}
    (hx : G.EdgeDomain z x) :
    G.EdgeDomain z (G.edge x) := by
  rcases hx with hx | hx
  · exact Or.inl (PermReachable.trans G.edge
      (PermReachable.symm G.edge (PermReachable.forward G.edge x)) hx)
  · exact Or.inr (PermReachable.trans G.edge
      (PermReachable.symm G.edge (PermReachable.forward G.edge x)) hx)

theorem edgeDomain_edge_symm {z x : G.Dart}
    (hx : G.EdgeDomain z x) :
    G.EdgeDomain z (G.edge.symm x) := by
  rcases hx with hx | hx
  · exact Or.inl (PermReachable.trans G.edge
      (PermReachable.symm G.edge (PermReachable.backward G.edge x)) hx)
  · exact Or.inr (PermReachable.trans G.edge
      (PermReachable.symm G.edge (PermReachable.backward G.edge x)) hx)

theorem edgeDomain_of_edgeOrbit_eq_left {z x : G.Dart}
    (hx : PermOrbit.of G.edge x = PermOrbit.of G.edge z) :
    G.EdgeDomain z x :=
  Or.inl (Quotient.exact hx)

theorem edgeDomain_of_edgeOrbit_eq_right {z x : G.Dart}
    (hx : PermOrbit.of G.edge x = PermOrbit.of G.edge (G.node z)) :
    G.EdgeDomain z x :=
  Or.inr (Quotient.exact hx)

theorem edgeDomain_iff_edgeOrbit_eq {z x : G.Dart} :
    G.EdgeDomain z x ↔
      PermOrbit.of G.edge x = PermOrbit.of G.edge z ∨
        PermOrbit.of G.edge x = PermOrbit.of G.edge (G.node z) := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact Or.inl (PermOrbit.of_eq_of G.edge hx)
    · exact Or.inr (PermOrbit.of_eq_of G.edge hx)
  · intro hx
    rcases hx with hx | hx
    · exact G.edgeDomain_of_edgeOrbit_eq_left hx
    · exact G.edgeDomain_of_edgeOrbit_eq_right hx

theorem edgeOrbit_z_ne_node_of_not_cross
    {z : G.Dart} (hncross : ¬ G.CrossEdge z) :
    PermOrbit.of G.edge z ≠ PermOrbit.of G.edge (G.node z) := by
  intro h
  exact hncross (Quotient.exact h)

theorem edgeOrbit_z_eq_node_of_cross
    {z : G.Dart} (hcross : G.CrossEdge z) :
    PermOrbit.of G.edge z = PermOrbit.of G.edge (G.node z) :=
  PermOrbit.of_eq_of G.edge hcross

/-- The two original edge orbits affected by non-self `WalkupE`: the orbit of
`z` and the orbit of `node z`.  In the non-cross branch these are distinct;
Coq counts this set as the factor `2` in `fcard_skip_edge`. -/
def AffectedEdgeOrbit (z : G.Dart) : Type u :=
  {o : G.EdgeOrbit //
    o = PermOrbit.of G.edge z ∨
      o = PermOrbit.of G.edge (G.node z)}

noncomputable def affectedEdgeOrbitEquivBool
    {z : G.Dart}
    (hneq :
      PermOrbit.of G.edge z ≠ PermOrbit.of G.edge (G.node z)) :
    G.AffectedEdgeOrbit z ≃ Bool := by
  classical
  refine
    { toFun := fun o =>
        if o.1 = PermOrbit.of G.edge z then false else true
      invFun := fun b =>
        if b then
          ⟨PermOrbit.of G.edge (G.node z), Or.inr rfl⟩
        else
          ⟨PermOrbit.of G.edge z, Or.inl rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro o
    classical
    rcases o with ⟨o, ho⟩
    dsimp
    by_cases h : o = PermOrbit.of G.edge z
    · apply Subtype.ext
      dsimp
      rw [if_pos h]
      simp [h]
    · rcases ho with ho | ho
      · exact False.elim (h ho)
      · apply Subtype.ext
        dsimp
        rw [if_neg h]
        simp [ho]
  · intro b
    classical
    cases b
    · simp
    · simp [hneq.symm]

theorem affectedEdgeOrbit_card_of_not_cross
    {z : G.Dart} (hncross : ¬ G.CrossEdge z) :
    Nat.card (G.AffectedEdgeOrbit z) = 2 := by
  classical
  rw [Nat.card_congr
    (G.affectedEdgeOrbitEquivBool
      (G.edgeOrbit_z_ne_node_of_not_cross hncross))]
  simp

noncomputable def affectedEdgeOrbitEquivPUnitOfCross
    {z : G.Dart} (hcross : G.CrossEdge z) :
    G.AffectedEdgeOrbit z ≃ PUnit.{u + 1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨PermOrbit.of G.edge z, Or.inl rfl⟩
  left_inv o := by
    rcases o with ⟨o, ho⟩
    apply Subtype.ext
    change PermOrbit.of G.edge z = o
    rcases ho with ho | ho
    · exact ho.symm
    · rw [ho]
      exact G.edgeOrbit_z_eq_node_of_cross hcross
  right_inv u := by
    cases u
    rfl

theorem affectedEdgeOrbit_card_of_cross
    {z : G.Dart} (hcross : G.CrossEdge z) :
    Nat.card (G.AffectedEdgeOrbit z) = 1 := by
  rw [Nat.card_congr (G.affectedEdgeOrbitEquivPUnitOfCross hcross)]
  simp

theorem edgeDomain_quotient_out_iff
    (z : G.Dart) (o : G.EdgeOrbit) :
    G.EdgeDomain z (Quotient.out o) ↔
      o = PermOrbit.of G.edge z ∨
        o = PermOrbit.of G.edge (G.node z) := by
  constructor
  · intro hdom
    rcases (G.edgeDomain_iff_edgeOrbit_eq).mp hdom with h | h
    · exact Or.inl (by
        rw [← Quotient.out_eq o]
        exact h)
    · exact Or.inr (by
        rw [← Quotient.out_eq o]
        exact h)
  · intro h
    have hout :
        PermOrbit.of G.edge (Quotient.out o) = o :=
      Quotient.out_eq o
    rcases h with h | h
    · exact G.edgeDomain_of_edgeOrbit_eq_left (by
        rw [hout, h])
    · exact G.edgeDomain_of_edgeOrbit_eq_right (by
        rw [hout, h])

theorem not_edgeDomain_quotient_out_of_not_affected
    {z : G.Dart} {o : G.EdgeOrbit}
    (hoz : o ≠ PermOrbit.of G.edge z)
    (hon : o ≠ PermOrbit.of G.edge (G.node z)) :
    ¬ G.EdgeDomain z (Quotient.out o) := by
  intro hdom
  rcases (G.edgeDomain_quotient_out_iff z o).mp hdom with h | h
  · exact hoz h
  · exact hon h

theorem edgeOrbit_eq_left_or_right_of_edgeDomain
    {z x : G.Dart} (hx : G.EdgeDomain z x) :
    PermOrbit.of G.edge x = PermOrbit.of G.edge z ∨
      PermOrbit.of G.edge x = PermOrbit.of G.edge (G.node z) :=
  (G.edgeDomain_iff_edgeOrbit_eq).mp hx

/-- Two darts are either in the same original edge orbit, or both belong to
the affected edge-domain of a Walkup deletion. -/
def SameEdgeOrbitOrAffected (z x y : G.Dart) : Prop :=
  PermReachable G.edge x y ∨ (G.EdgeDomain z x ∧ G.EdgeDomain z y)

theorem edgeDomain_of_permReachable
    {z x y : G.Dart} (hx : G.EdgeDomain z x)
    (hyx : PermReachable G.edge y x) :
    G.EdgeDomain z y := by
  rcases hx with hx | hx
  · exact Or.inl (PermReachable.trans G.edge hyx hx)
  · exact Or.inr (PermReachable.trans G.edge hyx hx)

theorem sameEdgeOrbitOrAffected_refl
    (z x : G.Dart) :
    G.SameEdgeOrbitOrAffected z x x :=
  Or.inl (PermReachable.refl G.edge x)

theorem sameEdgeOrbitOrAffected_symm
    {z x y : G.Dart}
    (hxy : G.SameEdgeOrbitOrAffected z x y) :
    G.SameEdgeOrbitOrAffected z y x := by
  rcases hxy with hxy | hxy
  · exact Or.inl (PermReachable.symm G.edge hxy)
  · exact Or.inr ⟨hxy.2, hxy.1⟩

theorem sameEdgeOrbitOrAffected_trans
    {z x y w : G.Dart}
    (hxy : G.SameEdgeOrbitOrAffected z x y)
    (hyw : G.SameEdgeOrbitOrAffected z y w) :
    G.SameEdgeOrbitOrAffected z x w := by
  rcases hxy with hxy | hxy
  · rcases hyw with hyw | hyw
    · exact Or.inl (PermReachable.trans G.edge hxy hyw)
    · exact Or.inr
        ⟨G.edgeDomain_of_permReachable hyw.1 hxy, hyw.2⟩
  · rcases hyw with hyw | hyw
    · exact Or.inr
        ⟨hxy.1,
          G.edgeDomain_of_permReachable hxy.2
            (PermReachable.symm G.edge hyw)⟩
    · exact Or.inr ⟨hxy.1, hyw.2⟩

theorem walkupE_edge_step_sameEdgeOrbitOrAffected_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z)
    (x : (G.walkupE z).Dart) :
    G.SameEdgeOrbitOrAffected z x.1 (((G.walkupE z).edge x).1) := by
  by_cases hxnode : x.1 = G.node z
  · right
    constructor
    · rw [hxnode]
      exact G.edgeDomain_node z
    · have hval : (((G.walkupE z).edge x).1 : G.Dart) = G.edge z := by
        rw [G.walkupE_edge_apply_coe, hxnode]
        exact G.walkupSkipEdgeAux_node_of_not_link_self hz
      rw [hval]
      exact Or.inl
        (PermReachable.symm G.edge (PermReachable.forward G.edge z))
  · by_cases hxpred : x.1 = G.edge.symm z
    · right
      constructor
      · rw [hxpred]
        exact Or.inl (by
          simpa using PermReachable.forward G.edge (G.edge.symm z))
      · have hval :
            (((G.walkupE z).edge x).1 : G.Dart) =
              G.edge (G.node z) := by
          rw [G.walkupE_edge_apply_coe, hxpred]
          exact G.walkupSkipEdgeAux_edge_symm_of_not_link_self hz
        rw [hval]
        exact Or.inr
          (PermReachable.symm G.edge
            (PermReachable.forward G.edge (G.node z)))
    · left
      have hval :
          (((G.walkupE z).edge x).1 : G.Dart) = G.edge x.1 :=
        G.walkupE_edge_apply_of_not_link_self_of_regular
          hz x hxnode hxpred
      rw [hval]
      exact PermReachable.forward G.edge x.1

theorem walkupE_edgePermReachable_sameEdgeOrbitOrAffected_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hxy : PermReachable (G.walkupE z).edge x y) :
    G.SameEdgeOrbitOrAffected z x.1 y.1 := by
  induction hxy with
  | refl =>
      exact G.sameEdgeOrbitOrAffected_refl z x.1
  | @tail b c hxb hbc ih =>
      have hstep :
          G.SameEdgeOrbitOrAffected z b.1 c.1 := by
        cases hbc with
        | forward =>
            exact G.walkupE_edge_step_sameEdgeOrbitOrAffected_of_not_link_self
              hz b
        | backward =>
            exact G.sameEdgeOrbitOrAffected_symm (by
              simpa using
                G.walkupE_edge_step_sameEdgeOrbitOrAffected_of_not_link_self
                  hz ((G.walkupE z).edge.symm b))
      exact G.sameEdgeOrbitOrAffected_trans ih hstep

theorem edgeOrbit_eq_of_walkupE_edgeOrbit_eq_of_not_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hxdom : ¬ G.EdgeDomain z x.1)
    (hxy :
      PermOrbit.of (G.walkupE z).edge x =
        PermOrbit.of (G.walkupE z).edge y) :
    PermOrbit.of G.edge x.1 = PermOrbit.of G.edge y.1 := by
  have hrel :
      G.SameEdgeOrbitOrAffected z x.1 y.1 :=
    G.walkupE_edgePermReachable_sameEdgeOrbitOrAffected_of_not_link_self
      hz (Quotient.exact hxy)
  rcases hrel with hrel | hrel
  · exact PermOrbit.of_eq_of G.edge hrel
  · exact False.elim (hxdom hrel.1)

theorem not_edgeDomain_of_permReachable
    {z x y : G.Dart} (hxdom : ¬ G.EdgeDomain z x)
    (hxy : PermReachable G.edge x y) :
    ¬ G.EdgeDomain z y := by
  intro hydom
  exact hxdom
    (G.edgeDomain_of_permReachable hydom hxy)

theorem ne_z_of_not_edgeDomain
    {z x : G.Dart} (hxdom : ¬ G.EdgeDomain z x) :
    x ≠ z := by
  intro hxz
  exact hxdom (by simpa [hxz] using G.edgeDomain_self z)

theorem ne_node_of_not_edgeDomain
    {z x : G.Dart} (hxdom : ¬ G.EdgeDomain z x) :
    x ≠ G.node z := by
  intro hxz
  exact hxdom (by simpa [hxz] using G.edgeDomain_node z)

theorem ne_edge_symm_of_not_edgeDomain
    {z x : G.Dart} (hxdom : ¬ G.EdgeDomain z x) :
    x ≠ G.edge.symm z := by
  intro hxz
  exact hxdom (by
    rw [hxz]
    exact Or.inl (by
      simpa using PermReachable.forward G.edge (G.edge.symm z)))

theorem edge_ne_z_of_not_edgeDomain
    {z x : G.Dart} (hxdom : ¬ G.EdgeDomain z x) :
    G.edge x ≠ z := by
  intro hxz
  exact G.ne_edge_symm_of_not_edgeDomain hxdom
    ((G.edge_eq_iff_eq_edge_symm).mp hxz)

theorem edge_symm_ne_z_of_not_edgeDomain
    {z x : G.Dart} (hxdom : ¬ G.EdgeDomain z x) :
    G.edge.symm x ≠ z := by
  intro hxz
  have hx : x = G.edge z := by
    calc
      x = G.edge (G.edge.symm x) := by simp
      _ = G.edge z := by rw [hxz]
  exact hxdom (by
    rw [hx]
    exact Or.inl
      (PermReachable.symm G.edge (PermReachable.forward G.edge z)))

theorem walkupE_edgePermReachable_original_forward_of_not_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x : (G.walkupE z).Dart}
    (hxdom : ¬ G.EdgeDomain z x.1) :
    PermReachable (G.walkupE z).edge x
      (⟨G.edge x.1, G.edge_ne_z_of_not_edgeDomain hxdom⟩ :
        (G.walkupE z).Dart) := by
  have hxnode : x.1 ≠ G.node z :=
    G.ne_node_of_not_edgeDomain hxdom
  have hxpred : x.1 ≠ G.edge.symm z :=
    G.ne_edge_symm_of_not_edgeDomain hxdom
  exact G.walkupE_edgePermReachable_of_original_edge_regular
    hz rfl hxnode hxpred

theorem walkupE_edgePermReachable_original_backward_of_not_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x : (G.walkupE z).Dart}
    (hxdom : ¬ G.EdgeDomain z x.1) :
    PermReachable (G.walkupE z).edge x
      (⟨G.edge.symm x.1, G.edge_symm_ne_z_of_not_edgeDomain hxdom⟩ :
        (G.walkupE z).Dart) := by
  have hpred_dom :
      ¬ G.EdgeDomain z (G.edge.symm x.1) := by
    intro hdom
    exact hxdom (by simpa using G.edgeDomain_edge hdom)
  have hforward :
      PermReachable (G.walkupE z).edge
        (⟨G.edge.symm x.1, G.edge_symm_ne_z_of_not_edgeDomain hxdom⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge (G.edge.symm x.1),
            G.edge_ne_z_of_not_edgeDomain hpred_dom⟩ :
          (G.walkupE z).Dart) :=
    G.walkupE_edgePermReachable_original_forward_of_not_edgeDomain
      hz hpred_dom
  have htarget :
      (⟨G.edge (G.edge.symm x.1),
          G.edge_ne_z_of_not_edgeDomain hpred_dom⟩ :
        (G.walkupE z).Dart) = x := by
    apply Subtype.ext
    simp
  rw [htarget] at hforward
  exact PermReachable.symm (G.walkupE z).edge hforward

theorem walkupE_edgePermReachable_of_original_edgeReachable_not_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hxdom : ¬ G.EdgeDomain z x.1)
    (hxy : PermReachable G.edge x.1 y.1) :
    PermReachable (G.walkupE z).edge x y := by
  suffices hmain :
      ∀ {y₀ : G.Dart}, PermReachable G.edge x.1 y₀ →
        ∀ hy₀ : y₀ ≠ z,
          PermReachable (G.walkupE z).edge x
            (⟨y₀, hy₀⟩ : (G.walkupE z).Dart) by
    simpa using hmain hxy y.2
  intro y₀ hxy₀
  induction hxy₀ with
  | refl =>
      intro hx_ne
      have hsub : (⟨x.1, hx_ne⟩ : (G.walkupE z).Dart) = x := by
        apply Subtype.ext
        rfl
      rw [hsub]
      exact PermReachable.refl (G.walkupE z).edge x
  | @tail b c hxb hbc ih =>
      intro hc_ne
      have hbdom : ¬ G.EdgeDomain z b :=
        G.not_edgeDomain_of_permReachable hxdom hxb
      have hb_ne : b ≠ z := G.ne_z_of_not_edgeDomain hbdom
      let b' : (G.walkupE z).Dart := ⟨b, hb_ne⟩
      have ih' : PermReachable (G.walkupE z).edge x b' :=
        ih hb_ne
      have hstep : PermReachable (G.walkupE z).edge b'
          (⟨c, hc_ne⟩ : (G.walkupE z).Dart) := by
        cases hbc with
        | forward =>
            simpa [b'] using
              G.walkupE_edgePermReachable_original_forward_of_not_edgeDomain
                hz (x := b') hbdom
        | backward =>
            simpa [b'] using
              G.walkupE_edgePermReachable_original_backward_of_not_edgeDomain
                hz (x := b') hbdom
      exact PermReachable.trans (G.walkupE z).edge ih' hstep

theorem walkupE_edgeOrbit_eq_of_original_edgeOrbit_eq_not_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hxdom : ¬ G.EdgeDomain z x.1)
    (hxy : PermOrbit.of G.edge x.1 = PermOrbit.of G.edge y.1) :
    PermOrbit.of (G.walkupE z).edge x =
      PermOrbit.of (G.walkupE z).edge y :=
  PermOrbit.of_eq_of (G.walkupE z).edge
    (G.walkupE_edgePermReachable_of_original_edgeReachable_not_edgeDomain
      hz hxdom (Quotient.exact hxy))


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
