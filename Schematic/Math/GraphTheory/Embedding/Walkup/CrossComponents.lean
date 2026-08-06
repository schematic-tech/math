import Schematic.Math.GraphTheory.Embedding.Walkup.NonCrossEdgeOrbits

/-! Components in the cross-edge branch of Walkup deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

def walkupECrossComponentA
    {z : G.Dart} (hz : ¬ G.Link z z) : (G.walkupE z).Dart :=
  ⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩

def walkupECrossComponentB
    {z : G.Dart} (hz : ¬ G.Link z z) : (G.walkupE z).Dart :=
  ⟨G.face z, G.face_ne_self_of_not_link_self hz⟩

theorem walkupE_reachable_crossComponentA_to_node
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    (G.walkupE z).Reachable
      (G.walkupECrossComponentA hz)
      (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart) :=
  (G.walkupE z).edgePermReachable_reachable
    (G.walkupE_edgePermReachable_edge_to_node_of_cross hz hcross)

theorem walkupE_reachable_crossComponentB_to_edge_node
    {z : G.Dart} (hz : ¬ G.Link z z) :
    (G.walkupE z).Reachable
      (G.walkupECrossComponentB hz)
      (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart) :=
  G.walkupE_reachable_face_to_edge_node_of_not_link_self hz

theorem walkupE_reachable_of_link_away_component
    {z : G.Dart} {x y : (G.walkupE z).Dart}
    (hz : ¬ G.Link z z)
    (hxz : ¬ G.Reachable x.1 z) (hxy : G.Link x.1 y.1) :
    (G.walkupE z).Reachable x y := by
  rcases hxy with hxy | hxy | hxy
  · have hxnode : x.1 ≠ G.node z := by
      intro hxnode
      apply hxz
      rw [hxnode]
      exact G.reachable_node_symm z
    have hxpred : x.1 ≠ G.edge.symm z := by
      intro hxpred
      apply hxz
      rw [hxpred]
      exact G.edgePermReachable_reachable
        (by simpa using PermReachable.forward G.edge (G.edge.symm z))
    have hedge : (G.walkupE z).edge x = y := by
      apply Subtype.ext
      calc
        (((G.walkupE z).edge x).1 : G.Dart) = G.edge x.1 :=
          G.walkupE_edge_apply_of_not_link_self_of_regular
            hz x hxnode hxpred
        _ = y.1 := hxy.symm
    rw [← hedge]
    exact (G.walkupE z).reachable_edge x
  · have hnode_ne : G.node x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hxy, hbad])
    have hnode : (G.walkupE z).node x = y := by
      apply Subtype.ext
      change ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) =
            G.node x.1 := PermSkip.skip_apply_of_apply_ne G.node x hnode_ne
        _ = y.1 := hxy.symm
    rw [← hnode]
    exact (G.walkupE z).reachable_node x
  · have hface_ne : G.face x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hxy, hbad])
    have hface : (G.walkupE z).face x = y := by
      apply Subtype.ext
      change ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) =
            G.face x.1 := PermSkip.skip_apply_of_apply_ne G.face x hface_ne
        _ = y.1 := hxy.symm
    rw [← hface]
    exact (G.walkupE z).reachable_face x

theorem walkupE_reachable_of_reachable_away_component
    {z : G.Dart} {x y : (G.walkupE z).Dart}
    (hz : ¬ G.Link z z)
    (hxz : ¬ G.Reachable x.1 z) (hxy : G.Reachable x.1 y.1) :
    (G.walkupE z).Reachable x y := by
  let W := G.walkupE z
  have hmain :
      ∀ {y₀ : G.Dart}, G.Reachable x.1 y₀ →
        ∀ hy₀ : y₀ ≠ z, W.Reachable x ⟨y₀, hy₀⟩ := by
    intro y₀ hxy₀
    induction hxy₀ with
    | refl =>
        intro hx_ne
        have hsub : (⟨x.1, hx_ne⟩ : G.DeletedDart z) = x := by
          apply Subtype.ext
          rfl
        simpa [W, hsub] using W.reachable_refl x
    | @tail b c hxb hbc ih =>
        intro hc_ne
        have hb_ne : b ≠ z := by
          intro hbz
          exact hxz (by simpa [hbz] using hxb)
        let b' : W.Dart := ⟨b, hb_ne⟩
        have hxb' : W.Reachable x b' := ih hb_ne
        have hbz_unreach : ¬ G.Reachable b z := by
          intro hbz_reach
          exact hxz (hxb.trans hbz_reach)
        have hbc' : G.Link b'.1 (⟨c, hc_ne⟩ : W.Dart).1 := by
          simpa [b'] using hbc
        exact hxb'.trans
          (G.walkupE_reachable_of_link_away_component
            hz hbz_unreach hbc')
  simpa [W] using hmain hxy y.2

theorem walkupEComponentProjection_injective_of_ne_deleted_component
    {z : G.Dart} (hz : ¬ G.Link z z)
    {q r : (G.walkupE z).Component}
    (hq : G.walkupEComponentProjection z q ≠ G.componentOf z)
    (hqr :
      G.walkupEComponentProjection z q =
        G.walkupEComponentProjection z r) :
    q = r := by
  revert hq hqr
  refine Quotient.inductionOn₂ q r ?_
  intro x y hq hqr
  change G.componentOf x.1 ≠ G.componentOf z at hq
  change G.componentOf x.1 = G.componentOf y.1 at hqr
  have hxz : ¬ G.Reachable x.1 z := by
    intro hxz
    exact hq (G.componentOf_eq_componentOf hxz)
  exact (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_reachable_of_reachable_away_component
      hz hxz
      ((G.componentOf_eq_iff).mp hqr))

theorem walkupE_crossComponentSide_of_link_from_deleted
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {y : (G.walkupE z).Dart} (hzy : G.Link z y.1) :
    (G.walkupE z).Reachable (G.walkupECrossComponentA hz) y ∨
      (G.walkupE z).Reachable (G.walkupECrossComponentB hz) y := by
  rcases hzy with hzy | hzy | hzy
  · left
    have hy : y = G.walkupECrossComponentA hz := by
      apply Subtype.ext
      exact hzy
    rw [hy]
    exact (G.walkupE z).reachable_refl (G.walkupECrossComponentA hz)
  · left
    have hy :
        y =
          (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart) := by
      apply Subtype.ext
      exact hzy
    rw [hy]
    exact G.walkupE_reachable_crossComponentA_to_node hz hcross
  · right
    have hy : y = G.walkupECrossComponentB hz := by
      apply Subtype.ext
      exact hzy
    rw [hy]
    exact (G.walkupE z).reachable_refl (G.walkupECrossComponentB hz)

theorem walkupE_crossComponentSide_step
    {z : G.Dart} (hz : ¬ G.Link z z)
    {x y : (G.walkupE z).Dart}
    (hxy : G.Link x.1 y.1)
    (hside :
      (G.walkupE z).Reachable (G.walkupECrossComponentA hz) x ∨
        (G.walkupE z).Reachable (G.walkupECrossComponentB hz) x) :
    (G.walkupE z).Reachable (G.walkupECrossComponentA hz) y ∨
      (G.walkupE z).Reachable (G.walkupECrossComponentB hz) y := by
  rcases hxy with hxy | hxy | hxy
  · by_cases hxnode : x.1 = G.node z
    · right
      have hy :
          y =
            (⟨G.edge (G.node z),
                G.edge_node_ne_self_of_not_link_self hz⟩ :
              (G.walkupE z).Dart) := by
        apply Subtype.ext
        rw [hxy, hxnode]
      rw [hy]
      exact G.walkupE_reachable_crossComponentB_to_edge_node hz
    · by_cases hxpred : x.1 = G.edge.symm z
      · have yz : y.1 = z := by
          rw [hxy, hxpred]
          simp
        exact False.elim (y.2 yz)
      · have hedge : (G.walkupE z).edge x = y := by
          apply Subtype.ext
          calc
            (((G.walkupE z).edge x).1 : G.Dart) = G.edge x.1 :=
              G.walkupE_edge_apply_of_not_link_self_of_regular
                hz x hxnode hxpred
            _ = y.1 := hxy.symm
        have hstep : (G.walkupE z).Reachable x y := by
          rw [← hedge]
          exact (G.walkupE z).reachable_edge x
        rcases hside with hside | hside
        · exact Or.inl (hside.trans hstep)
        · exact Or.inr (hside.trans hstep)
  · have hnode_ne : G.node x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hxy, hbad])
    have hnode : (G.walkupE z).node x = y := by
      apply Subtype.ext
      change ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) =
            G.node x.1 := PermSkip.skip_apply_of_apply_ne G.node x hnode_ne
        _ = y.1 := hxy.symm
    have hstep : (G.walkupE z).Reachable x y := by
      rw [← hnode]
      exact (G.walkupE z).reachable_node x
    rcases hside with hside | hside
    · exact Or.inl (hside.trans hstep)
    · exact Or.inr (hside.trans hstep)
  · have hface_ne : G.face x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hxy, hbad])
    have hface : (G.walkupE z).face x = y := by
      apply Subtype.ext
      change ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) =
            G.face x.1 := PermSkip.skip_apply_of_apply_ne G.face x hface_ne
        _ = y.1 := hxy.symm
    have hstep : (G.walkupE z).Reachable x y := by
      rw [← hface]
      exact (G.walkupE z).reachable_face x
    rcases hside with hside | hside
    · exact Or.inl (hside.trans hstep)
    · exact Or.inr (hside.trans hstep)

theorem walkupE_crossComponentSide_of_reachable_from_deleted
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {y : (G.walkupE z).Dart} (hzy : G.Reachable z y.1) :
    (G.walkupE z).Reachable (G.walkupECrossComponentA hz) y ∨
      (G.walkupE z).Reachable (G.walkupECrossComponentB hz) y := by
  let W := G.walkupE z
  have hmain :
      ∀ {y₀ : G.Dart}, G.Reachable z y₀ →
        ∀ hy₀ : y₀ ≠ z,
          W.Reachable (G.walkupECrossComponentA hz) ⟨y₀, hy₀⟩ ∨
            W.Reachable (G.walkupECrossComponentB hz) ⟨y₀, hy₀⟩ := by
    intro y₀ hzy₀
    induction hzy₀ with
    | refl =>
        intro hz_ne
        exact False.elim (hz_ne rfl)
    | @tail b c hzb hbc ih =>
        intro hc_ne
        by_cases hbz : b = z
        · exact G.walkupE_crossComponentSide_of_link_from_deleted
            hz hcross (y := ⟨c, hc_ne⟩) (by simpa [hbz] using hbc)
        · let b' : W.Dart := ⟨b, hbz⟩
          have hbside := ih hbz
          exact G.walkupE_crossComponentSide_step hz
            (x := b') (y := ⟨c, hc_ne⟩) (by simpa [b'] using hbc)
            hbside
  simpa [W] using hmain hzy y.2

theorem walkupEComponentProjection_fiber_deleted_eq_crossSide
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {q : (G.walkupE z).Component}
    (hq : G.walkupEComponentProjection z q = G.componentOf z) :
    q = (G.walkupE z).componentOf (G.walkupECrossComponentA hz) ∨
      q = (G.walkupE z).componentOf (G.walkupECrossComponentB hz) := by
  revert hq
  refine Quotient.inductionOn q ?_
  intro x hq
  change G.componentOf x.1 = G.componentOf z at hq
  have hzx : G.Reachable z x.1 :=
    G.reachable_symm ((G.componentOf_eq_iff).mp hq)
  rcases G.walkupE_crossComponentSide_of_reachable_from_deleted
      hz hcross hzx with hA | hB
  · left
    exact (G.walkupE z).componentOf_eq_componentOf
      ((G.walkupE z).reachable_symm hA)
  · right
    exact (G.walkupE z).componentOf_eq_componentOf
      ((G.walkupE z).reachable_symm hB)

theorem walkupE_cross_componentCount_le
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    (G.walkupE z).componentCount ≤ G.componentCount + 1 := by
  classical
  have hsurj : Function.Surjective G.componentOf := by
    intro c
    refine Quotient.inductionOn c ?_
    intro x
    exact ⟨x, rfl⟩
  letI : Finite G.Component := Finite.of_surjective G.componentOf hsurj
  let A : (G.walkupE z).Component :=
    (G.walkupE z).componentOf (G.walkupECrossComponentA hz)
  let B : (G.walkupE z).Component :=
    (G.walkupE z).componentOf (G.walkupECrossComponentB hz)
  let f : (G.walkupE z).Component → G.Component :=
    G.walkupEComponentProjection z
  let F : (G.walkupE z).Component → Option G.Component :=
    fun q => if q = A then none else some (f q)
  have hinj : Function.Injective F := by
    intro q r hqr
    by_cases hqA : q = A
    · subst q
      by_cases hrA : r = A
      · exact hrA.symm
      · simp [F, hrA] at hqr
    · by_cases hrA : r = A
      · subst r
        simp [F, hqA] at hqr
      · have hfqr : f q = f r := by
          simpa [F, hqA, hrA] using hqr
        by_cases hqdel : f q = G.componentOf z
        · have hqside :
              q = A ∨ q = B := by
            simpa [A, B, f] using
              G.walkupEComponentProjection_fiber_deleted_eq_crossSide
                hz hcross (q := q) (by simpa [f] using hqdel)
          have hrdel : f r = G.componentOf z := by
            rwa [← hfqr]
          have hrside :
              r = A ∨ r = B := by
            simpa [A, B, f] using
              G.walkupEComponentProjection_fiber_deleted_eq_crossSide
                hz hcross (q := r) (by simpa [f] using hrdel)
          have hqB : q = B := by
            rcases hqside with hq | hq
            · exact False.elim (hqA hq)
            · exact hq
          have hrB : r = B := by
            rcases hrside with hr | hr
            · exact False.elim (hrA hr)
            · exact hr
          exact hqB.trans hrB.symm
        · exact G.walkupEComponentProjection_injective_of_ne_deleted_component
            hz (q := q) (r := r) (by simpa [f] using hqdel)
            (by simpa [f] using hfqr)
  have hcard :
      Nat.card (G.walkupE z).Component ≤ Nat.card (Option G.Component) :=
    Nat.card_le_card_of_injective F hinj
  rw [Finite.card_option] at hcard
  unfold componentCount
  exact hcard


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
