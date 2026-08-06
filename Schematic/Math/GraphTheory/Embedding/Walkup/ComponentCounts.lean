import Schematic.Math.GraphTheory.Embedding.Walkup.Construction

/-! Component and Euler-count behavior of Walkup deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

theorem walkupSkipEdgeAux_reachable
    {z : G.Dart} (x : G.DeletedDart z) :
    G.Reachable x.1 (G.walkupSkipEdgeAux z x.1) := by
  unfold walkupSkipEdgeAux
  split_ifs with hez hfe hex
  · exact G.reachable_edge x.1
  · have hface : G.Reachable (G.edge x.1) z := by
      simpa [hfe] using G.reachable_face (G.edge x.1)
    exact (G.reachable_edge x.1).trans
      (hface.trans (G.reachable_edge z))
  · have hedge : G.Reachable x.1 z := by
      simpa [hex] using G.reachable_edge x.1
    exact hedge.trans
      ((G.reachable_node z).trans (G.reachable_edge (G.node z)))
  · exact G.reachable_edge x.1

theorem walkupE_link_reachable
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : (G.walkupE z).Link x y) :
    G.Reachable x.1 y.1 := by
  rcases hxy with hxy | hxy | hxy
  · subst y
    rw [G.walkupE_edge_apply_coe]
    exact G.walkupSkipEdgeAux_reachable x
  · subst y
    have hperm :
        PermReachable G.node x.1 ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) :=
      PermSkip.skip_permReachable G.node x
    simpa [walkupE_node, walkupSkipNode] using
      G.nodePermReachable_reachable hperm
  · subst y
    have hperm :
        PermReachable G.face x.1 ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) :=
      PermSkip.skip_permReachable G.face x
    simpa [walkupE_face, walkupSkipFace] using
      G.facePermReachable_reachable hperm

theorem walkupE_reachable_reachable
    {z : G.Dart} {x y : G.DeletedDart z}
    (hxy : (G.walkupE z).Reachable x y) :
    G.Reachable x.1 y.1 :=
  hxy.lift' Subtype.val fun _ _ h => G.walkupE_link_reachable h

theorem walkupE_link_of_link_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z)
    {x y : G.DeletedDart z}
    (hxy : G.Link x.1 y.1) :
    (G.walkupE z).Reachable x y := by
  rcases hxy with hxy | hxy | hxy
  · have hy : y.1 = G.edge x.1 := hxy
    have hedge : (G.walkupE z).edge x = y := by
      apply Subtype.ext
      calc
        ((G.walkupE z).edge x).1 = G.edge x.1 :=
          G.walkupE_edge_apply_coe_of_edge_fixed he x
        _ = y.1 := hy.symm
    rw [← hedge]
    exact (G.walkupE z).reachable_edge x
  · have hy : y.1 = G.node x.1 := hxy
    have hnode_ne : G.node x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hy, hbad])
    have hnode : (G.walkupE z).node x = y := by
      apply Subtype.ext
      change ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) =
            G.node x.1 := PermSkip.skip_apply_of_apply_ne G.node x hnode_ne
        _ = y.1 := hy.symm
    rw [← hnode]
    exact (G.walkupE z).reachable_node x
  · have hy : y.1 = G.face x.1 := hxy
    have hface_ne : G.face x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hy, hbad])
    have hface : (G.walkupE z).face x = y := by
      apply Subtype.ext
      change ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) =
            G.face x.1 := PermSkip.skip_apply_of_apply_ne G.face x hface_ne
        _ = y.1 := hy.symm
    rw [← hface]
    exact (G.walkupE z).reachable_face x

theorem walkupE_componentOf_eq_of_link_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z)
    {x y : G.DeletedDart z}
    (hxy : G.Link x.1 y.1) :
    (G.walkupE z).componentOf x = (G.walkupE z).componentOf y :=
  (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_link_of_link_of_edge_fixed he hxy)

theorem walkupE_link_of_link_of_link_self
    {z : G.Dart} (hz : G.Link z z)
    {x y : G.DeletedDart z}
    (hxy : G.Link x.1 y.1) :
    (G.walkupE z).Reachable x y := by
  rcases hxy with hxy | hxy | hxy
  · have hy : y.1 = G.edge x.1 := hxy
    have hedge_ne : G.edge x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hy, hbad])
    have hedge : (G.walkupE z).edge x = y := by
      apply Subtype.ext
      have hperm :
          (G.walkupE z).edge x = (PermSkip.skip G.edge z) x := by
        exact congrArg (fun f : Equiv.Perm (G.DeletedDart z) => f x)
          (G.walkupE_edge_eq_skip_edge_of_link_self hz)
      have hval :
          ((G.walkupE z).edge x).1 =
            ((PermSkip.skip G.edge z x : G.DeletedDart z) : G.Dart) :=
        congrArg Subtype.val hperm
      calc
        ((G.walkupE z).edge x).1 =
            ((PermSkip.skip G.edge z x : G.DeletedDart z) : G.Dart) := hval
        _ = G.edge x.1 := PermSkip.skip_apply_of_apply_ne G.edge x hedge_ne
        _ = y.1 := hy.symm
    rw [← hedge]
    exact (G.walkupE z).reachable_edge x
  · have hy : y.1 = G.node x.1 := hxy
    have hnode_ne : G.node x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hy, hbad])
    have hnode : (G.walkupE z).node x = y := by
      apply Subtype.ext
      change ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) =
            G.node x.1 := PermSkip.skip_apply_of_apply_ne G.node x hnode_ne
        _ = y.1 := hy.symm
    rw [← hnode]
    exact (G.walkupE z).reachable_node x
  · have hy : y.1 = G.face x.1 := hxy
    have hface_ne : G.face x.1 ≠ z := by
      intro hbad
      exact y.2 (by rw [hy, hbad])
    have hface : (G.walkupE z).face x = y := by
      apply Subtype.ext
      change ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) =
            G.face x.1 := PermSkip.skip_apply_of_apply_ne G.face x hface_ne
        _ = y.1 := hy.symm
    rw [← hface]
    exact (G.walkupE z).reachable_face x

theorem walkupE_componentOf_eq_of_link_of_link_self
    {z : G.Dart} (hz : G.Link z z)
    {x y : G.DeletedDart z}
    (hxy : G.Link x.1 y.1) :
    (G.walkupE z).componentOf x = (G.walkupE z).componentOf y :=
  (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_link_of_link_of_link_self hz hxy)

def walkupELinkSelfComponentDart
    {z : G.Dart} (he : G.edge z ≠ z) (x : G.Dart) :
    G.DeletedDart z :=
  if hx : x = z then ⟨G.edge z, he⟩ else ⟨x, hx⟩

theorem walkupE_reachable_representatives_of_link_of_link_self_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z)
    {x y : G.Dart} (hxy : G.Link x y) :
    (G.walkupE z).Reachable
      (G.walkupELinkSelfComponentDart he x)
      (G.walkupELinkSelfComponentDart he y) := by
  by_cases hx : x = z
  · by_cases hy : y = z
    · have hsame :
          G.walkupELinkSelfComponentDart he x =
            G.walkupELinkSelfComponentDart he y := by
        apply Subtype.ext
        simp [walkupELinkSelfComponentDart, hx, hy]
      simpa [hsame] using
        (G.walkupE z).reachable_refl
          (G.walkupELinkSelfComponentDart he x)
    · rcases hxy with hxy | hxy | hxy
      · have hyedge : y = G.edge z := by
          calc
            y = G.edge x := hxy
            _ = G.edge z := by rw [hx]
        have hsame :
            G.walkupELinkSelfComponentDart he x =
              G.walkupELinkSelfComponentDart he y := by
          apply Subtype.ext
          calc
            (G.walkupELinkSelfComponentDart he x).1 = G.edge z := by
              simp [walkupELinkSelfComponentDart, hx]
            _ = y := hyedge.symm
            _ = (G.walkupELinkSelfComponentDart he y).1 := by
              simp [walkupELinkSelfComponentDart, hy]
        simpa [hsame] using
          (G.walkupE z).reachable_refl
            (G.walkupELinkSelfComponentDart he x)
      · have hynode : y = G.node z := by
          calc
            y = G.node x := hxy
            _ = G.node z := by rw [hx]
        rcases hz with hz_edge | hz_node | hz_face
        · exact False.elim (he hz_edge.symm)
        · exact False.elim (hy (by simpa [hynode] using hz_node.symm))
        · have hf : G.face z = z := hz_face.symm
          have hsource :
              G.walkupELinkSelfComponentDart he x =
                (⟨G.edge z, he⟩ : G.DeletedDart z) := by
            apply Subtype.ext
            simp [walkupELinkSelfComponentDart, hx]
          have htarget :
              G.walkupELinkSelfComponentDart he y =
                (⟨G.node z, G.node_ne_of_face_eq_self_of_edge_ne hf he⟩ :
                  G.DeletedDart z) := by
            apply Subtype.ext
            calc
              (G.walkupELinkSelfComponentDart he y).1 = y := by
                simp [walkupELinkSelfComponentDart, hy]
              _ = G.node z := hynode
          simpa [hsource, htarget] using
            G.walkupE_reachable_edge_to_node_of_face_eq_self_of_edge_ne hf he
      · have hyface : y = G.face z := by
          calc
            y = G.face x := hxy
            _ = G.face z := by rw [hx]
        rcases hz with hz_edge | hz_node | hz_face
        · exact False.elim (he hz_edge.symm)
        · have hn : G.node z = z := hz_node.symm
          have hsource :
              G.walkupELinkSelfComponentDart he x =
                (⟨G.edge z, he⟩ : G.DeletedDart z) := by
            apply Subtype.ext
            simp [walkupELinkSelfComponentDart, hx]
          have htarget :
              G.walkupELinkSelfComponentDart he y =
                (⟨G.face z, G.face_ne_of_node_eq_self_of_edge_ne hn he⟩ :
                  G.DeletedDart z) := by
            apply Subtype.ext
            calc
              (G.walkupELinkSelfComponentDart he y).1 = y := by
                simp [walkupELinkSelfComponentDart, hy]
              _ = G.face z := hyface
          simpa [hsource, htarget] using
            G.walkupE_reachable_edge_to_face_of_node_eq_self_of_edge_ne hn he
        · exact False.elim (hy (by simpa [hyface] using hz_face.symm))
  · by_cases hy : y = z
    · rcases hxy with hxy | hxy | hxy
      · have hedge : (G.walkupE z).edge
            (G.walkupELinkSelfComponentDart he x) =
            (G.walkupELinkSelfComponentDart he y) := by
          apply Subtype.ext
          have hperm :
              (G.walkupE z).edge
                  (G.walkupELinkSelfComponentDart he x) =
                (PermSkip.skip G.edge z)
                  (G.walkupELinkSelfComponentDart he x) := by
            exact congrArg
              (fun f : Equiv.Perm (G.DeletedDart z) =>
                f (G.walkupELinkSelfComponentDart he x))
              (G.walkupE_edge_eq_skip_edge_of_link_self hz)
          have hval :
              (((G.walkupE z).edge
                    (G.walkupELinkSelfComponentDart he x)) :
                  G.DeletedDart z).1 =
                ((PermSkip.skip G.edge z
                    (G.walkupELinkSelfComponentDart he x) :
                  G.DeletedDart z) : G.Dart) :=
            congrArg Subtype.val hperm
          have hxedge : G.edge
              (G.walkupELinkSelfComponentDart he x).1 = z := by
            simpa [walkupELinkSelfComponentDart, hx, hy] using hxy.symm
          calc
            (((G.walkupE z).edge
                  (G.walkupELinkSelfComponentDart he x)) :
                G.DeletedDart z).1 =
                ((PermSkip.skip G.edge z
                    (G.walkupELinkSelfComponentDart he x) :
                  G.DeletedDart z) : G.Dart) := hval
            _ = G.edge z := PermSkip.skip_apply_of_apply_eq G.edge
              (G.walkupELinkSelfComponentDart he x) hxedge
            _ = (G.walkupELinkSelfComponentDart he y).1 := by
              simp [walkupELinkSelfComponentDart, hy]
        rw [← hedge]
        exact (G.walkupE z).reachable_edge
          (G.walkupELinkSelfComponentDart he x)
      · rcases hz with hz_edge | hz_node | hz_face
        · exact False.elim (he hz_edge.symm)
        · have hn : G.node z = z := hz_node.symm
          have hx_eq_z : x = z := by
            apply G.node.injective
            calc
              G.node x = y := hxy.symm
              _ = z := hy
              _ = G.node z := hn.symm
          exact False.elim (hx hx_eq_z)
        · have hf : G.face z = z := hz_face.symm
          let u : G.DeletedDart z :=
            G.walkupELinkSelfComponentDart he x
          let v : G.DeletedDart z :=
            ⟨G.node z, G.node_ne_of_face_eq_self_of_edge_ne hf he⟩
          have hnode : (G.walkupE z).node u = v := by
            apply Subtype.ext
            change ((G.walkupSkipNode z u : G.DeletedDart z) : G.Dart) =
              v.1
            have hxnode : G.node u.1 = z := by
              simpa [u, walkupELinkSelfComponentDart, hx, hy] using hxy.symm
            calc
              ((G.walkupSkipNode z u : G.DeletedDart z) : G.Dart) =
                  G.node z := PermSkip.skip_apply_of_apply_eq G.node u hxnode
              _ = v.1 := rfl
          have h₁ : (G.walkupE z).Reachable u v := by
            rw [← hnode]
            exact (G.walkupE z).reachable_node u
          have h₂ : (G.walkupE z).Reachable v
              (G.walkupELinkSelfComponentDart he y) := by
            have hbase :=
              G.walkupE_reachable_edge_to_node_of_face_eq_self_of_edge_ne
                hf he
            have htarget :
                G.walkupELinkSelfComponentDart he y =
                  (⟨G.edge z, he⟩ : G.DeletedDart z) := by
              apply Subtype.ext
              simp [walkupELinkSelfComponentDart, hy]
            simpa [htarget] using (G.walkupE z).reachable_symm hbase
          simpa [u] using h₁.trans h₂
      · rcases hz with hz_edge | hz_node | hz_face
        · exact False.elim (he hz_edge.symm)
        · have hn : G.node z = z := hz_node.symm
          have hxedge : x = G.edge z := by
            apply G.face.injective
            calc
              G.face x = y := hxy.symm
              _ = z := hy
              _ = G.face (G.edge z) := by
                simpa [hn] using (G.face_edge_node z).symm
          have hsame :
              G.walkupELinkSelfComponentDart he x =
                G.walkupELinkSelfComponentDart he y := by
            apply Subtype.ext
            calc
              (G.walkupELinkSelfComponentDart he x).1 = x := by
                simp [walkupELinkSelfComponentDart, hx]
              _ = G.edge z := hxedge
              _ = (G.walkupELinkSelfComponentDart he y).1 := by
                simp [walkupELinkSelfComponentDart, hy]
          simpa [hsame] using
            (G.walkupE z).reachable_refl
              (G.walkupELinkSelfComponentDart he x)
        · have hf : G.face z = z := hz_face.symm
          have hx_eq_z : x = z := by
            apply G.face.injective
            calc
              G.face x = y := hxy.symm
              _ = z := hy
              _ = G.face z := hf.symm
          exact False.elim (hx hx_eq_z)
    · have hxy' : G.Link
          (G.walkupELinkSelfComponentDart he x).1
          (G.walkupELinkSelfComponentDart he y).1 := by
        simpa [walkupELinkSelfComponentDart, hx, hy] using hxy
      exact G.walkupE_link_of_link_of_link_self hz hxy'

theorem walkupE_componentOf_representatives_eq_of_link_self_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z)
    {x y : G.Dart} (hxy : G.Link x y) :
    (G.walkupE z).componentOf
        (G.walkupELinkSelfComponentDart he x) =
      (G.walkupE z).componentOf
        (G.walkupELinkSelfComponentDart he y) :=
  (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_reachable_representatives_of_link_of_link_self_edge_ne
      hz he hxy)

theorem walkupE_componentOf_representatives_eq_of_reachable_link_self_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z)
    {x y : G.Dart} (hxy : G.Reachable x y) :
    (G.walkupE z).componentOf
        (G.walkupELinkSelfComponentDart he x) =
      (G.walkupE z).componentOf
        (G.walkupELinkSelfComponentDart he y) :=
  hxy.apply_eq
    (fun x => (G.walkupE z).componentOf
      (G.walkupELinkSelfComponentDart he x))
    (fun {_ _} h =>
      G.walkupE_componentOf_representatives_eq_of_link_self_edge_ne hz he h)

noncomputable def walkupEComponentEquivOfLinkSelfEdgeNe
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    (G.walkupE z).Component ≃ G.Component where
  toFun :=
    Quotient.map
      (fun x : G.DeletedDart z => x.1)
      (by
        intro x y hxy
        exact G.walkupE_reachable_reachable hxy)
  invFun :=
    Quotient.lift
      (fun x : G.Dart =>
        (G.walkupE z).componentOf
          (G.walkupELinkSelfComponentDart he x))
      (by
        intro x y hxy
        exact
          G.walkupE_componentOf_representatives_eq_of_reachable_link_self_edge_ne
            hz he hxy)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    have hrep_x : G.walkupELinkSelfComponentDart he x.1 = x := by
      apply Subtype.ext
      simp [walkupELinkSelfComponentDart, x.2]
    change
      (G.walkupE z).componentOf
          (G.walkupELinkSelfComponentDart he x.1) =
        Quot.mk (G.walkupE z).reachableSetoid x
    rw [hrep_x]
    rfl
  right_inv c := by
    refine Quotient.inductionOn c ?_
    intro x
    by_cases hx : x = z
    · change G.componentOf
          ((G.walkupELinkSelfComponentDart he x : G.DeletedDart z) :
            G.Dart) = G.componentOf x
      calc
        G.componentOf
            ((G.walkupELinkSelfComponentDart he x : G.DeletedDart z) :
              G.Dart) =
            G.componentOf (G.edge z) := by
              simp [walkupELinkSelfComponentDart, hx]
        _ = G.componentOf z := G.componentOf_edge z
        _ = G.componentOf x := by rw [hx]
    · change G.componentOf
          ((G.walkupELinkSelfComponentDart he x : G.DeletedDart z) :
            G.Dart) = G.componentOf x
      simp [walkupELinkSelfComponentDart, hx]

theorem walkupE_componentCount_eq_of_link_self_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    (G.walkupE z).componentCount = G.componentCount := by
  change Nat.card (G.walkupE z).Component = Nat.card G.Component
  exact Nat.card_congr (G.walkupEComponentEquivOfLinkSelfEdgeNe hz he)

theorem walkupE_componentCount_step_of_link_self_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    1 + (G.walkupE z).componentCount = G.componentCount + 1 := by
  have h := G.walkupE_componentCount_eq_of_link_self_edge_ne hz he
  omega

theorem walkupE_eulerLeft_step_of_link_self_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    2 * 1 + (G.walkupE z).eulerLeft = G.eulerLeft + 1 := by
  have hcomp := G.walkupE_componentCount_step_of_link_self_edge_ne hz he
  have hdart := G.walkupE_dart_card_add_one z
  unfold eulerLeft componentCount at *
  omega

theorem walkupE_nonEdgeFixedCount_of_link_self
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    ∃ a e b : Nat,
      b ≤ a ∧
        a + (G.walkupE z).componentCount = G.componentCount + 1 ∧
          e + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 ∧
            e + (if G.node z = z then 1 else 0) +
              (if G.face z = z then 1 else 0) = 2 * b := by
  have hcomp := G.walkupE_componentCount_step_of_link_self_edge_ne hz he
  have hedge := G.walkupE_edgeOrbit_step_of_link_self_of_edge_ne hz he
  have hind := G.node_face_indicator_add_eq_one_of_link_self_of_edge_ne hz he
  exact ⟨1, 1, 1, le_rfl, hcomp, hedge, by omega⟩

theorem face_eq_node_symm_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) :
    G.face z = G.node.symm z := by
  apply G.node.injective
  calc
    G.node (G.face z) = z := by
      simpa [he] using G.node_face_edge z
    _ = G.node (G.node.symm z) := by simp

theorem walkupE_reachable_of_link_through_deleted_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z)
    {x y : G.DeletedDart z}
    (hxz : G.Link x.1 z) (hzy : G.Link z y.1) :
    (G.walkupE z).Reachable x y := by
  rcases hxz with hxz_edge | hxz_node | hxz_face
  · have hx_eq_z : x.1 = z := by
      apply G.edge.injective
      rw [← hxz_edge, he]
    exact False.elim (x.2 hx_eq_z)
  · rcases hzy with hzy_edge | hzy_node | hzy_face
    · have hy_eq_z : y.1 = z := by
        rw [hzy_edge, he]
      exact False.elim (y.2 hy_eq_z)
    · have hnode : (G.walkupE z).node x = y := by
        apply Subtype.ext
        change ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) = y.1
        calc
          ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) =
              G.node z := PermSkip.skip_apply_of_apply_eq G.node x hxz_node.symm
          _ = y.1 := hzy_node.symm
      rw [← hnode]
      exact (G.walkupE z).reachable_node x
    · have hx_val : x.1 = G.node.symm z := by
        calc
          x.1 = G.node.symm (G.node x.1) := by simp
          _ = G.node.symm z := by rw [← hxz_node]
      have hxy : x = y := by
        apply Subtype.ext
        calc
          x.1 = G.node.symm z := hx_val
          _ = G.face z := (G.face_eq_node_symm_of_edge_fixed he).symm
          _ = y.1 := hzy_face.symm
      simpa [hxy] using (G.walkupE z).reachable_refl x
  · rcases hzy with hzy_edge | hzy_node | hzy_face
    · have hy_eq_z : y.1 = z := by
        rw [hzy_edge, he]
      exact False.elim (y.2 hy_eq_z)
    · have hx_val : x.1 = G.face.symm z := by
        calc
          x.1 = G.face.symm (G.face x.1) := by simp
          _ = G.face.symm z := by rw [← hxz_face]
      have hedge : (G.walkupE z).edge y = x := by
        apply Subtype.ext
        calc
          ((G.walkupE z).edge y).1 = G.edge y.1 :=
            G.walkupE_edge_apply_coe_of_edge_fixed he y
          _ = G.edge (G.node z) := by rw [hzy_node]
          _ = G.face.symm z := G.edge_node_eq_face_symm z
          _ = x.1 := hx_val.symm
      rw [← hedge]
      exact (G.walkupE z).reachable_edge_symm y
    · have hface : (G.walkupE z).face x = y := by
        apply Subtype.ext
        change ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) = y.1
        calc
          ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) =
              G.face z := PermSkip.skip_apply_of_apply_eq G.face x hxz_face.symm
          _ = y.1 := hzy_face.symm
      rw [← hface]
      exact (G.walkupE z).reachable_face x

theorem face_ne_of_edge_fixed_node_ne
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    G.face z ≠ z := by
  intro hf
  exact hn ((G.node_eq_self_iff_face_eq_self_of_edge_eq_self he).mpr hf)

theorem edge_node_ne_of_edge_fixed_node_ne
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    G.edge (G.node z) ≠ z := by
  intro hbad
  have he_symm : G.edge.symm z = z := by
    calc
      G.edge.symm z = G.edge.symm (G.edge z) := by rw [he]
      _ = z := by simp
  exact hn
    (calc
      G.node z = G.edge.symm (G.edge (G.node z)) := by simp
      _ = G.edge.symm z := by rw [hbad]
      _ = z := he_symm)

theorem walkupE_reachable_node_to_face_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    (G.walkupE z).Reachable
      (⟨G.node z, hn⟩ : G.DeletedDart z)
      (⟨G.face z, G.face_ne_of_edge_fixed_node_ne he hn⟩ :
        G.DeletedDart z) := by
  let u : G.DeletedDart z := ⟨G.node z, hn⟩
  let w : G.DeletedDart z :=
    ⟨G.edge (G.node z), G.edge_node_ne_of_edge_fixed_node_ne he hn⟩
  let v : G.DeletedDart z :=
    ⟨G.face z, G.face_ne_of_edge_fixed_node_ne he hn⟩
  have huw : (G.walkupE z).edge u = w := by
    apply Subtype.ext
    calc
      ((G.walkupE z).edge u).1 = G.edge u.1 :=
        G.walkupE_edge_apply_coe_of_edge_fixed he u
      _ = w.1 := rfl
  have hface_edge_node : G.face (G.edge (G.node z)) = z := by
    rw [G.edge_node_eq_face_symm]
    simp
  have hwv : (G.walkupE z).face w = v := by
    apply Subtype.ext
    change ((G.walkupSkipFace z w : G.DeletedDart z) : G.Dart) = v.1
    calc
      ((G.walkupSkipFace z w : G.DeletedDart z) : G.Dart) =
          G.face z := PermSkip.skip_apply_of_apply_eq G.face w hface_edge_node
      _ = v.1 := rfl
  have huw_reach : (G.walkupE z).Reachable u w := by
    rw [← huw]
    exact (G.walkupE z).reachable_edge u
  have hwv_reach : (G.walkupE z).Reachable w v := by
    rw [← hwv]
    exact (G.walkupE z).reachable_face w
  simpa [u, v] using huw_reach.trans hwv_reach

def walkupEEdgeFixedComponentDart
    {z : G.Dart} (hn : G.node z ≠ z) (x : G.Dart) :
    G.DeletedDart z :=
  if hx : x = z then ⟨G.node z, hn⟩ else ⟨x, hx⟩

theorem walkupE_reachable_representatives_of_link_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z)
    {x y : G.Dart} (hxy : G.Link x y) :
    (G.walkupE z).Reachable
      (G.walkupEEdgeFixedComponentDart hn x)
      (G.walkupEEdgeFixedComponentDart hn y) := by
  by_cases hx : x = z
  · by_cases hy : y = z
    · have hsame :
          G.walkupEEdgeFixedComponentDart hn x =
            G.walkupEEdgeFixedComponentDart hn y := by
        apply Subtype.ext
        simp [walkupEEdgeFixedComponentDart, hx, hy]
      simpa [hsame] using
        (G.walkupE z).reachable_refl
          (G.walkupEEdgeFixedComponentDart hn x)
    · rcases hxy with hxy | hxy | hxy
      · have hyz : y = z := by
          calc
            y = G.edge x := hxy
            _ = G.edge z := by rw [hx]
            _ = z := he
        exact False.elim (hy hyz)
      · have hynode : y = G.node z := by
          calc
            y = G.node x := hxy
            _ = G.node z := by rw [hx]
        have hsame :
            G.walkupEEdgeFixedComponentDart hn x =
              G.walkupEEdgeFixedComponentDart hn y := by
          apply Subtype.ext
          calc
            (G.walkupEEdgeFixedComponentDart hn x).1 = G.node z := by
              simp [walkupEEdgeFixedComponentDart, hx]
            _ = y := hynode.symm
            _ = (G.walkupEEdgeFixedComponentDart hn y).1 := by
              simp [walkupEEdgeFixedComponentDart, hy]
        simpa [hsame] using
          (G.walkupE z).reachable_refl
            (G.walkupEEdgeFixedComponentDart hn x)
      · have hyface : y = G.face z := by
          calc
            y = G.face x := hxy
            _ = G.face z := by rw [hx]
        have hsource :
            G.walkupEEdgeFixedComponentDart hn x =
              (⟨G.node z, hn⟩ : G.DeletedDart z) := by
          apply Subtype.ext
          simp [walkupEEdgeFixedComponentDart, hx]
        have htarget :
            G.walkupEEdgeFixedComponentDart hn y =
              (⟨G.face z, G.face_ne_of_edge_fixed_node_ne he hn⟩ :
                G.DeletedDart z) := by
          apply Subtype.ext
          calc
            (G.walkupEEdgeFixedComponentDart hn y).1 = y := by
              simp [walkupEEdgeFixedComponentDart, hy]
            _ = G.face z := hyface
        simpa [hsource, htarget] using
          G.walkupE_reachable_node_to_face_of_edge_fixed he hn
  · by_cases hy : y = z
    · have hxz : G.Link
          (G.walkupEEdgeFixedComponentDart hn x).1 z := by
        simpa [walkupEEdgeFixedComponentDart, hx, hy] using hxy
      have hzy : G.Link z (G.node z) := Or.inr (Or.inl rfl)
      have hreach :=
        G.walkupE_reachable_of_link_through_deleted_of_edge_fixed he
          (x := G.walkupEEdgeFixedComponentDart hn x)
          (y := (⟨G.node z, hn⟩ : G.DeletedDart z))
          hxz hzy
      simpa [walkupEEdgeFixedComponentDart, hx, hy] using hreach
    · have hxy' : G.Link
          (G.walkupEEdgeFixedComponentDart hn x).1
          (G.walkupEEdgeFixedComponentDart hn y).1 := by
        simpa [walkupEEdgeFixedComponentDart, hx, hy] using hxy
      exact G.walkupE_link_of_link_of_edge_fixed he hxy'

theorem walkupE_componentOf_representatives_eq_of_link_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z)
    {x y : G.Dart} (hxy : G.Link x y) :
    (G.walkupE z).componentOf
        (G.walkupEEdgeFixedComponentDart hn x) =
      (G.walkupE z).componentOf
        (G.walkupEEdgeFixedComponentDart hn y) :=
  (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_reachable_representatives_of_link_of_edge_fixed he hn hxy)

theorem walkupE_componentOf_representatives_eq_of_reachable_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z)
    {x y : G.Dart} (hxy : G.Reachable x y) :
    (G.walkupE z).componentOf
        (G.walkupEEdgeFixedComponentDart hn x) =
      (G.walkupE z).componentOf
        (G.walkupEEdgeFixedComponentDart hn y) :=
  hxy.apply_eq
    (fun x => (G.walkupE z).componentOf
      (G.walkupEEdgeFixedComponentDart hn x))
    (fun {_ _} h =>
      G.walkupE_componentOf_representatives_eq_of_link_of_edge_fixed he hn h)

noncomputable def walkupEComponentEquivOfEdgeFixedNodeNe
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    (G.walkupE z).Component ≃ G.Component where
  toFun :=
    Quotient.map
      (fun x : G.DeletedDart z => x.1)
      (by
        intro x y hxy
        exact G.walkupE_reachable_reachable hxy)
  invFun :=
    Quotient.lift
      (fun x : G.Dart =>
        (G.walkupE z).componentOf
          (G.walkupEEdgeFixedComponentDart hn x))
      (by
        intro x y hxy
        exact
          G.walkupE_componentOf_representatives_eq_of_reachable_of_edge_fixed
            he hn hxy)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    have hrep_x : G.walkupEEdgeFixedComponentDart hn x.1 = x := by
      apply Subtype.ext
      simp [walkupEEdgeFixedComponentDart, x.2]
    change
      (G.walkupE z).componentOf
          (G.walkupEEdgeFixedComponentDart hn x.1) =
        Quot.mk (G.walkupE z).reachableSetoid x
    rw [hrep_x]
    rfl
  right_inv c := by
    refine Quotient.inductionOn c ?_
    intro x
    by_cases hx : x = z
    · change G.componentOf
          ((G.walkupEEdgeFixedComponentDart hn x : G.DeletedDart z) : G.Dart) =
        G.componentOf x
      calc
        G.componentOf
            ((G.walkupEEdgeFixedComponentDart hn x : G.DeletedDart z) :
              G.Dart) =
            G.componentOf (G.node z) := by
              simp [walkupEEdgeFixedComponentDart, hx]
        _ = G.componentOf z := G.componentOf_node z
        _ = G.componentOf x := by rw [hx]
    · change G.componentOf
          ((G.walkupEEdgeFixedComponentDart hn x : G.DeletedDart z) : G.Dart) =
        G.componentOf x
      simp [walkupEEdgeFixedComponentDart, hx]

theorem walkupE_componentCount_eq_of_edge_fixed_node_ne
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    (G.walkupE z).componentCount = G.componentCount := by
  change Nat.card (G.walkupE z).Component = Nat.card G.Component
  exact Nat.card_congr (G.walkupEComponentEquivOfEdgeFixedNodeNe he hn)

theorem walkupE_eulerLeft_step_of_edge_fixed_node_ne
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    2 * 1 + (G.walkupE z).eulerLeft = G.eulerLeft + 1 := by
  have hcomp := G.walkupE_componentCount_eq_of_edge_fixed_node_ne he hn
  have hdart := G.walkupE_dart_card_add_one z
  unfold eulerLeft componentCount at *
  omega

theorem walkupE_stepCount_of_edge_fixed_node_ne
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z ≠ z) :
    ∃ a b : Nat,
      b ≤ a ∧
        2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 ∧
          2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1 :=
  ⟨1, 1, le_rfl,
    G.walkupE_eulerLeft_step_of_edge_fixed_node_ne he hn,
    by simpa [hn] using G.walkupE_eulerRight_step_of_edge_eq he⟩

theorem walkupE_link_of_link_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z)
    {x y : G.DeletedDart z}
    (hxy : G.Link x.1 y.1) :
    (G.walkupE z).Reachable x y := by
  rcases hxy with hxy | hxy | hxy
  · have hy : y.1 = G.edge x.1 := hxy
    have hedge : (G.walkupE z).edge x = y := by
      apply Subtype.ext
      have hperm :
          (G.walkupE z).edge x = (PermSkip.skip G.edge z) x := by
        exact congrArg (fun f : Equiv.Perm (G.DeletedDart z) => f x)
          (G.walkupE_edge_eq_skip_edge_of_edge_eq he)
      have hval :
          ((G.walkupE z).edge x).1 =
            ((PermSkip.skip G.edge z x : G.DeletedDart z) : G.Dart) :=
        congrArg Subtype.val hperm
      calc
        ((G.walkupE z).edge x).1 =
            ((PermSkip.skip G.edge z x : G.DeletedDart z) : G.Dart) := hval
        _ = G.edge x.1 := PermSkip.skip_apply_of_fixed G.edge he x
        _ = y.1 := hy.symm
    rw [← hedge]
    exact (G.walkupE z).reachable_edge x
  · have hy : y.1 = G.node x.1 := hxy
    have hnode : (G.walkupE z).node x = y := by
      apply Subtype.ext
      change ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipNode z x : G.DeletedDart z) : G.Dart) =
            G.node x.1 := PermSkip.skip_apply_of_fixed G.node hn x
        _ = y.1 := hy.symm
    rw [← hnode]
    exact (G.walkupE z).reachable_node x
  · have hy : y.1 = G.face x.1 := hxy
    have hface : (G.walkupE z).face x = y := by
      apply Subtype.ext
      change ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) = y.1
      calc
        ((G.walkupSkipFace z x : G.DeletedDart z) : G.Dart) =
            G.face x.1 := PermSkip.skip_apply_of_fixed G.face hf x
        _ = y.1 := hy.symm
    rw [← hface]
    exact (G.walkupE z).reachable_face x

theorem walkupE_componentOf_eq_of_link_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z)
    {x y : G.DeletedDart z}
    (hxy : G.Link x.1 y.1) :
    (G.walkupE z).componentOf x = (G.walkupE z).componentOf y :=
  (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_link_of_link_of_all_fixed he hn hf hxy)

theorem eq_of_link_to_all_fixed
    {x z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z)
    (hxz : G.Link x z) :
    x = z := by
  rcases hxz with hxz | hxz | hxz
  · have hedge : G.edge x = G.edge z := by
      rw [← hxz, he]
    exact G.edge.injective hedge
  · have hnode : G.node x = G.node z := by
      rw [← hxz, hn]
    exact G.node.injective hnode
  · have hface : G.face x = G.face z := by
      rw [← hxz, hf]
    exact G.face.injective hface

theorem eq_of_reachable_to_all_fixed
    {x z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z)
    (hxz : G.Reachable x z) :
    x = z := by
  induction hxz with
  | refl =>
      rfl
  | tail hxy hyz ih =>
      have hy_eq_z := G.eq_of_link_to_all_fixed he hn hf hyz
      exact
        (ih (by simpa [hy_eq_z] using he)
            (by simpa [hy_eq_z] using hn)
            (by simpa [hy_eq_z] using hf)).trans hy_eq_z

theorem walkupE_reachable_of_reachable_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z)
    {x y : G.DeletedDart z}
    (hxy : G.Reachable x.1 y.1) :
    (G.walkupE z).Reachable x y := by
  let W := G.walkupE z
  have hmain :
      ∀ {y₀ : G.Dart}, G.Reachable x.1 y₀ →
        ∀ hy₀ : y₀ ≠ z, W.Reachable x ⟨y₀, hy₀⟩ := by
    intro y₀ hxy₀
    refine Relation.ReflTransGen.recOn hxy₀ ?_ ?_
    · intro hx_ne
      have hsub : (⟨x.1, hx_ne⟩ : G.DeletedDart z) = x := by
          apply Subtype.ext
          rfl
      simpa [W, hsub] using (G.walkupE z).reachable_refl x
    · intro b c hxb hby ih hc_ne
      have hb_ne : b ≠ z := by
        intro hbz
        have hxz : G.Reachable x.1 z := by
          simpa [hbz] using hxb
        exact x.2 (G.eq_of_reachable_to_all_fixed he hn hf hxz)
      let b' : G.DeletedDart z := ⟨b, hb_ne⟩
      have hxb' : W.Reachable x b' := ih hb_ne
      have hby' : G.Link b'.1 c := by
        simpa [b'] using hby
      exact hxb'.trans
        (G.walkupE_link_of_link_of_all_fixed he hn hf hby')
  simpa using hmain hxy y.2

/-- Projection from components of `WalkupE z` to components of the original
hypermap.  This is the quotient-level map behind the `Euler_lhs_WalkupE`
component-count calculation. -/
noncomputable def walkupEComponentProjection (z : G.Dart) :
    (G.walkupE z).Component → G.Component :=
  Quotient.map
    (fun x : G.DeletedDart z => x.1)
    (by
      intro x y hxy
      exact G.walkupE_reachable_reachable hxy)

@[simp]
theorem walkupEComponentProjection_componentOf
    {z : G.Dart} (x : (G.walkupE z).Dart) :
    G.walkupEComponentProjection z ((G.walkupE z).componentOf x) =
      G.componentOf x.1 :=
  rfl

theorem walkupEComponentProjection_componentOf_eq_iff
    {z : G.Dart} (x y : (G.walkupE z).Dart) :
    G.walkupEComponentProjection z ((G.walkupE z).componentOf x) =
        G.walkupEComponentProjection z ((G.walkupE z).componentOf y) ↔
      G.Reachable x.1 y.1 := by
  rw [G.walkupEComponentProjection_componentOf x,
    G.walkupEComponentProjection_componentOf y,
    G.componentOf_eq_iff]

theorem walkupE_reachable_iff_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z)
    {x y : G.DeletedDart z} :
    (G.walkupE z).Reachable x y ↔ G.Reachable x.1 y.1 := by
  constructor
  · exact G.walkupE_reachable_reachable
  · exact G.walkupE_reachable_of_reachable_of_all_fixed he hn hf

/-- If the deleted dart is fixed by all three permutations, it is an isolated
component.  The components of the deleted Walkup map are exactly the remaining
components of the original hypermap. -/
noncomputable def walkupEComponentEquivOfAllFixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z) :
    (G.walkupE z).Component ≃
      {c : G.Component // c ≠ G.componentOf z} where
  toFun q :=
    Quotient.lift
      (fun x : G.DeletedDart z =>
        ⟨G.componentOf x.1, by
          intro hbad
          exact x.2
            (G.eq_of_reachable_to_all_fixed he hn hf
              ((G.componentOf_eq_iff).mp hbad))⟩)
      (by
        intro x y hxy
        apply Subtype.ext
        exact G.componentOf_eq_componentOf
          (G.walkupE_reachable_reachable hxy))
      q
  invFun c :=
    let x := Quotient.out c.1
    have hx : x ≠ z := by
      intro hxz
      have hout : G.componentOf x = c.1 := Quotient.out_eq c.1
      exact c.2 (by simpa [hxz] using hout.symm)
    (G.walkupE z).componentOf (⟨x, hx⟩ : G.DeletedDart z)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    let y := Quotient.out (G.componentOf x.1)
    have hy : y ≠ z := by
      intro hyz
      have hout : G.componentOf y = G.componentOf x.1 :=
        Quotient.out_eq (G.componentOf x.1)
      exact x.2
        (G.eq_of_reachable_to_all_fixed he hn hf
          (G.reachable_symm
            ((G.componentOf_eq_iff).mp (by simpa [hyz] using hout))))
    apply (G.walkupE z).componentOf_eq_componentOf
    exact (G.walkupE_reachable_iff_of_all_fixed he hn hf).mpr
      ((G.componentOf_eq_iff).mp
        (Quotient.out_eq (G.componentOf x.1)))
  right_inv c := by
    apply Subtype.ext
    dsimp
    exact Quotient.out_eq c.1

theorem walkupE_componentCount_add_one_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z) :
    (G.walkupE z).componentCount + 1 = G.componentCount := by
  classical
  have hsurj : Function.Surjective G.componentOf := by
    intro c
    refine Quotient.inductionOn c ?_
    intro x
    exact ⟨x, rfl⟩
  letI : Finite G.Component := Finite.of_surjective G.componentOf hsurj
  letI : Fintype G.Component := Fintype.ofFinite G.Component
  change Nat.card (G.walkupE z).Component + 1 = Nat.card G.Component
  rw [Nat.card_congr (G.walkupEComponentEquivOfAllFixed he hn hf)]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa [Nat.add_comm] using DeletedPoint.card_add_one (G.componentOf z)

theorem walkupE_eulerLeft_step_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z) :
    2 * 2 + (G.walkupE z).eulerLeft = G.eulerLeft + 1 := by
  have hcomp := G.walkupE_componentCount_add_one_of_all_fixed he hn hf
  have hdart := G.walkupE_dart_card_add_one z
  unfold eulerLeft componentCount at *
  omega

theorem walkupE_exists_eulerLeft_step_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z) :
    ∃ a : Nat, 2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 :=
  ⟨2, G.walkupE_eulerLeft_step_of_all_fixed he hn hf⟩

theorem walkupE_stepCount_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z) :
    ∃ a b : Nat,
      b ≤ a ∧
        2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 ∧
          2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1 :=
  ⟨2, 2, le_rfl,
    G.walkupE_eulerLeft_step_of_all_fixed he hn hf,
    by simpa [hn] using G.walkupE_eulerRight_step_of_edge_eq he⟩

theorem walkupE_stepCount_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) :
    ∃ a b : Nat,
      b ≤ a ∧
        2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 ∧
          2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1 := by
  by_cases hn : G.node z = z
  · have hf : G.face z = z :=
      (G.node_eq_self_iff_face_eq_self_of_edge_eq_self he).mp hn
    exact G.walkupE_stepCount_of_all_fixed he hn hf
  · exact G.walkupE_stepCount_of_edge_fixed_node_ne he hn

theorem walkupE_eulerLeft_step_of_componentCount_step
    {z : G.Dart} {a : Nat}
    (hcomp : a + (G.walkupE z).componentCount =
      G.componentCount + 1) :
    2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 := by
  have hdart := G.walkupE_dart_card_add_one z
  unfold eulerLeft componentCount at *
  omega

theorem walkupE_eulerRight_step_of_edgeOrbit_step
    {z : G.Dart} {e b : Nat}
    (hedge : e + (G.walkupE z).edgeOrbitCount =
      G.edgeOrbitCount + 1)
    (hsum : e + (if G.node z = z then 1 else 0) +
        (if G.face z = z then 1 else 0) = 2 * b) :
    2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1 := by
  have hnode := G.walkupE_nodeOrbitCount_add_indicator z
  have hface := G.walkupE_faceOrbitCount_add_indicator z
  unfold eulerRight at *
  omega

theorem walkupE_eulerRight_step_of_link_self_of_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    2 * 1 + (G.walkupE z).eulerRight = G.eulerRight + 1 := by
  have hedge := G.walkupE_edgeOrbit_step_of_link_self_of_edge_ne hz he
  have hind := G.node_face_indicator_add_eq_one_of_link_self_of_edge_ne hz he
  exact G.walkupE_eulerRight_step_of_edgeOrbit_step
    (e := 1) (b := 1) hedge (by omega)

theorem walkupE_stepCount_of_count_steps
    {z : G.Dart} {a e b : Nat}
    (hba : b ≤ a)
    (hcomp : a + (G.walkupE z).componentCount =
      G.componentCount + 1)
    (hedge : e + (G.walkupE z).edgeOrbitCount =
      G.edgeOrbitCount + 1)
    (hsum : e + (if G.node z = z then 1 else 0) +
        (if G.face z = z then 1 else 0) = 2 * b) :
    ∃ a b : Nat,
      b ≤ a ∧
        2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 ∧
          2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1 :=
  ⟨a, b, hba,
    G.walkupE_eulerLeft_step_of_componentCount_step hcomp,
    G.walkupE_eulerRight_step_of_edgeOrbit_step hedge hsum⟩


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
