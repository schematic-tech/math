import Schematic.Math.GraphTheory.Separations

/-!
Abstract interfaces for graph contractions. The concrete quotient construction
should be filled in here before replacing the theorem stubs in the paper proof.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

def contractionTargetGraph
    (G : SimpleGraph V) {W : Type u} (f : V -> W) : SimpleGraph W where
  Adj x y := x ≠ y ∧ Exists fun v : V => Exists fun w : V => f v = x ∧ f w = y ∧ G.Adj v w
  symm := by
    rintro x y ⟨hxy, v, w, hv, hw, hadj⟩
    exact ⟨hxy.symm, w, v, hw, hv, hadj.symm⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

structure GraphContraction (G : SimpleGraph V) where
  Target : Type u
  graph : SimpleGraph Target
  map : V -> Target
  map_adj :
    forall {v w : V}, G.Adj v w -> map v = map w ∨ graph.Adj (map v) (map w)
  edge_lift :
    forall {y z : Target}, graph.Adj y z ->
      Exists fun v : V => Exists fun w : V => map v = y ∧ map w = z ∧ G.Adj v w
  surjective : Function.Surjective map
  connected_fiber : forall y : Target, (G.induce {v : V | map v = y}).Connected

def GraphContraction.ofMap
    (G : SimpleGraph V) {W : Type u} (f : V -> W)
    (hsurj : Function.Surjective f)
    (hfiber : forall y : W, (G.induce {v : V | f v = y}).Connected) :
    GraphContraction G where
  Target := W
  graph := contractionTargetGraph G f
  map := f
  map_adj := by
    intro v w hvw
    by_cases h : f v = f w
    · exact Or.inl h
    · exact Or.inr ⟨h, v, w, rfl, rfl, hvw⟩
  edge_lift := by
    intro y z hyz
    exact hyz.2
  surjective := hsurj
  connected_fiber := hfiber

theorem colorable_of_contractionTarget_colorable_with_independent_fiber
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {W : Type u}
    (f : V -> W) (y : W) {S : Set V} {u : V}
    (hS_independent :
      forall a : V, a ∈ S ->
        forall b : V, b ∈ S -> a ≠ b -> Not (G.Adj a b))
    (hS_map : forall v : V, v ∈ S -> f v = y)
    (houtside_map_ne : forall v : V, v ∉ S -> v ≠ u -> f v ≠ y)
    (houtside_map_injective :
      forall a b : V,
        a ∉ S -> a ≠ u -> b ∉ S -> b ≠ u -> f a = f b -> a = b)
    (hneighbor_card : (G.neighborSet u \ S).ncard <= 2)
    (hquot_color : (contractionTargetGraph G f).Colorable 4) :
    G.Colorable 4 := by
  classical
  letI : DecidablePred (fun v : V => v ∉ S) := Classical.decPred _
  rcases hquot_color with ⟨cq⟩
  let outsideNeighbors : Finset V := (G.neighborFinset u).filter fun v => v ∉ S
  have houtsideNeighbors_set : (outsideNeighbors : Set V) = G.neighborSet u \ S := by
    ext v
    simp [outsideNeighbors, SimpleGraph.mem_neighborFinset]
  have houtsideNeighbors_card : outsideNeighbors.card <= 2 := by
    rw [← Set.ncard_coe_finset, houtsideNeighbors_set]
    exact hneighbor_card
  let outsideColors : Finset (Fin 4) := outsideNeighbors.image (fun v => cq (f v))
  let forbidden : Finset (Fin 4) := insert (cq y) outsideColors
  have houtsideColors_card : outsideColors.card <= outsideNeighbors.card := by
    exact Finset.card_image_le
  have hforbidden_card : forbidden.card <= outsideColors.card + 1 := by
    exact Finset.card_insert_le _ _
  have hforbidden_lt : forbidden.card < Fintype.card (Fin 4) := by
    simp [forbidden] at hforbidden_card ⊢
    omega
  obtain ⟨cu, _hcu_univ, hcu_not_forbidden⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (s := forbidden) (t := (Finset.univ : Finset (Fin 4))) (by
        simpa using hforbidden_lt)
  let color : V -> Fin 4 := fun v =>
    if v = u then cu else if v ∈ S then cq y else cq (f v)
  refine ⟨Coloring.mk color ?_⟩
  intro a b hab hsame
  by_cases hau : a = u
  · subst a
    have hb_ne_u : b ≠ u := hab.ne'
    by_cases hbS : b ∈ S
    · have hcolor_b : color b = cq y := by simp [color, hb_ne_u, hbS]
      have hcolor_u : color u = cu := by simp [color]
      have hcu_ne : cu ≠ cq y := by
        intro h
        exact hcu_not_forbidden (by rw [h]; exact Finset.mem_insert_self _ _)
      exact hcu_ne (by simpa [hcolor_u, hcolor_b] using hsame)
    · have hb_mem_outside : b ∈ outsideNeighbors := by
        simp [outsideNeighbors, SimpleGraph.mem_neighborFinset, hab, hbS]
      have hb_color_mem : cq (f b) ∈ outsideColors := by
        exact Finset.mem_image.mpr ⟨b, hb_mem_outside, rfl⟩
      have hcolor_b : color b = cq (f b) := by simp [color, hb_ne_u, hbS]
      have hcolor_u : color u = cu := by simp [color]
      have hcu_ne : cu ≠ cq (f b) := by
        intro h
        exact hcu_not_forbidden (by
          rw [h]
          exact Finset.mem_insert_of_mem hb_color_mem)
      exact hcu_ne (by simpa [hcolor_u, hcolor_b] using hsame)
  · by_cases hbu : b = u
    · subst b
      have ha_ne_u : a ≠ u := hau
      by_cases haS : a ∈ S
      · have hcolor_a : color a = cq y := by simp [color, ha_ne_u, haS]
        have hcolor_u : color u = cu := by simp [color]
        have hcu_ne : cu ≠ cq y := by
          intro h
          exact hcu_not_forbidden (by rw [h]; exact Finset.mem_insert_self _ _)
        exact hcu_ne (by simpa [hcolor_a, hcolor_u, eq_comm] using hsame.symm)
      · have ha_mem_outside : a ∈ outsideNeighbors := by
          simp [outsideNeighbors, SimpleGraph.mem_neighborFinset, hab.symm, haS]
        have ha_color_mem : cq (f a) ∈ outsideColors := by
          exact Finset.mem_image.mpr ⟨a, ha_mem_outside, rfl⟩
        have hcolor_a : color a = cq (f a) := by simp [color, ha_ne_u, haS]
        have hcolor_u : color u = cu := by simp [color]
        have hcu_ne : cu ≠ cq (f a) := by
          intro h
          exact hcu_not_forbidden (by
            rw [h]
            exact Finset.mem_insert_of_mem ha_color_mem)
        exact hcu_ne (by simpa [hcolor_a, hcolor_u, eq_comm] using hsame.symm)
    · by_cases haS : a ∈ S
      · by_cases hbS : b ∈ S
        · exact hS_independent a haS b hbS hab.ne hab
        · have hfa : f a = y := hS_map a haS
          have hfb_ne : f b ≠ y := houtside_map_ne b hbS hbu
          have hneq : f a ≠ f b := by
            intro h
            exact hfb_ne (h ▸ hfa)
          have hqadj : (contractionTargetGraph G f).Adj (f a) (f b) :=
            ⟨hneq, a, b, rfl, rfl, hab⟩
          exact cq.valid hqadj
            (by simpa [color, hau, hbu, haS, hbS, hfa] using hsame)
      · by_cases hbS : b ∈ S
        · have hfb : f b = y := hS_map b hbS
          have hfa_ne : f a ≠ y := houtside_map_ne a haS hau
          have hneq : f a ≠ f b := by
            intro h
            exact hfa_ne (h.trans hfb)
          have hqadj : (contractionTargetGraph G f).Adj (f a) (f b) :=
            ⟨hneq, a, b, rfl, rfl, hab⟩
          exact cq.valid hqadj
            (by simpa [color, hau, hbu, haS, hbS, hfb] using hsame)
        · have hneq : f a ≠ f b := by
            intro h
            exact hab.ne (houtside_map_injective a b haS hau hbS hbu h)
          have hqadj : (contractionTargetGraph G f).Adj (f a) (f b) :=
            ⟨hneq, a, b, rfl, rfl, hab⟩
          exact cq.valid hqadj
            (by simpa [color, hau, hbu, haS, hbS] using hsame)

noncomputable def GraphContraction.collapseSubgraph
    (G : SimpleGraph V)
    (H : G.Subgraph)
    (hH_connected : H.coe.Connected) :
    GraphContraction G := by
  classical
  let Target : Type u := Option {v : V // v ∉ H.verts}
  let f : V -> Target := fun v =>
    if hv : v ∈ H.verts then none else some ⟨v, hv⟩
  exact GraphContraction.ofMap G f
    (by
      intro y
      cases y with
      | none =>
          obtain ⟨v⟩ := hH_connected.nonempty
          exact ⟨v, by simp [f, v.2]⟩
      | some v =>
          exact ⟨v, by simp [f, v.2]⟩)
    (by
      intro y
      cases y with
      | none =>
          have hfiber_eq : {v : V | f v = none} = H.verts := by
            ext v
            by_cases hv : v ∈ H.verts <;> simp [f, hv]
          have hH_induce : (G.induce H.verts).Connected := by
            refine {
              preconnected := ?_
              nonempty := ?_
            }
            · intro a b
              let aH : H.verts := ⟨a, a.2⟩
              let bH : H.verts := ⟨b, b.2⟩
              let F : H.coe →g (G.induce H.verts) := {
                toFun := fun x => ⟨x, x.2⟩
                map_rel' := by
                  intro x y hxy
                  exact H.adj_sub hxy }
              exact (hH_connected aH bH).map F
            · obtain ⟨v⟩ := hH_connected.nonempty
              exact ⟨⟨v, v.2⟩⟩
          rw [hfiber_eq]
          exact hH_induce
      | some a =>
          have hfiber_eq : {v : V | f v = some a} = ({(a : V)} : Set V) := by
            ext v
            constructor
            · intro hvmap
              by_cases hvH : v ∈ H.verts
              · simp [f, hvH] at hvmap
              · have hvmap' :
                    some (⟨v, hvH⟩ : {v : V // v ∉ H.verts}) = some a := by
                  change (if h : v ∈ H.verts then none else some ⟨v, h⟩) =
                    some a at hvmap
                  rw [dif_neg hvH] at hvmap
                  exact hvmap
                injection hvmap' with hsub
                exact congrArg Subtype.val hsub
            · intro hv_eq
              subst v
              simp [f, a.2]
          rw [hfiber_eq]
          exact SimpleGraph.Connected.of_subsingleton)


end Schematic.Math.GraphTheory
