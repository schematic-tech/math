import Schematic.Math.GraphTheory.Embedding.Geometry

/-!
Orbit-count lemmas for the hypermap proof.

The discharging total uses Euler counts: one connected component, two darts
per edge orbit in a plain map, three darts per node orbit in a cubic map, and
exact Euler equality from the nontruncated genus theorem.  This file proves the
finite orbit-count pieces without importing the certificate layer.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

/-- The elements in one cyclic orbit, viewed as a finite subtype. -/
def PermClass {α : Type u} (σ : Equiv.Perm α) (x : α) : Type u :=
  { y : α // PermReachable σ x y }

instance permClassFinite
    {α : Type u} [Finite α]
    (σ : Equiv.Perm α) (x : α) :
    Finite (PermClass σ x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance permClassFintype
    {α : Type u} [Fintype α]
    (σ : Equiv.Perm α) (x : α) :
    Fintype (PermClass σ x) :=
  Fintype.ofFinite (PermClass σ x)

/-- The disjoint union of permutation classes, indexed by cyclic orbits, is the
ambient type. -/
noncomputable def permClassSigmaEquiv
    {α : Type u} [Fintype α] (σ : Equiv.Perm α) :
    (Sigma fun o : PermOrbit σ => PermClass σ (Quotient.out o)) ≃ α where
  toFun p := p.2.1
  invFun x :=
    ⟨PermOrbit.of σ x,
      ⟨x, Quotient.exact (Quotient.out_eq (PermOrbit.of σ x))⟩⟩
  left_inv p := by
    rcases p with ⟨o, y, hy⟩
    dsimp
    have hout : PermOrbit.of σ (Quotient.out o) = o :=
      Quotient.out_eq o
    have hyorbit :
        PermOrbit.of σ (Quotient.out o) = PermOrbit.of σ y :=
      PermOrbit.of_eq_of σ hy
    have ho : PermOrbit.of σ y = o := hyorbit.symm.trans hout
    cases ho
    simp
  right_inv x := rfl

theorem sum_permClass_card_eq_card
    {α : Type u} [Fintype α] (σ : Equiv.Perm α) :
    (∑ o : PermOrbit σ, Nat.card (PermClass σ (Quotient.out o))) =
      Fintype.card α := by
  simp_rw [Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (permClassSigmaEquiv σ)

namespace Hypermap

variable {G : Hypermap.{u}}

abbrev EdgeClass (G : Hypermap.{u}) (x : G.Dart) : Type u :=
  PermClass G.edge x

abbrev NodeClass (G : Hypermap.{u}) (x : G.Dart) : Type u :=
  PermClass G.node x

theorem Connected.componentCount_eq_one
    (hG : G.Connected) :
    G.componentCount = 1 := by
  have hsub : Subsingleton G.Component := ⟨by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact Quot.sound (hG.2 x y)⟩
  have hnonempty : Nonempty G.Component := by
    rcases hG.1 with ⟨x⟩
    exact ⟨G.componentOf x⟩
  letI : Subsingleton G.Component := hsub
  letI : Nonempty G.Component := hnonempty
  exact Nat.card_unique

noncomputable def edgeOrbitComponentMap :
    G.EdgeOrbit → G.Component :=
  Quotient.lift
    (fun x : G.Dart => G.componentOf x)
    (by
      intro x y hxy
      exact Quot.sound (G.edgePermReachable_reachable hxy))

theorem edgeOrbitComponentMap_surjective :
    Function.Surjective (edgeOrbitComponentMap (G := G)) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro x
  exact ⟨PermOrbit.of G.edge x, rfl⟩

theorem componentCount_le_edgeOrbitCount :
    G.componentCount ≤ G.edgeOrbitCount := by
  classical
  letI : DecidableRel G.reachableSetoid.r := Classical.decRel _
  letI : Fintype G.Component := Quotient.fintype G.reachableSetoid
  rw [componentCount, edgeOrbitCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective (edgeOrbitComponentMap (G := G))
    (edgeOrbitComponentMap_surjective (G := G))

noncomputable def nodeOrbitComponentMap :
    G.NodeOrbit → G.Component :=
  Quotient.lift
    (fun x : G.Dart => G.componentOf x)
    (by
      intro x y hxy
      exact Quot.sound (G.nodePermReachable_reachable hxy))

theorem nodeOrbitComponentMap_surjective :
    Function.Surjective (nodeOrbitComponentMap (G := G)) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro x
  exact ⟨PermOrbit.of G.node x, rfl⟩

theorem componentCount_le_nodeOrbitCount :
    G.componentCount ≤ G.nodeOrbitCount := by
  classical
  letI : DecidableRel G.reachableSetoid.r := Classical.decRel _
  letI : Fintype G.Component := Quotient.fintype G.reachableSetoid
  rw [componentCount, nodeOrbitCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective (nodeOrbitComponentMap (G := G))
    (nodeOrbitComponentMap_surjective (G := G))

noncomputable def faceOrbitComponentMap :
    G.FaceOrbit → G.Component :=
  Quotient.lift
    (fun x : G.Dart => G.componentOf x)
    (by
      intro x y hxy
      exact Quot.sound (G.facePermReachable_reachable hxy))

theorem faceOrbitComponentMap_surjective :
    Function.Surjective (faceOrbitComponentMap (G := G)) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro x
  exact ⟨PermOrbit.of G.face x, rfl⟩

theorem componentCount_le_faceOrbitCount :
    G.componentCount ≤ G.faceOrbitCount := by
  classical
  letI : DecidableRel G.reachableSetoid.r := Classical.decRel _
  letI : Fintype G.Component := Quotient.fintype G.reachableSetoid
  rw [componentCount, faceOrbitCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective (faceOrbitComponentMap (G := G))
    (faceOrbitComponentMap_surjective (G := G))

theorem eulerPlanar_of_eulerLeft_le_eulerRight
    (h : G.eulerLeft ≤ G.eulerRight) :
    G.EulerPlanar := by
  rw [EulerPlanar, genus, Nat.sub_eq_zero_of_le h]

theorem Plain.edge_link_eq
    (hG : G.Plain) {x y : G.Dart}
    (hxy : PermLink G.edge x y) :
    y = G.edge x := by
  cases hxy with
  | forward => rfl
  | backward => simp [Plain.edge_symm_eq (G := G) hG x]

theorem Plain.edge_reachable_cases
    (hG : G.Plain) {x y : G.Dart}
    (hxy : PermReachable G.edge x y) :
    y = x ∨ y = G.edge x := by
  induction hxy with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
      rcases ih with rfl | hb
      · exact Or.inr (Plain.edge_link_eq (G := G) hG hbc)
      · have hc : _ = _ := Plain.edge_link_eq (G := G) hG hbc
        exact Or.inl (by rw [hc, hb, Plain.edge_edge (G := G) hG x])

noncomputable def Plain.fin2EquivEdgeClass
    (hG : G.Plain) (x : G.Dart) :
    Fin 2 ≃ G.EdgeClass x where
  toFun i :=
    if (i : Nat) = 0 then
      ⟨x, PermReachable.refl G.edge x⟩
    else
      ⟨G.edge x, PermReachable.forward G.edge x⟩
  invFun y :=
    if y.1 = x then 0 else 1
  left_inv i := by
    apply Fin.ext
    have hi : (i : Nat) = 0 ∨ (i : Nat) = 1 := by omega
    rcases hi with hi | hi
    · simp [hi]
    · simp [hi, Plain.edge_ne (G := G) hG x]
  right_inv y := by
    rcases y with ⟨y, hy⟩
    rcases Plain.edge_reachable_cases (G := G) hG hy with rfl | rfl
    · simp
    · simp [Plain.edge_ne (G := G) hG x]

theorem Plain.edgeClass_card
    (hG : G.Plain) (x : G.Dart) :
    Nat.card (G.EdgeClass x) = 2 := by
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr
    (Plain.fin2EquivEdgeClass (G := G) hG x)).symm

theorem Plain.card_dart_eq_two_mul_edgeOrbitCount
    (hG : G.Plain) :
    Fintype.card G.Dart = 2 * G.edgeOrbitCount := by
  rw [← sum_permClass_card_eq_card G.edge]
  change
    (∑ o : G.EdgeOrbit, Nat.card (G.EdgeClass (Quotient.out o))) =
      2 * G.edgeOrbitCount
  simp_rw [Plain.edgeClass_card (G := G) hG]
  simp [Hypermap.edgeOrbitCount, Nat.card_eq_fintype_card, Nat.mul_comm]

theorem reachable_iff_permReachable_edge_of_node_eq_edge_face_eq_refl
    (hplain : G.Plain)
    (hnode : G.node = G.edge)
    (hface : G.face = Equiv.refl G.Dart)
    {x y : G.Dart} :
    G.Reachable x y ↔ PermReachable G.edge x y := by
  constructor
  · intro h
    induction h with
    | refl => exact PermReachable.refl G.edge x
    | tail _ hbc ih =>
        apply PermReachable.trans G.edge ih
        rcases hbc with hbc | hbc | hbc
        · subst hbc
          exact PermReachable.forward G.edge _
        · subst hbc
          rw [hnode]
          exact PermReachable.forward G.edge _
        · subst hbc
          rw [hface]
          exact PermReachable.refl G.edge _
  · intro h
    induction h with
    | refl => exact G.reachable_refl x
    | @tail b _c _hxb hbc ih =>
        apply Relation.ReflTransGen.trans ih
        cases hbc with
        | forward => exact G.reachable_edge b
        | backward =>
            have hs : G.edge.symm b = G.edge b :=
              Hypermap.Plain.edge_symm_eq (G := G) hplain b
            rw [hs]
            exact G.reachable_edge b

theorem componentCount_eq_edgeOrbitCount_of_node_eq_edge_face_eq_refl
    (hplain : G.Plain)
    (hnode : G.node = G.edge)
    (hface : G.face = Equiv.refl G.Dart) :
    G.componentCount = G.edgeOrbitCount := by
  classical
  let e : G.Component ≃ G.EdgeOrbit :=
    Quotient.congr (Equiv.refl G.Dart) (by
      intro x y
      exact G.reachable_iff_permReachable_edge_of_node_eq_edge_face_eq_refl
        hplain hnode hface)
  letI : DecidableRel G.reachableSetoid.r := Classical.decRel _
  letI : Fintype G.Component := Quotient.fintype G.reachableSetoid
  rw [componentCount, edgeOrbitCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact Fintype.card_congr e

theorem faceOrbitCount_eq_card_of_face_eq_refl
    (hface : G.face = Equiv.refl G.Dart) :
    G.faceOrbitCount = Fintype.card G.Dart := by
  classical
  let e : G.FaceOrbit ≃ G.Dart := by
    rw [show G.FaceOrbit = PermOrbit (Equiv.refl G.Dart) by
      simp [FaceOrbit, hface]]
    exact permOrbitReflEquiv G.Dart
  rw [faceOrbitCount, Nat.card_eq_fintype_card]
  exact Fintype.card_congr e

theorem nodeOrbitCount_eq_edgeOrbitCount_of_node_eq_edge
    (hnode : G.node = G.edge) :
    G.nodeOrbitCount = G.edgeOrbitCount := by
  classical
  let e : G.NodeOrbit ≃ G.EdgeOrbit :=
    Quotient.congr (Equiv.refl G.Dart) (by
      intro x y
      change PermReachable G.node x y ↔ PermReachable G.edge x y
      rw [hnode])
  rw [nodeOrbitCount, edgeOrbitCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact Fintype.card_congr e

theorem eulerPlanar_of_plain_node_eq_edge_face_eq_refl
    (hplain : G.Plain)
    (hnode : G.node = G.edge)
    (hface : G.face = Equiv.refl G.Dart) :
    G.EulerPlanar := by
  classical
  have hcomp :=
    G.componentCount_eq_edgeOrbitCount_of_node_eq_edge_face_eq_refl
      hplain hnode hface
  have hnode_count := G.nodeOrbitCount_eq_edgeOrbitCount_of_node_eq_edge hnode
  have hface_count := G.faceOrbitCount_eq_card_of_face_eq_refl hface
  have hdart := hplain.card_dart_eq_two_mul_edgeOrbitCount
  rw [EulerPlanar, genus, eulerLeft, eulerRight, hcomp, hnode_count,
    hface_count, hdart]
  omega

theorem Cubic.node_node_ne_self
    (hG : G.Cubic) (x : G.Dart) :
    G.node (G.node x) ≠ x := by
  intro hbad
  have hfixed : G.node x = x := by
    calc
      G.node x = G.node (G.node (G.node x)) := by rw [hbad]
      _ = x := (hG x).1
  exact (hG x).2 hfixed

theorem Cubic.node_ne_node_node
    (hG : G.Cubic) (x : G.Dart) :
    G.node x ≠ G.node (G.node x) := by
  intro hbad
  exact (hG x).2 (G.node.injective hbad).symm

theorem Cubic.node_symm_eq_node_node
    (hG : G.Cubic) (x : G.Dart) :
    G.node.symm x = G.node (G.node x) := by
  apply G.node.injective
  calc
    G.node (G.node.symm x) = x := by simp
    _ = G.node (G.node (G.node x)) := ((hG x).1).symm

theorem Cubic.node_link_cases
    (hG : G.Cubic) {x y : G.Dart}
    (hxy : PermLink G.node x y) :
    y = G.node x ∨ y = G.node (G.node x) := by
  cases hxy with
  | forward => exact Or.inl rfl
  | backward =>
      exact Or.inr
        (by simp [Cubic.node_symm_eq_node_node (G := G) hG x])

theorem Cubic.node_reachable_cases
    (hG : G.Cubic) {x y : G.Dart}
    (hxy : PermReachable G.node x y) :
    y = x ∨ y = G.node x ∨ y = G.node (G.node x) := by
  induction hxy with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
      rcases ih with rfl | hb | hb
      · rcases Cubic.node_link_cases (G := G) hG hbc with hc | hc
        · exact Or.inr (Or.inl hc)
        · exact Or.inr (Or.inr hc)
      · rcases Cubic.node_link_cases (G := G) hG hbc with hc | hc
        · exact Or.inr (Or.inr (by rw [hc, hb]))
        · exact Or.inl (by rw [hc, hb, (hG x).1])
      · rcases Cubic.node_link_cases (G := G) hG hbc with hc | hc
        · exact Or.inl (by rw [hc, hb, (hG x).1])
        · exact Or.inr (Or.inl (by rw [hc, hb, (hG x).1]))

noncomputable def Cubic.fin3EquivNodeClass
    (hG : G.Cubic) (x : G.Dart) :
    Fin 3 ≃ G.NodeClass x where
  toFun i :=
    if (i : Nat) = 0 then
      ⟨x, PermReachable.refl G.node x⟩
    else if (i : Nat) = 1 then
      ⟨G.node x, PermReachable.forward G.node x⟩
    else
      ⟨G.node (G.node x),
        PermReachable.trans G.node (PermReachable.forward G.node x)
          (PermReachable.forward G.node (G.node x))⟩
  invFun y :=
    if y.1 = x then 0 else if y.1 = G.node x then 1 else 2
  left_inv i := by
    apply Fin.ext
    have hi :
        (i : Nat) = 0 ∨ (i : Nat) = 1 ∨ (i : Nat) = 2 := by
      omega
    rcases hi with hi | hi | hi
    · simp [hi]
    · simp [hi, (hG x).2]
    · simp [hi, Cubic.node_node_ne_self (G := G) hG x, (hG x).2]
  right_inv y := by
    rcases y with ⟨y, hy⟩
    rcases Cubic.node_reachable_cases (G := G) hG hy with rfl | rfl | rfl
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      simp [(hG x).2]
    · apply Subtype.ext
      simp [Cubic.node_node_ne_self (G := G) hG x, (hG x).2]

theorem Cubic.nodeClass_card
    (hG : G.Cubic) (x : G.Dart) :
    Nat.card (G.NodeClass x) = 3 := by
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_congr
    (Cubic.fin3EquivNodeClass (G := G) hG x)).symm

theorem Cubic.card_dart_eq_three_mul_nodeOrbitCount
    (hG : G.Cubic) :
    Fintype.card G.Dart = 3 * G.nodeOrbitCount := by
  rw [← sum_permClass_card_eq_card G.node]
  change
    (∑ o : G.NodeOrbit, Nat.card (G.NodeClass (Quotient.out o))) =
      3 * G.nodeOrbitCount
  simp_rw [Cubic.nodeClass_card (G := G) hG]
  simp [Hypermap.nodeOrbitCount, Nat.card_eq_fintype_card, Nat.mul_comm]

theorem euler_eq_of_evenGenus_planar
    (heven : G.EvenGenus)
    (hplanar : G.EulerPlanar) :
    G.eulerLeft = G.eulerRight := by
  unfold Hypermap.EvenGenus at heven
  unfold Hypermap.EulerPlanar at hplanar
  rw [hplanar] at heven
  simpa using heven

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
