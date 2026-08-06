import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.PredicateSkipping

/-!
Predicate restriction of finite hypermaps and preservation of Euler planarity.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Hypermap

/-- Coq `sub_genus` target: keep a predicate of darts, preserving the cyclic
order of both the edge and node permutations and deriving the face
permutation from the hypermap cancellation law. -/
noncomputable def predicateRestriction
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep] :
    Hypermap.{u} where
  Dart := {x : G.Dart // keep x}
  edge := PermSkipPredicate.skip G.edge
  node := PermSkipPredicate.skip G.node
  face :=
    (PermSkipPredicate.skip G.edge).symm.trans
      (PermSkipPredicate.skip G.node).symm
  node_face_edge := by
    intro x
    simp

@[simp]
theorem predicateRestriction_edge_val
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep]
    (x : (G.predicateRestriction keep).Dart) :
    ((G.predicateRestriction keep).edge x).1 =
      ((G.edge : G.Dart → G.Dart)^[
        (PermSkipPredicate.firstReturnIndex G.edge x) + 1]) x.1 :=
  PermSkipPredicate.skip_apply_val G.edge x

@[simp]
theorem predicateRestriction_node_val
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep]
    (x : (G.predicateRestriction keep).Dart) :
    ((G.predicateRestriction keep).node x).1 =
      ((G.node : G.Dart → G.Dart)^[
        (PermSkipPredicate.firstReturnIndex G.node x) + 1]) x.1 :=
  PermSkipPredicate.skip_apply_val G.node x

/-- Flatten a surviving dart through one preliminary `WalkupF` deletion. -/
def predicateRestrictionWalkupFEquiv
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep]
    (z : G.Dart) (hz : ¬ keep z) :
    (G.predicateRestriction keep).Dart ≃
      ((G.walkupF z).predicateRestriction
        (fun w : (G.walkupF z).Dart => keep w.1)).Dart where
  toFun x :=
    ⟨⟨x.1, fun hxz => hz (hxz ▸ x.2)⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Hypermap form of Coq `skip_skip1`: predicate restriction factors through
one rejected-dart `WalkupF`. -/
noncomputable def predicateRestrictionWalkupFIso
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep]
    (z : G.Dart) (hz : ¬ keep z) :
    Hypermap.Iso (G.predicateRestriction keep)
      ((G.walkupF z).predicateRestriction
        (fun w : (G.walkupF z).Dart => keep w.1)) :=
  Hypermap.Iso.ofEdgeNode
    (predicateRestrictionWalkupFEquiv G keep z hz)
    (by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact
        PermSkipPredicate.skip_skipPoint_val G.edge z hz x)
    (by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact
        PermSkipPredicate.skip_skipPoint_val G.node z hz x)

/-- If every dart survives, predicate restriction is isomorphic to the
original hypermap. -/
noncomputable def predicateRestrictionIsoOfAll
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep]
    (hall : ∀ x, keep x) :
    Hypermap.Iso (G.predicateRestriction keep) G :=
  Hypermap.Iso.ofEdgeNode
    { toFun := fun x => x.1
      invFun := fun x => ⟨x, hall x⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; rfl }
    (by
      intro x
      exact
        PermSkipPredicate.skip_apply_of_next_mem G.edge x
          (hall (G.edge x.1)))
    (by
      intro x
      exact
        PermSkipPredicate.skip_apply_of_next_mem G.node x
          (hall (G.node x.1)))

/-- Coq `sub_planar`: preserving the cyclic order of edge and node while
discarding darts preserves Euler-planarity. -/
theorem predicateRestriction_eulerPlanar
    (G : Hypermap.{u}) (keep : G.Dart → Prop) [DecidablePred keep]
    (hG : G.EulerPlanar) :
    (G.predicateRestriction keep).EulerPlanar := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ H : Hypermap.{u},
      Fintype.card H.Dart = n →
        ∀ q : H.Dart → Prop, ∀ _ : DecidablePred q,
          H.EulerPlanar → (H.predicateRestriction q).EulerPlanar
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro H hcard q dq hplanar
        letI : DecidablePred q := dq
        by_cases hall : ∀ x, q x
        · let φ : Hypermap.Iso (H.predicateRestriction q) H :=
            predicateRestrictionIsoOfAll H q hall
          exact (φ.eulerPlanar_iff).mpr hplanar
        · push Not at hall
          obtain ⟨z, hz⟩ := hall
          let H' := H.walkupF z
          let q' : H'.Dart → Prop := fun w => q w.1
          let dq' : DecidablePred q' := fun w => dq w.1
          letI : DecidablePred q' := dq'
          have hcardPos : 0 < Fintype.card H.Dart :=
            Fintype.card_pos_iff.mpr ⟨z⟩
          have hcard' :
              Fintype.card H'.Dart < n := by
            rw [← hcard]
            change Fintype.card (H.walkupF z).Dart <
              Fintype.card H.Dart
            rw [H.walkupF_dart_card z]
            omega
          have hplanar' : H'.EulerPlanar :=
            Unavoidability.walkupF_eulerPlanar_of_eulerPlanar H z hplanar
          have hrestricted' :
              (H'.predicateRestriction q').EulerPlanar :=
            ih (Fintype.card H'.Dart) hcard' H' rfl q' dq' hplanar'
          let φ : Hypermap.Iso (H.predicateRestriction q)
              (H'.predicateRestriction q') :=
            predicateRestrictionWalkupFIso H q z hz
          exact (φ.eulerPlanar_iff).mpr hrestricted'
  exact hP (Fintype.card G.Dart) G rfl keep inferInstance hG

end Hypermap

end FourColor

end Schematic.Math.GraphTheory

