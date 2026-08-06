import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.InsertedNodePermutation
import Schematic.Math.GraphTheory.Embedding.KuratowskiLeaf.OrbitCode

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u v
namespace LeafExtension

def insertedLeafNodeSomeOrbitCode
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) :
    ExtDart α -> Option (PermOrbit σ) :=
  ExtDart.code none (some (PermOrbit.of σ p))
    (fun x => some (PermOrbit.of σ x))

theorem insertedLeafNodeSomeOrbitCode_of_link
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α)
    {x y : ExtDart α}
    (hxy : PermLink (insertedLeafNode σ (some p)) x y) :
    insertedLeafNodeSomeOrbitCode σ p x =
      insertedLeafNodeSomeOrbitCode σ p y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge =>
          simp [insertedLeafNodeSomeOrbitCode]
          exact (PermOrbit.of_apply σ p).symm
      | old x =>
          by_cases hx : x = p
          · subst x
            simp [insertedLeafNodeSomeOrbitCode, insertedLeafNode_old_some]
          · simp [insertedLeafNodeSomeOrbitCode, insertedLeafNode_old_some, hx]
            exact (PermOrbit.of_apply σ x).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge =>
          change some (PermOrbit.of σ p) =
            insertedLeafNodeSomeOrbitCode σ p (ExtDart.old p)
          rfl
      | old x =>
          by_cases hx : x = σ p
          · subst x
            simp [insertedLeafNodeSomeOrbitCode]
            exact PermOrbit.of_apply σ p
          · have hpre : σ.symm x ≠ p := by
              intro h
              apply hx
              calc
                x = σ (σ.symm x) := by simp
                _ = σ p := by rw [h]
            simp [insertedLeafNodeSomeOrbitCode,
              insertedLeafNode_symm_old_some_of_ne σ p x hx]
            exact (PermOrbit.of_symm_apply σ x).symm

theorem insertedLeafNodeSomeOrbitCode_of_reachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α)
    {x y : ExtDart α}
    (hxy : PermReachable (insertedLeafNode σ (some p)) x y) :
    insertedLeafNodeSomeOrbitCode σ p x =
      insertedLeafNodeSomeOrbitCode σ p y :=
  code_eq_of_reflTransGen (insertedLeafNodeSomeOrbitCode σ p)
    (insertedLeafNodeSomeOrbitCode_of_link σ p) hxy

noncomputable def insertedLeafNodeSomeOrbitEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) :
    PermOrbit (insertedLeafNode σ (some p)) ≃ Option (PermOrbit σ) where
  toFun :=
    Quotient.lift
      (insertedLeafNodeSomeOrbitCode σ p)
      (by
        intro x y hxy
        exact insertedLeafNodeSomeOrbitCode_of_reachable σ p hxy)
  invFun
    | none => PermOrbit.of (insertedLeafNode σ (some p)) ExtDart.new
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (insertedLeafNode σ (some p)) (ExtDart.old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (insertedLeafNode σ (some p))
              (insertedLeafNode_old_reachable_of_permReachable σ (some p) hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge =>
            apply PermOrbit.of_eq_of
            simpa [insertedLeafNode_old_some] using
              (PermReachable.forward (insertedLeafNode σ (some p))
                (ExtDart.old p))
        | old x => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h x => rfl

def insertedLeafNodeNoneOrbitCode
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) :
    ExtDart α -> Option (Option (PermOrbit σ)) :=
  ExtDart.code none (some none)
    (fun x => some (some (PermOrbit.of σ x)))

theorem insertedLeafNodeNoneOrbitCode_of_link
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α)
    {x y : ExtDart α}
    (hxy : PermLink (insertedLeafNode σ none) x y) :
    insertedLeafNodeNoneOrbitCode σ x =
      insertedLeafNodeNoneOrbitCode σ y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          simp [insertedLeafNodeNoneOrbitCode]
          exact (PermOrbit.of_apply σ x).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old x =>
          simp [insertedLeafNodeNoneOrbitCode]
          exact (PermOrbit.of_symm_apply σ x).symm

theorem insertedLeafNodeNoneOrbitCode_of_reachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α)
    {x y : ExtDart α}
    (hxy : PermReachable (insertedLeafNode σ none) x y) :
    insertedLeafNodeNoneOrbitCode σ x =
      insertedLeafNodeNoneOrbitCode σ y :=
  code_eq_of_reflTransGen (insertedLeafNodeNoneOrbitCode σ)
    (insertedLeafNodeNoneOrbitCode_of_link σ) hxy

noncomputable def insertedLeafNodeNoneOrbitEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    PermOrbit (insertedLeafNode σ none) ≃ Option (Option (PermOrbit σ)) where
  toFun :=
    Quotient.lift
      (insertedLeafNodeNoneOrbitCode σ)
      (by
        intro x y hxy
        exact insertedLeafNodeNoneOrbitCode_of_reachable σ hxy)
  invFun
    | none => PermOrbit.of (insertedLeafNode σ none) ExtDart.new
    | some none => PermOrbit.of (insertedLeafNode σ none) ExtDart.newEdge
    | some (some q) =>
        Quotient.lift
          (fun x => PermOrbit.of (insertedLeafNode σ none) (ExtDart.old x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (insertedLeafNode σ none)
              (insertedLeafNode_old_reachable_of_permReachable σ none hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge => rfl
        | old x => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        cases q with
        | none => rfl
        | some q =>
            induction q using Quotient.inductionOn with
            | h x => rfl


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
