import Schematic.Math.GraphTheory.Embedding.DartExtension.ReachabilityTransport

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace ExtDart.Perm

open Hypermap

variable {α : Type u} (σ : Equiv.Perm α)

/-- Classify the orbits of an extended edge permutation. -/
def edgeOrbitCode : ExtDart α → Option (PermOrbit σ)
  | ExtDart.new => none
  | ExtDart.newEdge => none
  | ExtDart.old y => some (PermOrbit.of σ y)

theorem edgeOrbitCode_of_link
    {x y : ExtDart α}
    (hxy : PermLink (edge σ) x y) :
    edgeOrbitCode σ x = edgeOrbitCode σ y := by
  cases hxy with
  | forward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old y =>
          simpa [edgeOrbitCode, edge] using (PermOrbit.of_apply σ y).symm
  | backward =>
      cases x with
      | new => rfl
      | newEdge => rfl
      | old y =>
          simpa [edgeOrbitCode, edge] using (PermOrbit.of_symm_apply σ y).symm

theorem edgeOrbitCode_of_reachable
    {x y : ExtDart α}
    (hxy : PermReachable (edge σ) x y) :
    edgeOrbitCode σ x = edgeOrbitCode σ y :=
  hxy.apply_eq (edgeOrbitCode σ) (fun {_ _} h => edgeOrbitCode_of_link σ h)

theorem old_reachable_of_link
    {x y : α}
    (hxy : PermLink σ x y) :
    PermReachable (edge σ) (ExtDart.old x) (ExtDart.old y) := by
  cases hxy with
  | forward =>
      simpa [edge] using
        (PermReachable.forward (edge σ) (ExtDart.old x))
  | backward =>
      simpa [edge] using
        (PermReachable.backward (edge σ) (ExtDart.old x))

theorem old_reachable
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable (edge σ) (ExtDart.old x) (ExtDart.old y) :=
  Relation.ReflTransGen.lift' ExtDart.old
    (fun _ _ h => old_reachable_of_link σ h) hxy

theorem old_reachable_iff
    {x y : α} :
    PermReachable (edge σ) (ExtDart.old x) (ExtDart.old y) ↔
      PermReachable σ x y := by
  constructor
  · intro hxy
    have hcode := edgeOrbitCode_of_reachable σ hxy
    have horbit : PermOrbit.of σ x = PermOrbit.of σ y := by
      exact Option.some.inj (by simpa [edgeOrbitCode] using hcode)
    exact Quotient.exact horbit
  · exact old_reachable σ

/-- Extending a permutation by a fresh transposition adds one orbit. -/
noncomputable def edgeOrbitEquiv :
    PermOrbit (edge σ) ≃ Option (PermOrbit σ) where
  toFun :=
    Quotient.lift
      (edgeOrbitCode σ)
      (fun _ _ hxy => edgeOrbitCode_of_reachable σ hxy)
  invFun
    | none => PermOrbit.of (edge σ) ExtDart.new
    | some q =>
        Quotient.lift
          (fun x => PermOrbit.of (edge σ) (ExtDart.old x))
          (fun _ _ hxy => PermOrbit.of_eq_of (edge σ) (old_reachable σ hxy))
          q
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
        cases x with
        | new => rfl
        | newEdge =>
            apply PermOrbit.of_eq_of
            simpa [edge] using
              (PermReachable.forward (edge σ) ExtDart.new)
        | old _ => rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q =>
        induction q using Quotient.inductionOn with
        | h _ => rfl

theorem edgeOrbitCard [Fintype α] :
    Nat.card (PermOrbit (edge σ)) = Nat.card (PermOrbit σ) + 1 := by
  rw [Nat.card_congr (edgeOrbitEquiv σ)]
  haveI : Finite α := Finite.of_fintype α
  haveI : Finite (PermOrbit σ) := Quotient.finite (permOrbitSetoid σ)
  exact Finite.card_option

end ExtDart.Perm

end FourColor

end Schematic.Math.GraphTheory
