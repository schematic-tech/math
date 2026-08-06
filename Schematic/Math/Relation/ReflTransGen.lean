import Mathlib.Logic.Relation

/-! Small reusable transport helpers for reflexive-transitive closures. -/

namespace Relation.ReflTransGen

variable {α : Sort u} {β : Sort v}
variable {r : α → α → Prop} {p : β → β → Prop}

/-- A function constant on one-step links is constant on their
reflexive-transitive closure. -/
theorem apply_eq
    {a b : α}
    (hab : Relation.ReflTransGen r a b)
    (f : α → β)
    (hstep : ∀ ⦃a b⦄, r a b → f a = f b) :
    f a = f b := by
  induction hab with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hstep hbc)

/-- Compatibility name for mapping a reflexive-transitive closure when one
source step may become several target steps. -/
theorem liftClosure
    (f : α → β)
    (hstep : ∀ a b, r a b → Relation.ReflTransGen p (f a) (f b))
    {a b : α}
    (hab : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen p (f a) (f b) :=
  hab.lift' f hstep

/-- Reverse a closure when every forward step can be traversed backwards by a
possibly multi-step path.  This weakens the one-step symmetry assumption of
`symmetric` to the form used by generated reachability relations. -/
theorem symm_of_step
    (hstep : ∀ ⦃a b⦄, r a b → Relation.ReflTransGen r b a)
    {a b : α} (hab : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen r b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (hstep hbc).trans ih

/-- Lift a closure to a subtype when the predicate is propagated along source
closures and source steps lift between any chosen subtype witnesses.  This is
the dependent counterpart of `liftClosure`: it centralizes the otherwise
repeated induction needed for invariant-defined subobjects. -/
theorem liftSubtype
    {P : α → Prop}
    {s : Subtype P → Subtype P → Prop}
    (hclosed : ∀ ⦃a b⦄, Relation.ReflTransGen r a b → P a → P b)
    (hstep : ∀ ⦃a b⦄ (ha : P a) (hb : P b),
      r a b → s ⟨a, ha⟩ ⟨b, hb⟩)
    (x : Subtype P) {y : α} (hy : P y)
    (hxy : Relation.ReflTransGen r x.1 y) :
    Relation.ReflTransGen s x ⟨y, hy⟩ := by
  revert hy
  induction hxy with
  | refl =>
      intro hy
      have h : (⟨x.1, hy⟩ : Subtype P) = x := Subtype.ext rfl
      rw [h]
  | @tail b c hxb hbc ih =>
      intro hc
      have hb : P b := hclosed hxb x.2
      exact Relation.ReflTransGen.trans (ih hb)
        (Relation.ReflTransGen.single (hstep hb hc hbc))

end Relation.ReflTransGen
