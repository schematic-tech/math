import Schematic.Math.GraphTheory.Embedding.WalkupGeometry.Counting

/-!
Generic transport of relational paths through a deleted-point subtype.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor

universe u

/-- Lift a relational path pointwise through a one-point deletion. The
predicate `P` carries any transform-specific condition needed for each
noninitial path element. -/
theorem liftRelPathThroughDeletedPoint
    {α : Type u} {z x : α} {p : List α}
    {R : α → α → Prop}
    {S : DeletedPoint z → DeletedPoint z → Prop}
    (P : α → Prop)
    (hx : x ≠ z)
    (havoid : z ∉ p)
    (hgood : ∀ y ∈ p, P y)
    (hlift : ∀ {a b : α} (ha : a ≠ z) (hb : b ≠ z),
      P b → R a b → S ⟨a, ha⟩ ⟨b, hb⟩)
    (hp : List.RelPath R x p) :
    ∃ q : List (DeletedPoint z),
      q.map Subtype.val = p ∧ List.RelPath S ⟨x, hx⟩ q := by
  induction p generalizing x with
  | nil =>
      exact ⟨[], rfl, trivial⟩
  | cons y p ih =>
      have hy : y ≠ z := by
        intro hyz
        exact havoid (by simp [hyz])
      have havoidTail : z ∉ p := by
        intro hz
        exact havoid (by simp [hz])
      have hgoodY : P y := hgood y (by simp)
      have hgoodTail : ∀ a ∈ p, P a := by
        intro a ha
        exact hgood a (by simp [ha])
      rcases hp with ⟨hxy, hyp⟩
      rcases ih hy havoidTail hgoodTail hyp with
        ⟨q, hqmap, hqpath⟩
      refine ⟨⟨y, hy⟩ :: q, ?_, ?_⟩
      · change y :: q.map Subtype.val = y :: p
        rw [hqmap]
      · exact ⟨hlift hx hy hgoodY hxy, hqpath⟩

end FourColor
end Schematic.Math.GraphTheory
