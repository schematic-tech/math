import Schematic.Math.GraphTheory.Embedding.DartExtension.ReachabilityTransport

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u v
namespace LeafExtension

/-- Node permutation for adding a leaf dart-pair to an existing rotation node.
`ExtDart.new` is the dart out of the new leaf and is always a singleton node.
If `pivot = none`, the opposite fresh dart is also singleton; if
`pivot = some p`, `ExtDart.newEdge` is inserted immediately after the old dart
`p` in the old node cycle. -/
def insertedLeafNode
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivot : Option α) :
    Equiv.Perm (ExtDart α) where
  toFun
    | ExtDart.new => ExtDart.new
    | ExtDart.newEdge =>
        match pivot with
        | none => ExtDart.newEdge
        | some p => ExtDart.old (σ p)
    | ExtDart.old x =>
        match pivot with
        | none => ExtDart.old (σ x)
        | some p => if x = p then ExtDart.newEdge else ExtDart.old (σ x)
  invFun
    | ExtDart.new => ExtDart.new
    | ExtDart.newEdge =>
        match pivot with
        | none => ExtDart.newEdge
        | some p => ExtDart.old p
    | ExtDart.old y =>
        match pivot with
        | none => ExtDart.old (σ.symm y)
        | some p =>
            if y = σ p then ExtDart.newEdge else ExtDart.old (σ.symm y)
  left_inv := by
    intro x
    cases pivot with
    | none =>
        cases x <;> simp
    | some p =>
        cases x with
        | new => rfl
        | newEdge => simp
        | old x =>
            by_cases hx : x = p
            · subst x
              simp
            · have hsx : σ x ≠ σ p := by
                intro h
                exact hx (σ.injective h)
              simp [hx, hsx]
  right_inv := by
    intro x
    cases pivot with
    | none =>
        cases x <;> simp
    | some p =>
        cases x with
        | new => rfl
        | newEdge => simp
        | old y =>
            by_cases hy : y = σ p
            · subst y
              simp
            · have hpre : σ.symm y ≠ p := by
                intro h
                apply hy
                calc
                  y = σ (σ.symm y) := by simp
                  _ = σ p := by rw [h]
              simp [hy, hpre]

@[simp]
theorem insertedLeafNode_new
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivot : Option α) :
    insertedLeafNode σ pivot ExtDart.new = ExtDart.new :=
  rfl

@[simp]
theorem insertedLeafNode_newEdge_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) :
    insertedLeafNode σ none ExtDart.newEdge = ExtDart.newEdge :=
  rfl

@[simp]
theorem insertedLeafNode_newEdge_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) :
    insertedLeafNode σ (some p) ExtDart.newEdge = ExtDart.old (σ p) :=
  rfl

@[simp]
theorem insertedLeafNode_old_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (x : α) :
    insertedLeafNode σ none (ExtDart.old x) = ExtDart.old (σ x) :=
  rfl

theorem insertedLeafNode_old_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p x : α) :
    insertedLeafNode σ (some p) (ExtDart.old x) =
      if x = p then ExtDart.newEdge else ExtDart.old (σ x) :=
  rfl

@[simp]
theorem insertedLeafNode_symm_newEdge_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) :
    (insertedLeafNode σ (some p)).symm ExtDart.newEdge = ExtDart.old p :=
  rfl

@[simp]
theorem insertedLeafNode_symm_old_image_some
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p : α) :
    (insertedLeafNode σ (some p)).symm (ExtDart.old (σ p)) =
      ExtDart.newEdge := by
  simp [insertedLeafNode]

theorem insertedLeafNode_symm_old_some_of_ne
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p x : α)
    (hx : x ≠ σ p) :
    (insertedLeafNode σ (some p)).symm (ExtDart.old x) =
      ExtDart.old (σ.symm x) := by
  simp [insertedLeafNode, hx]

@[simp]
theorem insertedLeafNode_symm_old_none
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (x : α) :
    (insertedLeafNode σ none).symm (ExtDart.old x) =
      ExtDart.old (σ.symm x) :=
  rfl

theorem insertedLeafNode_old_forward_reachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivot : Option α) (x : α) :
    PermReachable (insertedLeafNode σ pivot)
      (ExtDart.old x) (ExtDart.old (σ x)) := by
  cases pivot with
  | none =>
      simpa using
        (PermReachable.forward (insertedLeafNode σ none) (ExtDart.old x))
  | some p =>
      by_cases hx : x = p
      · subst x
        exact
          PermReachable.trans (insertedLeafNode σ (some p))
            (by
              simpa [insertedLeafNode_old_some] using
                (PermReachable.forward (insertedLeafNode σ (some p))
                  (ExtDart.old p)))
            (by
              simpa using
                (PermReachable.forward (insertedLeafNode σ (some p))
                  ExtDart.newEdge))
      · simpa [insertedLeafNode_old_some, hx] using
          (PermReachable.forward (insertedLeafNode σ (some p))
            (ExtDart.old x))

theorem insertedLeafNode_old_reachable_of_permReachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (pivot : Option α)
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable (insertedLeafNode σ pivot)
      (ExtDart.old x) (ExtDart.old y) :=
  hxy.lift' ExtDart.old fun x _ hlink => by
    cases hlink with
    | forward => exact insertedLeafNode_old_forward_reachable σ pivot x
    | backward =>
        exact PermReachable.symm (insertedLeafNode σ pivot) (by
          simpa using
            insertedLeafNode_old_forward_reachable σ pivot (σ.symm x))

theorem insertedLeafNode_newEdge_reachable_old_of_permReachable
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) {p x : α}
    (hpx : PermReachable σ p x) :
    PermReachable (insertedLeafNode σ (some p))
      ExtDart.newEdge (ExtDart.old x) := by
  have hnew_p :
      PermReachable (insertedLeafNode σ (some p))
        ExtDart.newEdge (ExtDart.old p) := by
    exact
      PermReachable.symm (insertedLeafNode σ (some p))
        (by
          simpa [insertedLeafNode_old_some] using
            (PermReachable.forward (insertedLeafNode σ (some p))
              (ExtDart.old p)))
  exact
    PermReachable.trans (insertedLeafNode σ (some p)) hnew_p
      (insertedLeafNode_old_reachable_of_permReachable σ (some p) hpx)


end LeafExtension

end FourColor

end Schematic.Math.GraphTheory
