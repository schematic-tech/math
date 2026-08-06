import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.PredicateSkipping

/-!
Restriction of a permutation with at most one forbidden point in each label fibre.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace PermSkipFiber

variable {α : Type u} {β : Type v}
variable [DecidableEq α]
variable {keep : α → Prop} [DecidablePred keep]

/-- Apply `σ`, skipping one non-surviving point when necessary. -/
def skipAux (σ : Equiv.Perm α) (x : α) : α :=
  if keep (σ x) then σ x else σ (σ x)

omit [DecidableEq α] in
theorem skipAux_mem
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (hunique :
      ∀ {x y : α}, label x = label y →
        ¬ keep x → ¬ keep y → x = y)
    {x : α} (hx : keep x) :
    keep (skipAux (keep := keep) σ x) := by
  unfold skipAux
  split_ifs with hnext
  · exact hnext
  · by_contra hnext₂
    have heq : σ x = σ (σ x) :=
      hunique (hlabel (σ x)).symm hnext hnext₂
    have hxEq : x = σ x :=
      σ.injective heq
    exact hnext (hxEq ▸ hx)

omit [DecidableEq α] in
theorem skipAux_label
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (x : α) :
    label (skipAux (keep := keep) σ x) = label x := by
  unfold skipAux
  split_ifs
  · exact hlabel x
  · exact (hlabel (σ x)).trans (hlabel x)

omit [DecidableEq α] in
theorem label_symm
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (x : α) :
    label (σ.symm x) = label x := by
  have h := hlabel (σ.symm x)
  simpa using h.symm

omit [DecidableEq α] in
theorem skipAux_symm_skipAux
    (σ : Equiv.Perm α)
    {x : α} (hx : keep x) :
    skipAux (keep := keep) σ.symm
        (skipAux (keep := keep) σ x) = x := by
  by_cases hnext : keep (σ x)
  · simp [skipAux, hnext, hx]
  · simp [skipAux, hnext]

/-- Restrict a permutation by skipping the unique forbidden point in each
label fibre. -/
def skip
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (hunique :
      ∀ {x y : α}, label x = label y →
        ¬ keep x → ¬ keep y → x = y) :
    Equiv.Perm {x : α // keep x} where
  toFun x :=
    ⟨skipAux (keep := keep) σ x,
      skipAux_mem σ label hlabel hunique x.2⟩
  invFun x :=
    ⟨skipAux (keep := keep) σ.symm x,
      skipAux_mem σ.symm label
        (label_symm σ label hlabel) hunique x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact skipAux_symm_skipAux σ x.2
  right_inv x := by
    apply Subtype.ext
    exact skipAux_symm_skipAux σ.symm x.2

omit [DecidableEq α] in
@[simp]
theorem skip_apply_val
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (hunique :
      ∀ {x y : α}, label x = label y →
        ¬ keep x → ¬ keep y → x = y)
    (x : {x : α // keep x}) :
    ((skip σ label hlabel hunique x : {x : α // keep x}) : α) =
      skipAux (keep := keep) σ x :=
  rfl

omit [DecidableEq α] in
theorem skip_preserves
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (hunique :
      ∀ {x y : α}, label x = label y →
        ¬ keep x → ¬ keep y → x = y)
    (x : {x : α // keep x}) :
    label (skip σ label hlabel hunique x) = label x :=
  skipAux_label σ label hlabel x

omit [DecidableEq α] in
theorem skip_permReachable_of_iterate_eq
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (hunique :
      ∀ {x y : α}, label x = label y →
        ¬ keep x → ¬ keep y → x = y)
    {x y : α} (hx : keep x) (hy : keep y) :
    ∀ n : Nat, (σ : α → α)^[n] x = y →
      PermReachable (skip σ label hlabel hunique)
        (⟨x, hx⟩ : {x : α // keep x})
        (⟨y, hy⟩ : {x : α // keep x})
  | 0, hxy => by
      have hsub :
          (⟨x, hx⟩ : {x : α // keep x}) =
            (⟨y, hy⟩ : {x : α // keep x}) :=
        Subtype.ext hxy
      rw [hsub]
      exact PermReachable.refl (skip σ label hlabel hunique) ⟨y, hy⟩
  | n + 1, hxy => by
      rw [Function.iterate_succ_apply] at hxy
      by_cases hstep : keep (σ x)
      · have hfirst :
            skip σ label hlabel hunique
                (⟨x, hx⟩ : {x : α // keep x}) =
              (⟨σ x, hstep⟩ : {x : α // keep x}) := by
          apply Subtype.ext
          simp [skip, skipAux, hstep]
        exact
          PermReachable.trans (skip σ label hlabel hunique)
            (by
              simpa [hfirst] using
                PermReachable.forward (skip σ label hlabel hunique)
                  (⟨x, hx⟩ : {x : α // keep x}))
            (skip_permReachable_of_iterate_eq σ label hlabel hunique
              hstep hy n hxy)
      · cases n with
        | zero =>
            have hxy' : σ x = y := by
              simpa using hxy
            exact False.elim (hstep (hxy'.symm ▸ hy))
        | succ m =>
            have hnext :
                keep (σ (σ x)) :=
              by
                simpa [skipAux, hstep] using
                  (skipAux_mem σ label hlabel hunique hx)
            have htail :
                (σ : α → α)^[m] (σ (σ x)) = y := by
              rw [Function.iterate_succ_apply] at hxy
              exact hxy
            have hfirst :
                skip σ label hlabel hunique
                    (⟨x, hx⟩ : {x : α // keep x}) =
                  (⟨σ (σ x), hnext⟩ : {x : α // keep x}) := by
              apply Subtype.ext
              simp [skip, skipAux, hstep]
            exact
              PermReachable.trans (skip σ label hlabel hunique)
                (by
                  simpa [hfirst] using
                    PermReachable.forward (skip σ label hlabel hunique)
                      (⟨x, hx⟩ : {x : α // keep x}))
                (skip_permReachable_of_iterate_eq σ label hlabel hunique
                  hnext hy m htail)

omit [DecidableEq α] in
theorem skip_permReachable_of_permReachable
    [Fintype α]
    (σ : Equiv.Perm α) (label : α → β)
    (hlabel : ∀ x, label (σ x) = label x)
    (hunique :
      ∀ {x y : α}, label x = label y →
        ¬ keep x → ¬ keep y → x = y)
    {x y : {x : α // keep x}}
    (hxy : PermReachable σ x y) :
    PermReachable (skip σ label hlabel hunique) x y := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
  exact
    skip_permReachable_of_iterate_eq σ label hlabel hunique
      x.2 y.2 n hn

omit [DecidableEq α] in
theorem subtypePerm_iterate_val
    {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm α)
    (hσ : ∀ x, p (σ x) ↔ p x)
    (x : {x : α // p x}) :
    ∀ n : Nat,
      (((σ.subtypePerm hσ : {x : α // p x} → {x : α // p x})^[n]) x).1 =
        ((σ : α → α)^[n]) x.1
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Equiv.Perm.subtypePerm_apply]
      simpa using
        subtypePerm_iterate_val σ hσ ((σ.subtypePerm hσ) x) n

omit [DecidableEq α] in
theorem subtypePerm_permReachable_of_permReachable
    [Fintype α]
    {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm α)
    (hσ : ∀ x, p (σ x) ↔ p x)
    {x y : {x : α // p x}}
    (hxy : PermReachable σ x y) :
    PermReachable (σ.subtypePerm hσ) x y := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
  apply permReachable_of_iterate_eq
  apply Subtype.ext
  rw [subtypePerm_iterate_val]
  exact hn

end PermSkipFiber

end FourColor

end Schematic.Math.GraphTheory

