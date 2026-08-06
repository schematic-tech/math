import Schematic.Math.GraphTheory.Embedding.Hypermap

/-!
Walkup point-deletion primitives.

Coq `walkup.v` begins by deleting one dart from the domain of a permutation and
splicing the surrounding cycle back together.  This file ports that reusable
permutation-level construction before the three hypermap-specific Walkup
transforms are introduced.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

/-- The type obtained by deleting one point from a finite permutation domain. -/
abbrev DeletedPoint {α : Type u} (z : α) :=
  {x : α // x ≠ z}

namespace DeletedPoint

variable {α : Type u} [Fintype α] [DecidableEq α]

theorem card (z : α) :
    Fintype.card (DeletedPoint z) = Fintype.card α - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun x : α => x = z)]
  simp

theorem card_add_one (z : α) :
    Fintype.card (DeletedPoint z) + 1 = Fintype.card α := by
  rw [card]
  exact Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨z⟩))

theorem card_lt (z : α) :
    Fintype.card (DeletedPoint z) < Fintype.card α := by
  rw [← card_add_one z]
  exact Nat.lt_succ_self _

/-- Reinsert into the deleted domain by using `u` as the value at the deleted
point.  This is the Lean analogue of Coq's `insubd` use in `WalkupI`. -/
def lift {z : α} (u : DeletedPoint z) (x : α) : DeletedPoint z :=
  if h : x = z then u else ⟨x, h⟩

omit [Fintype α] in
@[simp]
theorem lift_coe {z : α} (u : DeletedPoint z) (x : α) :
    ((lift u x : DeletedPoint z) : α) = if x = z then u.1 else x := by
  unfold lift
  by_cases h : x = z
  · simp [h]
  · simp [h]

omit [Fintype α] in
theorem lift_coe_of_ne {z x : α} (u : DeletedPoint z) (hx : x ≠ z) :
    ((lift u x : DeletedPoint z) : α) = x := by
  rw [lift_coe]
  simp [hx]

omit [Fintype α] [DecidableEq α] in
theorem exists_list_coe_eq
    {z : α} :
    ∀ p : List α, z ∉ p → ∃ q : List (DeletedPoint z), q.map Subtype.val = p
  | [], _ => ⟨[], rfl⟩
  | x :: p, hp => by
      have hx : x ≠ z := by
        intro hxz
        apply hp
        simp [hxz.symm]
      have hp_tail : z ∉ p := by
        intro hzp
        apply hp
        simp [hzp]
      rcases exists_list_coe_eq p hp_tail with ⟨q, hq⟩
      exact ⟨⟨x, hx⟩ :: q, by simp [hq]⟩

end DeletedPoint

namespace PermSkip

variable {α : Type u} [DecidableEq α]

/-- Coq `skip1`: apply `σ`, but if this lands on the deleted point `z`, jump to
the next point of the same cycle. -/
def skipAux (σ : Equiv.Perm α) (z x : α) : α :=
  if σ x = z then σ z else σ x

theorem skipAux_ne_deleted
    (σ : Equiv.Perm α) {z : α} (x : DeletedPoint z) :
    skipAux σ z x.1 ≠ z := by
  unfold skipAux
  split_ifs with hx
  · intro hz
    have hsame : σ z = σ x.1 := by
      rw [hz, hx]
    exact x.2 ((σ.injective hsame).symm)
  · exact hx

theorem skipAux_symm_skipAux
    (σ : Equiv.Perm α) {z x : α} (hx : x ≠ z) :
    skipAux σ.symm z (skipAux σ z x) = x := by
  by_cases hσx : σ x = z
  · have hpre : σ.symm z = x := by
      rw [← hσx]
      simp
    simp [skipAux, hσx, hpre]
  · simp [skipAux, hσx, hx]

theorem skipAux_skipAux_symm
    (σ : Equiv.Perm α) {z x : α} (hx : x ≠ z) :
    skipAux σ z (skipAux σ.symm z x) = x := by
  simpa using
    (skipAux_symm_skipAux (σ := σ.symm) (z := z) (x := x) hx)

/-- Coq `skip`: the deleted-domain permutation induced by `skipAux`. -/
def skip (σ : Equiv.Perm α) (z : α) : Equiv.Perm (DeletedPoint z) where
  toFun x := ⟨skipAux σ z x.1, skipAux_ne_deleted σ x⟩
  invFun x := ⟨skipAux σ.symm z x.1, skipAux_ne_deleted σ.symm x⟩
  left_inv x := by
    apply Subtype.ext
    exact skipAux_symm_skipAux σ x.2
  right_inv x := by
    apply Subtype.ext
    exact skipAux_skipAux_symm σ x.2

@[simp]
theorem skip_apply_val
    (σ : Equiv.Perm α) (z : α) (x : DeletedPoint z) :
    ((skip σ z x : DeletedPoint z) : α) = skipAux σ z x.1 :=
  rfl

theorem skip_apply_of_apply_ne
    (σ : Equiv.Perm α) {z : α} (x : DeletedPoint z)
    (hx : σ x.1 ≠ z) :
    ((skip σ z x : DeletedPoint z) : α) = σ x.1 := by
  simp [skip, skipAux, hx]

theorem skip_apply_of_apply_eq
    (σ : Equiv.Perm α) {z : α} (x : DeletedPoint z)
    (hx : σ x.1 = z) :
    ((skip σ z x : DeletedPoint z) : α) = σ z := by
  simp [skip, skipAux, hx]

theorem skip_apply_of_fixed
    (σ : Equiv.Perm α) {z : α} (hz : σ z = z)
    (x : DeletedPoint z) :
    ((skip σ z x : DeletedPoint z) : α) = σ x.1 := by
  have hx : σ x.1 ≠ z := by
    intro hbad
    have hsame : σ x.1 = σ z := by rw [hbad, hz]
    exact x.2 (σ.injective hsame)
  exact skip_apply_of_apply_ne σ x hx

theorem skip_involutive_of_fixed
    (σ : Equiv.Perm α) {z : α} (hz : σ z = z)
    (hσ₂ : ∀ x : α, σ (σ x) = x)
    (x : DeletedPoint z) :
    skip σ z (skip σ z x) = x := by
  apply Subtype.ext
  rw [skip_apply_of_fixed σ hz]
  rw [skip_apply_of_fixed σ hz]
  exact hσ₂ x.1

theorem skipAux_permReachable
    (σ : Equiv.Perm α) {z : α} (x : DeletedPoint z) :
    PermReachable σ x.1 (skipAux σ z x.1) := by
  unfold skipAux
  by_cases hx : σ x.1 = z
  · simp [hx]
    exact PermReachable.trans σ (PermReachable.forward σ x.1)
      (by simpa [hx] using PermReachable.forward σ (σ x.1))
  · simpa [hx] using PermReachable.forward σ x.1

theorem skip_permReachable
    (σ : Equiv.Perm α) {z : α} (x : DeletedPoint z) :
    PermReachable σ x.1 ((skip σ z x : DeletedPoint z) : α) := by
  rw [skip_apply_val]
  exact skipAux_permReachable σ x

theorem skip_symm_permReachable
    (σ : Equiv.Perm α) {z : α} (x : DeletedPoint z) :
    PermReachable σ x.1 (((skip σ z).symm x : DeletedPoint z) : α) := by
  have hsymm :
      PermReachable σ.symm x.1
        (((skip σ z).symm x : DeletedPoint z) : α) := by
    change PermReachable σ.symm x.1 (skipAux σ.symm z x.1)
    exact skipAux_permReachable σ.symm x
  exact (permReachable_symmPerm_iff σ).mp hsymm

theorem skip_link_permReachable
    (σ : Equiv.Perm α) {z : α} {x y : DeletedPoint z}
    (hxy : PermLink (skip σ z) x y) :
    PermReachable σ x.1 y.1 := by
  cases hxy with
  | forward =>
      exact skip_permReachable σ x
  | backward =>
      exact skip_symm_permReachable σ x

theorem skip_permReachable_project
    (σ : Equiv.Perm α) {z : α} {x y : DeletedPoint z}
    (hxy : PermReachable (skip σ z) x y) :
    PermReachable σ x.1 y.1 :=
  PermReachable.map_of_forward_simulation (skip σ z) σ Subtype.val
    (skip_permReachable σ) hxy

theorem skip_permReachable_of_iterate_eq
    (σ : Equiv.Perm α) {z x y : α}
    (hx : x ≠ z) (hy : y ≠ z) :
    ∀ n : Nat, (σ : α → α)^[n] x = y →
      PermReachable (skip σ z)
        (⟨x, hx⟩ : DeletedPoint z) (⟨y, hy⟩ : DeletedPoint z)
  | 0, hxy => by
      have hsub :
          (⟨x, hx⟩ : DeletedPoint z) = (⟨y, hy⟩ : DeletedPoint z) :=
        Subtype.ext hxy
      rw [hsub]
      exact PermReachable.refl (skip σ z) ⟨y, hy⟩
  | n + 1, hxy => by
      rw [Function.iterate_succ_apply] at hxy
      by_cases hstep : σ x = z
      · cases n with
        | zero =>
            exact False.elim (hy (by simpa [hstep] using hxy.symm))
        | succ m =>
            have hσz : σ z ≠ z := by
              intro hfix
              have hsame : σ x = σ z := by rw [hstep, hfix]
              exact hx (σ.injective hsame)
            have hnext :
                (σ : α → α)^[m] (σ z) = y := by
              rw [Function.iterate_succ_apply] at hxy
              simpa [hstep] using hxy
            have hfirst :
                skip σ z (⟨x, hx⟩ : DeletedPoint z) =
                  (⟨σ z, hσz⟩ : DeletedPoint z) := by
              apply Subtype.ext
              simp [skip, skipAux, hstep]
            exact PermReachable.trans (skip σ z)
              (by simpa [hfirst] using
                PermReachable.forward (skip σ z) ⟨x, hx⟩)
              (skip_permReachable_of_iterate_eq σ hσz hy m hnext)
      · have hfirst :
            skip σ z (⟨x, hx⟩ : DeletedPoint z) =
              (⟨σ x, hstep⟩ : DeletedPoint z) := by
          apply Subtype.ext
          simp [skip, skipAux, hstep]
        exact PermReachable.trans (skip σ z)
          (by simpa [hfirst] using
            PermReachable.forward (skip σ z) ⟨x, hx⟩)
          (skip_permReachable_of_iterate_eq σ hstep hy n hxy)

theorem skip_permReachable_of_permReachable
    (σ : Equiv.Perm α) [Fintype α] {z : α} {x y : DeletedPoint z}
    (hxy : PermReachable σ x.1 y.1) :
    PermReachable (skip σ z) x y := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
  simpa using skip_permReachable_of_iterate_eq σ x.2 y.2 n hn

theorem skip_permReachable_iff
    (σ : Equiv.Perm α) [Fintype α] {z : α} {x y : DeletedPoint z} :
    PermReachable (skip σ z) x y ↔ PermReachable σ x.1 y.1 := by
  constructor
  · exact skip_permReachable_project σ
  · exact skip_permReachable_of_permReachable σ

/-- Choose a representative away from `z`; if asked for `z`, use its
successor under `σ`.  This is only useful when `z` is not fixed by `σ`. -/
def deletedRepresentative
    (σ : Equiv.Perm α) {z : α} (hz : σ z ≠ z) (x : α) :
    DeletedPoint z :=
  if h : x = z then ⟨σ z, hz⟩ else ⟨x, h⟩

theorem deletedRepresentative_coe_of_ne
    (σ : Equiv.Perm α) {z x : α} (hz : σ z ≠ z) (hx : x ≠ z) :
    ((deletedRepresentative σ hz x : DeletedPoint z) : α) = x := by
  simp [deletedRepresentative, hx]

theorem deletedRepresentative_reachable_self
    (σ : Equiv.Perm α) {z : α} (hz : σ z ≠ z) (x : α) :
    PermReachable σ (deletedRepresentative σ hz x).1 x := by
  unfold deletedRepresentative
  by_cases hx : x = z
  · subst x
    simp
    exact PermReachable.symm σ (PermReachable.forward σ z)
  · simpa [hx] using PermReachable.refl σ x

noncomputable def orbitOfSkip
    (σ : Equiv.Perm α) {z : α} :
    PermOrbit (skip σ z) → PermOrbit σ :=
  Quotient.lift
    (fun x : DeletedPoint z => PermOrbit.of σ x.1)
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of σ (skip_permReachable_project σ hxy))

noncomputable def orbitToSkipOfNotFixed
    (σ : Equiv.Perm α) [Fintype α] {z : α} (hz : σ z ≠ z) :
    PermOrbit σ → PermOrbit (skip σ z) :=
  Quotient.lift
    (fun x : α => PermOrbit.of (skip σ z) (deletedRepresentative σ hz x))
    (by
      intro x y hxy
      have hx : PermReachable σ (deletedRepresentative σ hz x).1 x :=
        deletedRepresentative_reachable_self σ hz x
      have hy : PermReachable σ (deletedRepresentative σ hz y).1 y :=
        deletedRepresentative_reachable_self σ hz y
      have hxy' :
          PermReachable σ (deletedRepresentative σ hz x).1
            (deletedRepresentative σ hz y).1 :=
        PermReachable.trans σ hx
          (PermReachable.trans σ hxy (PermReachable.symm σ hy))
      exact PermOrbit.of_eq_of (skip σ z)
        (skip_permReachable_of_permReachable σ hxy'))

/-- If `z` is not a singleton `σ`-cycle, deleting it preserves cyclic orbit
quotients.  This is the quotient-level form of the non-fixed branch of Coq's
`fcard_skip`. -/
noncomputable def orbitEquivOfNotFixed
    (σ : Equiv.Perm α) [Fintype α] {z : α} (hz : σ z ≠ z) :
    PermOrbit (skip σ z) ≃ PermOrbit σ where
  toFun := orbitOfSkip σ
  invFun := orbitToSkipOfNotFixed σ hz
  left_inv q := by
    refine Quot.inductionOn q ?_
    intro x
    apply PermOrbit.of_eq_of
    have hx :
        (deletedRepresentative σ hz x.1 : DeletedPoint z) = x := by
      apply Subtype.ext
      exact deletedRepresentative_coe_of_ne σ hz x.2
    rw [hx]
    exact PermReachable.refl (skip σ z) x
  right_inv q := by
    refine Quot.inductionOn q ?_
    intro x
    exact PermOrbit.of_eq_of σ (deletedRepresentative_reachable_self σ hz x)

theorem orbitCount_skip_of_not_fixed
    (σ : Equiv.Perm α) [Fintype α] {z : α} (hz : σ z ≠ z) :
    Nat.card (PermOrbit (skip σ z)) = Nat.card (PermOrbit σ) :=
  Nat.card_congr (orbitEquivOfNotFixed σ hz)

omit [DecidableEq α] in
theorem iterate_fixed
    (σ : Equiv.Perm α) {z : α} (hz : σ z = z) :
    ∀ n : Nat, (σ : α → α)^[n] z = z
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, hz, iterate_fixed σ hz n]

omit [DecidableEq α] in
theorem eq_of_permReachable_fixed
    (σ : Equiv.Perm α) [Fintype α] {z x : α}
    (hz : σ z = z) (hxz : PermReachable σ x z) :
    x = z := by
  rcases permReachable_exists_iterate σ hxz with ⟨n, hn⟩
  have hz_iter : (σ : α → α)^[n] z = z := iterate_fixed σ hz n
  exact Function.Injective.iterate σ.injective n (by simp [hn, hz_iter])

omit [DecidableEq α] in
theorem not_permReachable_fixed_of_ne
    (σ : Equiv.Perm α) [Fintype α] {z x : α}
    (hz : σ z = z) (hx : x ≠ z) :
    ¬ PermReachable σ x z := by
  intro hxz
  exact hx (eq_of_permReachable_fixed σ hz hxz)

noncomputable def orbitEquivOfFixed
    (σ : Equiv.Perm α) [Fintype α] {z : α} (hz : σ z = z) :
    PermOrbit (skip σ z) ≃ {o : PermOrbit σ // o ≠ PermOrbit.of σ z} where
  toFun q :=
    Quotient.lift
      (fun x : DeletedPoint z =>
        ⟨PermOrbit.of σ x.1, by
          intro hbad
          exact x.2 (eq_of_permReachable_fixed σ hz (Quotient.exact hbad))⟩)
      (by
        intro x y hxy
        apply Subtype.ext
        exact PermOrbit.of_eq_of σ (skip_permReachable_project σ hxy))
      q
  invFun o :=
    let x := Quotient.out o.1
    have hx : x ≠ z := by
      intro hxz
      have hout : PermOrbit.of σ x = o.1 := Quotient.out_eq o.1
      exact o.2 (by simpa [hxz] using hout.symm)
    PermOrbit.of (skip σ z) (⟨x, hx⟩ : DeletedPoint z)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    apply PermOrbit.of_eq_of
    let y := Quotient.out (PermOrbit.of σ x.1)
    have hy : y ≠ z := by
      intro hyz
      have hout : PermOrbit.of σ y = PermOrbit.of σ x.1 :=
        Quotient.out_eq (PermOrbit.of σ x.1)
      exact x.2 (eq_of_permReachable_fixed σ hz
        (PermReachable.symm σ (Quotient.exact (by simpa [hyz] using hout))))
    have hreach : PermReachable σ y x.1 :=
      Quotient.exact (Quotient.out_eq (PermOrbit.of σ x.1))
    exact skip_permReachable_of_permReachable σ hreach
  right_inv o := by
    apply Subtype.ext
    dsimp
    exact Quotient.out_eq o.1

theorem orbitCount_skip_add_one_of_fixed
    (σ : Equiv.Perm α) [Fintype α] {z : α} (hz : σ z = z) :
    Nat.card (PermOrbit (skip σ z)) + 1 = Nat.card (PermOrbit σ) := by
  classical
  rw [Nat.card_congr (orbitEquivOfFixed σ hz)]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simpa [Nat.add_comm] using DeletedPoint.card_add_one (PermOrbit.of σ z)

theorem orbitCount_skip_add_indicator
    (σ : Equiv.Perm α) [Fintype α] (z : α) :
    (if σ z = z then 1 else 0) + Nat.card (PermOrbit (skip σ z)) =
      Nat.card (PermOrbit σ) := by
  by_cases hz : σ z = z
  · have h := orbitCount_skip_add_one_of_fixed σ hz
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    simpa [hz, Nat.add_comm] using h
  · have h := orbitCount_skip_of_not_fixed σ hz
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    simpa [hz] using h

theorem skip_periodAtMostThree
    (σ : Equiv.Perm α)
    (hσ : ∀ x : α,
      σ x = x ∨ σ (σ x) = x ∨ σ (σ (σ x)) = x)
    {z : α} (x : DeletedPoint z) :
    skip σ z x = x ∨
      skip σ z (skip σ z x) = x ∨
        skip σ z (skip σ z (skip σ z x)) = x := by
  rcases hσ x.1 with hfixed | htwo | hthree
  · left
    apply Subtype.ext
    have hne : σ x.1 ≠ z := by
      rw [hfixed]
      exact x.2
    rw [skip_apply_of_apply_ne σ x hne, hfixed]
  · by_cases hstep : σ x.1 = z
    · left
      apply Subtype.ext
      rw [skip_apply_of_apply_eq σ x hstep]
      calc
        σ z = σ (σ x.1) := by rw [hstep]
        _ = x.1 := htwo
    · right
      left
      apply Subtype.ext
      have hne₂ : σ ((skip σ z x : DeletedPoint z) : α) ≠ z := by
        rw [skip_apply_of_apply_ne σ x hstep, htwo]
        exact x.2
      rw [skip_apply_of_apply_ne σ (skip σ z x) hne₂,
        skip_apply_of_apply_ne σ x hstep, htwo]
  · by_cases hstep₁ : σ x.1 = z
    · right
      left
      apply Subtype.ext
      have hne₂ : σ ((skip σ z x : DeletedPoint z) : α) ≠ z := by
        rw [skip_apply_of_apply_eq σ x hstep₁]
        have hx : σ (σ z) = x.1 := by
          calc
            σ (σ z) = σ (σ (σ x.1)) := by rw [hstep₁]
            _ = x.1 := hthree
        rw [hx]
        exact x.2
      rw [skip_apply_of_apply_ne σ (skip σ z x) hne₂,
        skip_apply_of_apply_eq σ x hstep₁]
      calc
        σ (σ z) = σ (σ (σ x.1)) := by rw [hstep₁]
        _ = x.1 := hthree
    · by_cases hstep₂ : σ (σ x.1) = z
      · right
        left
        apply Subtype.ext
        have htoz : σ ((skip σ z x : DeletedPoint z) : α) = z := by
          rw [skip_apply_of_apply_ne σ x hstep₁, hstep₂]
        rw [skip_apply_of_apply_eq σ (skip σ z x) htoz]
        calc
          σ z = σ (σ (σ x.1)) := by rw [hstep₂]
          _ = x.1 := hthree
      · right
        right
        apply Subtype.ext
        have hne₂ : σ ((skip σ z x : DeletedPoint z) : α) ≠ z := by
          rw [skip_apply_of_apply_ne σ x hstep₁]
          exact hstep₂
        have hne₃ :
            σ ((skip σ z (skip σ z x) : DeletedPoint z) : α) ≠ z := by
          rw [skip_apply_of_apply_ne σ (skip σ z x) hne₂,
            skip_apply_of_apply_ne σ x hstep₁, hthree]
          exact x.2
        rw [skip_apply_of_apply_ne σ (skip σ z (skip σ z x)) hne₃,
          skip_apply_of_apply_ne σ (skip σ z x) hne₂,
          skip_apply_of_apply_ne σ x hstep₁, hthree]

theorem skip_symm_apply_val
    (σ : Equiv.Perm α) (z : α) (x : DeletedPoint z) :
    ((skip σ z).symm x : DeletedPoint z) =
      ⟨skipAux σ.symm z x.1, skipAux_ne_deleted σ.symm x⟩ :=
  rfl

@[simp]
theorem skip_symm_apply_val_coe
    (σ : Equiv.Perm α) (z : α) (x : DeletedPoint z) :
    (((skip σ z).symm x : DeletedPoint z) : α) =
      skipAux σ.symm z x.1 :=
  rfl

end PermSkip

end FourColor

end Schematic.Math.GraphTheory
