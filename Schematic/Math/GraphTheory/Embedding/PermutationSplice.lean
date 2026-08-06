import Schematic.Math.GraphTheory.Embedding.Hypermap
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
Successor splices for finite permutations.

If `p` and `q` lie in distinct cycles of `σ`, swapping the successors
`σ p` and `σ q` merges those two cycles.  This is the local permutation
surgery used when planar rotation systems are joined at a cut vertex.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

/-- Disjoint sum of two permutations. -/
def permSum
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Equiv.Perm (Sum α β) :=
  Equiv.sumCongr σ τ

@[simp]
theorem permSum_apply_inl
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (x : α) :
    permSum σ τ (Sum.inl x) = Sum.inl (σ x) :=
  rfl

@[simp]
theorem permSum_apply_inr
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (y : β) :
    permSum σ τ (Sum.inr y) = Sum.inr (τ y) :=
  rfl

@[simp]
theorem permSum_symm_apply_inl
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (x : α) :
    (permSum σ τ).symm (Sum.inl x) = Sum.inl (σ.symm x) :=
  rfl

@[simp]
theorem permSum_symm_apply_inr
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) (y : β) :
    (permSum σ τ).symm (Sum.inr y) = Sum.inr (τ.symm y) :=
  rfl

theorem permSum_reachable_inl
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable (permSum σ τ) (Sum.inl x) (Sum.inl y) :=
  PermReachable.map_of_forward_simulation σ (permSum σ τ) Sum.inl
    (fun z => by
      simpa using PermReachable.forward (permSum σ τ) (Sum.inl z)) hxy

theorem permSum_reachable_inr
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    {x y : β}
    (hxy : PermReachable τ x y) :
    PermReachable (permSum σ τ) (Sum.inr x) (Sum.inr y) :=
  PermReachable.map_of_forward_simulation τ (permSum σ τ) Sum.inr
    (fun z => by
      simpa using PermReachable.forward (permSum σ τ) (Sum.inr z)) hxy

def permSumOrbitCode
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Sum α β → Sum (PermOrbit σ) (PermOrbit τ)
  | Sum.inl x => Sum.inl (PermOrbit.of σ x)
  | Sum.inr y => Sum.inr (PermOrbit.of τ y)

theorem permSumOrbitCode_of_link
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    {x y : Sum α β}
    (hxy : PermLink (permSum σ τ) x y) :
    permSumOrbitCode σ τ x = permSumOrbitCode σ τ y := by
  cases hxy with
  | forward =>
      cases x with
      | inl x =>
          simp [permSumOrbitCode, PermOrbit.of_apply]
      | inr y =>
          simp [permSumOrbitCode, PermOrbit.of_apply]
  | backward =>
      cases x with
      | inl x =>
          simp [permSumOrbitCode, PermOrbit.of_symm_apply]
      | inr y =>
          simp [permSumOrbitCode, PermOrbit.of_symm_apply]

theorem permSumOrbitCode_of_reachable
    {α β : Type u}
    (σ : Equiv.Perm α) (τ : Equiv.Perm β)
    {x y : Sum α β}
    (hxy : PermReachable (permSum σ τ) x y) :
    permSumOrbitCode σ τ x = permSumOrbitCode σ τ y :=
  hxy.apply_eq (permSumOrbitCode σ τ)
    (fun {_ _} h => permSumOrbitCode_of_link σ τ h)

/-- Cyclic orbits of a disjoint sum of permutations are the disjoint sum of
the cyclic orbit types. -/
noncomputable def permSumOrbitEquiv
    {α β : Type u} [Fintype α] [Fintype β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    PermOrbit (permSum σ τ) ≃ Sum (PermOrbit σ) (PermOrbit τ) where
  toFun :=
    Quotient.lift
      (permSumOrbitCode σ τ)
      (by
        intro x y hxy
        exact permSumOrbitCode_of_reachable σ τ hxy)
  invFun
    | Sum.inl o =>
        Quotient.lift
          (fun x => PermOrbit.of (permSum σ τ) (Sum.inl x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (permSum σ τ)
              (permSum_reachable_inl σ τ hxy))
          o
    | Sum.inr o =>
        Quotient.lift
          (fun x => PermOrbit.of (permSum σ τ) (Sum.inr x))
          (by
            intro x y hxy
            exact PermOrbit.of_eq_of (permSum σ τ)
              (permSum_reachable_inr σ τ hxy))
          o
  left_inv := by
    intro o
    induction o using Quotient.inductionOn with
    | h x =>
        cases x <;> rfl
  right_inv := by
    intro o
    cases o with
    | inl o =>
        induction o using Quotient.inductionOn with
        | h x => rfl
    | inr o =>
        induction o using Quotient.inductionOn with
        | h y => rfl

theorem permSum_orbitCount
    {α β : Type u} [Fintype α] [Fintype β]
    (σ : Equiv.Perm α) (τ : Equiv.Perm β) :
    Nat.card (PermOrbit (permSum σ τ)) =
      Nat.card (PermOrbit σ) + Nat.card (PermOrbit τ) := by
  rw [Nat.card_congr (permSumOrbitEquiv σ τ)]
  simp

/-- Swap the successors of `p` and `q` in a permutation. -/
def permSplice
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) :
    Equiv.Perm α :=
  σ.trans (Equiv.swap (σ p) (σ q))

@[simp]
theorem permSplice_apply_left
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) :
    permSplice σ p q p = σ q := by
  simp [permSplice]

@[simp]
theorem permSplice_apply_right
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) :
    permSplice σ p q q = σ p := by
  simp [permSplice]

theorem permSplice_apply_of_ne
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q x : α)
    (hxp : x ≠ p) (hxq : x ≠ q) :
    permSplice σ p q x = σ x := by
  have hsxp : σ x ≠ σ p := fun h => hxp (σ.injective h)
  have hsxq : σ x ≠ σ q := fun h => hxq (σ.injective h)
  simp [permSplice, Equiv.swap_apply_of_ne_of_ne hsxp hsxq]

/-- A successor splice preserves any code already preserved by the old
permutation, provided the two splice points have the same code. -/
theorem permSplice_preserves
    {α : Type u} {β : Type*} [DecidableEq α]
    (σ : Equiv.Perm α) (code : α -> β)
    (hσ : forall z, code (σ z) = code z)
    (p q : α) (hpq : code p = code q)
    (z : α) :
    code (permSplice σ p q z) = code z := by
  by_cases hzp : z = p
  · subst z
    rw [permSplice_apply_left, hσ q, hpq]
  · by_cases hzq : z = q
    · subst z
      rw [permSplice_apply_right, hσ p, hpq]
    · rw [permSplice_apply_of_ne σ p q z hzp hzq, hσ]

@[simp]
theorem permSplice_symm_apply
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q x : α) :
    (permSplice σ p q).symm x =
      σ.symm (Equiv.swap (σ p) (σ q) x) :=
  rfl

theorem permSplice_comm
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) :
    permSplice σ p q = permSplice σ q p := by
  simp only [permSplice, Equiv.swap_comm]

theorem permSplice_involutive
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) :
    permSplice (permSplice σ p q) p q = σ := by
  apply Equiv.ext
  intro x
  simp [permSplice, Equiv.swap_comm]

/-- Swapping successors at two distinct points of one permutation cycle cuts
that cycle into two cycles.  This is the same-cycle counterpart of
`permSplice_left_reachable_right`. -/
theorem permSplice_not_reachable_of_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hpq : PermReachable σ p q)
    (hpq_ne : p ≠ q) :
    ¬ PermReachable (permSplice σ p q) p q := by
  intro hspliced
  let τ := permSplice σ p q
  obtain ⟨N, hNpos, hNq, hNmin⟩ :=
    permReachable_exists_first_positive_iterate τ hspliced hpq_ne
  have hno_return_p :
      forall k : Nat, 0 < k -> k < N -> (τ : α -> α)^[k] p ≠ p := by
    intro k hkpos hkN hkreturn
    have hk_le : k ≤ N := Nat.le_of_lt hkN
    have hsmall : N - k < N := by omega
    have hsmall_q : (τ : α -> α)^[N - k] p = q := by
      calc
        (τ : α -> α)^[N - k] p =
            (τ : α -> α)^[N - k] ((τ : α -> α)^[k] p) := by
              rw [hkreturn]
        _ = (τ : α -> α)^[(N - k) + k] p := by
              rw [Function.iterate_add_apply]
        _ = (τ : α -> α)^[N] p := by rw [Nat.sub_add_cancel hk_le]
        _ = q := hNq
    exact hNmin (N - k) hsmall hsmall_q
  have hiterate :
      forall j : Nat, 1 ≤ j -> j ≤ N ->
        (τ : α -> α)^[j] p = (σ : α -> α)^[j] q := by
    intro j hjpos hjN
    induction j with
    | zero => omega
    | succ j ih =>
        by_cases hjzero : j = 0
        · subst j
          simp [τ, permSplice_apply_left]
        · have hjpos' : 0 < j := Nat.pos_of_ne_zero hjzero
          have hjN' : j ≤ N := le_trans (Nat.le_succ j) hjN
          have hjltN : j < N := by omega
          have ih' : (τ : α -> α)^[j] p = (σ : α -> α)^[j] q :=
            ih hjpos' hjN'
          have hcurrent_ne_p : (σ : α -> α)^[j] q ≠ p := by
            intro hcurrent
            exact hno_return_p j hjpos' hjltN (ih'.trans hcurrent)
          have hcurrent_ne_q : (σ : α -> α)^[j] q ≠ q := by
            intro hcurrent
            exact hNmin j hjltN (ih'.trans hcurrent)
          calc
            (τ : α -> α)^[j.succ] p =
                τ ((τ : α -> α)^[j] p) := by
                  rw [Function.iterate_succ_apply']
            _ = τ ((σ : α -> α)^[j] q) := by rw [ih']
            _ = σ ((σ : α -> α)^[j] q) := by
                  exact permSplice_apply_of_ne σ p q _
                    hcurrent_ne_p hcurrent_ne_q
            _ = (σ : α -> α)^[j.succ] q := by
                  rw [Function.iterate_succ_apply']
  have hNiterate : (τ : α -> α)^[N] p = (σ : α -> α)^[N] q :=
    hiterate N (by omega) (le_refl N)
  have hperiod : Function.IsPeriodicPt (σ : α -> α) N q := by
    exact hNiterate.symm.trans hNq
  have hqp : PermReachable σ q p := PermReachable.symm σ hpq
  obtain ⟨m, hm⟩ := permReachable_exists_iterate σ hqp
  have hmod : (σ : α -> α)^[m % N] q = p :=
    (hperiod.iterate_mod_apply m).trans hm
  have hmod_lt : m % N < N := Nat.mod_lt m hNpos
  by_cases hmod_zero : m % N = 0
  · have hqp_eq : q = p := by simpa [hmod_zero] using hmod
    exact hpq_ne hqp_eq.symm
  · have hmod_pos : 0 < m % N := Nat.pos_of_ne_zero hmod_zero
    have hmod_iterate :=
      hiterate (m % N) hmod_pos (Nat.le_of_lt hmod_lt)
    exact hno_return_p (m % N) hmod_pos hmod_lt
      (hmod_iterate.trans hmod)

private theorem permSplice_cycle_arc
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) :
    PermReachable (permSplice σ p q) (σ q) q := by
  let hperiod := perm_exists_pos_iterate_eq_self σ q
  let n := Nat.find hperiod
  have hn_pos : 0 < n := (Nat.find_spec hperiod).1
  have hn_eq : (σ : α → α)^[n] q = q := (Nat.find_spec hperiod).2
  have hn_min :
      ∀ k : ℕ, k < n →
        ¬ (0 < k ∧ (σ : α → α)^[k] q = q) := by
    intro k hk
    exact Nat.find_min hperiod hk
  have hqp : ¬ PermReachable σ q p := by
    intro h
    exact hsep (PermReachable.symm σ h)
  have hwalk :
      ∀ k : ℕ, k < n →
        PermReachable (permSplice σ p q)
          (σ q) ((σ : α → α)^[k + 1] q) := by
    intro k hk
    induction k with
    | zero =>
        simpa using
          (PermReachable.refl (permSplice σ p q) (σ q))
    | succ k ih =>
        have hk_lt : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
        have hprev :
            PermReachable (permSplice σ p q)
              (σ q) ((σ : α → α)^[k + 1] q) :=
          ih hk_lt
        have hsource_ne_q : (σ : α → α)^[k + 1] q ≠ q := by
          intro heq
          exact hn_min (k + 1) hk
            ⟨Nat.succ_pos k, heq⟩
        have hsource_ne_p : (σ : α → α)^[k + 1] q ≠ p := by
          intro heq
          apply hqp
          exact permReachable_of_iterate_eq σ heq
        have hstep :
            PermReachable (permSplice σ p q)
              ((σ : α → α)^[k + 1] q)
              (σ ((σ : α → α)^[k + 1] q)) := by
          rw [← permSplice_apply_of_ne σ p q
            ((σ : α → α)^[k + 1] q) hsource_ne_p hsource_ne_q]
          exact PermReachable.forward (permSplice σ p q)
            ((σ : α → α)^[k + 1] q)
        exact PermReachable.trans (permSplice σ p q) hprev
          (by
            simpa [Function.iterate_succ_apply'] using hstep)
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos) with ⟨d, hd⟩
  have hd_lt : d < n := by
    rw [hd]
    exact Nat.lt_succ_self d
  have hlast := hwalk d hd_lt
  have hd_eq : (σ : α → α)^[d + 1] q = q := by
    have h := hn_eq
    rw [hd] at h
    simpa [Nat.succ_eq_add_one] using h
  simpa [hd_eq] using hlast

/-- Every old successor step remains reachable after two distinct cycles are
spliced.  At a splice point the route traverses the other old cycle before
returning to the original successor. -/
theorem permSplice_old_forward_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q x : α)
    (hsep : ¬ PermReachable σ p q) :
    PermReachable (permSplice σ p q) x (σ x) := by
  by_cases hxp : x = p
  · subst x
    exact
      PermReachable.trans (permSplice σ p q)
        (by
          simpa using
            (PermReachable.forward (permSplice σ p q) p))
        (PermReachable.trans (permSplice σ p q)
          (permSplice_cycle_arc σ p q hsep)
          (by
            simpa using
              (PermReachable.forward (permSplice σ p q) q)))
  · by_cases hxq : x = q
    · subst x
      have hsep' : ¬ PermReachable σ q p := by
        intro h
        exact hsep (PermReachable.symm σ h)
      exact
        PermReachable.trans (permSplice σ p q)
          (by
            simpa using
              (PermReachable.forward (permSplice σ p q) q))
          (PermReachable.trans (permSplice σ p q)
            (by
              rw [permSplice_comm σ p q]
              exact permSplice_cycle_arc σ q p hsep')
            (by
              simpa using
                (PermReachable.forward (permSplice σ p q) p)))
    · rw [← permSplice_apply_of_ne σ p q x hxp hxq]
      exact PermReachable.forward (permSplice σ p q) x

/-- Reachability in an old permutation cycle lifts through a splice of two
distinct cycles. -/
theorem permSplice_reachable_of_old_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q)
    {x y : α}
    (hxy : PermReachable σ x y) :
    PermReachable (permSplice σ p q) x y := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
  have hiter :
      ∀ k : ℕ,
        PermReachable (permSplice σ p q)
          x ((σ : α → α)^[k] x) := by
    intro k
    induction k with
    | zero =>
        exact PermReachable.refl (permSplice σ p q) x
    | succ k ih =>
        exact
          PermReachable.trans (permSplice σ p q) ih
            (by
              simpa [Function.iterate_succ_apply'] using
                permSplice_old_forward_reachable σ p q
                  ((σ : α → α)^[k] x) hsep)
  simpa [hn] using hiter n

/-- The two selected old cycles become one splice cycle. -/
theorem permSplice_left_reachable_right
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) :
    PermReachable (permSplice σ p q) p q := by
  exact
    PermReachable.trans (permSplice σ p q)
      (by
        simpa using
          (PermReachable.forward (permSplice σ p q) p))
      (permSplice_cycle_arc σ p q hsep)

theorem permSplice_selected_orbits_ne
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) :
    PermOrbit.of σ p ≠ PermOrbit.of σ q := by
  intro h
  exact hsep (Quotient.exact h)

/-- Orbit code for a splice: the old orbit of `q` is represented by the old
orbit of `p`, while every other old orbit keeps its own representative. -/
noncomputable def permSpliceOrbitCode
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) (x : α) :
    {o : PermOrbit σ // o ≠ PermOrbit.of σ q} := by
  classical
  by_cases hqx : PermReachable σ q x
  · exact ⟨PermOrbit.of σ p, permSplice_selected_orbits_ne σ p q hsep⟩
  · refine ⟨PermOrbit.of σ x, ?_⟩
    intro hx
    apply hqx
    exact PermReachable.symm σ (Quotient.exact hx)

private theorem permSpliceOrbitCode_apply
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) (x : α) :
    permSpliceOrbitCode σ p q hsep x =
      permSpliceOrbitCode σ p q hsep (permSplice σ p q x) := by
  classical
  by_cases hxp : x = p
  · subst x
    have hqp : ¬ PermReachable σ q p := by
      intro h
      exact hsep (PermReachable.symm σ h)
    have hqσq : PermReachable σ q (σ q) :=
      PermReachable.forward σ q
    apply Subtype.ext
    simp [permSpliceOrbitCode, hqp, hqσq]
  · by_cases hxq : x = q
    · subst x
      have hqq : PermReachable σ q q :=
        PermReachable.refl σ q
      have hqσp : ¬ PermReachable σ q (σ p) := by
        intro h
        apply hsep
        exact
          PermReachable.symm σ
            (PermReachable.trans σ h
              (by
                simpa using PermReachable.backward σ (σ p)))
      apply Subtype.ext
      simp [permSpliceOrbitCode, hqq, hqσp]
      exact (PermOrbit.of_apply σ p).symm
    · have happly := permSplice_apply_of_ne σ p q x hxp hxq
      have hreach_iff :
          PermReachable σ q x ↔ PermReachable σ q (σ x) := by
        constructor
        · intro h
          exact PermReachable.trans σ h (PermReachable.forward σ x)
        · intro h
          exact
            PermReachable.trans σ h
              (by
                simpa using PermReachable.backward σ (σ x))
      rw [happly]
      by_cases hqx : PermReachable σ q x
      · have hqσx : PermReachable σ q (σ x) := hreach_iff.mp hqx
        simp [permSpliceOrbitCode, hqx, hqσx]
      · have hqσx : ¬ PermReachable σ q (σ x) :=
          fun h => hqx (hreach_iff.mpr h)
        apply Subtype.ext
        simp [permSpliceOrbitCode, hqx, hqσx]
        exact (PermOrbit.of_apply σ x).symm

theorem permSpliceOrbitCode_of_link
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q)
    {x y : α}
    (hxy : PermLink (permSplice σ p q) x y) :
    permSpliceOrbitCode σ p q hsep x =
      permSpliceOrbitCode σ p q hsep y := by
  cases hxy with
  | forward =>
      exact permSpliceOrbitCode_apply σ p q hsep x
  | backward =>
      have h :=
        permSpliceOrbitCode_apply σ p q hsep
          ((permSplice σ p q).symm x)
      rw [(permSplice σ p q).apply_symm_apply x] at h
      exact h.symm

theorem permSpliceOrbitCode_of_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q)
    {x y : α}
    (hxy : PermReachable (permSplice σ p q) x y) :
    permSpliceOrbitCode σ p q hsep x =
      permSpliceOrbitCode σ p q hsep y :=
  hxy.apply_eq (permSpliceOrbitCode σ p q hsep)
    (fun {_ _} h => permSpliceOrbitCode_of_link σ p q hsep h)

/-- Splicing two distinct permutation cycles removes exactly the old `q`
orbit from the orbit quotient, using the old `p` orbit as the representative
of the merged cycle. -/
noncomputable def permSpliceOrbitEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) :
    PermOrbit (permSplice σ p q) ≃
      {o : PermOrbit σ // o ≠ PermOrbit.of σ q} where
  toFun :=
    Quotient.lift
      (permSpliceOrbitCode σ p q hsep)
      (by
        intro x y hxy
        exact permSpliceOrbitCode_of_reachable σ p q hsep hxy)
  invFun o :=
    Quotient.lift
      (fun x => PermOrbit.of (permSplice σ p q) x)
      (by
        intro x y hxy
        exact PermOrbit.of_eq_of (permSplice σ p q)
          (permSplice_reachable_of_old_reachable σ p q hsep hxy))
      o.1
  left_inv := by
    intro o
    induction o using Quotient.inductionOn with
    | h x =>
        simp only [Quotient.lift_mk]
        by_cases hqx : PermReachable σ q x
        · simp only [permSpliceOrbitCode, hqx, dite_true]
          change
            (Quotient.lift
              (fun z => PermOrbit.of (permSplice σ p q) z) _
              (PermOrbit.of σ p)) =
                PermOrbit.of (permSplice σ p q) x
          change
            PermOrbit.of (permSplice σ p q) p =
              PermOrbit.of (permSplice σ p q) x
          apply PermOrbit.of_eq_of
          exact
            PermReachable.trans (permSplice σ p q)
              (permSplice_left_reachable_right σ p q hsep)
              (permSplice_reachable_of_old_reachable σ p q hsep hqx)
        · simp only [permSpliceOrbitCode, hqx, dite_false]
          change
            (Quotient.lift
              (fun z => PermOrbit.of (permSplice σ p q) z) _
              (PermOrbit.of σ x)) =
                PermOrbit.of (permSplice σ p q) x
          rfl
  right_inv := by
    rintro ⟨o, ho⟩
    apply Subtype.ext
    induction o using Quotient.inductionOn with
    | h x =>
        have hqx : ¬ PermReachable σ q x := by
          intro h
          apply ho
          exact PermOrbit.of_eq_of σ (PermReachable.symm σ h)
        change (permSpliceOrbitCode σ p q hsep x).1 = PermOrbit.of σ x
        simp [permSpliceOrbitCode, hqx]

theorem permSplice_orbitCount
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hsep : ¬ PermReachable σ p q) :
    Nat.card (PermOrbit (permSplice σ p q)) + 1 =
      Nat.card (PermOrbit σ) := by
  classical
  rw [Nat.card_congr (permSpliceOrbitEquiv σ p q hsep)]
  have hcard :=
    Nat.card_congr
      (Equiv.optionSubtypeNe (PermOrbit.of σ q))
  simpa using hcard

/-- Splicing two distinct points on one permutation cycle creates exactly one
new cycle.  Applying the distinct-cycle count to the involutive splice gives
the result without choosing representatives for the two new arcs. -/
theorem permSplice_orbitCount_of_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q)
    (hne : p ≠ q) :
    Nat.card (PermOrbit σ) + 1 =
      Nat.card (PermOrbit (permSplice σ p q)) := by
  let τ := permSplice σ p q
  have hsep : ¬ PermReachable τ p q :=
    permSplice_not_reachable_of_reachable σ p q hreach hne
  have hcount := permSplice_orbitCount τ p q hsep
  rw [show permSplice τ p q = σ by
    exact permSplice_involutive σ p q] at hcount
  exact hcount

end FourColor

end Schematic.Math.GraphTheory
