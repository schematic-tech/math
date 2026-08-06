import Schematic.Math.GraphTheory.Embedding.DartExtension


namespace Schematic.Math.GraphTheory

namespace FourColor

universe u v

namespace EdgeDeletion

/-- Split a finite permutation cycle at the predecessors of two distinct
points, inserting the two fresh darts as the cross-links.  This is the
face-permutation skeleton for adding an edge between two darts on the same
face. -/
def splitFacePerm
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) (hpq : p ≠ q) :
    Equiv.Perm (ExtDart α) where
  toFun
    | ExtDart.new => ExtDart.old q
    | ExtDart.newEdge => ExtDart.old p
    | ExtDart.old x =>
        if x = σ.symm p then ExtDart.new
        else if x = σ.symm q then ExtDart.newEdge
        else ExtDart.old (σ x)
  invFun
    | ExtDart.new => ExtDart.old (σ.symm p)
    | ExtDart.newEdge => ExtDart.old (σ.symm q)
    | ExtDart.old y =>
        if y = q then ExtDart.new
        else if y = p then ExtDart.newEdge
        else ExtDart.old (σ.symm y)
  left_inv := by
    intro x
    cases x with
    | new =>
        simp
    | newEdge =>
        simp [hpq]
    | old x =>
        by_cases hxp : x = σ.symm p
        · subst x
          simp
        · by_cases hxq : x = σ.symm q
          · subst x
            simp [hxp]
          · have hsx_ne_q : σ x ≠ q := by
              intro h
              apply hxq
              calc
                x = σ.symm (σ x) := by simp
                _ = σ.symm q := by rw [h]
            have hsx_ne_p : σ x ≠ p := by
              intro h
              apply hxp
              calc
                x = σ.symm (σ x) := by simp
                _ = σ.symm p := by rw [h]
            simp [hxp, hxq, hsx_ne_q, hsx_ne_p]
  right_inv := by
    intro x
    cases x with
    | new =>
        simp
    | newEdge =>
        have hsymm_qp : σ.symm q ≠ σ.symm p := by
          intro h
          exact hpq ((σ.symm.injective h).symm)
        simp [hsymm_qp]
    | old y =>
        by_cases hyq : y = q
        · subst y
          simp
        · by_cases hyp : y = p
          · subst y
            simp [hpq]
          · have hpre_ne_p : σ.symm y ≠ σ.symm p := by
              intro h
              apply hyp
              exact σ.symm.injective h
            have hpre_ne_q : σ.symm y ≠ σ.symm q := by
              intro h
              apply hyq
              exact σ.symm.injective h
            simp [hyq, hyp, hpre_ne_p, hpre_ne_q]

@[simp]
theorem splitFacePerm_new
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) (hpq : p ≠ q) :
    splitFacePerm σ p q hpq ExtDart.new = ExtDart.old q :=
  rfl

@[simp]
theorem splitFacePerm_newEdge
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) (hpq : p ≠ q) :
    splitFacePerm σ p q hpq ExtDart.newEdge = ExtDart.old p :=
  rfl

@[simp]
theorem splitFacePerm_old
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q x : α) (hpq : p ≠ q) :
    splitFacePerm σ p q hpq (ExtDart.old x) =
      if x = σ.symm p then ExtDart.new
      else if x = σ.symm q then ExtDart.newEdge
      else ExtDart.old (σ x) :=
  rfl

@[simp]
theorem splitFacePerm_symm_new
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) (hpq : p ≠ q) :
    (splitFacePerm σ p q hpq).symm ExtDart.new =
      ExtDart.old (σ.symm p) :=
  rfl

@[simp]
theorem splitFacePerm_symm_newEdge
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α) (hpq : p ≠ q) :
    (splitFacePerm σ p q hpq).symm ExtDart.newEdge =
      ExtDart.old (σ.symm q) :=
  rfl

@[simp]
theorem splitFacePerm_symm_old
    {α : Type u} [DecidableEq α]
    (σ : Equiv.Perm α) (p q y : α) (hpq : p ≠ q) :
    (splitFacePerm σ p q hpq).symm (ExtDart.old y) =
      if y = q then ExtDart.new
      else if y = p then ExtDart.newEdge
      else ExtDart.old (σ.symm y) :=
  rfl

/-- First positive forward hit of `q` from `p` along a finite permutation
orbit.  This gives a canonical orientation of the old face cycle between the
two cofacial edge-insertion cut points. -/
noncomputable def splitFaceFirstHit
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    ℕ :=
  Classical.choose
    (permReachable_exists_first_positive_iterate σ hreach hpq)

theorem splitFaceFirstHit_pos
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    0 < splitFaceFirstHit σ p q hreach hpq :=
  (Classical.choose_spec
    (permReachable_exists_first_positive_iterate σ hreach hpq)).1

theorem splitFaceFirstHit_iter
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    (σ : α → α)^[splitFaceFirstHit σ p q hreach hpq] p = q :=
  (Classical.choose_spec
    (permReachable_exists_first_positive_iterate σ hreach hpq)).2.1

theorem splitFaceFirstHit_min
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    (k : ℕ)
    (hk : k < splitFaceFirstHit σ p q hreach hpq) :
    (σ : α → α)^[k] p ≠ q :=
  (Classical.choose_spec
    (permReachable_exists_first_positive_iterate σ hreach hpq)).2.2 k hk

/-- The old darts on the `p`-to-`q` side of the cut, including `p` and
excluding `q`. -/
def splitFaceSide
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    (x : α) : Prop :=
  ∃ k : ℕ,
    k < splitFaceFirstHit σ p q hreach hpq ∧
      (σ : α → α)^[k] p = x

theorem splitFaceSide_p
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    splitFaceSide σ p q hreach hpq p :=
  ⟨0, splitFaceFirstHit_pos σ p q hreach hpq, rfl⟩

theorem not_splitFaceSide_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    ¬ splitFaceSide σ p q hreach hpq q := by
  rintro ⟨k, hk, hkq⟩
  exact splitFaceFirstHit_min σ p q hreach hpq k hk hkq

theorem splitFaceSide_pred_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    splitFaceSide σ p q hreach hpq (σ.symm q) := by
  let N := splitFaceFirstHit σ p q hreach hpq
  have hpos : 0 < N := splitFaceFirstHit_pos σ p q hreach hpq
  have hiter : (σ : α → α)^[N] p = q :=
    splitFaceFirstHit_iter σ p q hreach hpq
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨m, hN⟩
  refine ⟨m, ?_, ?_⟩
  · change m < N
    rw [hN]
    exact Nat.lt_succ_self m
  · apply σ.injective
    calc
      σ (((σ : α → α)^[m]) p) =
          (σ : α → α)^[m + 1] p := by
        rw [Function.iterate_succ_apply']
      _ = (σ : α → α)^[N] p := by
        rw [hN]
      _ = q := hiter
      _ = σ (σ.symm q) := by simp

theorem splitFaceSide_step_or_pred_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : splitFaceSide σ p q hreach hpq x) :
    splitFaceSide σ p q hreach hpq (σ x) ∨ x = σ.symm q := by
  rcases hx with ⟨k, hk, hkx⟩
  let N := splitFaceFirstHit σ p q hreach hpq
  have hsucc_le : k + 1 <= N := Nat.succ_le_of_lt hk
  rcases lt_or_eq_of_le hsucc_le with hlt | hEq
  · left
    refine ⟨k + 1, ?_, ?_⟩
    · exact hlt
    · rw [Function.iterate_succ_apply', hkx]
  · right
    apply σ.injective
    calc
      σ x = σ (((σ : α → α)^[k]) p) := by rw [hkx]
      _ = (σ : α → α)^[k + 1] p := by
        rw [Function.iterate_succ_apply']
      _ = (σ : α → α)^[N] p := by rw [hEq]
      _ = q := splitFaceFirstHit_iter σ p q hreach hpq
      _ = σ (σ.symm q) := by simp

theorem splitFaceSide_step_of_ne_pred_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : splitFaceSide σ p q hreach hpq x)
    (hne : x ≠ σ.symm q) :
    splitFaceSide σ p q hreach hpq (σ x) := by
  rcases splitFaceSide_step_or_pred_q σ p q hreach hpq hx with hside | hpred
  · exact hside
  · exact False.elim (hne hpred)

theorem splitFaceSide_of_step_or_pred_p
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : splitFaceSide σ p q hreach hpq (σ x)) :
    splitFaceSide σ p q hreach hpq x ∨ x = σ.symm p := by
  rcases hx with ⟨k, hk, hkx⟩
  cases k with
  | zero =>
      right
      apply σ.injective
      calc
        σ x = p := hkx.symm
        _ = σ (σ.symm p) := by simp
  | succ n =>
      left
      refine ⟨n, ?_, ?_⟩
      · exact Nat.lt_trans (Nat.lt_succ_self n) hk
      · apply σ.injective
        calc
          σ (((σ : α → α)^[n]) p) =
              (σ : α → α)^[n + 1] p := by
            rw [Function.iterate_succ_apply']
          _ = σ x := hkx

theorem not_splitFaceSide_step_of_ne_pred_p
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : ¬ splitFaceSide σ p q hreach hpq x)
    (hne : x ≠ σ.symm p) :
    ¬ splitFaceSide σ p q hreach hpq (σ x) := by
  intro hstep
  rcases splitFaceSide_of_step_or_pred_p σ p q hreach hpq hstep with hside | hpred
  · exact hx hside
  · exact hne hpred

theorem splitFacePerm_pred_p_orbit_eq_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) :
    PermOrbit.of σ (σ.symm p) = PermOrbit.of σ q := by
  apply PermOrbit.of_eq_of
  exact PermReachable.trans σ
    (by simpa using (PermReachable.forward σ (σ.symm p)))
    hreach

theorem not_splitFaceSide_pred_p
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    ¬ splitFaceSide σ p q hreach hpq (σ.symm p) := by
  rintro ⟨k, hk, hkpred⟩
  let N := splitFaceFirstHit σ p q hreach hpq
  have hiter : (σ : α → α)^[N] p = q :=
    splitFaceFirstHit_iter σ p q hreach hpq
  let r := k + 1
  have hrpos : 0 < r := Nat.succ_pos k
  have hrle : r <= N := Nat.succ_le_of_lt hk
  have hperiod : (σ : α → α)^[r] p = p := by
    change (σ : α → α)^[k + 1] p = p
    calc
      (σ : α → α)^[k + 1] p = σ (((σ : α → α)^[k]) p) := by
        rw [Function.iterate_succ_apply']
      _ = σ (σ.symm p) := by rw [hkpred]
      _ = p := by simp
  rcases lt_or_eq_of_le hrle with hrlt | hreq
  · let m := N - r
    have hm_lt : m < N := by
      dsimp [m]
      omega
    have hm_hit : (σ : α → α)^[m] p = q := by
      calc
        (σ : α → α)^[m] p =
            (σ : α → α)^[m] (((σ : α → α)^[r]) p) := by
          rw [hperiod]
        _ = (σ : α → α)^[m + r] p := by
          exact (Function.iterate_add_apply (f := (σ : α → α)) m r p).symm
        _ = (σ : α → α)^[N] p := by
          have hmr : m + r = N := by
            dsimp [m]
            omega
          rw [hmr]
        _ = q := hiter
    exact splitFaceFirstHit_min σ p q hreach hpq m hm_lt hm_hit
  · apply hpq
    have hq_eq_p : q = p := by
      calc
        q = (σ : α → α)^[N] p := hiter.symm
        _ = (σ : α → α)^[r] p := by rw [hreq]
        _ = p := hperiod
    exact hq_eq_p.symm

/-- Code the two face cycles obtained by cutting the old `σ`-orbit at the
predecessors of `p` and `q`.  The `none` code is the old `p`-to-`q` side
together with `newEdge`; `some _` keeps every old face orbit, with the
cofacial `p/q` orbit represented by the complementary side and `new`. -/
noncomputable def splitFaceOrbitCode
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    ExtDart α -> Option (PermOrbit σ) := by
  classical
  exact fun
  | ExtDart.new => some (PermOrbit.of σ q)
  | ExtDart.newEdge => none
  | ExtDart.old x =>
      if splitFaceSide σ p q hreach hpq x then
        none
      else
        some (PermOrbit.of σ x)

theorem splitFaceOrbitCode_forward
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    (x : ExtDart α) :
    splitFaceOrbitCode σ p q hreach hpq x =
      splitFaceOrbitCode σ p q hreach hpq
        (splitFacePerm σ p q hpq x) := by
  cases x with
  | new =>
      simp [splitFaceOrbitCode, not_splitFaceSide_q σ p q hreach hpq]
  | newEdge =>
      simp [splitFaceOrbitCode, splitFaceSide_p σ p q hreach hpq]
  | old x =>
      by_cases hxp : x = σ.symm p
      · subst x
        simp [splitFacePerm_old, splitFaceOrbitCode,
          not_splitFaceSide_pred_p σ p q hreach hpq]
        exact splitFacePerm_pred_p_orbit_eq_q σ p q hreach
      · by_cases hxq : x = σ.symm q
        · subst x
          simp [splitFacePerm_old, splitFaceOrbitCode,
            splitFaceSide_pred_q σ p q hreach hpq, hxp]
        · by_cases hxside : splitFaceSide σ p q hreach hpq x
          · have hstep :
                splitFaceSide σ p q hreach hpq (σ x) :=
              splitFaceSide_step_of_ne_pred_q σ p q hreach hpq hxside hxq
            simp [splitFacePerm_old, splitFaceOrbitCode, hxp, hxq, hxside,
              hstep]
          · have hstep :
                ¬ splitFaceSide σ p q hreach hpq (σ x) :=
              not_splitFaceSide_step_of_ne_pred_p σ p q hreach hpq hxside hxp
            simp [splitFacePerm_old, splitFaceOrbitCode, hxp, hxq, hxside,
              hstep]
            exact (PermOrbit.of_apply σ x).symm

theorem splitFaceOrbitCode_of_link
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x y : ExtDart α}
    (hxy : PermLink (splitFacePerm σ p q hpq) x y) :
    splitFaceOrbitCode σ p q hreach hpq x =
      splitFaceOrbitCode σ p q hreach hpq y := by
  cases hxy with
  | forward =>
      exact splitFaceOrbitCode_forward σ p q hreach hpq x
  | backward =>
      have h :=
        splitFaceOrbitCode_forward σ p q hreach hpq
          ((splitFacePerm σ p q hpq).symm x)
      simpa using h.symm

theorem splitFaceOrbitCode_of_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x y : ExtDart α}
    (hxy : PermReachable (splitFacePerm σ p q hpq) x y) :
    splitFaceOrbitCode σ p q hreach hpq x =
      splitFaceOrbitCode σ p q hreach hpq y :=
  hxy.apply_eq (splitFaceOrbitCode σ p q hreach hpq)
    (fun {_ _} h => splitFaceOrbitCode_of_link σ p q hreach hpq h)

theorem splitFaceSide_orbit_eq_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : splitFaceSide σ p q hreach hpq x) :
    PermOrbit.of σ x = PermOrbit.of σ q := by
  rcases hx with ⟨k, _hk, hkx⟩
  have hpx : PermReachable σ p x :=
    permReachable_of_iterate_eq σ hkx
  exact PermOrbit.of_eq_of σ
    (PermReachable.trans σ (PermReachable.symm σ hpx) hreach)

theorem splitFacePerm_newEdge_reachable_old_of_side
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : splitFaceSide σ p q hreach hpq x) :
    PermReachable (splitFacePerm σ p q hpq) ExtDart.newEdge
      (ExtDart.old x) := by
  rcases hx with ⟨k, hk, hkx⟩
  let N := splitFaceFirstHit σ p q hreach hpq
  have hiter :
      ∀ n : ℕ, n < N →
        PermReachable (splitFacePerm σ p q hpq) ExtDart.newEdge
          (ExtDart.old (((σ : α → α)^[n]) p)) := by
    intro n hn
    induction n with
    | zero =>
        have h := PermReachable.forward
          (splitFacePerm σ p q hpq) ExtDart.newEdge
        simpa [splitFacePerm_newEdge] using h
    | succ n ih =>
        have hnlt : n < N := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hprev := ih hnlt
        let y := ((σ : α → α)^[n]) p
        have hy_ne_pred_p : y ≠ σ.symm p := by
          intro hy
          exact not_splitFaceSide_pred_p σ p q hreach hpq
            ⟨n, hnlt, hy⟩
        have hy_ne_pred_q : y ≠ σ.symm q := by
          intro hy
          exact splitFaceFirstHit_min σ p q hreach hpq (n + 1) hn (by
            calc
              (σ : α → α)^[n + 1] p =
                  σ (((σ : α → α)^[n]) p) := by
                rw [Function.iterate_succ_apply']
              _ = σ y := rfl
              _ = σ (σ.symm q) := by rw [hy]
              _ = q := by simp)
        have hstep :
            PermReachable (splitFacePerm σ p q hpq)
              (ExtDart.old y) (ExtDart.old (σ y)) := by
          have h := PermReachable.forward
            (splitFacePerm σ p q hpq) (ExtDart.old y)
          simpa [splitFacePerm_old, hy_ne_pred_p, hy_ne_pred_q] using h
        exact PermReachable.trans (splitFacePerm σ p q hpq) hprev
          (by
            simpa [y, Function.iterate_succ_apply'] using hstep)
  simpa [hkx] using hiter k hk

theorem splitFacePerm_old_side_reachable_newEdge
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hx : splitFaceSide σ p q hreach hpq x) :
    PermReachable (splitFacePerm σ p q hpq) (ExtDart.old x)
      ExtDart.newEdge :=
  PermReachable.symm (splitFacePerm σ p q hpq)
    (splitFacePerm_newEdge_reachable_old_of_side σ p q hreach hpq hx)

theorem not_splitFaceSide_of_orbit_ne_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (horbit : PermOrbit.of σ x ≠ PermOrbit.of σ q) :
    ¬ splitFaceSide σ p q hreach hpq x := by
  intro hx
  exact horbit (splitFaceSide_orbit_eq_q σ p q hreach hpq hx)

theorem splitFacePerm_old_forward_reachable_of_orbit_ne_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (horbit : PermOrbit.of σ x ≠ PermOrbit.of σ q) :
    PermReachable (splitFacePerm σ p q hpq)
      (ExtDart.old x) (ExtDart.old (σ x)) := by
  have hx_ne_pred_p : x ≠ σ.symm p := by
    intro hx
    apply horbit
    calc
      PermOrbit.of σ x = PermOrbit.of σ (σ.symm p) := by rw [hx]
      _ = PermOrbit.of σ q :=
        splitFacePerm_pred_p_orbit_eq_q σ p q hreach
  have hx_ne_pred_q : x ≠ σ.symm q := by
    intro hx
    apply horbit
    calc
      PermOrbit.of σ x = PermOrbit.of σ (σ.symm q) := by rw [hx]
      _ = PermOrbit.of σ q := PermOrbit.of_symm_apply σ q
  have h := PermReachable.forward
    (splitFacePerm σ p q hpq) (ExtDart.old x)
  simpa [splitFacePerm_old, hx_ne_pred_p, hx_ne_pred_q] using h

theorem splitFacePerm_old_backward_reachable_of_orbit_ne_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (horbit : PermOrbit.of σ x ≠ PermOrbit.of σ q) :
    PermReachable (splitFacePerm σ p q hpq)
      (ExtDart.old x) (ExtDart.old (σ.symm x)) := by
  have hpre_orbit :
      PermOrbit.of σ (σ.symm x) ≠ PermOrbit.of σ q := by
    intro hpre
    apply horbit
    calc
      PermOrbit.of σ x = PermOrbit.of σ (σ.symm x) :=
        (PermOrbit.of_symm_apply σ x).symm
      _ = PermOrbit.of σ q := hpre
  exact PermReachable.symm (splitFacePerm σ p q hpq)
    (by
      simpa using
        (splitFacePerm_old_forward_reachable_of_orbit_ne_q
          σ p q hreach hpq hpre_orbit))

theorem splitFacePerm_old_reachable_of_permReachable_of_orbit_ne_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x y : α}
    (horbit : PermOrbit.of σ x ≠ PermOrbit.of σ q)
    (hxy : PermReachable σ x y) :
    PermReachable (splitFacePerm σ p q hpq)
      (ExtDart.old x) (ExtDart.old y) := by
  induction hxy with
  | refl =>
      exact PermReachable.refl (splitFacePerm σ p q hpq) (ExtDart.old x)
  | @tail b c hxb hbc ih =>
      have hb_orbit : PermOrbit.of σ b ≠ PermOrbit.of σ q := by
        intro hbq
        apply horbit
        exact (PermOrbit.of_eq_of σ hxb).trans hbq
      have hstep :
          PermReachable (splitFacePerm σ p q hpq)
            (ExtDart.old b) (ExtDart.old c) := by
        cases hbc with
        | forward =>
            exact splitFacePerm_old_forward_reachable_of_orbit_ne_q
              σ p q hreach hpq hb_orbit
        | backward =>
            exact splitFacePerm_old_backward_reachable_of_orbit_ne_q
              σ p q hreach hpq hb_orbit
      exact PermReachable.trans (splitFacePerm σ p q hpq) ih hstep

theorem splitFacePerm_new_reachable_old_of_not_side_orbit_eq_q
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q)
    {x : α}
    (hxnot : ¬ splitFaceSide σ p q hreach hpq x)
    (hxorbit : PermOrbit.of σ x = PermOrbit.of σ q) :
    PermReachable (splitFacePerm σ p q hpq) ExtDart.new
      (ExtDart.old x) := by
  classical
  have hqx : PermReachable σ q x := Quotient.exact hxorbit.symm
  have hpx : PermReachable σ p x := PermReachable.trans σ hreach hqx
  have hpx_ne : p ≠ x := by
    intro hpx_eq
    subst x
    exact hxnot (splitFaceSide_p σ p q hreach hpq)
  let firstX :=
    Classical.choose
      (permReachable_exists_first_positive_iterate σ hpx hpx_ne)
  have hfirstX_spec :
      0 < firstX ∧
        (σ : α → α)^[firstX] p = x ∧
          ∀ k : ℕ, k < firstX → (σ : α → α)^[k] p ≠ x :=
    Classical.choose_spec
      (permReachable_exists_first_positive_iterate σ hpx hpx_ne)
  let N := splitFaceFirstHit σ p q hreach hpq
  have hN_iter : (σ : α → α)^[N] p = q :=
    splitFaceFirstHit_iter σ p q hreach hpq
  have hN_le_firstX : N <= firstX := by
    by_contra hle
    have hlt : firstX < N := Nat.lt_of_not_ge hle
    exact hxnot ⟨firstX, hlt, hfirstX_spec.2.1⟩
  let d := firstX - N
  have hN_add_d : N + d = firstX := by
    dsimp [d]
    omega
  have hd_iter : (σ : α → α)^[d] q = x := by
    calc
      (σ : α → α)^[d] q =
          (σ : α → α)^[d] (((σ : α → α)^[N]) p) := by
        rw [hN_iter]
      _ = (σ : α → α)^[d + N] p := by
        rw [Function.iterate_add_apply]
      _ = (σ : α → α)^[firstX] p := by
        have hdN : d + N = firstX := by
          dsimp [d]
          omega
        rw [hdN]
      _ = x := hfirstX_spec.2.1
  have period_before_firstX_contra :
      ∀ R : ℕ, 0 < R → R <= firstX →
        (σ : α → α)^[R] p = p → False := by
    intro R hRpos hRle hRperiod
    rcases lt_or_eq_of_le hRle with hRlt | hReq
    · let m := firstX - R
      have hm_lt : m < firstX := by
        dsimp [m]
        omega
      have hm_hit : (σ : α → α)^[m] p = x := by
        calc
          (σ : α → α)^[m] p =
              (σ : α → α)^[m] (((σ : α → α)^[R]) p) := by
            rw [hRperiod]
          _ = (σ : α → α)^[m + R] p := by
            exact (Function.iterate_add_apply (f := (σ : α → α)) m R p).symm
          _ = (σ : α → α)^[firstX] p := by
            have hmR : m + R = firstX := by
              dsimp [m]
              omega
            rw [hmR]
          _ = x := hfirstX_spec.2.1
      exact hfirstX_spec.2.2 m hm_lt hm_hit
    · apply hpx_ne
      calc
        p = (σ : α → α)^[R] p := hRperiod.symm
        _ = (σ : α → α)^[firstX] p := by rw [hReq]
        _ = x := hfirstX_spec.2.1
  have repeat_q_before_firstX_contra :
      ∀ R : ℕ, N < R → R <= firstX →
        (σ : α → α)^[R] p = q → False := by
    intro R hNR hRle hRq
    let m := firstX - R + N
    have hm_lt : m < firstX := by
      dsimp [m]
      omega
    have hm_hit : (σ : α → α)^[m] p = x := by
      calc
        (σ : α → α)^[m] p =
            (σ : α → α)^[firstX - R] (((σ : α → α)^[N]) p) := by
          dsimp [m]
          rw [Function.iterate_add_apply]
        _ = (σ : α → α)^[firstX - R] q := by rw [hN_iter]
        _ = (σ : α → α)^[firstX - R] (((σ : α → α)^[R]) p) := by
          rw [hRq]
        _ = (σ : α → α)^[firstX - R + R] p := by
          exact (Function.iterate_add_apply
            (f := (σ : α → α)) (firstX - R) R p).symm
        _ = (σ : α → α)^[firstX] p := by
          have hsub : firstX - R + R = firstX := by omega
          rw [hsub]
        _ = x := hfirstX_spec.2.1
    exact hfirstX_spec.2.2 m hm_lt hm_hit
  have hiter :
      ∀ n : ℕ, n <= d →
        PermReachable (splitFacePerm σ p q hpq) ExtDart.new
          (ExtDart.old (((σ : α → α)^[n]) q)) := by
    intro n hn
    induction n with
    | zero =>
        have h := PermReachable.forward
          (splitFacePerm σ p q hpq) ExtDart.new
        simpa [splitFacePerm_new] using h
    | succ n ih =>
        have hnle : n <= d := Nat.le_trans (Nat.le_succ n) hn
        have hnlt : n < d := Nat.lt_of_succ_le hn
        have hprev := ih hnle
        let y := ((σ : α → α)^[n]) q
        have hy_as_p : y = ((σ : α → α)^[N + n]) p := by
          calc
            y = (σ : α → α)^[n] q := rfl
            _ = (σ : α → α)^[n] (((σ : α → α)^[N]) p) := by
              rw [hN_iter]
            _ = (σ : α → α)^[n + N] p := by
              rw [Function.iterate_add_apply]
            _ = (σ : α → α)^[N + n] p := by
              rw [Nat.add_comm]
        have hRle : N + n + 1 <= firstX := by
          dsimp [d] at hnlt
          omega
        have hy_ne_pred_p : y ≠ σ.symm p := by
          intro hy
          exact period_before_firstX_contra (N + n + 1)
            (by omega) hRle (by
              calc
                (σ : α → α)^[N + n + 1] p =
                    σ (((σ : α → α)^[N + n]) p) := by
                  rw [Function.iterate_succ_apply']
                _ = σ y := by rw [hy_as_p]
                _ = σ (σ.symm p) := by rw [hy]
                _ = p := by simp)
        have hy_ne_pred_q : y ≠ σ.symm q := by
          intro hy
          exact repeat_q_before_firstX_contra (N + n + 1)
            (by omega) hRle (by
              calc
                (σ : α → α)^[N + n + 1] p =
                    σ (((σ : α → α)^[N + n]) p) := by
                  rw [Function.iterate_succ_apply']
                _ = σ y := by rw [hy_as_p]
                _ = σ (σ.symm q) := by rw [hy]
                _ = q := by simp)
        have hstep :
            PermReachable (splitFacePerm σ p q hpq)
              (ExtDart.old y) (ExtDart.old (σ y)) := by
          have h := PermReachable.forward
            (splitFacePerm σ p q hpq) (ExtDart.old y)
          simpa [splitFacePerm_old, hy_ne_pred_p, hy_ne_pred_q] using h
        exact PermReachable.trans (splitFacePerm σ p q hpq) hprev
          (by
            simpa [y, Function.iterate_succ_apply'] using hstep)
  simpa [hd_iter] using hiter d le_rfl

noncomputable def splitFaceOrbitInv
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (_hreach : PermReachable σ p q) (hpq : p ≠ q) :
    Option (PermOrbit σ) -> PermOrbit (splitFacePerm σ p q hpq) := by
  classical
  exact fun
  | none => PermOrbit.of (splitFacePerm σ p q hpq) ExtDart.newEdge
  | some o =>
      if o = PermOrbit.of σ q then
        PermOrbit.of (splitFacePerm σ p q hpq) ExtDart.new
      else
        PermOrbit.of (splitFacePerm σ p q hpq)
          (ExtDart.old (Quotient.out o))

noncomputable def splitFaceOrbitEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    PermOrbit (splitFacePerm σ p q hpq) ≃ Option (PermOrbit σ) where
  toFun :=
    Quotient.lift
      (splitFaceOrbitCode σ p q hreach hpq)
      (by
        intro x y hxy
        exact splitFaceOrbitCode_of_reachable σ p q hreach hpq hxy)
  invFun := splitFaceOrbitInv σ p q hreach hpq
  left_inv := by
    intro o
    induction o using Quotient.inductionOn with
    | h x =>
        cases x with
        | new =>
            change
              splitFaceOrbitInv σ p q hreach hpq
                  (splitFaceOrbitCode σ p q hreach hpq ExtDart.new) =
                PermOrbit.of (splitFacePerm σ p q hpq) ExtDart.new
            simp [splitFaceOrbitInv, splitFaceOrbitCode]
        | newEdge =>
            change
              splitFaceOrbitInv σ p q hreach hpq
                  (splitFaceOrbitCode σ p q hreach hpq ExtDart.newEdge) =
                PermOrbit.of (splitFacePerm σ p q hpq) ExtDart.newEdge
            simp [splitFaceOrbitInv, splitFaceOrbitCode]
        | old x =>
            by_cases hxside : splitFaceSide σ p q hreach hpq x
            · change
                splitFaceOrbitInv σ p q hreach hpq
                    (splitFaceOrbitCode σ p q hreach hpq (ExtDart.old x)) =
                  PermOrbit.of (splitFacePerm σ p q hpq) (ExtDart.old x)
              simp [splitFaceOrbitInv, splitFaceOrbitCode, hxside]
              exact PermOrbit.of_eq_of (splitFacePerm σ p q hpq)
                (splitFacePerm_newEdge_reachable_old_of_side
                  σ p q hreach hpq hxside)
            · by_cases hxorbit : PermOrbit.of σ x = PermOrbit.of σ q
              · change
                  splitFaceOrbitInv σ p q hreach hpq
                      (splitFaceOrbitCode σ p q hreach hpq (ExtDart.old x)) =
                    PermOrbit.of (splitFacePerm σ p q hpq) (ExtDart.old x)
                simp [splitFaceOrbitInv, splitFaceOrbitCode, hxside, hxorbit]
                exact PermOrbit.of_eq_of (splitFacePerm σ p q hpq)
                  (splitFacePerm_new_reachable_old_of_not_side_orbit_eq_q
                    σ p q hreach hpq hxside hxorbit)
              · change
                  splitFaceOrbitInv σ p q hreach hpq
                      (splitFaceOrbitCode σ p q hreach hpq (ExtDart.old x)) =
                    PermOrbit.of (splitFacePerm σ p q hpq) (ExtDart.old x)
                have hout :
                    PermOrbit.of σ (Quotient.out (PermOrbit.of σ x)) =
                      PermOrbit.of σ x :=
                  Quotient.out_eq (PermOrbit.of σ x)
                have hout_ne :
                    PermOrbit.of σ (Quotient.out (PermOrbit.of σ x)) ≠
                      PermOrbit.of σ q := by
                  intro hbad
                  exact hxorbit (hout.symm.trans hbad)
                have hreach_out :
                    PermReachable σ (Quotient.out (PermOrbit.of σ x)) x :=
                  Quotient.exact hout
                have hsplit :
                    PermReachable (splitFacePerm σ p q hpq)
                      (ExtDart.old (Quotient.out (PermOrbit.of σ x)))
                      (ExtDart.old x) :=
                  splitFacePerm_old_reachable_of_permReachable_of_orbit_ne_q
                    σ p q hreach hpq hout_ne hreach_out
                simp [splitFaceOrbitInv, splitFaceOrbitCode, hxside, hxorbit]
                exact PermOrbit.of_eq_of (splitFacePerm σ p q hpq) hsplit
  right_inv := by
    intro o
    cases o with
    | none =>
        rw [show splitFaceOrbitInv σ p q hreach hpq none =
          PermOrbit.of (splitFacePerm σ p q hpq)
            (ExtDart.newEdge : ExtDart α) by rfl]
        unfold PermOrbit.of
        rfl
    | some o =>
        by_cases ho : o = PermOrbit.of σ q
        · subst o
          rw [show splitFaceOrbitInv σ p q hreach hpq
              (some (PermOrbit.of σ q)) =
            PermOrbit.of (splitFacePerm σ p q hpq)
              (ExtDart.new : ExtDart α) by
                simp [splitFaceOrbitInv]]
          unfold PermOrbit.of
          rfl
        · have hout : PermOrbit.of σ (Quotient.out o) = o :=
            Quotient.out_eq o
          have hout_ne :
              PermOrbit.of σ (Quotient.out o) ≠ PermOrbit.of σ q := by
            intro hbad
            exact ho (hout.symm.trans hbad)
          have hnot :
              ¬ splitFaceSide σ p q hreach hpq (Quotient.out o) :=
            not_splitFaceSide_of_orbit_ne_q σ p q hreach hpq hout_ne
          rw [show splitFaceOrbitInv σ p q hreach hpq (some o) =
            PermOrbit.of (splitFacePerm σ p q hpq)
              (ExtDart.old (Quotient.out o)) by
                simp [splitFaceOrbitInv, ho]]
          unfold PermOrbit.of
          change
            splitFaceOrbitCode σ p q hreach hpq
                (ExtDart.old (Quotient.out o)) =
              some o
          simp [splitFaceOrbitCode, hnot, hout]

theorem splitFacePerm_orbitCount_of_reachable
    {α : Type u} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (p q : α)
    (hreach : PermReachable σ p q) (hpq : p ≠ q) :
    Nat.card (PermOrbit (splitFacePerm σ p q hpq)) =
      Nat.card (PermOrbit σ) + 1 := by
  rw [Nat.card_congr (splitFaceOrbitEquiv σ p q hreach hpq)]
  haveI : Finite (PermOrbit σ) :=
    Quotient.finite (permOrbitSetoid σ)
  rw [Finite.card_option]


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
