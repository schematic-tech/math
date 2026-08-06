import Schematic.Math.GraphTheory.Embedding.RotationSystemDeletion

/-!
First-return restriction of a finite permutation to a predicate.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace PermSkipPredicate

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {keep : α → Prop} [DecidablePred keep]

omit [DecidableEq α] [DecidablePred keep] in
/-- A surviving point of a finite permutation returns to the surviving
predicate after a positive number of steps. -/
theorem firstReturn_exists
    (σ : Equiv.Perm α) (x : {x : α // keep x}) :
    ∃ n : Nat, keep (((σ : α → α)^[n + 1]) x.1) := by
  have hxPeriodic :
      x.1 ∈ Function.periodicPts (σ : α → α) :=
    σ.injective.mem_periodicPts x.1
  have hperiodPos :
      0 < Function.minimalPeriod (σ : α → α) x.1 :=
    Function.minimalPeriod_pos_of_mem_periodicPts hxPeriodic
  refine ⟨(Function.minimalPeriod (σ : α → α) x.1).pred, ?_⟩
  have hsucc :
      (Function.minimalPeriod (σ : α → α) x.1).pred + 1 =
        Function.minimalPeriod (σ : α → α) x.1 := by
    exact Nat.succ_pred_eq_of_pos hperiodPos
  rw [hsucc, Function.iterate_minimalPeriod]
  exact x.2

/-- The number of skipped points before the first positive return to
`keep`. This is Coq `ex_minn (skip_proof ...)`. -/
noncomputable def firstReturnIndex
    (σ : Equiv.Perm α) (x : {x : α // keep x}) : Nat :=
  Nat.find (firstReturn_exists σ x)

omit [DecidableEq α] in
theorem firstReturnIndex_spec
    (σ : Equiv.Perm α) (x : {x : α // keep x}) :
    keep (((σ : α → α)^[(firstReturnIndex σ x) + 1]) x.1) := by
  exact Nat.find_spec (firstReturn_exists σ x)

omit [DecidableEq α] in
theorem firstReturnIndex_min
    (σ : Equiv.Perm α) (x : {x : α // keep x})
    {n : Nat}
    (hn : keep (((σ : α → α)^[n + 1]) x.1)) :
    firstReturnIndex σ x ≤ n := by
  exact Nat.find_min' (firstReturn_exists σ x) hn

/-- The first positive iterate of `σ` that lies in `keep`. -/
noncomputable def firstReturn
    (σ : Equiv.Perm α) :
    {x : α // keep x} → {x : α // keep x} :=
  fun x =>
    ⟨((σ : α → α)^[(firstReturnIndex σ x) + 1]) x.1,
      firstReturnIndex_spec σ x⟩

omit [DecidableEq α] in
@[simp]
theorem firstReturn_val
    (σ : Equiv.Perm α) (x : {x : α // keep x}) :
    (firstReturn σ x).1 =
      ((σ : α → α)^[(firstReturnIndex σ x) + 1]) x.1 :=
  rfl

theorem firstReturn_injective
    (σ : Equiv.Perm α) :
    Function.Injective (firstReturn (keep := keep) σ) := by
  intro x y hxy
  let n := firstReturnIndex σ x
  let m := firstReturnIndex σ y
  have hiter :
      ((σ : α → α)^[n + 1]) x.1 =
        ((σ : α → α)^[m + 1]) y.1 := by
    exact congrArg Subtype.val hxy
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · let k := m - (n + 1)
    have hexponent : (n + 1) + (k + 1) = m + 1 := by
      dsimp [k]
      omega
    have hval :
        x.1 = ((σ : α → α)^[k + 1]) y.1 := by
      apply (σ.injective.iterate (n + 1))
      calc
        ((σ : α → α)^[n + 1]) x.1 =
            ((σ : α → α)^[m + 1]) y.1 := hiter
        _ = ((σ : α → α)^[(n + 1) + (k + 1)]) y.1 := by
          rw [hexponent]
        _ = ((σ : α → α)^[n + 1])
              (((σ : α → α)^[k + 1]) y.1) := by
          rw [Function.iterate_add_apply]
    have hkKeep :
        keep (((σ : α → α)^[k + 1]) y.1) := by
      rw [← hval]
      exact x.2
    have hminimal : m ≤ k := by
      exact firstReturnIndex_min σ y hkKeep
    dsimp [k] at hminimal
    omega
  · apply Subtype.ext
    apply (σ.injective.iterate (n + 1))
    simpa [hnm] using hiter
  · let k := n - (m + 1)
    have hexponent : (m + 1) + (k + 1) = n + 1 := by
      dsimp [k]
      omega
    have hval :
        y.1 = ((σ : α → α)^[k + 1]) x.1 := by
      apply (σ.injective.iterate (m + 1))
      calc
        ((σ : α → α)^[m + 1]) y.1 =
            ((σ : α → α)^[n + 1]) x.1 := hiter.symm
        _ = ((σ : α → α)^[(m + 1) + (k + 1)]) x.1 := by
          rw [hexponent]
        _ = ((σ : α → α)^[m + 1])
              (((σ : α → α)^[k + 1]) x.1) := by
          rw [Function.iterate_add_apply]
    have hkKeep :
        keep (((σ : α → α)^[k + 1]) x.1) := by
      rw [← hval]
      exact y.2
    have hminimal : n ≤ k := by
      exact firstReturnIndex_min σ x hkKeep
    dsimp [k] at hminimal
    omega

/-- Coq `skip p f`: restrict a finite permutation to a predicate by taking
the first positive iterate that survives. -/
noncomputable def skip
    (σ : Equiv.Perm α) :
    Equiv.Perm {x : α // keep x} :=
  Equiv.ofBijective (firstReturn σ)
    ⟨firstReturn_injective σ,
      Finite.surjective_of_injective (firstReturn_injective σ)⟩

@[simp]
theorem skip_apply_val
    (σ : Equiv.Perm α) (x : {x : α // keep x}) :
    (skip σ x).1 =
      ((σ : α → α)^[(firstReturnIndex σ x) + 1]) x.1 := by
  change (firstReturn σ x).1 = _
  rfl

theorem skip_eq_of_first
    (σ : Equiv.Perm α) (x : {x : α // keep x})
    {n : Nat}
    (hn : keep (((σ : α → α)^[n + 1]) x.1))
    (hmin :
      ∀ m : Nat,
        keep (((σ : α → α)^[m + 1]) x.1) → n ≤ m) :
    (skip σ x).1 = ((σ : α → α)^[n + 1]) x.1 := by
  rw [skip_apply_val]
  have hindex : firstReturnIndex σ x = n := by
    apply Nat.le_antisymm
    · exact firstReturnIndex_min σ x hn
    · exact hmin _ (firstReturnIndex_spec σ x)
  rw [hindex]

theorem skip_permReachable
    (σ : Equiv.Perm α) (x : {x : α // keep x}) :
    PermReachable σ x.1 (skip σ x).1 := by
  rw [skip_apply_val]
  exact permReachable_of_iterate_eq σ rfl

/-- Positive-return witness for a point that need not itself survive. -/
def HasReturn
    (σ : Equiv.Perm α) (x : α) : Prop :=
  ∃ n : Nat, keep (((σ : α → α)^[n + 1]) x)

/-- Coq's total `skip p f`: if the orbit reaches `keep`, take its first
positive such iterate; otherwise leave the point fixed. -/
noncomputable def skipValue
    (σ : Equiv.Perm α) (x : α) : α := by
  classical
  exact
    if h : HasReturn (keep := keep) σ x then
      ((σ : α → α)^[(Nat.find h) + 1]) x
    else
      x

omit [Fintype α] [DecidableEq α] in
theorem skipValue_spec
    (σ : Equiv.Perm α) (x : α)
    (h : HasReturn (keep := keep) σ x) :
    keep (skipValue (keep := keep) σ x) := by
  rw [skipValue, dif_pos h]
  exact Nat.find_spec h

omit [Fintype α] [DecidableEq α] in
theorem skipValue_eq_of_first
    (σ : Equiv.Perm α) (x : α)
    (hreturn : HasReturn (keep := keep) σ x)
    {n : Nat}
    (hn : keep (((σ : α → α)^[n + 1]) x))
    (hmin :
      ∀ m : Nat,
        keep (((σ : α → α)^[m + 1]) x) → n ≤ m) :
    skipValue (keep := keep) σ x =
      ((σ : α → α)^[n + 1]) x := by
  rw [skipValue, dif_pos hreturn]
  have hindex : Nat.find hreturn = n := by
    apply Nat.le_antisymm
    · exact Nat.find_min' hreturn hn
    · exact hmin _ (Nat.find_spec hreturn)
  rw [hindex]

omit [Fintype α] [DecidableEq α] in
theorem skipValue_of_next_mem
    (σ : Equiv.Perm α) (x : α)
    (hnext : keep (σ x)) :
    skipValue (keep := keep) σ x = σ x := by
  apply skipValue_eq_of_first (n := 0) σ x
    ⟨0, by simpa using hnext⟩
  · simpa using hnext
  · intro m _
    omega

omit [Fintype α] [DecidableEq α] [DecidablePred keep] in
theorem hasReturn_tail
    (σ : Equiv.Perm α) (x : α)
    (hreturn : HasReturn (keep := keep) σ x)
    (hnext : ¬ keep (σ x)) :
    HasReturn (keep := keep) σ (σ x) := by
  rcases hreturn with ⟨n, hn⟩
  cases n with
  | zero =>
      exact False.elim (hnext (by simpa using hn))
  | succ m =>
      refine ⟨m, ?_⟩
      simpa [Function.iterate_succ_apply] using hn

omit [Fintype α] [DecidableEq α] in
theorem find_hasReturn_tail_add_one
    (σ : Equiv.Perm α) (x : α)
    (hreturn : HasReturn (keep := keep) σ x)
    (hnext : ¬ keep (σ x)) :
    Nat.find (hasReturn_tail σ x hreturn hnext) + 1 =
      Nat.find hreturn := by
  let htail := hasReturn_tail σ x hreturn hnext
  let m := Nat.find htail
  have hm :
      keep (((σ : α → α)^[m + 1]) (σ x)) :=
    Nat.find_spec htail
  have horig :
      keep (((σ : α → α)^[(m + 1) + 1]) x) := by
    simpa [Function.iterate_succ_apply] using hm
  have hnm : Nat.find hreturn ≤ m + 1 :=
    Nat.find_min' hreturn horig
  have hn :
      keep (((σ : α → α)^[(Nat.find hreturn) + 1]) x) :=
    Nat.find_spec hreturn
  cases hfind : Nat.find hreturn with
  | zero =>
      rw [hfind] at hn
      exact False.elim (hnext (by simpa using hn))
  | succ k =>
      have htailAtK :
          keep (((σ : α → α)^[k + 1]) (σ x)) := by
        rw [hfind] at hn
        simpa [Function.iterate_succ_apply] using hn
      have hmk : m ≤ k :=
        Nat.find_min' htail htailAtK
      have hkm : k ≤ m := by
        rw [hfind] at hnm
        omega
      have hmkEq : m = k := Nat.le_antisymm hmk hkm
      have hfindTail :
          Nat.find (hasReturn_tail σ x hreturn hnext) = m := by
        apply congrArg Nat.find
        exact Subsingleton.elim _ _
      exact (congrArg Nat.succ hfindTail).trans
        (congrArg Nat.succ hmkEq)

omit [Fintype α] [DecidableEq α] in
/-- Coq `skip_first`: when the immediate successor is rejected, starting
before or at that rejected successor has the same first surviving return. -/
theorem skipValue_first
    (σ : Equiv.Perm α) (x : α)
    (hreturn : HasReturn (keep := keep) σ x)
    (hnext : ¬ keep (σ x)) :
    skipValue (keep := keep) σ x =
      skipValue (keep := keep) σ (σ x) := by
  let htail := hasReturn_tail σ x hreturn hnext
  let m := Nat.find htail
  have hm :
      keep (((σ : α → α)^[m + 1]) (σ x)) :=
    Nat.find_spec htail
  have hcand :
      keep (((σ : α → α)^[(m + 1) + 1]) x) := by
    simpa [Function.iterate_succ_apply] using hm
  have hfirst :
      skipValue (keep := keep) σ x =
        ((σ : α → α)^[(m + 1) + 1]) x := by
    apply skipValue_eq_of_first σ x hreturn hcand
    intro k hk
    cases k with
    | zero =>
        exact False.elim (hnext (by simpa using hk))
    | succ l =>
        have htailk :
            keep (((σ : α → α)^[l + 1]) (σ x)) := by
          simpa [Function.iterate_succ_apply] using hk
        have hml : m ≤ l := Nat.find_min' htail htailk
        omega
  have htailValue :
      skipValue (keep := keep) σ (σ x) =
        ((σ : α → α)^[m + 1]) (σ x) := by
    rw [skipValue, dif_pos htail]
  rw [hfirst, htailValue]
  simp [Function.iterate_succ_apply]

theorem skipValue_eq_skip
    (σ : Equiv.Perm α) (x : {x : α // keep x}) :
    skipValue (keep := keep) σ x.1 = (skip σ x).1 := by
  have hreturn : HasReturn (keep := keep) σ x.1 :=
    firstReturn_exists σ x
  rw [skipValue, dif_pos hreturn]
  rfl

omit [DecidableEq α] [DecidablePred keep] in
theorem hasReturn_of_permReachable
    (σ : Equiv.Perm α) {x y : α}
    (hy : keep y)
    (hxy : PermReachable σ x y) :
    HasReturn (keep := keep) σ x := by
  rcases permReachable_exists_iterate σ hxy with ⟨n, hn⟩
  cases n with
  | zero =>
      have hxyEq : x = y := by simpa using hn
      let xs : {x : α // keep x} := ⟨x, hxyEq.symm ▸ hy⟩
      exact firstReturn_exists σ xs
  | succ m =>
      exact ⟨m, by simpa using hn.symm ▸ hy⟩

/-- Coq `skip_skip1`: deleting one rejected point first and then skipping all
other rejected points gives the same first-return map as skipping them in one
step. -/
theorem skipValue_skipPoint
    (σ : Equiv.Perm α) (z : α)
    (hz : ¬ keep z)
    {x : α} (hxz : x ≠ z)
    (hreturn : HasReturn (keep := keep) σ x) :
    skipValue (keep := keep) σ x =
      (skipValue
        (keep := fun w : DeletedPoint z => keep w.1)
        (PermSkip.skip σ z) (⟨x, hxz⟩ : DeletedPoint z)).1 := by
  let τ : Equiv.Perm (DeletedPoint z) := PermSkip.skip σ z
  let keep' : DeletedPoint z → Prop := fun w => keep w.1
  have nestedReturn
      (w : DeletedPoint z)
      (hw : HasReturn (keep := keep) σ w.1) :
      HasReturn (keep := keep') τ w := by
    rcases hw with ⟨r, hr⟩
    let y : α := ((σ : α → α)^[r + 1]) w.1
    have hy : keep y := hr
    have hyz : y ≠ z := by
      intro hyzEq
      exact hz (hyzEq ▸ hy)
    let yD : DeletedPoint z := ⟨y, hyz⟩
    have hreach :
        PermReachable τ w yD := by
      exact
        PermSkip.skip_permReachable_of_iterate_eq σ
          w.2 hyz (r + 1) rfl
    exact hasReturn_of_permReachable τ hy hreach
  let xD : DeletedPoint z := ⟨x, hxz⟩
  let hNested := nestedReturn xD hreturn
  have aux :
      ∀ n : Nat, ∀ w : DeletedPoint z,
        ∀ hw : HasReturn (keep := keep) σ w.1,
        ∀ hwNested : HasReturn (keep := keep') τ w,
          Nat.find hwNested = n →
            skipValue (keep := keep) σ w.1 =
              (skipValue (keep := keep') τ w).1 := by
    intro n
    induction n with
    | zero =>
        intro w hw hwNested hfind
        have hkeepNext : keep' (τ w) := by
          have hspec := Nat.find_spec hwNested
          rw [hfind] at hspec
          simpa using hspec
        have hnested :
            skipValue (keep := keep') τ w = τ w := by
          rw [skipValue, dif_pos hwNested, hfind]
          rfl
        by_cases hstep : σ w.1 = z
        · have hτval : (τ w).1 = σ z := by
            exact PermSkip.skip_apply_of_apply_eq σ w hstep
          have hfirstRejected : ¬ keep (σ w.1) := by
            rw [hstep]
            exact hz
          have hzReturn :
              HasReturn (keep := keep) σ z := by
            simpa [hstep] using
              hasReturn_tail σ w.1 hw hfirstRejected
          have hσz : keep (σ z) := by
            simpa [keep', hτval] using hkeepNext
          calc
            skipValue (keep := keep) σ w.1 =
                skipValue (keep := keep) σ (σ w.1) :=
              skipValue_first σ w.1 hw hfirstRejected
            _ = skipValue (keep := keep) σ z := by rw [hstep]
            _ = σ z := skipValue_of_next_mem σ z hσz
            _ = (τ w).1 := hτval.symm
            _ = (skipValue (keep := keep') τ w).1 := by rw [hnested]
        · have hτval : (τ w).1 = σ w.1 :=
            PermSkip.skip_apply_of_apply_ne σ w hstep
          have hσw : keep (σ w.1) := by
            simpa [keep', hτval] using hkeepNext
          calc
            skipValue (keep := keep) σ w.1 = σ w.1 :=
              skipValue_of_next_mem σ w.1 hσw
            _ = (τ w).1 := hτval.symm
            _ = (skipValue (keep := keep') τ w).1 := by rw [hnested]
    | succ n ih =>
        intro w hw hwNested hfind
        have hnextRejected : ¬ keep' (τ w) := by
          intro hnext
          have hzero : Nat.find hwNested ≤ 0 :=
            Nat.find_min' hwNested (by simpa using hnext)
          rw [hfind] at hzero
          omega
        let hwNestedTail :=
          hasReturn_tail τ w hwNested hnextRejected
        have hfindTail : Nat.find hwNestedTail = n := by
          have hadd :=
            find_hasReturn_tail_add_one τ w hwNested hnextRejected
          rw [hfind] at hadd
          omega
        by_cases hstep : σ w.1 = z
        · have hτval : (τ w).1 = σ z :=
            PermSkip.skip_apply_of_apply_eq σ w hstep
          have hfirstRejected : ¬ keep (σ w.1) := by
            rw [hstep]
            exact hz
          have hzReturn :
              HasReturn (keep := keep) σ z := by
            simpa [hstep] using
              hasReturn_tail σ w.1 hw hfirstRejected
          have hsecondRejected : ¬ keep (σ z) := by
            simpa [keep', hτval] using hnextRejected
          have hnextReturn :
              HasReturn (keep := keep) σ (τ w).1 := by
            rw [hτval]
            exact hasReturn_tail σ z hzReturn hsecondRejected
          calc
            skipValue (keep := keep) σ w.1 =
                skipValue (keep := keep) σ (σ w.1) :=
              skipValue_first σ w.1 hw hfirstRejected
            _ = skipValue (keep := keep) σ z := by rw [hstep]
            _ = skipValue (keep := keep) σ (σ z) :=
              skipValue_first σ z hzReturn hsecondRejected
            _ = skipValue (keep := keep) σ (τ w).1 := by rw [hτval]
            _ = (skipValue (keep := keep') τ (τ w)).1 :=
              ih (τ w) hnextReturn hwNestedTail hfindTail
            _ = (skipValue (keep := keep') τ w).1 := by
              exact congrArg Subtype.val
                (skipValue_first τ w hwNested hnextRejected).symm
        · have hτval : (τ w).1 = σ w.1 :=
            PermSkip.skip_apply_of_apply_ne σ w hstep
          have hfirstRejected : ¬ keep (σ w.1) := by
            simpa [keep', hτval] using hnextRejected
          have hnextReturn :
              HasReturn (keep := keep) σ (τ w).1 := by
            rw [hτval]
            exact hasReturn_tail σ w.1 hw hfirstRejected
          calc
            skipValue (keep := keep) σ w.1 =
                skipValue (keep := keep) σ (σ w.1) :=
              skipValue_first σ w.1 hw hfirstRejected
            _ = skipValue (keep := keep) σ (τ w).1 := by rw [hτval]
            _ = (skipValue (keep := keep') τ (τ w)).1 :=
              ih (τ w) hnextReturn hwNestedTail hfindTail
            _ = (skipValue (keep := keep') τ w).1 := by
              exact congrArg Subtype.val
                (skipValue_first τ w hwNested hnextRejected).symm
  exact aux (Nat.find hNested) xD hreturn hNested rfl

theorem skip_skipPoint_val
    (σ : Equiv.Perm α) (z : α)
    (hz : ¬ keep z)
    (x : {x : α // keep x}) :
    let xD : DeletedPoint z := ⟨x.1, fun hxz => hz (hxz ▸ x.2)⟩
    let keep' : DeletedPoint z → Prop := fun w => keep w.1
    (skip σ x).1 =
      (skip (keep := keep') (PermSkip.skip σ z)
        (⟨xD, x.2⟩ : {w : DeletedPoint z // keep' w})).1.1 := by
  dsimp
  have hxz : x.1 ≠ z := fun hxz => hz (hxz ▸ x.2)
  have hreturn : HasReturn (keep := keep) σ x.1 :=
    firstReturn_exists σ x
  rw [← skipValue_eq_skip σ x]
  rw [skipValue_skipPoint σ z hz hxz hreturn]
  let xD : DeletedPoint z := ⟨x.1, hxz⟩
  let xKeep : {w : DeletedPoint z // keep w.1} := ⟨xD, x.2⟩
  exact congrArg Subtype.val
    (skipValue_eq_skip (keep := fun w : DeletedPoint z => keep w.1)
      (PermSkip.skip σ z) xKeep)

theorem skip_apply_of_next_mem
    (σ : Equiv.Perm α) (x : {x : α // keep x})
    (hnext : keep (σ x.1)) :
    (skip σ x).1 = σ x.1 := by
  rw [← skipValue_eq_skip σ x]
  exact skipValue_of_next_mem σ x.1 hnext

end PermSkipPredicate

end FourColor

end Schematic.Math.GraphTheory

