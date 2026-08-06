import Mathlib.Dynamics.PeriodicPts.Lemmas
import Schematic.Math.GraphTheory.Embedding.Geometry

/-!
Finite face orbits and arity for hypermaps.

This is generic permutation and hypermap theory. It is kept below the
four-colour-specific local-configuration representation.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

/-- A finite permutation orbit can be represented by a forward iterate whose
index is strictly smaller than the minimal period. -/
theorem permReachable_exists_iterate_lt_minimalPeriod
    {α : Type u} [Fintype α] (σ : Equiv.Perm α) {x y : α}
    (hxy : PermReachable σ x y) :
    ∃ n : ℕ,
      n < Function.minimalPeriod (σ : α → α) x ∧
        (σ : α → α)^[n] x = y := by
  classical
  have hxper : x ∈ Function.periodicPts (σ : α → α) :=
    σ.injective.mem_periodicPts x
  have hpos : 0 < Function.minimalPeriod (σ : α → α) x :=
    Function.minimalPeriod_pos_of_mem_periodicPts hxper
  rcases permReachable_exists_iterate σ hxy with ⟨k, hk⟩
  refine ⟨k % Function.minimalPeriod (σ : α → α) x,
    Nat.mod_lt _ hpos, ?_⟩
  rw [Function.iterate_mod_minimalPeriod_eq]
  exact hk

/-- The custom bidirectional permutation orbit subtype is equivalent to the
minimal-period indexing type. -/
noncomputable def permReachableMinimalPeriodEquiv
    {α : Type u} [Fintype α] (σ : Equiv.Perm α) (x : α) :
    { y : α // PermReachable σ x y } ≃
      Fin (Function.minimalPeriod (σ : α → α) x) where
  toFun z := by
    classical
    let h := permReachable_exists_iterate_lt_minimalPeriod σ z.2
    exact ⟨Nat.find h, (Nat.find_spec h).1⟩
  invFun i :=
    ⟨(σ : α → α)^[i.1] x, permReachable_of_iterate_eq σ rfl⟩
  left_inv z := by
    classical
    apply Subtype.ext
    let h := permReachable_exists_iterate_lt_minimalPeriod σ z.2
    exact (Nat.find_spec h).2
  right_inv i := by
    classical
    apply Fin.ext
    let h := permReachable_exists_iterate_lt_minimalPeriod σ
      (permReachable_of_iterate_eq σ (x := x)
        (y := (σ : α → α)^[i.1] x) rfl)
    have hlt : Nat.find h < Function.minimalPeriod (σ : α → α) x :=
      (Nat.find_spec h).1
    have hiter :
        (σ : α → α)^[Nat.find h] x =
          (σ : α → α)^[i.1] x :=
      (Nat.find_spec h).2
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (f := (σ : α → α)) (x := x) hlt i.2).mp hiter

namespace Hypermap

variable (G : Hypermap)

/-- The face orbit containing a dart. -/
def FaceClass (x : G.Dart) : Type _ :=
  { y : G.Dart // PermReachable G.face x y }

instance faceClassFinite (x : G.Dart) : Finite (G.FaceClass x) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance faceClassFintype (x : G.Dart) : Fintype (G.FaceClass x) :=
  Fintype.ofFinite (G.FaceClass x)

/-- Face arity: the number of darts in the face orbit of `x`. -/
noncomputable def arity (x : G.Dart) : Nat :=
  Nat.card (G.FaceClass x)

/-- Face classes are indexed by the minimal period of the face permutation. -/
noncomputable def faceClassEquivMinimalPeriod (x : G.Dart) :
    G.FaceClass x ≃
      Fin (Function.minimalPeriod (G.face : G.Dart → G.Dart) x) :=
  permReachableMinimalPeriodEquiv G.face x

/-- The cardinal definition of face arity agrees with the usual minimal
period of the face permutation. -/
theorem arity_eq_minimalPeriod (x : G.Dart) :
    G.arity x =
      Function.minimalPeriod (G.face : G.Dart → G.Dart) x := by
  calc
    G.arity x = Fintype.card (G.FaceClass x) := by
      simp [Hypermap.arity, Nat.card_eq_fintype_card]
    _ =
        Fintype.card
          (Fin (Function.minimalPeriod (G.face : G.Dart → G.Dart) x)) :=
      Fintype.card_congr (G.faceClassEquivMinimalPeriod x)
    _ = Function.minimalPeriod (G.face : G.Dart → G.Dart) x :=
      Fintype.card_fin _

/-- Iterating around a face by its arity returns to the starting dart. -/
theorem face_iterate_arity (x : G.Dart) :
    (G.face : G.Dart → G.Dart)^[G.arity x] x = x := by
  rw [G.arity_eq_minimalPeriod x]
  exact Function.iterate_minimalPeriod
    (f := (G.face : G.Dart → G.Dart)) (x := x)

/-- Face arities are positive because every dart is periodic under the finite
face permutation. -/
theorem arity_pos (x : G.Dart) :
    0 < G.arity x := by
  rw [G.arity_eq_minimalPeriod x]
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    (G.face.injective.mem_periodicPts x)

/-- A face iterate returns to its starting dart exactly at multiples of the
face arity. -/
theorem face_iterate_eq_self_iff_arity_dvd
    {n : Nat} {x : G.Dart} :
    (G.face : G.Dart → G.Dart)^[n] x = x ↔ G.arity x ∣ n := by
  rw [G.arity_eq_minimalPeriod x]
  exact Function.isPeriodicPt_iff_minimalPeriod_dvd

/-- Any return time around a face is divisible by the face arity. -/
theorem arity_dvd_of_face_iterate_eq_self
    {n : Nat} {x : G.Dart}
    (h : (G.face : G.Dart → G.Dart)^[n] x = x) :
    G.arity x ∣ n :=
  G.face_iterate_eq_self_iff_arity_dvd.mp h

/-- Equivalent face classes have the same arity. -/
noncomputable def faceClassEquivOfReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.FaceClass x ≃ G.FaceClass y where
  toFun z := ⟨z.1, PermReachable.trans G.face
    (PermReachable.symm G.face hxy) z.2⟩
  invFun z := ⟨z.1, PermReachable.trans G.face hxy z.2⟩
  left_inv z := by
    cases z
    rfl
  right_inv z := by
    cases z
    rfl

theorem arity_eq_of_faceReachable
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    G.arity x = G.arity y :=
  Nat.card_congr (G.faceClassEquivOfReachable hxy)

/-- Mirror hypermaps invert the face permutation, so face classes are
unchanged. -/
noncomputable def mirrorFaceClassEquiv (x : G.Dart) :
    G.mirror.FaceClass x ≃ G.FaceClass x where
  toFun z := by
    refine ⟨z.1, ?_⟩
    exact (permReachable_symmPerm_iff G.face).mp
      (by simpa [Hypermap.mirror] using z.2)
  invFun z := by
    refine ⟨z.1, ?_⟩
    simpa [Hypermap.mirror] using
      ((permReachable_symmPerm_iff G.face).mpr z.2)
  left_inv z := by
    cases z
    rfl
  right_inv z := by
    cases z
    rfl

theorem arity_mirror (x : G.Dart) :
    G.mirror.arity x = G.arity x :=
  Nat.card_congr (G.mirrorFaceClassEquiv x)

/-- The disjoint union of all face classes, indexed by face orbits, is the
dart type itself. -/
noncomputable def faceClassSigmaEquivDart :
    (Sigma fun o : G.FaceOrbit => G.FaceClass (Quotient.out o)) ≃ G.Dart where
  toFun p := p.2.1
  invFun x :=
    ⟨PermOrbit.of G.face x,
      ⟨x, Quotient.exact (Quotient.out_eq (PermOrbit.of G.face x))⟩⟩
  left_inv p := by
    rcases p with ⟨o, y, hy⟩
    dsimp
    have hout : PermOrbit.of G.face (Quotient.out o) = o :=
      Quotient.out_eq o
    have hyorbit : PermOrbit.of G.face (Quotient.out o) =
        PermOrbit.of G.face y :=
      PermOrbit.of_eq_of G.face hy
    have ho : PermOrbit.of G.face y = o := hyorbit.symm.trans hout
    cases ho
    simp
  right_inv x := rfl

theorem sum_arity_faceOrbit_eq_card_dart :
    (∑ o : G.FaceOrbit, G.arity (Quotient.out o)) = Fintype.card G.Dart := by
  change
    (∑ o : G.FaceOrbit, Nat.card (G.FaceClass (Quotient.out o))) =
      Fintype.card G.Dart
  simp_rw [Nat.card_eq_fintype_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr G.faceClassSigmaEquivDart

theorem arity_face (x : G.Dart) :
    G.arity (G.face x) = G.arity x :=
  (G.arity_eq_of_faceReachable (PermReachable.forward G.face x)).symm

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
