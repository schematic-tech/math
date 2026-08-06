import Schematic.Math.GraphTheory.Planarity.Basic

/-!
Menger/linkage and rerouting tools used in the 3- and 4-separation cases.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def vertexTriple (x y z : V) : Fin 3 -> V
  | 0 => x
  | 1 => y
  | 2 => z

theorem vertexTriple_zero (x y z : V) :
    vertexTriple x y z 0 = x := rfl

theorem vertexTriple_one (x y z : V) :
    vertexTriple x y z 1 = y := rfl

theorem vertexTriple_two (x y z : V) :
    vertexTriple x y z 2 = z := rfl

theorem vertexTriple_injective {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (vertexTriple x y z) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [vertexTriple] at hij ⊢
  · exact False.elim (hxy hij)
  · exact False.elim (hxz hij)
  · exact False.elim (hxy hij.symm)
  · exact False.elim (hyz hij)
  · exact False.elim (hxz hij.symm)
  · exact False.elim (hyz hij.symm)

theorem vertexTriple_range {x y z : V} :
    Set.range (vertexTriple x y z) = ({x, y, z} : Set V) := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [vertexTriple]
  · intro hv
    simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Choose an ordered injective triple inside a set of cardinality at least
three.

This is the finite selection step used by the GM IX `(2.2)` set-to-boundary
linkage argument: after a component is known to contain at least three society
boundary vertices, we need an ordered `Fin 3` triple of distinct boundary
targets. -/
theorem exists_injective_fin3_mem_of_ncard_ge_three
    {A : Set V} (hA : 3 <= A.ncard) :
    Exists fun boundary : Fin 3 -> V =>
      Function.Injective boundary ∧ forall i : Fin 3, boundary i ∈ A := by
  classical
  obtain ⟨B, hBA, hBcard⟩ :=
    Set.exists_subset_card_eq (s := A) hA
  rcases Set.ncard_eq_three.mp hBcard with
    ⟨x, y, z, hxy, hxz, hyz, hB⟩
  refine ⟨vertexTriple x y z, vertexTriple_injective hxy hxz hyz, ?_⟩
  intro i
  apply hBA
  have hi : vertexTriple x y z i ∈ ({x, y, z} : Set V) := by
    fin_cases i <;> simp [vertexTriple]
  simpa [hB] using hi

theorem vertexTriple_equiv_range (x y z : V) (e : Fin 3 ≃ Fin 3) :
    Set.range (fun i : Fin 3 => vertexTriple x y z (e i)) =
      ({x, y, z} : Set V) := by
  rw [← vertexTriple_range (x := x) (y := y) (z := z)]
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

theorem vertexTriple_equiv_set (x y z : V) (e : Fin 3 ≃ Fin 3) :
    ({vertexTriple x y z (e 0),
      vertexTriple x y z (e 1),
      vertexTriple x y z (e 2)} : Set V) =
      ({x, y, z} : Set V) := by
  rw [← vertexTriple_equiv_range x y z e]
  ext v
  constructor
  · intro hv
    simp [Set.mem_insert_iff] at hv
    rcases hv with hv | hv | hv
    · exact ⟨0, hv.symm⟩
    · exact ⟨1, hv.symm⟩
    · exact ⟨2, hv.symm⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [Set.mem_insert_iff]

theorem vertexTriple_equiv_zero_ne_one {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Fin 3 ≃ Fin 3) :
    vertexTriple x y z (e 0) ≠ vertexTriple x y z (e 1) := by
  intro h
  have hinj := vertexTriple_injective hxy hxz hyz
  have h01 : (0 : Fin 3) = 1 := e.injective (hinj h)
  exact Fin.zero_ne_one h01

theorem vertexTriple_equiv_zero_ne_two {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Fin 3 ≃ Fin 3) :
    vertexTriple x y z (e 0) ≠ vertexTriple x y z (e 2) := by
  intro h
  have hinj := vertexTriple_injective hxy hxz hyz
  have h02 : (0 : Fin 3) = 2 := e.injective (hinj h)
  exact (by decide : (0 : Fin 3) ≠ 2) h02

theorem vertexTriple_equiv_one_ne_two {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Fin 3 ≃ Fin 3) :
    vertexTriple x y z (e 1) ≠ vertexTriple x y z (e 2) := by
  intro h
  have hinj := vertexTriple_injective hxy hxz hyz
  have h12 : (1 : Fin 3) = 2 := e.injective (hinj h)
  exact (by decide : (1 : Fin 3) ≠ 2) h12

theorem vertexTriple_equiv_pairwise_ne {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : Fin 3 ≃ Fin 3) :
    vertexTriple x y z (e 0) ≠ vertexTriple x y z (e 1) ∧
      vertexTriple x y z (e 0) ≠ vertexTriple x y z (e 2) ∧
        vertexTriple x y z (e 1) ≠ vertexTriple x y z (e 2) :=
  ⟨vertexTriple_equiv_zero_ne_one hxy hxz hyz e,
    vertexTriple_equiv_zero_ne_two hxy hxz hyz e,
    vertexTriple_equiv_one_ne_two hxy hxz hyz e⟩

theorem pairwise_ne_of_triple_set_eq {X Y Z x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hset : ({X, Y, Z} : Set V) = ({x, y, z} : Set V)) :
    X ≠ Y ∧ X ≠ Z ∧ Y ≠ Z := by
  classical
  have htarget_card : ({x, y, z} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  have hsource_card : ({X, Y, Z} : Set V).ncard = 3 := by
    rw [hset, htarget_card]
  have hcard_pair_le (a b : V) : ({a, b} : Set V).ncard <= 2 := by
    calc
      ({a, b} : Set V).ncard <= ({b} : Set V).ncard + 1 := by
        simpa using Set.ncard_insert_le a ({b} : Set V)
      _ = 2 := by simp
  have hXY : X ≠ Y := by
    intro h
    have hsub : ({X, Y, Z} : Set V) ⊆ ({X, Z} : Set V) := by
      intro a ha
      simp [Set.mem_insert_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inl h.symm
      · exact Or.inr rfl
    have hle : ({X, Y, Z} : Set V).ncard <= 2 :=
      le_trans (Set.ncard_le_ncard hsub) (hcard_pair_le X Z)
    omega
  have hXZ : X ≠ Z := by
    intro h
    have hsub : ({X, Y, Z} : Set V) ⊆ ({X, Y} : Set V) := by
      intro a ha
      simp [Set.mem_insert_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inl h.symm
    have hle : ({X, Y, Z} : Set V).ncard <= 2 :=
      le_trans (Set.ncard_le_ncard hsub) (hcard_pair_le X Y)
    omega
  have hYZ : Y ≠ Z := by
    intro h
    have hsub : ({X, Y, Z} : Set V) ⊆ ({X, Y} : Set V) := by
      intro a ha
      simp [Set.mem_insert_iff] at ha ⊢
      rcases ha with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr h.symm
    have hle : ({X, Y, Z} : Set V).ncard <= 2 :=
      le_trans (Set.ncard_le_ncard hsub) (hcard_pair_le X Y)
    omega
  exact ⟨hXY, hXZ, hYZ⟩

theorem vertexTriple_some_apply (x y z : V) (i : Fin 3) :
    vertexTriple (some x) (some y) (some z) i =
      some (vertexTriple x y z i) := by
  fin_cases i <;> rfl


end Schematic.Math.GraphTheory
