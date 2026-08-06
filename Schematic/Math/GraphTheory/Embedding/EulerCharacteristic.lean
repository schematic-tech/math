import Schematic.Math.GraphTheory.Embedding.WalkupPlanarity
import Schematic.Math.GraphTheory.Embedding.Counts
import Schematic.Math.GraphTheory.Embedding.HypermapComponent

/-!
Euler-characteristic inequalities for finite hypermaps.

The Walkup count equations imply the standard connected-hypermap Euler
inequality by induction on the number of darts: deleting one dart by
`WalkupE` preserves enough Euler-count structure to lift
`eulerRight ≤ eulerLeft` from the smaller hypermap.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

universe u

theorem eulerRight_le_eulerLeft (G : Hypermap.{u}) :
    G.eulerRight ≤ G.eulerLeft := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ G : Hypermap.{u}, Fintype.card G.Dart = n →
      G.eulerRight ≤ G.eulerLeft
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hcard
      by_cases hnonempty : Nonempty G.Dart
      · rcases hnonempty with ⟨z⟩
        have hsmall :
            Fintype.card (G.walkupE z).Dart < n := by
          simpa [hcard] using G.walkupE_dart_card_lt z
        have hH :
            (G.walkupE z).eulerRight ≤ (G.walkupE z).eulerLeft :=
          ih (Fintype.card (G.walkupE z).Dart) hsmall
            (G.walkupE z) rfl
        rcases Unavoidability.walkupEStepCountFormula_proved G z with
          ⟨a, b, hba, hleft, hright⟩
        omega
      · haveI : IsEmpty G.Dart := ⟨fun z => hnonempty ⟨z⟩⟩
        haveI : IsEmpty G.Component := ⟨by
          intro c
          refine Quotient.inductionOn c ?_
          intro x
          exact isEmptyElim x⟩
        haveI : IsEmpty G.EdgeOrbit := ⟨by
          intro o
          refine Quotient.inductionOn o ?_
          intro x
          exact isEmptyElim x⟩
        haveI : IsEmpty G.NodeOrbit := ⟨by
          intro o
          refine Quotient.inductionOn o ?_
          intro x
          exact isEmptyElim x⟩
        haveI : IsEmpty G.FaceOrbit := ⟨by
          intro o
          refine Quotient.inductionOn o ?_
          intro x
          exact isEmptyElim x⟩
        simp [Hypermap.eulerLeft, Hypermap.eulerRight,
          Hypermap.componentCount, Hypermap.edgeOrbitCount,
          Hypermap.nodeOrbitCount, Hypermap.faceOrbitCount]
  exact hP (Fintype.card G.Dart) G rfl

theorem evenGenus (G : Hypermap.{u}) :
    G.EvenGenus := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ G : Hypermap.{u}, Fintype.card G.Dart = n → G.EvenGenus
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro G hcard
      by_cases hnonempty : Nonempty G.Dart
      · rcases hnonempty with ⟨z⟩
        have hsmall :
            Fintype.card (G.walkupE z).Dart < n := by
          simpa [hcard] using G.walkupE_dart_card_lt z
        have hH :
            (G.walkupE z).EvenGenus :=
          ih (Fintype.card (G.walkupE z).Dart) hsmall
            (G.walkupE z) rfl
        unfold Hypermap.EvenGenus at hH
        rcases Unavoidability.walkupEStepCountFormula_proved G z with
          ⟨a, b, hba, hleft, hright⟩
        let k := a - b + (G.walkupE z).genus
        have hformula : G.eulerLeft = 2 * k + G.eulerRight := by
          omega
        have hdiff : G.eulerLeft - G.eulerRight = 2 * k := by
          omega
        unfold Hypermap.EvenGenus Hypermap.genus
        rw [hdiff]
        simpa [k, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          hformula
      · haveI : IsEmpty G.Dart := ⟨fun z => hnonempty ⟨z⟩⟩
        haveI : IsEmpty G.Component := ⟨by
          intro c
          refine Quotient.inductionOn c ?_
          intro x
          exact isEmptyElim x⟩
        haveI : IsEmpty G.EdgeOrbit := ⟨by
          intro o
          refine Quotient.inductionOn o ?_
          intro x
          exact isEmptyElim x⟩
        haveI : IsEmpty G.NodeOrbit := ⟨by
          intro o
          refine Quotient.inductionOn o ?_
          intro x
          exact isEmptyElim x⟩
        haveI : IsEmpty G.FaceOrbit := ⟨by
          intro o
          refine Quotient.inductionOn o ?_
          intro x
          exact isEmptyElim x⟩
        simp [Hypermap.EvenGenus, Hypermap.genus, Hypermap.eulerLeft,
          Hypermap.eulerRight, Hypermap.componentCount,
          Hypermap.edgeOrbitCount, Hypermap.nodeOrbitCount,
          Hypermap.faceOrbitCount]
  exact hP (Fintype.card G.Dart) G rfl

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
