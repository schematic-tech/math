import Schematic.Math.GraphTheory.Embedding.Geometry
import Schematic.Math.GraphTheory.Embedding.Walkup

/-!
Counting, precubicity, and genus preliminaries for Walkup geometry.
-/

namespace Schematic.Math.GraphTheory
namespace FourColor
namespace Hypermap

universe u

variable (G : Hypermap.{u})

theorem walkupE_precubic
    (hG : G.Precubic) (z : G.Dart) :
    (G.walkupE z).Precubic := by
  intro x
  simpa [walkupE_node, walkupSkipNode] using
    (PermSkip.skip_periodAtMostThree G.node hG (z := z) x)

theorem walkupE_walkupE_precubic
    (hG : G.Precubic) {z : G.Dart} (u : (G.walkupE z).Dart) :
    ((G.walkupE z).walkupE u).Precubic :=
  (G.walkupE z).walkupE_precubic (G.walkupE_precubic hG z) u

theorem walkupE_eulerPlanar_of_genus_le
    {z : G.Dart}
    (hle : (G.walkupE z).genus ≤ G.genus) :
    G.EulerPlanar → (G.walkupE z).EulerPlanar := by
  intro hplanar
  unfold EulerPlanar at *
  omega

theorem walkupE_walkupE_eulerPlanar_of_genus_le
    {z : G.Dart} {u : (G.walkupE z).Dart}
    (hle₁ : (G.walkupE z).genus ≤ G.genus)
    (hle₂ : ((G.walkupE z).walkupE u).genus ≤
      (G.walkupE z).genus) :
    G.EulerPlanar → ((G.walkupE z).walkupE u).EulerPlanar := by
  intro hplanar
  unfold EulerPlanar at *
  omega

theorem genus_le_of_eulerDiff_le
    (H : Hypermap.{u})
    (hle : H.eulerLeft - H.eulerRight ≤ G.eulerLeft - G.eulerRight) :
    H.genus ≤ G.genus := by
  unfold genus
  exact Nat.div_le_div_right hle

theorem eulerDiff_le_of_walkup_step_counts
    (H : Hypermap.{u}) {a b : Nat}
    (hba : b ≤ a)
    (hleft : 2 * a + H.eulerLeft = G.eulerLeft + 1)
    (hright : 2 * b + H.eulerRight = G.eulerRight + 1) :
    H.eulerLeft - H.eulerRight ≤ G.eulerLeft - G.eulerRight := by
  omega

theorem genus_le_of_walkup_step_counts
    (H : Hypermap.{u}) {a b : Nat}
    (hba : b ≤ a)
    (hleft : 2 * a + H.eulerLeft = G.eulerLeft + 1)
    (hright : 2 * b + H.eulerRight = G.eulerRight + 1) :
    H.genus ≤ G.genus :=
  G.genus_le_of_eulerDiff_le H
    (G.eulerDiff_le_of_walkup_step_counts H hba hleft hright)

theorem permOrbit_count_eq_one_of_forall_reachable
    {α : Type u} (σ : Equiv.Perm α) (x₀ : α)
    (hreach : ∀ x y : α, PermReachable σ x y) :
    Nat.card (PermOrbit σ) = 1 := by
  letI : Nonempty (PermOrbit σ) := ⟨PermOrbit.of σ x₀⟩
  letI : Subsingleton (PermOrbit σ) := ⟨by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact Quot.sound (hreach x y)⟩
  exact Nat.card_unique

theorem componentCount_eq_one_of_forall_reachable
    (x₀ : G.Dart)
    (hreach : ∀ x y : G.Dart, G.Reachable x y) :
    G.componentCount = 1 := by
  unfold componentCount
  letI : Nonempty G.Component := ⟨G.componentOf x₀⟩
  letI : Subsingleton G.Component := ⟨by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro x y
    exact Quot.sound (hreach x y)⟩
  exact Nat.card_unique

theorem permReachable_of_three_cycle_cover
    {α : Type u} (σ : Equiv.Perm α) {x y z : α}
    (hcover : ∀ a : α, a = x ∨ a = y ∨ a = z)
    (hxy : σ x = y) (hyz : σ y = z) (hzx : σ z = x) :
    ∀ a b : α, PermReachable σ a b := by
  have hxyR : PermReachable σ x y := by
    simpa [hxy] using PermReachable.forward σ x
  have hyzR : PermReachable σ y z := by
    simpa [hyz] using PermReachable.forward σ y
  have hzxR : PermReachable σ z x := by
    simpa [hzx] using PermReachable.forward σ z
  have hxzR : PermReachable σ x z :=
    PermReachable.trans σ hxyR hyzR
  have hyxR : PermReachable σ y x :=
    PermReachable.trans σ hyzR hzxR
  have hzyR : PermReachable σ z y :=
    PermReachable.trans σ hzxR hxyR
  intro a b
  rcases hcover a with rfl | rfl | rfl
  · rcases hcover b with rfl | rfl | rfl
    · exact PermReachable.refl σ _
    · exact hxyR
    · exact hxzR
  · rcases hcover b with rfl | rfl | rfl
    · exact hyxR
    · exact PermReachable.refl σ _
    · exact hyzR
  · rcases hcover b with rfl | rfl | rfl
    · exact hzxR
    · exact hzyR
    · exact PermReachable.refl σ _

end Hypermap
end FourColor
end Schematic.Math.GraphTheory

