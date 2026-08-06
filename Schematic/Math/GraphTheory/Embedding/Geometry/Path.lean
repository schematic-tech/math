import Schematic.Math.GraphTheory.Embedding.Geometry.List
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

namespace List

/-- A finite path represented by the successive vertices after its source. -/
def RelPath {α : Type _} (R : α → α → Prop) (x : α) : List α → Prop
  | [] => True
  | y :: p => R x y ∧ RelPath R y p

namespace RelPath

variable {α : Type _} {R S : α → α → Prop}

@[simp]
theorem nil (x : α) : List.RelPath R x [] := by
  trivial

@[simp]
theorem cons (x y : α) (p : List α) :
    List.RelPath R x (y :: p) ↔ R x y ∧ List.RelPath R y p := by
  rfl

theorem iff_isChain {x : α} {p : List α} :
    List.RelPath R x p ↔ List.IsChain R (x :: p) := by
  induction p generalizing x with
  | nil => simp [List.RelPath]
  | cons y p ih => rw [List.RelPath.cons, List.isChain_cons_cons, ih]

theorem imp
    (hRS : ∀ ⦃x y⦄, R x y → S x y)
    {x : α} {p : List α}
    (hp : List.RelPath R x p) :
    List.RelPath S x p := by
  induction p generalizing x with
  | nil => trivial
  | cons y p ih => exact ⟨hRS hp.1, ih hp.2⟩

theorem snoc
    {x y z : α} {p : List α}
    (hp : List.RelPath R x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : R y z) :
    List.RelPath R x (p ++ [z]) := by
  induction p generalizing x with
  | nil =>
      simp [List.RelPath, List.getLastD] at hp hlast ⊢
      subst y
      exact hyz
  | cons w p ih =>
      have hlastTail : (w :: p).getLastD w = y := by
        simpa [List.getLastD] using hlast
      exact ⟨hp.1, ih hp.2 hlastTail⟩

theorem append
    {x y : α} {p q : List α}
    (hp : List.RelPath R x p)
    (hlast : (x :: p).getLastD x = y)
    (hq : List.RelPath R y q) :
    List.RelPath R x (p ++ q) := by
  induction p generalizing x with
  | nil =>
      simp [List.getLastD] at hlast
      subst y
      exact hq
  | cons z p ih =>
      have hlastTail : (z :: p).getLastD z = y := by
        simpa [List.getLastD] using hlast
      exact ⟨hp.1, ih hp.2 hlastTail⟩

theorem append_cons
    {x y z : α} {p q : List α}
    (hp : List.RelPath R x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : R y z)
    (hq : List.RelPath R z q) :
    List.RelPath R x (p ++ z :: q) := by
  have hpz := snoc hp hlast hyz
  have hlastz : (x :: (p ++ [z])).getLastD x = z :=
    List.getLastD_cons_append_singleton x z p
  simpa [List.append_assoc] using append hpz hlastz hq

theorem split_append_cons
    {x y : α} {p q : List α}
    (hp : List.RelPath R x (p ++ y :: q)) :
    List.RelPath R x p ∧ R ((x :: p).getLastD x) y ∧ List.RelPath R y q := by
  induction p generalizing x with
  | nil =>
      exact ⟨by simp [List.RelPath], by simpa [List.getLastD] using hp.1, hp.2⟩
  | cons z p ih =>
      rcases ih hp.2 with ⟨hpPrefix, hlink, hsuffix⟩
      exact ⟨⟨hp.1, hpPrefix⟩, by simpa [List.getLastD] using hlink, hsuffix⟩

theorem prefix_of_append
    {x : α} {p q : List α}
    (hp : List.RelPath R x (p ++ q)) :
    List.RelPath R x p := by
  induction p generalizing x with
  | nil => trivial
  | cons y p ih => exact ⟨hp.1, ih hp.2⟩

theorem suffix_of_append
    {s x : α} {p q : List α}
    (hp : List.RelPath R s (p ++ x :: q)) :
    List.RelPath R x q := by
  induction p generalizing s with
  | nil => exact hp.2
  | cons _ p ih => exact ih hp.2

theorem last_rel_of_append_cons
    {x y : α} {p q : List α}
    (hp : List.RelPath R x (p ++ y :: q)) :
    R ((x :: p).getLastD x) y :=
  (split_append_cons hp).2.1

theorem to_reflTransGen
    {x y : α} {p : List α}
    (hp : List.RelPath R x (p ++ [y])) :
    Relation.ReflTransGen R x y := by
  induction p generalizing x with
  | nil => exact Relation.ReflTransGen.single hp.1
  | cons _ p ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single hp.1) (ih hp.2)

theorem exists_to_iterate
    (f : α → α) (n : Nat) (x : α) :
    ∃ p : List α,
      List.RelPath (fun a b => f a = b) x p ∧
        (x :: p).getLastD x = (f^[n]) x := by
  induction n generalizing x with
  | zero => exact ⟨[], by simp [List.RelPath, List.getLastD]⟩
  | succ n ih =>
      rcases ih (f x) with ⟨p, hp, hlast⟩
      exact ⟨f x :: p, ⟨rfl, hp⟩,
        by simpa [List.getLastD, Function.iterate_succ_apply] using hlast⟩

theorem reflTransGen_to_iterate
    (f : α → α)
    (hstep : ∀ x, R x (f x))
    (n : Nat) (x : α) :
    Relation.ReflTransGen R x ((f^[n]) x) := by
  induction n generalizing x with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (hstep x))
        (by simpa [Function.iterate_succ_apply] using ih (f x))

end RelPath

end List
