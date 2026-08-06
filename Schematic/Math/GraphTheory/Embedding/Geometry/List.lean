import Mathlib.Data.List.Basic

namespace List

theorem getLastD_cons_append_singleton
    {α : Type _} (x y : α) (p : List α) :
    (x :: (p ++ [y])).getLastD x = y := by
  induction p generalizing x with
  | nil => simp [List.getLastD]
  | cons z p ih => simp [List.getLastD]

theorem getLastD_cons_append_cons
    {α : Type _} (x z : α) (p c : List α) :
    (x :: (p ++ z :: c)).getLastD x = (z :: c).getLastD z := by
  induction p generalizing x with
  | nil => simp [List.getLastD]
  | cons y p ih => simp [List.getLastD]

theorem getLastD_cons_append_self
    {α : Type _} (x : α) (p q : List α) :
    (x :: (p ++ x :: q)).getLastD x = (x :: q).getLastD x := by
  simpa using List.getLastD_cons_append_cons x x p q

theorem getLastD_cons_mem
    {α : Type _} (x : α) (p : List α) :
    (x :: p).getLastD x ∈ x :: p := by
  simpa only [List.getLastD_cons] using
    (List.getLastD_mem_cons (l := p) (a := x))

theorem getLastD_cons_cons_mem_tail
    {α : Type _} (x y : α) (p : List α) :
    (x :: y :: p).getLastD x ∈ y :: p := by
  simpa only [List.getLastD_cons] using
    (List.getLastD_mem_cons (l := p) (a := y))

theorem getLast?_getD_cons_append_singleton
    {α : Type _} (x y : α) (p : List α) :
    (x :: (p ++ [y])).getLast?.getD x = y := by
  rw [← List.getLastD_eq_getLast?]
  exact List.getLastD_cons_append_singleton x y p

end List
