import Schematic.Math.GraphTheory.Minors.Society.SplitRouting

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

end GMIX24Split

@[simp]
theorem Tripod.cast_attach {S T : GeneralSociety V}
    (h : S = T) (X : S.Tripod) (i : Fin 3) :
    (h ▸ X : T.Tripod).attach i = X.attach i := by
  cases h
  rfl

@[simp]
theorem Tripod.mem_vertexSet_iff_exists_branch {S : GeneralSociety V}
    (T : S.Tripod) (x : V) :
    x ∈ T.vertexSet ↔
      Exists fun i : Fin 3 =>
        x ∈ (T.rim i).support ∨ x ∈ (T.leg i).support := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr hi⟩
  · rintro ⟨i, hi | hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩

/-- Branchwise cleanliness is the same as cleanliness against the tripod's
vertex set. -/
theorem Tripod.clean_vertex_of_branch_clean {S : GeneralSociety V}
    (T : S.Tripod) {G : SimpleGraph V} {x a : V} (q : G.Walk x a)
    (hclean :
      forall w : V, w ∈ q.support ->
        (Exists fun i : Fin 3 =>
          w ∈ (T.rim i).support ∨ w ∈ (T.leg i).support) ->
        w = x) :
    forall w : V, w ∈ q.support -> w ∈ T.vertexSet -> w = x := by
  intro w hw hwT
  exact hclean w hw ((T.mem_vertexSet_iff_exists_branch w).mp hwT)

namespace GMIX24Split

@[simp]
theorem canonicalOfNoCross.rightTripodOnReverse_attach
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    (canonicalOfNoCross.rightTripodOnReverse P hno_cross T).attach i =
      T.attach i :=
  Tripod.cast_attach
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm T i

@[simp]
theorem canonicalOfNoCross.rightTripodOnReverse_rim_internalVertices
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (i : Fin 3) :
    Walk.InternalVertices
        ((canonicalOfNoCross.rightTripodOnReverse P hno_cross T).rim i) =
      Walk.InternalVertices (T.rim i) :=
  Tripod.cast_rim_internalVertices
    (GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross).symm T i


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
