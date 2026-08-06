import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountCases
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwo
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountThree

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_obstruction_of_maximal_from_source_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (htripod_first :
      forall {l : Fin 4},
        l = 1 ∨ l = 3 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.firstPath.support ->
          y ∈ X.secondPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod)
    (htripod_second :
      forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.leftSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_count_cases
        P hno_cross X with hzero | hone_or_two_or_three
  · exact
      GMIX24Split.canonicalOfNoCross_left_cross_obstruction_of_maximal_count_zero
        P hno_cross X hmax hzero
  · rcases hone_or_two_or_three with hone | htwo_or_three
    · exact
        GMIX24Split.canonicalOfNoCross_left_cross_obstruction_of_maximal_count_one_from_clean_branch_tripod
          P hno_cross X hmax hone htripod_first htripod_second
    · rcases htwo_or_three with htwo | hthree
      · exact Or.inl
          (GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_two_from_adjacent_cases
            P hno_cross X htwo)
      · exact Or.inl
          (GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_three_from_side_order
            P hno_cross X hthree)

theorem canonicalOfNoCross_right_cross_obstruction_of_maximal_from_source_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hmax : CrossOffPathCountMaximal P X)
    (htripod_first :
      forall {l : Fin 4},
        l = 1 ∨ l = 3 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.firstPath.support ->
          y ∈ X.secondPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod)
    (htripod_second :
      forall {l : Fin 4},
        l = 0 ∨ l = 2 ->
        X.endpoints.endpoint l ∉ P.pathSet ->
        (forall i : Fin 4, i ≠ l ->
          X.endpoints.endpoint i ∈ P.pathSet) ->
      forall {x y : V} (r : S.graph.Walk x y),
        x ∈ X.secondPath.support ->
          y ∈ X.firstPath.support ->
            r.IsPath ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.secondPath.support -> w = x) ->
              (forall w : V, w ∈ r.support ->
                w ∈ X.firstPath.support -> w = y) ->
              (forall w : V, w ∈ r.support -> w ∈ P.rightSide) ->
                (forall w : V, w ∈ r.support -> w ∈ P.outside) ->
                  Nonempty S.Tripod) :
    Nonempty S.Cross ∨ Nonempty S.Tripod := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  have hsources :
      GMIX24Split.LeftMaximalCrossSourceCases P.reverse hno_cross Xrev := by
    simpa [GMIX24Split.LeftMaximalCrossSourceCases,
      GMIX24Split.RightMaximalCrossSourceCases, Xrev,
      GMIX24Split.canonicalOfNoCross_reverseRightCross] using
      (show GMIX24Split.RightMaximalCrossSourceCases P hno_cross X from
        ⟨htripod_first, htripod_second⟩)
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_obstruction_of_maximal_from_source_cases
      P.reverse hno_cross Xrev (hmax.reverseRight hno_cross)
      hsources.1 hsources.2


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

