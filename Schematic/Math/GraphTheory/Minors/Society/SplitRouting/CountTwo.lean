import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoAdjacent01
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoAdjacent12
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoAdjacent23
import Schematic.Math.GraphTheory.Minors.Society.SplitRouting.CountTwoAdjacent30

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

theorem canonicalOfNoCross_left_cross_lift_of_count_two_from_adjacent_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 2) :
    Nonempty S.Cross := by
  classical
  rcases
      GMIX24Split.canonicalOfNoCross_left_cross_count_two_path_adjacent_cases
        P hno_cross X hcount with h01 | hrest
  · rcases h01 with ⟨h0_path, h1_path, h2_off, h3_off⟩
    exact
      GMIX24Split.canonicalOfNoCross_left_cross_lift_of_adjacent01
        P hno_cross X h0_path h1_path h2_off h3_off
  · rcases hrest with h12 | hrest
    · rcases h12 with ⟨h1_path, h2_path, h0_off, h3_off⟩
      exact
        GMIX24Split.canonicalOfNoCross_left_cross_lift_of_adjacent12
          P hno_cross X h1_path h2_path h0_off h3_off
    · rcases hrest with h23 | h30
      · rcases h23 with ⟨h2_path, h3_path, h0_off, h1_off⟩
        exact
          GMIX24Split.canonicalOfNoCross_left_cross_lift_of_adjacent23
            P hno_cross X h2_path h3_path h0_off h1_off
      · rcases h30 with ⟨h3_path, h0_path, h1_off, h2_off⟩
        exact
          GMIX24Split.canonicalOfNoCross_left_cross_lift_of_adjacent30
            P hno_cross X h3_path h0_path h1_off h2_off

theorem canonicalOfNoCross_right_cross_lift_of_count_two_from_adjacent_cases
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (X : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Cross)
    (hcount : crossOffPathEndpointCount X P = 2) :
    Nonempty S.Cross := by
  classical
  let Xrev :=
    GMIX24Split.canonicalOfNoCross_reverseRightCross P hno_cross X
  exact
    GMIX24Split.canonicalOfNoCross_left_cross_lift_of_count_two_from_adjacent_cases
      P.reverse hno_cross Xrev (by
        simpa [Xrev, GMIX24Split.canonicalOfNoCross_reverseRightCross,
          crossOffPathEndpointCount, crossOffPathEndpointFinset] using hcount)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory

