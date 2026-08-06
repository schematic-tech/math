import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.SourceFacts

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split

/-- A full contact/median source package automatically supplies the residual
source package.

This is the formal direction from the earlier source formulation to the
sharper residual formulation: once the clean tail is known to start on the
median branch, the checked disjointness lemma
`tripod_median_branch_not_residual` rules out the endpoint and degenerate
non-median-rim residual alternatives. -/
theorem LeftTripodContactSourceFacts.to_residual_source_facts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (F : LeftTripodContactSourceFacts P hno_cross) :
    LeftTripodResidualSourceFacts P hno_cross where
  path_contacts := F.path_contacts
  residual_impossible := by
    intro T x a q hxT ha hq_path hq_side hq_outside hq_clean
      i j k hij hik hjk hij_order hjk_order hresidual
    exact
      GMIX24Split.tripod_median_branch_not_residual T hij hik hjk
        (F.median_branch T x a q hxT ha hq_path hq_side hq_outside
          hq_clean hij hik hjk hij_order hjk_order)
        (GMIX24Split.tripod_leg_nil_residual_to_residual T
          (i := i) (k := k) (x := x) hresidual)

end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
