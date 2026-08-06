import Schematic.Math.GraphTheory.Minors.Society.RuralGluing

/-!
Stable terminal-path and tripod-rerouting helpers for the GM IX `(2.4)`
source proof.  Keeping these declarations outside the live obligation lets
Lean reuse their compiled environment while the final case analysis changes.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- The side-tripod conclusion from the printed GM IX `(2.4)` side-tripod
paragraph.

The source argument assumes a tripod in one of the two canonical side
societies and derives an ambient tripod in `S`.  The natural local theorem is
therefore side-tripod freeness itself, not the older downstream package of
arc/path contacts and outer-nil linkage facts. -/
structure SideTripodObligations
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S) : Prop where
  left_free :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
  right_free :
    Not (Nonempty
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod)

/-- Direct rural-gluing conclusion from the printed GM IX `(2.4)` proof.

This is the single gluing operation in the source proof. -/
def RuralGluingObligations
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S) : Prop :=
  Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Rural ->
    Nonempty (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Rural ->
      Nonempty S.Rural

/-- The remaining local source obligations for one canonical GM IX `(2.4)`
cut path.

The printed proof has a side-tripod paragraph and a rural-gluing sentence.
This is the live source endpoint: the mixed Kuratowski obstruction packages
are implementation support for the current planarity encoding, not independent
source paragraphs. -/
structure LocalObligations
    (hno_cross : Not (Nonempty S.Cross))
    (P : GMIX24CutPath S) : Prop where
  side_tripods : SideTripodObligations hno_cross P
  glues_rural : RuralGluingObligations hno_cross P

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
