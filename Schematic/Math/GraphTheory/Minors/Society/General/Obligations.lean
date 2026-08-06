import Schematic.Math.GraphTheory.Minors.Society.General.SideTripodObligation
import Schematic.Math.GraphTheory.Embedding.RotationSystemSoundness.PlanaritySoundness

/-! Side-tripod and rural-gluing obligations for a canonical cut path. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}

/-- Source side-tripod paragraph for the canonical cut path. -/
theorem side_tripod_obligations
    [Fintype V] [Fintype (Sym2 V)]
    (S : GeneralSociety V)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (P : GMIX24CutPath S) :
    SideTripodObligations hno_cross P := by
  exact
    { left_free :=
        left_side_tripod_obligation (S := S) hno_cross hno_tripod P
      right_free :=
        left_side_tripod_obligation (S := S) hno_cross hno_tripod P.reverse }

/-- Direct source rural-gluing sentence for the canonical cut.

This is the actual final sentence of the printed GM IX `(2.4)` proof: after
the two smaller side societies are rural, their drawings glue along the
induced cut path to a rural drawing of the original society.  The older mixed
`K_5`/`K_{3,3}` packages below remain available as one possible implementation
of this sentence for the current `Rural = IsPlanar` encoding, but they are not
the source-level obligation. -/
theorem rural_gluing_obligations
    [Fintype V] [Fintype (Sym2 V)]
    (S : GeneralSociety V)
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
    (hlarge : 3 <= S.boundarySet.ncard)
    (P : GMIX24CutPath S) :
    RuralGluingObligations hno_cross P := by
  intro hleftRural hrightRural
  let dOriginal : DecidableEq V := inferInstance
  have hplanar : IsPlanar S.graph := by
    classical
    rcases exists_diskRuralCertificate_of_canonical_side_rural
        hthree P hno_cross hlarge hleftRural hrightRural with
      ⟨C⟩
    let A :=
      S.boundaryAugmentedGraphOfLength (C.n + 3) C.boundary_length
    let dA : DecidableRel A.Adj := Classical.decRel _
    letI : DecidableRel A.Adj := dA
    have hEuler : FourColor.HasEulerRotationSystem A := by
      refine ⟨?_, ?_⟩
      · simpa [A] using C.rotation
      · simpa [A] using C.dual_eulerPlanar
    exact IsPlanar.mono le_sup_left
      (@FourColor.RotationSoundness.hasEulerRotationSystem_isPlanar
        V _ _ A dA hEuler)
  refine ⟨{
    planar := hplanar
    disk := ?_
  }⟩
  intro _ dCurrent hboundary
  have hd : dCurrent = dOriginal := Subsingleton.elim _ _
  cases hd
  exact exists_diskRuralCertificate_of_canonical_side_rural
    hthree P hno_cross hboundary hleftRural hrightRural

/-- The assembled local source obligations for one canonical GM IX `(2.4)`
cut path. -/
theorem local_obligations
    (S : GeneralSociety V)
    [Fintype V] [Fintype (Sym2 V)]
    (hthree : S.ThreeConnected)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (hlarge : 3 <= S.boundarySet.ncard)
    (P : GMIX24CutPath S) :
    LocalObligations hno_cross P := by
  exact {
    side_tripods :=
      side_tripod_obligations (S := S) hno_cross hno_tripod P
    glues_rural :=
      rural_gluing_obligations (S := S) hthree hno_cross hlarge P }

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
