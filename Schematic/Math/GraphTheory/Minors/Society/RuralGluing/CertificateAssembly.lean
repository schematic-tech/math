import Schematic.Math.GraphTheory.Minors.Society.RuralGluing.AmbientGluing

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

/-- The marked-disk part of the source rural-gluing sentence, with every
degenerate boundary-arc case included.  A nonempty side arc supplies the
three boundary vertices needed to extract its recursive disk certificate;
when an arc is empty, the opposite certificate alone reconstructs the
ambient marked disk by the endpoint-edge insertion constructors above. -/
theorem exists_diskRuralCertificate_of_canonical_side_rural
    [Fintype V] [DecidableEq V]
    {S : GeneralSociety V}
    (hthree : S.ThreeConnected)
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hlarge : 3 <= S.boundarySet.ncard)
    (hleftRural : Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Rural)
    (hrightRural : Nonempty
      (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Rural) :
    Nonempty (DiskRuralCertificate S) := by
  classical
  rcases hleftRural with ⟨RL⟩
  rcases hrightRural with ⟨RR⟩
  obtain ⟨n, hlength⟩ : Exists fun n : Nat =>
      S.boundary.length = n + 3 := by
    use S.boundary.length - 3
    rw [S.boundarySet_ncard] at hlarge
    omega
  by_cases hleftArc : P.leftBoundaryArc.Nonempty
  · have hleftLarge :
        3 <= (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.boundarySet.ncard := by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact P.leftCutBoundarySet_ncard_ge_three_of_leftBoundaryArc_nonempty
        hleftArc
    rcases RL.disk hleftLarge with ⟨C₁⟩
    by_cases hrightArc : P.rightBoundaryArc.Nonempty
    · have hrightLarge :
          3 <= (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet.ncard := by
        rw [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
        exact P.rightCutBoundarySet_ncard_ge_three_of_rightBoundaryArc_nonempty
          hrightArc
      rcases RR.disk hrightLarge with ⟨C₂⟩
      exact C₁.exists_ambient_of_sideCertificates_bothArcs hthree P
        hno_cross C₂ hleftArc hrightArc n hlength
    · have hrightEmpty : P.rightBoundaryArc = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hrightArc
      exact C₁.exists_ambient_of_leftCertificate_rightArc_empty P hno_cross
        hrightEmpty hleftArc n hlength
  · have hleftEmpty : P.leftBoundaryArc = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hleftArc
    have hrightArc : P.rightBoundaryArc.Nonempty :=
      P.rightBoundaryArc_nonempty_of_leftBoundaryArc_eq_empty
        hlarge hleftEmpty
    have hrightLarge :
        3 <= (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.boundarySet.ncard := by
      rw [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
      exact P.rightCutBoundarySet_ncard_ge_three_of_rightBoundaryArc_nonempty
        hrightArc
    rcases RR.disk hrightLarge with ⟨C₂⟩
    exact C₂.exists_ambient_of_rightCertificate_leftArc_empty P hno_cross
      hleftEmpty hrightArc n hlength

end GeneralSociety

end Schematic.Math.GraphTheory
