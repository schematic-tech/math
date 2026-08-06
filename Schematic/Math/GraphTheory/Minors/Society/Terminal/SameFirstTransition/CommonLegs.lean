import Schematic.Math.GraphTheory.Minors.Society.Terminal.Symmetry

/-!
Shared leg constructions for all-nil clean and spliced transitions.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable {S : GeneralSociety V}

def Tripod.allNilCleanBridgeAttach
    {H : GeneralSociety V} (T : H.Tripod)
    (i k : Fin 3) : Fin 3 -> V
  | 0 => T.attach i
  | 1 => T.left
  | 2 => T.attach k

/-- Boundary legs shared by the all-collapsed clean-transition exchanges. -/
def Tripod.allNilCleanBridgeLeg
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V} (q : S.graph.Walk T.left a) :
    forall r : Fin 3,
      S.graph.Walk
        (GMIX24SourceProof.Tripod.allNilCleanBridgeAttach T i k r)
        (P.boundaryTriple a r)
  | 0 =>
      (P.pathTailToStart hi).copy
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl
  | 1 => q
  | 2 =>
      (P.pathTailToEnd hk).copy
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl

theorem Tripod.allNilCleanBridgeLeg_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    {i k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a : V} (q : S.graph.Walk T.left a)
    (hq_path : q.IsPath) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
        hleg_i_nil hleg_k_nil hi hk q r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.allNilCleanBridgeLeg] using
      (SimpleGraph.Walk.isPath_copy (P.pathTailToStart hi)
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl).mpr
          (P.pathTailToStart_isPath hi)
  · simpa [Tripod.allNilCleanBridgeLeg] using hq_path
  · simpa [Tripod.allNilCleanBridgeLeg] using
      (SimpleGraph.Walk.isPath_copy (P.pathTailToEnd hk)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
          (P.pathTailToEnd_isPath hk)

theorem Tripod.allNilCleanBridgeLegs_pairwise_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a : V} (q : S.graph.Walk T.left a)
    (hq_outside : forall z : V, z ∈ q.support -> z ∈ P.outside) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
            hleg_i_nil hleg_k_nil hi hk q r).support}
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilCleanBridgeLeg P T
            hleg_i_nil hleg_k_nil hi hk q s).support} := by
  have hstart_q : Disjoint
      {z : V | z ∈ (P.pathTailToStart hi).support}
      {z : V | z ∈ q.support} := by
    rw [Set.disjoint_left]
    intro z hzTail hzq
    exact (hq_outside z hzq).2
      (P.pathTailToStart_support_subset_pathSet hi z hzTail)
  have hq_end : Disjoint
      {z : V | z ∈ q.support}
      {z : V | z ∈ (P.pathTailToEnd hk).support} := by
    rw [Set.disjoint_left]
    intro z hzq hzTail
    exact (hq_outside z hzq).2
      (P.pathTailToEnd_support_subset_pathSet hk z hzTail)
  have hstart_end : Disjoint
      {z : V | z ∈ (P.pathTailToStart hi).support}
      {z : V | z ∈ (P.pathTailToEnd hk).support} :=
    P.pathTailToStart_support_disjoint_pathTailToEnd hi hk
      (lt_trans hij_order hjk_order)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.allNilCleanBridgeLeg,
      SimpleGraph.Walk.support_copy] using hstart_q
  · simpa [Tripod.allNilCleanBridgeLeg,
      SimpleGraph.Walk.support_copy] using hstart_end
  · simpa [Tripod.allNilCleanBridgeLeg,
      SimpleGraph.Walk.support_copy] using hstart_q.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.allNilCleanBridgeLeg,
      SimpleGraph.Walk.support_copy] using hq_end
  · simpa [Tripod.allNilCleanBridgeLeg,
      SimpleGraph.Walk.support_copy] using hstart_end.symm
  · simpa [Tripod.allNilCleanBridgeLeg,
      SimpleGraph.Walk.support_copy] using hq_end.symm
  · exact False.elim (hrs rfl)

/-- Attachments after splicing a carrier transition into the first contact
`c` with a clean boundary escape. -/
def Tripod.allNilSplicedTransitionAttach
    {H : GeneralSociety V} (T : H.Tripod)
    (i k : Fin 3) (c : V) : Fin 3 -> V
  | 0 => T.attach i
  | 1 => c
  | 2 => T.attach k

/-- The two ordered cut-path tails and the suffix of the boundary escape after
the splice point. -/
def Tripod.allNilSplicedTransitionLeg
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    {i k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a c : V} (tail : S.graph.Walk c a) :
    forall r : Fin 3,
      S.graph.Walk
        (GMIX24SourceProof.Tripod.allNilSplicedTransitionAttach T i k c r)
        (P.boundaryTriple a r)
  | 0 =>
      (P.pathTailToStart hi).copy
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl
  | 1 => tail
  | 2 =>
      (P.pathTailToEnd hk).copy
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl

theorem Tripod.allNilSplicedTransitionLeg_isPath
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    {i k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    {a c : V} (tail : S.graph.Walk c a)
    (htail_path : tail.IsPath) :
    forall r : Fin 3,
      (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
        hleg_i_nil hleg_k_nil hi hk tail r).IsPath := by
  intro r
  fin_cases r
  · simpa [Tripod.allNilSplicedTransitionLeg] using
      (SimpleGraph.Walk.isPath_copy (P.pathTailToStart hi)
        ((T.leg_nil_iff_boundary_eq_attach i).mp hleg_i_nil) rfl).mpr
          (P.pathTailToStart_isPath hi)
  · simpa [Tripod.allNilSplicedTransitionLeg] using htail_path
  · simpa [Tripod.allNilSplicedTransitionLeg] using
      (SimpleGraph.Walk.isPath_copy (P.pathTailToEnd hk)
        ((T.leg_nil_iff_boundary_eq_attach k).mp hleg_k_nil) rfl).mpr
          (P.pathTailToEnd_isPath hk)

theorem Tripod.allNilSplicedTransitionLegs_pairwise_disjoint
    [DecidableEq V]
    {S H : GeneralSociety V}
    (P : GMIX24CutPath S) (T : H.Tripod)
    {i j k : Fin 3}
    (hleg_i_nil : (T.leg i).Nil)
    (hleg_k_nil : (T.leg k).Nil)
    (hi : T.boundary i ∈ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    {a c : V} (tail : S.graph.Walk c a)
    (htail_outside : forall z : V, z ∈ tail.support -> z ∈ P.outside) :
    forall r s : Fin 3, r ≠ s ->
      Disjoint
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
            hleg_i_nil hleg_k_nil hi hk tail r).support}
        {z : V | z ∈
          (GMIX24SourceProof.Tripod.allNilSplicedTransitionLeg P T
            hleg_i_nil hleg_k_nil hi hk tail s).support} := by
  have hstart_tail : Disjoint
      {z : V | z ∈ (P.pathTailToStart hi).support}
      {z : V | z ∈ tail.support} := by
    rw [Set.disjoint_left]
    intro z hzPath hzTail
    exact (htail_outside z hzTail).2
      (P.pathTailToStart_support_subset_pathSet hi z hzPath)
  have htail_end : Disjoint
      {z : V | z ∈ tail.support}
      {z : V | z ∈ (P.pathTailToEnd hk).support} := by
    rw [Set.disjoint_left]
    intro z hzTail hzPath
    exact (htail_outside z hzTail).2
      (P.pathTailToEnd_support_subset_pathSet hk z hzPath)
  have hstart_end : Disjoint
      {z : V | z ∈ (P.pathTailToStart hi).support}
      {z : V | z ∈ (P.pathTailToEnd hk).support} :=
    P.pathTailToStart_support_disjoint_pathTailToEnd hi hk
      (lt_trans hij_order hjk_order)
  intro r s hrs
  fin_cases r <;> fin_cases s
  · exact False.elim (hrs rfl)
  · simpa [Tripod.allNilSplicedTransitionLeg,
      SimpleGraph.Walk.support_copy] using hstart_tail
  · simpa [Tripod.allNilSplicedTransitionLeg,
      SimpleGraph.Walk.support_copy] using hstart_end
  · simpa [Tripod.allNilSplicedTransitionLeg,
      SimpleGraph.Walk.support_copy] using hstart_tail.symm
  · exact False.elim (hrs rfl)
  · simpa [Tripod.allNilSplicedTransitionLeg,
      SimpleGraph.Walk.support_copy] using htail_end
  · simpa [Tripod.allNilSplicedTransitionLeg,
      SimpleGraph.Walk.support_copy] using hstart_end.symm
  · simpa [Tripod.allNilSplicedTransitionLeg,
      SimpleGraph.Walk.support_copy] using htail_end.symm
  · exact False.elim (hrs rfl)

end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
