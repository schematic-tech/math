import Schematic.Math.GraphTheory.Minors.Society.LastToFirst

/-!
Stable helpers for the hidden cut-path contact in the GM IX `(2.4)`
side-tripod argument.  This module is intentionally small: the final assembly
can change without re-elaborating the checked transition constructors.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24SourceProof

variable [DecidableEq V] {S : GeneralSociety V}


/-! ## A hidden rim contact forces a side cross -/

/-- The path from the left common end of a tripod to one of its boundary
feet. -/
def branchFromLeft {H : GeneralSociety V}
    (T : H.Tripod) (i : Fin 3) :
    H.graph.Walk T.left (T.boundary i) :=
  (T.leftToAttach i).append (T.leg i)

/-- The path from the right common end of a tripod to one of its boundary
feet. -/
def branchFromRight {H : GeneralSociety V}
    (T : H.Tripod) (i : Fin 3) :
    H.graph.Walk T.right (T.boundary i) :=
  (T.rightToAttach i).append (T.leg i)

theorem mem_branchFromLeft_iff {H : GeneralSociety V}
    (T : H.Tripod) (i : Fin 3) {z : V} :
    z ∈ (branchFromLeft T i).support ↔
      z ∈ (T.leftToAttach i).support ∨ z ∈ (T.leg i).support := by
  simp [branchFromLeft, SimpleGraph.Walk.mem_support_append_iff]

theorem mem_branchFromRight_iff {H : GeneralSociety V}
    (T : H.Tripod) (i : Fin 3) {z : V} :
    z ∈ (branchFromRight T i).support ↔
      z ∈ (T.rightToAttach i).support ∨ z ∈ (T.leg i).support := by
  simp [branchFromRight, SimpleGraph.Walk.mem_support_append_iff]

/-- A left half-branch and a right half-branch with different indices are
vertex-disjoint. -/
theorem branchFromLeft_disjoint_branchFromRight_of_ne
    {H : GeneralSociety V}
    (T : H.Tripod) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint {z : V | z ∈ (branchFromLeft T i).support}
      {z : V | z ∈ (branchFromRight T j).support} := by
  rw [Set.disjoint_left]
  intro z hzLeft hzRight
  rcases (mem_branchFromLeft_iff T i).mp hzLeft with hzLeftArm | hzLegI
  · rcases (mem_branchFromRight_iff T j).mp hzRight with
      hzRightArm | hzLegJ
    · have hzCommon : z = T.left :=
        T.leftToAttach_support_inter_rim_eq_left hij hzLeftArm
          (T.rightToAttach_support_subset_rim j hzRightArm)
      exact T.left_not_mem_rightToAttach j (by simpa [hzCommon] using hzRightArm)
    · have hzRimI : z ∈ (T.rim i).support :=
        T.leftToAttach_support_subset_rim i hzLeftArm
      have hzAttach : z = T.attach j :=
        T.legs_meet_rims_only_at_attach j i z hzLegJ hzRimI
      exact T.attach_not_mem_rim_of_ne (fun h => hij h.symm)
        (by simpa [hzAttach] using hzRimI)
  · rcases (mem_branchFromRight_iff T j).mp hzRight with
      hzRightArm | hzLegJ
    · have hzRimJ : z ∈ (T.rim j).support :=
        T.rightToAttach_support_subset_rim j hzRightArm
      have hzAttach : z = T.attach i :=
        T.legs_meet_rims_only_at_attach i j z hzLegI hzRimJ
      exact T.attach_not_mem_rim_of_ne hij
        (by simpa [hzAttach] using hzRimJ)
    · exact Set.disjoint_left.mp (T.legs_pairwise_disjoint i j hij)
        hzLegI hzLegJ

theorem leftPrefix_disjoint_branchFromRight
    {H : GeneralSociety V}
    (T : H.Tripod) {r : Fin 3} {z : V}
    (hz : z ∈ (T.leftToAttach r).support)
    (hzAttach : z ≠ T.attach r) :
    Disjoint
      {x : V | x ∈ ((T.leftToAttach r).takeUntil z hz).support}
      {x : V | x ∈ (branchFromRight T r).support} := by
  rw [Set.disjoint_left]
  intro x hx hxr
  rcases (mem_branchFromRight_iff T r).mp hxr with hxArm | hxLeg
  · exact Set.disjoint_left.mp
      (T.leftToAttach_takeUntil_support_disjoint_rightToAttach hz hzAttach)
      hx hxArm
  · exact Set.disjoint_left.mp
      (T.leftToAttach_takeUntil_support_disjoint_leg hz hzAttach) hx hxLeg

theorem rightPrefix_disjoint_branchFromLeft
    {H : GeneralSociety V}
    (T : H.Tripod) {r : Fin 3} {z : V}
    (hz : z ∈ (T.rightToAttach r).support)
    (hzAttach : z ≠ T.attach r) :
    Disjoint
      {x : V | x ∈ ((T.rightToAttach r).takeUntil z hz).support}
      {x : V | x ∈ (branchFromLeft T r).support} := by
  rw [Set.disjoint_left]
  intro x hx hxl
  rcases (mem_branchFromLeft_iff T r).mp hxl with hxArm | hxLeg
  · exact Set.disjoint_left.mp
      (T.rightToAttach_takeUntil_support_disjoint_leftToAttach hz hzAttach)
      hx hxArm
  · exact Set.disjoint_left.mp
      (T.rightToAttach_takeUntil_support_disjoint_leg hz hzAttach) hx hxLeg

/-- If `z` is on the left half of rim `r`, route `z` to any selected foot and
the other two feet to each other by two disjoint walks. -/
theorem exists_disjoint_pairing_of_mem_leftToAttach
    {H : GeneralSociety V}
    (T : H.Tripod) {z : V} {r i j k : Fin 3}
    (hz : z ∈ (T.leftToAttach r).support)
    (hzAttach : z ≠ T.attach r)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ p : H.graph.Walk z (T.boundary i),
      ∃ q : H.graph.Walk (T.boundary j) (T.boundary k),
        Disjoint {x : V | x ∈ p.support} {x : V | x ∈ q.support} := by
  rcases fin3_eq_of_pairwise hij hik hjk (m := r) with hri | hrj | hrk
  · subst r
    let p : H.graph.Walk z (T.boundary i) :=
      ((T.leftToAttach i).dropUntil z hz).append (T.leg i)
    let q : H.graph.Walk (T.boundary j) (T.boundary k) :=
      (branchFromRight T j).reverse.append (branchFromRight T k)
    refine ⟨p, q, ?_⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hxpBranch : x ∈ (branchFromLeft T i).support := by
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxp with
        hxArm | hxLeg
      · exact (mem_branchFromLeft_iff T i).mpr (Or.inl
          (SimpleGraph.Walk.support_dropUntil_subset (T.leftToAttach i) hz hxArm))
      · exact (mem_branchFromLeft_iff T i).mpr (Or.inr hxLeg)
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
      hxJRev | hxK
    · have hxJ : x ∈ (branchFromRight T j).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxJRev
      exact Set.disjoint_left.mp
        (branchFromLeft_disjoint_branchFromRight_of_ne T hij) hxpBranch hxJ
    · exact Set.disjoint_left.mp
        (branchFromLeft_disjoint_branchFromRight_of_ne T hik) hxpBranch hxK
  · subst r
    let p : H.graph.Walk z (T.boundary i) :=
      ((T.leftToAttach j).takeUntil z hz).reverse.append
        (branchFromLeft T i)
    let q : H.graph.Walk (T.boundary j) (T.boundary k) :=
      (branchFromRight T j).reverse.append (branchFromRight T k)
    refine ⟨p, q, ?_⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxp with
      hxPrefixRev | hxI
    · have hxPrefix :
          x ∈ ((T.leftToAttach j).takeUntil z hz).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxPrefixRev
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxJ : x ∈ (branchFromRight T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (leftPrefix_disjoint_branchFromRight T hz hzAttach) hxPrefix hxJ
      · have hxJBranch : x ∈ (branchFromLeft T j).support :=
          (mem_branchFromLeft_iff T j).mpr (Or.inl
            (SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach j) hz
              hxPrefix))
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hjk) hxJBranch hxK
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxJ : x ∈ (branchFromRight T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hij) hxI hxJ
      · exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hik) hxI hxK
  · subst r
    let p : H.graph.Walk z (T.boundary i) :=
      ((T.leftToAttach k).takeUntil z hz).reverse.append
        (branchFromLeft T i)
    let q : H.graph.Walk (T.boundary j) (T.boundary k) :=
      (branchFromRight T j).reverse.append (branchFromRight T k)
    refine ⟨p, q, ?_⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxp with
      hxPrefixRev | hxI
    · have hxPrefix :
          x ∈ ((T.leftToAttach k).takeUntil z hz).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxPrefixRev
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxKRev
      · have hxKBranch : x ∈ (branchFromLeft T k).support :=
          (mem_branchFromLeft_iff T k).mpr (Or.inl
            (SimpleGraph.Walk.support_takeUntil_subset (T.leftToAttach k) hz
              hxPrefix))
        have hxJ : x ∈ (branchFromRight T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hjk.symm)
          hxKBranch hxJ
      · exact Set.disjoint_left.mp
          (leftPrefix_disjoint_branchFromRight T hz hzAttach) hxPrefix hxKRev
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxJ : x ∈ (branchFromRight T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hij) hxI hxJ
      · exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hik) hxI hxK

/-- Right-half counterpart of
`exists_disjoint_pairing_of_mem_leftToAttach`. -/
theorem exists_disjoint_pairing_of_mem_rightToAttach
    {H : GeneralSociety V}
    (T : H.Tripod) {z : V} {r i j k : Fin 3}
    (hz : z ∈ (T.rightToAttach r).support)
    (hzAttach : z ≠ T.attach r)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ p : H.graph.Walk z (T.boundary i),
      ∃ q : H.graph.Walk (T.boundary j) (T.boundary k),
        Disjoint {x : V | x ∈ p.support} {x : V | x ∈ q.support} := by
  rcases fin3_eq_of_pairwise hij hik hjk (m := r) with hri | hrj | hrk
  · subst r
    let p : H.graph.Walk z (T.boundary i) :=
      ((T.rightToAttach i).dropUntil z hz).append (T.leg i)
    let q : H.graph.Walk (T.boundary j) (T.boundary k) :=
      (branchFromLeft T j).reverse.append (branchFromLeft T k)
    refine ⟨p, q, ?_⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hxpBranch : x ∈ (branchFromRight T i).support := by
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxp with
        hxArm | hxLeg
      · exact (mem_branchFromRight_iff T i).mpr (Or.inl
          (SimpleGraph.Walk.support_dropUntil_subset (T.rightToAttach i) hz hxArm))
      · exact (mem_branchFromRight_iff T i).mpr (Or.inr hxLeg)
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
      hxJRev | hxK
    · have hxJ : x ∈ (branchFromLeft T j).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxJRev
      exact Set.disjoint_left.mp
        (branchFromLeft_disjoint_branchFromRight_of_ne T hij.symm).symm
        hxpBranch hxJ
    · exact Set.disjoint_left.mp
        (branchFromLeft_disjoint_branchFromRight_of_ne T hik.symm).symm
        hxpBranch hxK
  · subst r
    let p : H.graph.Walk z (T.boundary i) :=
      ((T.rightToAttach j).takeUntil z hz).reverse.append
        (branchFromRight T i)
    let q : H.graph.Walk (T.boundary j) (T.boundary k) :=
      (branchFromLeft T j).reverse.append (branchFromLeft T k)
    refine ⟨p, q, ?_⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxp with
      hxPrefixRev | hxI
    · have hxPrefix :
          x ∈ ((T.rightToAttach j).takeUntil z hz).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxPrefixRev
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxJ : x ∈ (branchFromLeft T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (rightPrefix_disjoint_branchFromLeft T hz hzAttach) hxPrefix hxJ
      · have hxJBranch : x ∈ (branchFromRight T j).support :=
          (mem_branchFromRight_iff T j).mpr (Or.inl
            (SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach j) hz
              hxPrefix))
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hjk.symm).symm
          hxJBranch hxK
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxJ : x ∈ (branchFromLeft T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hij.symm).symm hxI hxJ
      · exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hik.symm).symm hxI hxK
  · subst r
    let p : H.graph.Walk z (T.boundary i) :=
      ((T.rightToAttach k).takeUntil z hz).reverse.append
        (branchFromRight T i)
    let q : H.graph.Walk (T.boundary j) (T.boundary k) :=
      (branchFromLeft T j).reverse.append (branchFromLeft T k)
    refine ⟨p, q, ?_⟩
    rw [Set.disjoint_left]
    intro x hxp hxq
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxp with
      hxPrefixRev | hxI
    · have hxPrefix :
          x ∈ ((T.rightToAttach k).takeUntil z hz).support := by
        simpa [SimpleGraph.Walk.support_reverse] using hxPrefixRev
      rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxKBranch : x ∈ (branchFromRight T k).support :=
          (mem_branchFromRight_iff T k).mpr (Or.inl
            (SimpleGraph.Walk.support_takeUntil_subset (T.rightToAttach k) hz
              hxPrefix))
        have hxJ : x ∈ (branchFromLeft T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hjk).symm
          hxKBranch hxJ
      · exact Set.disjoint_left.mp
          (rightPrefix_disjoint_branchFromLeft T hz hzAttach) hxPrefix hxK
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxq with
        hxJRev | hxK
      · have hxJ : x ∈ (branchFromLeft T j).support := by
          simpa [SimpleGraph.Walk.support_reverse] using hxJRev
        exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hij.symm).symm hxI hxJ
      · exact Set.disjoint_left.mp
          (branchFromLeft_disjoint_branchFromRight_of_ne T hik.symm).symm hxI hxK

/-- Every non-attachment point on a tripod rim admits all three two-path
pairings with the three boundary feet. -/
theorem exists_disjoint_pairing_of_rim_contact
    {H : GeneralSociety V}
    (T : H.Tripod) {z : V} {r i j k : Fin 3}
    (hz : z ∈ (T.rim r).support)
    (hzAttach : z ≠ T.attach r)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ p : H.graph.Walk z (T.boundary i),
      ∃ q : H.graph.Walk (T.boundary j) (T.boundary k),
        Disjoint {x : V | x ∈ p.support} {x : V | x ∈ q.support} := by
  rcases Walk.mem_support_takeUntil_or_dropUntil_of_mem_support
      (T.rim r) (T.attach_mem_rim r).1 hz with hzLeft | hzRight
  · exact exists_disjoint_pairing_of_mem_leftToAttach T
      (z := z) (r := r) (i := i) (j := j) (k := k)
      (by simpa [Tripod.leftToAttach] using hzLeft) hzAttach hij hik hjk
  · exact exists_disjoint_pairing_of_mem_rightToAttach T
      (z := z) (r := r) (i := i) (j := j) (k := k)
      (by
        simpa [Tripod.rightToAttach, Tripod.attachToRight,
          SimpleGraph.Walk.support_reverse] using hzRight)
      hzAttach hij hik hjk

/-- Endpoint order for the pairing `z--boundary i`,
`boundary j--boundary k`. -/
def hiddenPairingEndpoints (z : V) (boundary : Fin 3 → V)
    (i j k : Fin 3) : Fin 4 → V
  | 0 => z
  | 1 => boundary j
  | 2 => boundary i
  | 3 => boundary k

omit [DecidableEq V] in
theorem hiddenPairingEndpoints_mem
    {H : GeneralSociety V} (T : H.Tripod)
    {z : V} (hz : z ∈ H.boundarySet) (i j k : Fin 3) :
    ∀ a : Fin 4, hiddenPairingEndpoints z T.boundary i j k a ∈ H.boundarySet := by
  intro a
  fin_cases a
  · exact hz
  · exact T.boundary_mem j
  · exact T.boundary_mem i
  · exact T.boundary_mem k

omit [DecidableEq V] in
theorem hiddenPairingEndpoints_injective
    {H : GeneralSociety V} (T : H.Tripod)
    {z : V} (hz : ∀ a : Fin 3, z ≠ T.boundary a)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (hiddenPairingEndpoints z T.boundary i j k) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [hiddenPairingEndpoints] at hab ⊢ <;>
    first
    | rfl
    | exact False.elim (hz _ hab)
    | exact False.elim (hz _ hab.symm)
    | exact False.elim (hij (T.boundary_injective hab).symm)
    | exact False.elim (hij (T.boundary_injective hab))
    | exact False.elim (hik (T.boundary_injective hab))
    | exact False.elim (hik (T.boundary_injective hab).symm)
    | exact False.elim (hjk (T.boundary_injective hab))
    | exact False.elim (hjk (T.boundary_injective hab).symm)

omit [DecidableEq V] in
/-- Of the three pairings of four distinct cyclically ordered points, one of
the two orientations of one pairing is alternating. -/
theorem hiddenPairingEndpoints_one_alternating
    (Omega : CyclicBoundary V) (boundary : Fin 3 → V) {z : V}
    (hzMem : z ∈ Omega.vertexSet)
    (hboundaryMem : ∀ i : Fin 3, boundary i ∈ Omega.vertexSet)
    (hboundaryInj : Function.Injective boundary)
    (hz : ∀ i : Fin 3, z ≠ boundary i) :
    CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary 0 1 2) ∨
      CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary 0 2 1) ∨
      CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary 1 0 2) ∨
      CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary 1 2 0) ∨
      CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary 2 0 1) ∨
      CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary 2 1 0) := by
  classical
  letI : DecidableEq V := Classical.decEq V
  have before_total (a b : Fin 3) (hab : a ≠ b) :
      Omega.ClockwiseOpenBetween z (boundary b) (boundary a) ∨
        Omega.ClockwiseOpenBetween z (boundary a) (boundary b) := by
    have hza : z ≠ boundary a := hz a
    have hzb : z ≠ boundary b := hz b
    have habv : boundary a ≠ boundary b := fun h => hab (hboundaryInj h)
    by_cases hzbPos : Omega.indexOf z ≤ Omega.indexOf (boundary b)
    · by_cases hzaPos : Omega.indexOf z ≤ Omega.indexOf (boundary a)
      · by_cases habPos : Omega.indexOf (boundary a) ≤ Omega.indexOf (boundary b)
        · left
          exact GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_between_classical
            Omega (hboundaryMem a) hzbPos hzaPos habPos hza.symm habv
        · right
          exact GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_between_classical
            Omega (hboundaryMem b) hzaPos hzbPos (by omega) hzb.symm habv.symm
      · right
        exact GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
          Omega (hboundaryMem b) hzaPos (Or.inl hzbPos) hzb.symm habv.symm
    · by_cases hzaPos : Omega.indexOf z ≤ Omega.indexOf (boundary a)
      · left
        exact GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
          Omega (hboundaryMem a) hzbPos (Or.inl hzaPos) hza.symm habv
      · by_cases habPos : Omega.indexOf (boundary a) ≤ Omega.indexOf (boundary b)
        · left
          exact GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
            Omega (hboundaryMem a) hzbPos (Or.inr habPos) hza.symm habv
        · right
          exact GMIX24Split.CyclicBoundary.clockwiseOpenBetween_of_index_wrap_classical
            Omega (hboundaryMem b) hzaPos (Or.inr (by omega)) hzb.symm habv.symm
  have alternating (i j k : Fin 3)
      (hji : Omega.ClockwiseOpenBetween z (boundary i) (boundary j))
      (hik : Omega.ClockwiseOpenBetween z (boundary k) (boundary i)) :
      CrossEndpointAlternating Omega
        (hiddenPairingEndpoints z boundary i j k) := by
    dsimp [CrossEndpointAlternating, hiddenPairingEndpoints]
    exact ⟨hji,
      GMIX24Split.CyclicBoundary.clockwiseOpenBetween_rotate_right
        hzMem (hboundaryMem k) hik⟩
  rcases before_total 0 1 (by decide) with h01 | h10
  · rcases before_total 1 2 (by decide) with h12 | h21
    · exact Or.inr (Or.inr (Or.inl (alternating 1 0 2 h01 h12)))
    · rcases before_total 0 2 (by decide) with h02 | h20
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (alternating 2 0 1 h02 h21)))))
      · exact Or.inr (Or.inl (alternating 0 2 1 h20 h01))
  · rcases before_total 0 2 (by decide) with h02 | h20
    · exact Or.inl (alternating 0 1 2 h10 h02)
    · rcases before_total 1 2 (by decide) with h12 | h21
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (alternating 2 1 0 h12 h20)))))
      · exact Or.inr (Or.inr (Or.inr
          (Or.inl (alternating 1 2 0 h21 h10))))

/-- A boundary vertex on a tripod rim, distinct from the three feet and from
that rim's attachment, forces a cross in the same society. -/
theorem cross_of_hidden_rim_contact
    {H : GeneralSociety V}
    (T : H.Tripod) {z : V}
    (hzBoundary : z ∈ H.boundarySet)
    (hzNotFoot : ∀ a : Fin 3, z ≠ T.boundary a)
    {r : Fin 3} (hzRim : z ∈ (T.rim r).support)
    (hzAttach : z ≠ T.attach r) :
    Nonempty H.Cross := by
  classical
  have makeCross (i j k : Fin 3)
      (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (halt : CrossEndpointAlternating H.boundary
        (hiddenPairingEndpoints z T.boundary i j k)) :
      Nonempty H.Cross := by
    obtain ⟨p, q, hpq⟩ :=
      exists_disjoint_pairing_of_rim_contact T hzRim hzAttach hij hik hjk
    let E : CrossEndpoints H.boundary := {
      endpoint := hiddenPairingEndpoints z T.boundary i j k
      endpoint_mem := hiddenPairingEndpoints_mem T hzBoundary i j k
      endpoint_injective :=
        hiddenPairingEndpoints_injective T hzNotFoot hij hik hjk
      cyclic_alternating := halt
    }
    let p' : H.graph.Walk (E.endpoint 0) (E.endpoint 2) := by
      simpa [E, hiddenPairingEndpoints] using
        (p.toPath : H.graph.Walk z (T.boundary i))
    let q' : H.graph.Walk (E.endpoint 1) (E.endpoint 3) := by
      simpa [E, hiddenPairingEndpoints] using
        (q.toPath : H.graph.Walk (T.boundary j) (T.boundary k))
    have hp' : p'.IsPath := by
      simp [p', E, hiddenPairingEndpoints]
    have hq' : q'.IsPath := by
      simp [q', E, hiddenPairingEndpoints]
    apply Cross.of_disjoint_alternating_paths E hp' hq'
    have hpaths := Walk.toPath_support_disjoint (G := H.graph) hpq
    simpa [p', q', E, hiddenPairingEndpoints] using hpaths
  rcases hiddenPairingEndpoints_one_alternating H.boundary T.boundary
      hzBoundary T.boundary_mem T.boundary_injective hzNotFoot with
    h012 | h021 | h102 | h120 | h201 | h210
  · exact makeCross 0 1 2 (by decide) (by decide) (by decide) h012
  · exact makeCross 0 2 1 (by decide) (by decide) (by decide) h021
  · exact makeCross 1 0 2 (by decide) (by decide) (by decide) h102
  · exact makeCross 1 2 0 (by decide) (by decide) (by decide) h120
  · exact makeCross 2 0 1 (by decide) (by decide) (by decide) h201
  · exact makeCross 2 1 0 (by decide) (by decide) (by decide) h210
end GMIX24SourceProof

end GeneralSociety

end Schematic.Math.GraphTheory
