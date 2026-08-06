import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.Sides.Connectivity

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

/-- A path segment from `start` through a prescribed support set, followed by
a clean last-contact tail to the left boundary arc.  This is the support-level
version needed for mixed Kuratowski arms: the attachment segment need not lie
on the common-end endpoint path, only on the corresponding strict-subdivision
source-edge support. -/
structure SupportAttachedCleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (support : Set V) (start : V) : Type _ where
  x : V
  a : V
  attach : S.graph.Walk start x
  tail : S.graph.Walk x a
  a_mem_leftBoundaryArc : a ∈ P.leftBoundaryArc
  attach_isPath : attach.IsPath
  attach_support_subset :
    forall w : V, w ∈ attach.support -> w ∈ support
  tail_isPath : tail.IsPath
  tail_support_left :
    forall w : V, w ∈ tail.support -> w ∈ P.leftSide
  tail_support_outside :
    forall w : V, w ∈ tail.support -> w ∈ P.outside
  tail_internal_boundary_clean :
    Walk.InternalVertices tail ∩ S.boundarySet = ∅
  tail_clean_attach :
    forall w : V, w ∈ tail.support -> w ∈ attach.support -> w = x

/-- A path segment from `start` through a prescribed support set, followed by
a clean last-contact tail to the right boundary arc. -/
structure SupportAttachedCleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) (support : Set V) (start : V) : Type _ where
  x : V
  a : V
  attach : S.graph.Walk start x
  tail : S.graph.Walk x a
  a_mem_rightBoundaryArc : a ∈ P.rightBoundaryArc
  attach_isPath : attach.IsPath
  attach_support_subset :
    forall w : V, w ∈ attach.support -> w ∈ support
  tail_isPath : tail.IsPath
  tail_support_right :
    forall w : V, w ∈ tail.support -> w ∈ P.rightSide
  tail_support_outside :
    forall w : V, w ∈ tail.support -> w ∈ P.outside
  tail_internal_boundary_clean :
    Walk.InternalVertices tail ∩ S.boundarySet = ∅
  tail_clean_attach :
    forall w : V, w ∈ tail.support -> w ∈ attach.support -> w = x

noncomputable def SupportAttachedCleanTailToLeftBoundaryArc.walk
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc support start) :
    S.graph.Walk start A.a :=
  A.attach.append A.tail

noncomputable def SupportAttachedCleanTailToRightBoundaryArc.walk
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc support start) :
    S.graph.Walk start A.a :=
  A.attach.append A.tail

theorem SupportAttachedCleanTailToLeftBoundaryArc.walk_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc support start) :
    A.walk.IsPath := by
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    A.attach_isPath A.tail_isPath ?_
  intro w hwAttach hwTail
  exact A.tail_clean_attach w hwTail hwAttach

theorem SupportAttachedCleanTailToRightBoundaryArc.walk_isPath
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc support start) :
    A.walk.IsPath := by
  refine Walk.IsPath.append_of_support_inter_eq_endpoint
    A.attach_isPath A.tail_isPath ?_
  intro w hwAttach hwTail
  exact A.tail_clean_attach w hwTail hwAttach

theorem SupportAttachedCleanTailToLeftBoundaryArc.attach_mem_walk_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc support start)
    {w : V} (hw : w ∈ A.attach.support) :
    w ∈ A.walk.support := by
  rw [SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl hw

theorem SupportAttachedCleanTailToLeftBoundaryArc.tail_mem_walk_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc support start)
    {w : V} (hw : w ∈ A.tail.support) :
    w ∈ A.walk.support := by
  rw [SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inr hw

theorem SupportAttachedCleanTailToRightBoundaryArc.attach_mem_walk_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc support start)
    {w : V} (hw : w ∈ A.attach.support) :
    w ∈ A.walk.support := by
  rw [SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl hw

theorem SupportAttachedCleanTailToRightBoundaryArc.tail_mem_walk_support
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc support start)
    {w : V} (hw : w ∈ A.tail.support) :
    w ∈ A.walk.support := by
  rw [SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inr hw

theorem SupportAttachedCleanTailToLeftBoundaryArc.walk_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc support start)
    {w : V} (hw : w ∈ A.walk.support) :
    w ∈ support ∨ w ∈ P.leftSide := by
  rw [SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hwAttach | hwTail
  · exact Or.inl (A.attach_support_subset w hwAttach)
  · exact Or.inr (A.tail_support_left w hwTail)

theorem SupportAttachedCleanTailToRightBoundaryArc.walk_support_cases
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc support start)
    {w : V} (hw : w ∈ A.walk.support) :
    w ∈ support ∨ w ∈ P.rightSide := by
  rw [SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with hwAttach | hwTail
  · exact Or.inl (A.attach_support_subset w hwAttach)
  · exact Or.inr (A.tail_support_right w hwTail)

theorem SupportAttachedCleanTailToLeftBoundaryArc.a_mem_leftSide
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc support start) :
    A.a ∈ P.leftSide :=
  P.leftBoundaryArc_subset_leftSide A.a_mem_leftBoundaryArc

theorem SupportAttachedCleanTailToRightBoundaryArc.a_mem_rightSide
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {support : Set V} {start : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc support start) :
    A.a ∈ P.rightSide :=
  P.rightBoundaryArc_subset_rightSide A.a_mem_rightBoundaryArc

theorem SupportAttachedCleanTailToLeftBoundaryArc.a_ne_right
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportL supportR : Set V}
    {startL startR : V}
    (hno_cross : Not (Nonempty S.Cross))
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL)
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR) :
    L.a ≠ R.a := by
  intro h
  exact
    Set.disjoint_left.mp (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
      L.a_mem_leftSide
      (by simpa [h] using R.a_mem_rightSide)

theorem SupportAttachedCleanTailToRightBoundaryArc.a_ne_left
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportR supportL : Set V}
    {startR startL : V}
    (hno_cross : Not (Nonempty S.Cross))
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR)
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL) :
    R.a ≠ L.a := by
  intro h
  exact L.a_ne_right hno_cross R h.symm

theorem SupportAttachedCleanTailToRightBoundaryArc.tail_disjoint_left_tail
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportR supportL : Set V}
    {startR startL : V}
    (hno_cross : Not (Nonempty S.Cross))
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR)
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL) :
    Disjoint {v : V | v ∈ R.tail.support}
      {v : V | v ∈ L.tail.support} := by
  rw [Set.disjoint_left]
  intro v hvR hvL
  exact
    Set.disjoint_left.mp (P.leftSide_disjoint_rightSide_of_no_cross hno_cross)
      (L.tail_support_left v hvL)
      (R.tail_support_right v hvR)

theorem SupportAttachedCleanTailToLeftBoundaryArc.tail_disjoint_right_tail
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportL supportR : Set V}
    {startL startR : V}
    (hno_cross : Not (Nonempty S.Cross))
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL)
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR) :
    Disjoint {v : V | v ∈ L.tail.support}
      {v : V | v ∈ R.tail.support} :=
  (R.tail_disjoint_left_tail hno_cross L).symm

/-- If the two attachment segments, the two cross attachment-tail pairs, and
the two tails are disjoint, then the full support-attached right and left
legs are disjoint. -/
theorem SupportAttachedCleanTailToRightBoundaryArc.walk_disjoint_left_walk_of_parts
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportR supportL : Set V}
    {startR startL : V}
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR)
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL)
    (hAA :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.attach.support})
    (hAT :
      Disjoint {v : V | v ∈ R.attach.support}
        {v : V | v ∈ L.tail.support})
    (hTA :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.attach.support})
    (hTT :
      Disjoint {v : V | v ∈ R.tail.support}
        {v : V | v ∈ L.tail.support}) :
    Disjoint {v : V | v ∈ R.walk.support}
      {v : V | v ∈ L.walk.support} := by
  rw [Set.disjoint_left]
  intro v hvR hvL
  change v ∈ R.walk.support at hvR
  change v ∈ L.walk.support at hvL
  rw [SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvR
  rw [SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvL
  rcases hvR with hvR_attach | hvR_tail
  · rcases hvL with hvL_attach | hvL_tail
    · exact Set.disjoint_left.mp hAA hvR_attach hvL_attach
    · exact Set.disjoint_left.mp hAT hvR_attach hvL_tail
  · rcases hvL with hvL_attach | hvL_tail
    · exact Set.disjoint_left.mp hTA hvR_tail hvL_attach
    · exact Set.disjoint_left.mp hTT hvR_tail hvL_tail

/-- Symmetric full-leg disjointness for a left support-attached leg against a
right support-attached leg. -/
theorem SupportAttachedCleanTailToLeftBoundaryArc.walk_disjoint_right_walk_of_parts
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportL supportR : Set V}
    {startL startR : V}
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL)
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR)
    (hAA :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ R.attach.support})
    (hAT :
      Disjoint {v : V | v ∈ L.attach.support}
        {v : V | v ∈ R.tail.support})
    (hTA :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ R.attach.support})
    (hTT :
      Disjoint {v : V | v ∈ L.tail.support}
        {v : V | v ∈ R.tail.support}) :
    Disjoint {v : V | v ∈ L.walk.support}
      {v : V | v ∈ R.walk.support} :=
  (R.walk_disjoint_left_walk_of_parts L hAA.symm hTA.symm hAT.symm hTT.symm).symm

/-- Full-leg disjointness for two left support-attached legs from componentwise
disjointness. -/
theorem SupportAttachedCleanTailToLeftBoundaryArc.walk_disjoint_left_walk_of_parts
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportA supportB : Set V}
    {startA startB : V}
    (A : P.SupportAttachedCleanTailToLeftBoundaryArc supportA startA)
    (B : P.SupportAttachedCleanTailToLeftBoundaryArc supportB startB)
    (hAA :
      Disjoint {v : V | v ∈ A.attach.support}
        {v : V | v ∈ B.attach.support})
    (hAT :
      Disjoint {v : V | v ∈ A.attach.support}
        {v : V | v ∈ B.tail.support})
    (hTA :
      Disjoint {v : V | v ∈ A.tail.support}
        {v : V | v ∈ B.attach.support})
    (hTT :
      Disjoint {v : V | v ∈ A.tail.support}
        {v : V | v ∈ B.tail.support}) :
    Disjoint {v : V | v ∈ A.walk.support}
      {v : V | v ∈ B.walk.support} := by
  rw [Set.disjoint_left]
  intro v hvA hvB
  change v ∈ A.walk.support at hvA
  change v ∈ B.walk.support at hvB
  rw [SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvA
  rw [SupportAttachedCleanTailToLeftBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvB
  rcases hvA with hvA_attach | hvA_tail
  · rcases hvB with hvB_attach | hvB_tail
    · exact Set.disjoint_left.mp hAA hvA_attach hvB_attach
    · exact Set.disjoint_left.mp hAT hvA_attach hvB_tail
  · rcases hvB with hvB_attach | hvB_tail
    · exact Set.disjoint_left.mp hTA hvA_tail hvB_attach
    · exact Set.disjoint_left.mp hTT hvA_tail hvB_tail

/-- Full-leg disjointness for two right support-attached legs from
componentwise disjointness. -/
theorem SupportAttachedCleanTailToRightBoundaryArc.walk_disjoint_right_walk_of_parts
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportA supportB : Set V}
    {startA startB : V}
    (A : P.SupportAttachedCleanTailToRightBoundaryArc supportA startA)
    (B : P.SupportAttachedCleanTailToRightBoundaryArc supportB startB)
    (hAA :
      Disjoint {v : V | v ∈ A.attach.support}
        {v : V | v ∈ B.attach.support})
    (hAT :
      Disjoint {v : V | v ∈ A.attach.support}
        {v : V | v ∈ B.tail.support})
    (hTA :
      Disjoint {v : V | v ∈ A.tail.support}
        {v : V | v ∈ B.attach.support})
    (hTT :
      Disjoint {v : V | v ∈ A.tail.support}
        {v : V | v ∈ B.tail.support}) :
    Disjoint {v : V | v ∈ A.walk.support}
      {v : V | v ∈ B.walk.support} := by
  rw [Set.disjoint_left]
  intro v hvA hvB
  change v ∈ A.walk.support at hvA
  change v ∈ B.walk.support at hvB
  rw [SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvA
  rw [SupportAttachedCleanTailToRightBoundaryArc.walk,
    SimpleGraph.Walk.mem_support_append_iff] at hvB
  rcases hvA with hvA_attach | hvA_tail
  · rcases hvB with hvB_attach | hvB_tail
    · exact Set.disjoint_left.mp hAA hvA_attach hvB_attach
    · exact Set.disjoint_left.mp hAT hvA_attach hvB_tail
  · rcases hvB with hvB_attach | hvB_tail
    · exact Set.disjoint_left.mp hTA hvA_tail hvB_attach
    · exact Set.disjoint_left.mp hTT hvA_tail hvB_tail

theorem supportAttachedBoundary_injective_sideLeft
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportR supportL supportU : Set V}
    {startR startL startU : V}
    (hno_cross : Not (Nonempty S.Cross))
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR)
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL)
    (U : P.SupportAttachedCleanTailToLeftBoundaryArc supportU startU)
    (hLU : L.a ≠ U.a) :
    Function.Injective
      (fun i : Fin 3 =>
        if i = 0 then R.a else if i = 1 then L.a else U.a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact False.elim ((R.a_ne_left hno_cross L) hij)
  · exact False.elim ((R.a_ne_left hno_cross U) hij)
  · exact False.elim ((R.a_ne_left hno_cross L) hij.symm)
  · exact False.elim (hLU hij)
  · exact False.elim ((R.a_ne_left hno_cross U) hij.symm)
  · exact False.elim (hLU hij.symm)

theorem supportAttachedBoundary_injective_sideRight
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S} {supportR supportL supportU : Set V}
    {startR startL startU : V}
    (hno_cross : Not (Nonempty S.Cross))
    (R : P.SupportAttachedCleanTailToRightBoundaryArc supportR startR)
    (L : P.SupportAttachedCleanTailToLeftBoundaryArc supportL startL)
    (U : P.SupportAttachedCleanTailToRightBoundaryArc supportU startU)
    (hRU : R.a ≠ U.a) :
    Function.Injective
      (fun i : Fin 3 =>
        if i = 0 then R.a else if i = 1 then L.a else U.a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact False.elim ((R.a_ne_left hno_cross L) hij)
  · exact False.elim (hRU hij)
  · exact False.elim ((R.a_ne_left hno_cross L) hij.symm)
  · exact False.elim ((U.a_ne_left hno_cross L) hij.symm)
  · exact False.elim (hRU hij.symm)
  · exact False.elim ((U.a_ne_left hno_cross L) hij)

theorem exists_supportAttachedCleanTailToLeftBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {support : Set V} {start target : V}
    (q : S.graph.Walk start target)
    (hq_path : q.IsPath)
    (hq_support : forall w : V, w ∈ q.support -> w ∈ support)
    (htarget : target ∈ P.leftSide) :
    Nonempty (P.SupportAttachedCleanTailToLeftBoundaryArc support start) := by
  classical
  rcases P.exists_clean_tail_from_path_target_to_leftBoundaryArc
      hno_cross q htarget with
    ⟨x, a, tail, hxq, ha, htail_path, htail_left, htail_outside,
      htail_boundary, htail_clean⟩
  let attach : S.graph.Walk start x := q.takeUntil x hxq
  have hattach_path : attach.IsPath := by
    simpa [attach] using hq_path.takeUntil hxq
  have hattach_support :
      forall w : V, w ∈ attach.support -> w ∈ support := by
    intro w hw
    exact hq_support w
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hw))
  have hclean_attach :
      forall w : V, w ∈ tail.support -> w ∈ attach.support -> w = x := by
    intro w hwTail hwAttach
    exact htail_clean w hwTail
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hwAttach))
  exact ⟨{
    x := x
    a := a
    attach := attach
    tail := tail
    a_mem_leftBoundaryArc := ha
    attach_isPath := hattach_path
    attach_support_subset := hattach_support
    tail_isPath := htail_path
    tail_support_left := htail_left
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_attach := hclean_attach }⟩

theorem exists_supportAttachedCleanTailToRightBoundaryArc
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {support : Set V} {start target : V}
    (q : S.graph.Walk start target)
    (hq_path : q.IsPath)
    (hq_support : forall w : V, w ∈ q.support -> w ∈ support)
    (htarget : target ∈ P.rightSide) :
    Nonempty (P.SupportAttachedCleanTailToRightBoundaryArc support start) := by
  classical
  rcases P.exists_clean_tail_from_path_target_to_rightBoundaryArc
      hno_cross q htarget with
    ⟨x, a, tail, hxq, ha, htail_path, htail_right, htail_outside,
      htail_boundary, htail_clean⟩
  let attach : S.graph.Walk start x := q.takeUntil x hxq
  have hattach_path : attach.IsPath := by
    simpa [attach] using hq_path.takeUntil hxq
  have hattach_support :
      forall w : V, w ∈ attach.support -> w ∈ support := by
    intro w hw
    exact hq_support w
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hw))
  have hclean_attach :
      forall w : V, w ∈ tail.support -> w ∈ attach.support -> w = x := by
    intro w hwTail hwAttach
    exact htail_clean w hwTail
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hwAttach))
  exact ⟨{
    x := x
    a := a
    attach := attach
    tail := tail
    a_mem_rightBoundaryArc := ha
    attach_isPath := hattach_path
    attach_support_subset := hattach_support
    tail_isPath := htail_path
    tail_support_right := htail_right
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_attach := hclean_attach }⟩

theorem exists_supportAttachedCleanTailToLeftBoundaryArc_attach_avoids
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {support : Set V} {start target avoid : V}
    (q : S.graph.Walk start target)
    (hq_path : q.IsPath)
    (hq_support : forall w : V, w ∈ q.support -> w ∈ support)
    (htarget : target ∈ P.leftSide)
    (havoid : avoid ∉ q.support) :
    Exists fun A : P.SupportAttachedCleanTailToLeftBoundaryArc support start =>
      avoid ∉ A.attach.support := by
  classical
  rcases P.exists_clean_tail_from_path_target_to_leftBoundaryArc
      hno_cross q htarget with
    ⟨x, a, tail, hxq, ha, htail_path, htail_left, htail_outside,
      htail_boundary, htail_clean⟩
  let attach : S.graph.Walk start x := q.takeUntil x hxq
  have hattach_path : attach.IsPath := by
    simpa [attach] using hq_path.takeUntil hxq
  have hattach_support :
      forall w : V, w ∈ attach.support -> w ∈ support := by
    intro w hw
    exact hq_support w
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hw))
  have hclean_attach :
      forall w : V, w ∈ tail.support -> w ∈ attach.support -> w = x := by
    intro w hwTail hwAttach
    exact htail_clean w hwTail
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hwAttach))
  refine ⟨{
    x := x
    a := a
    attach := attach
    tail := tail
    a_mem_leftBoundaryArc := ha
    attach_isPath := hattach_path
    attach_support_subset := hattach_support
    tail_isPath := htail_path
    tail_support_left := htail_left
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_attach := hclean_attach }, ?_⟩
  intro havoid_attach
  exact havoid
    (SimpleGraph.Walk.support_takeUntil_subset q hxq
      (by simpa [attach] using havoid_attach))

theorem exists_supportAttachedCleanTailToRightBoundaryArc_attach_avoids
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {support : Set V} {start target avoid : V}
    (q : S.graph.Walk start target)
    (hq_path : q.IsPath)
    (hq_support : forall w : V, w ∈ q.support -> w ∈ support)
    (htarget : target ∈ P.rightSide)
    (havoid : avoid ∉ q.support) :
    Exists fun A : P.SupportAttachedCleanTailToRightBoundaryArc support start =>
      avoid ∉ A.attach.support := by
  classical
  rcases P.exists_clean_tail_from_path_target_to_rightBoundaryArc
      hno_cross q htarget with
    ⟨x, a, tail, hxq, ha, htail_path, htail_right, htail_outside,
      htail_boundary, htail_clean⟩
  let attach : S.graph.Walk start x := q.takeUntil x hxq
  have hattach_path : attach.IsPath := by
    simpa [attach] using hq_path.takeUntil hxq
  have hattach_support :
      forall w : V, w ∈ attach.support -> w ∈ support := by
    intro w hw
    exact hq_support w
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hw))
  have hclean_attach :
      forall w : V, w ∈ tail.support -> w ∈ attach.support -> w = x := by
    intro w hwTail hwAttach
    exact htail_clean w hwTail
      (SimpleGraph.Walk.support_takeUntil_subset q hxq
        (by simpa [attach] using hwAttach))
  refine ⟨{
    x := x
    a := a
    attach := attach
    tail := tail
    a_mem_rightBoundaryArc := ha
    attach_isPath := hattach_path
    attach_support_subset := hattach_support
    tail_isPath := htail_path
    tail_support_right := htail_right
    tail_support_outside := htail_outside
    tail_internal_boundary_clean := htail_boundary
    tail_clean_attach := hclean_attach }, ?_⟩
  intro havoid_attach
  exact havoid
    (SimpleGraph.Walk.support_takeUntil_subset q hxq
      (by simpa [attach] using havoid_attach))

theorem leftSide_inter_rightSide_eq_empty_of_no_cross [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross)) :
    P.leftSide ∩ P.rightSide = ∅ := by
  simpa [Set.disjoint_iff_inter_eq_empty] using
    P.leftSide_disjoint_rightSide_of_no_cross hno_cross

theorem not_adj_leftSide_rightSide_of_no_cross [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    {u v : V}
    (hu : u ∈ P.leftSide)
    (hv : v ∈ P.rightSide) :
    Not (S.graph.Adj u v) := by
  intro huv
  have hsides := P.leftSide_disjoint_rightSide_of_no_cross hno_cross
  have hu_left : u ∈ ComponentUnionMeeting S.graph P.leftBoundaryArc P.outside := by
    simpa [leftSide] using hu
  have hvX : v ∈ P.outside := P.rightSide_subset_outside hv
  rcases hu_left with ⟨huX, C, huC, a, haX, haA, haC⟩
  have huv_induce :
      (S.graph.induce P.outside).Adj
        (⟨u, huX⟩ : P.outside) (⟨v, hvX⟩ : P.outside) :=
    huv
  have hvC : (⟨v, hvX⟩ : P.outside) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp huC huv_induce
  have hvLeft : v ∈ P.leftSide := by
    change v ∈ ComponentUnionMeeting S.graph P.leftBoundaryArc P.outside
    exact ⟨hvX, C, hvC, a, haX, haA, haC⟩
  exact Set.disjoint_left.mp hsides hvLeft hv

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
