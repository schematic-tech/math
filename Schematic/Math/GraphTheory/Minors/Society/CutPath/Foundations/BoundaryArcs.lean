import Schematic.Math.GraphTheory.Minors.Society.CutPath.Foundations.PathIntervals

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24CutPath

def leftBoundaryArc [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : Set V :=
  S.boundary.clockwiseArcSet P.s P.t

def rightBoundaryArc [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) : Set V :=
  S.boundary.clockwiseArcSet P.t P.s

theorem leftBoundaryArc_subset [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArc ⊆ S.boundarySet := by
  simpa [leftBoundaryArc, GeneralSociety.boundarySet] using
    S.boundary.clockwiseArcSet_subset P.s P.t

theorem rightBoundaryArc_subset [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightBoundaryArc ⊆ S.boundarySet := by
  simpa [rightBoundaryArc, GeneralSociety.boundarySet] using
    S.boundary.clockwiseArcSet_subset P.t P.s

theorem leftBoundaryArc_finite [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArc.Finite :=
  S.boundarySet_finite.subset P.leftBoundaryArc_subset

theorem rightBoundaryArc_finite [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightBoundaryArc.Finite :=
  S.boundarySet_finite.subset P.rightBoundaryArc_subset

theorem leftBoundaryArc_union_right [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArc ∪ P.rightBoundaryArc =
      S.boundarySet \ ({P.s, P.t} : Set V) := by
  simpa [leftBoundaryArc, rightBoundaryArc, GeneralSociety.boundarySet] using
    S.boundary.clockwiseArcSet_union_reverse
      P.s_mem_boundary P.t_mem_boundary P.s_ne_t

theorem leftBoundaryArc_disjoint_right [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    Disjoint P.leftBoundaryArc P.rightBoundaryArc := by
  simpa [leftBoundaryArc, rightBoundaryArc] using
    S.boundary.clockwiseArcSet_disjoint_reverse
      P.s_mem_boundary P.s_ne_t

/-- Every ambient boundary vertex is one of the two cut endpoints or lies on
one of the two open boundary arcs they determine. -/
theorem boundary_mem_endpoint_or_arc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S) {z : V}
    (hz : z ∈ S.boundarySet) :
    z = P.s ∨ z = P.t ∨ z ∈ P.leftBoundaryArc ∨
      z ∈ P.rightBoundaryArc := by
  by_cases hzs : z = P.s
  · exact Or.inl hzs
  by_cases hzt : z = P.t
  · exact Or.inr (Or.inl hzt)
  have hzDiff : z ∈ S.boundarySet \ ({P.s, P.t} : Set V) := by
    refine ⟨hz, ?_⟩
    simp [hzs, hzt]
  have hzUnion : z ∈ P.leftBoundaryArc ∪ P.rightBoundaryArc := by
    rw [P.leftBoundaryArc_union_right]
    exact hzDiff
  rcases hzUnion with hzLeft | hzRight
  · exact Or.inr (Or.inr (Or.inl hzLeft))
  · exact Or.inr (Or.inr (Or.inr hzRight))

/-- With at least three boundary vertices, the two cut endpoints cannot exhaust
the boundary.  Consequently, if one open boundary arc is empty then the
opposite open arc is nonempty. -/
theorem rightBoundaryArc_nonempty_of_leftBoundaryArc_eq_empty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hlarge : 3 ≤ S.boundarySet.ncard)
    (hleft : P.leftBoundaryArc = ∅) :
    P.rightBoundaryArc.Nonempty := by
  by_contra hrightNonempty
  have hright : P.rightBoundaryArc = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hrightNonempty
  have hdiff : S.boundarySet \ ({P.s, P.t} : Set V) = ∅ := by
    rw [← P.leftBoundaryArc_union_right, hleft, hright]
    simp
  have hsubset : S.boundarySet ⊆ ({P.s, P.t} : Set V) := by
    intro z hz
    by_contra hzPair
    have hzDiff : z ∈ S.boundarySet \ ({P.s, P.t} : Set V) :=
      ⟨hz, hzPair⟩
    simp [hdiff] at hzDiff
  have hcard : S.boundarySet.ncard ≤ ({P.s, P.t} : Set V).ncard :=
    Set.ncard_le_ncard hsubset (Set.toFinite _)
  rw [Set.ncard_pair P.s_ne_t] at hcard
  omega

/-- Symmetric form of
`rightBoundaryArc_nonempty_of_leftBoundaryArc_eq_empty`. -/
theorem leftBoundaryArc_nonempty_of_rightBoundaryArc_eq_empty
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hlarge : 3 ≤ S.boundarySet.ncard)
    (hright : P.rightBoundaryArc = ∅) :
    P.leftBoundaryArc.Nonempty := by
  simpa using
    P.reverse.rightBoundaryArc_nonempty_of_leftBoundaryArc_eq_empty
      hlarge (by simpa using hright)

theorem leftBoundaryArc_subset_outside [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.leftBoundaryArc ⊆ P.outside := by
  intro v hv
  have hvopen : S.boundary.ClockwiseOpenBetween P.s P.t v := by
    simpa [leftBoundaryArc] using hv
  have hvboundary : v ∈ S.boundarySet :=
    P.leftBoundaryArc_subset hv
  refine ⟨Or.inr hvboundary, ?_⟩
  intro hvpath
  have hvint : v ∈ Walk.InternalVertices P.path :=
    ⟨hvpath, hvopen.2.1, hvopen.2.2⟩
  have hbad : v ∈ Walk.InternalVertices P.path ∩ S.boundarySet :=
    ⟨hvint, hvboundary⟩
  have hnot : v ∉ Walk.InternalVertices P.path ∩ S.boundarySet := by
    rw [P.internal_disjoint_boundary]
    simp
  exact hnot hbad

theorem leftBoundaryArc_not_mem_pathSet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.leftBoundaryArc) :
    v ∉ P.pathSet := by
  exact (P.leftBoundaryArc_subset_outside hv).2

theorem leftBoundaryArc_ne_s [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.leftBoundaryArc) :
    v ≠ P.s := by
  intro h
  exact P.leftBoundaryArc_not_mem_pathSet hv (by
    simpa [h] using P.s_mem_pathSet)

theorem leftBoundaryArc_ne_t [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.leftBoundaryArc) :
    v ≠ P.t := by
  intro h
  exact P.leftBoundaryArc_not_mem_pathSet hv (by
    simpa [h] using P.t_mem_pathSet)

theorem rightBoundaryArc_subset_outside [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) :
    P.rightBoundaryArc ⊆ P.outside := by
  intro v hv
  have hvopen : S.boundary.ClockwiseOpenBetween P.t P.s v := by
    simpa [rightBoundaryArc] using hv
  have hvboundary : v ∈ S.boundarySet :=
    P.rightBoundaryArc_subset hv
  refine ⟨Or.inr hvboundary, ?_⟩
  intro hvpath
  have hvint : v ∈ Walk.InternalVertices P.path :=
    ⟨hvpath, hvopen.2.2, hvopen.2.1⟩
  have hbad : v ∈ Walk.InternalVertices P.path ∩ S.boundarySet :=
    ⟨hvint, hvboundary⟩
  have hnot : v ∉ Walk.InternalVertices P.path ∩ S.boundarySet := by
    rw [P.internal_disjoint_boundary]
    simp
  exact hnot hbad

theorem rightBoundaryArc_not_mem_pathSet [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.rightBoundaryArc) :
    v ∉ P.pathSet := by
  exact (P.rightBoundaryArc_subset_outside hv).2

theorem rightBoundaryArc_ne_s [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.rightBoundaryArc) :
    v ≠ P.s := by
  intro h
  exact P.rightBoundaryArc_not_mem_pathSet hv (by
    simpa [h] using P.s_mem_pathSet)

theorem rightBoundaryArc_ne_t [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S) {v : V}
    (hv : v ∈ P.rightBoundaryArc) :
    v ≠ P.t := by
  intro h
  exact P.rightBoundaryArc_not_mem_pathSet hv (by
    simpa [h] using P.t_mem_pathSet)

/-- The three original boundary vertices used when a side obstruction is
converted back to the ambient society: the cut-path start, a boundary-arc
vertex, and the cut-path end. -/
def boundaryTriple {S : GeneralSociety V} (P : GMIX24CutPath S)
    (a : V) : Fin 3 -> V
  | 0 => P.s
  | 1 => a
  | 2 => P.t

/-- The same three ambient boundary vertices as `boundaryTriple`, with the
two cut-path ends reversed.

This orientation is used by the first-collapsed-leg residual in GM IX `(2.4)`:
the second ordered foot is routed forward to `t`, while the collapsed first
branch supplies a route back to `s`. -/
def boundaryTripleReverseEnds {S : GeneralSociety V} (P : GMIX24CutPath S)
    (a : V) : Fin 3 -> V
  | 0 => P.t
  | 1 => a
  | 2 => P.s

theorem boundaryTriple_mem_of_leftArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.leftBoundaryArc) :
    forall i : Fin 3, P.boundaryTriple a i ∈ S.boundarySet := by
  intro i
  fin_cases i
  · exact P.s_mem_boundary
  · exact P.leftBoundaryArc_subset ha
  · exact P.t_mem_boundary

theorem boundaryTriple_mem_of_rightArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.rightBoundaryArc) :
    forall i : Fin 3, P.boundaryTriple a i ∈ S.boundarySet := by
  intro i
  fin_cases i
  · exact P.s_mem_boundary
  · exact P.rightBoundaryArc_subset ha
  · exact P.t_mem_boundary

theorem boundaryTriple_injective_of_leftArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.leftBoundaryArc) :
    Function.Injective (P.boundaryTriple a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [boundaryTriple] at hij ⊢
  · exact False.elim (P.leftBoundaryArc_ne_s ha hij.symm)
  · exact False.elim (P.s_ne_t hij)
  · exact False.elim (P.leftBoundaryArc_ne_s ha hij)
  · exact False.elim (P.leftBoundaryArc_ne_t ha hij)
  · exact False.elim (P.s_ne_t hij.symm)
  · exact False.elim (P.leftBoundaryArc_ne_t ha hij.symm)

/-- Membership for the reversed-end ambient boundary triple. -/
theorem boundaryTripleReverseEnds_mem_of_leftArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.leftBoundaryArc) :
    forall i : Fin 3, P.boundaryTripleReverseEnds a i ∈ S.boundarySet := by
  intro i
  fin_cases i
  · exact P.t_mem_boundary
  · exact P.leftBoundaryArc_subset ha
  · exact P.s_mem_boundary

/-- Injectivity for the reversed-end ambient boundary triple. -/
theorem boundaryTripleReverseEnds_injective_of_leftArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.leftBoundaryArc) :
    Function.Injective (P.boundaryTripleReverseEnds a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [boundaryTripleReverseEnds] at hij ⊢
  · exact False.elim (P.leftBoundaryArc_ne_t ha hij.symm)
  · exact False.elim (P.s_ne_t hij.symm)
  · exact False.elim (P.leftBoundaryArc_ne_t ha hij)
  · exact False.elim (P.leftBoundaryArc_ne_s ha hij)
  · exact False.elim (P.s_ne_t hij)
  · exact False.elim (P.leftBoundaryArc_ne_s ha hij.symm)

theorem boundaryTriple_injective_of_rightArc [DecidableEq V]
    {S : GeneralSociety V} (P : GMIX24CutPath S)
    {a : V} (ha : a ∈ P.rightBoundaryArc) :
    Function.Injective (P.boundaryTriple a) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [boundaryTriple] at hij ⊢
  · exact False.elim (P.rightBoundaryArc_ne_s ha hij.symm)
  · exact False.elim (P.s_ne_t hij)
  · exact False.elim (P.rightBoundaryArc_ne_s ha hij)
  · exact False.elim (P.rightBoundaryArc_ne_t ha hij)
  · exact False.elim (P.s_ne_t hij.symm)
  · exact False.elim (P.rightBoundaryArc_ne_t ha hij.symm)

/-- Ordered tails from three old feet on the cut path to the ambient boundary
triple `(s, a, t)`: the first foot is sent backwards along `P` to `s`, the
middle foot uses the supplied clean tail to `a`, and the third foot is sent
forwards along `P` to `t`. -/
def orderedBoundaryTripleTails [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a) :
    forall i : Fin 3, S.graph.Walk (oldBoundary i) (P.boundaryTriple a i) :=
  Walk.orderedThreeBoundaryTails
    (oldBoundary := oldBoundary)
    (newBoundary := P.boundaryTriple a)
    P.path P.path_isPath
    (fun i => by simpa [pathSet] using hold i)
    middle

theorem orderedBoundaryTripleTails_isPath [DecidableEq V]
    {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    {middle : S.graph.Walk (oldBoundary 1) a}
    (hmiddle : middle.IsPath) :
    forall i : Fin 3,
      (P.orderedBoundaryTripleTails hold a middle i).IsPath := by
  intro i
  simpa [orderedBoundaryTripleTails] using
    Walk.orderedThreeBoundaryTails_isPath
      (oldBoundary := oldBoundary)
      (newBoundary := P.boundaryTriple a)
      P.path_isPath
      (fun i => by simpa [pathSet] using hold i)
      hmiddle i

theorem orderedBoundaryTripleTails_zero_support_subset_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    {z : V}
    (hz : z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support) :
    z ∈ P.pathSet := by
  have hzpath :
      z ∈ P.path.support := by
    simpa [orderedBoundaryTripleTails] using
      Walk.orderedThreeBoundaryTails_zero_support_subset
        (oldBoundary := oldBoundary)
        (newBoundary := P.boundaryTriple a)
        P.path_isPath
        (fun i => by simpa [pathSet] using hold i)
        middle hz
  simpa [pathSet] using hzpath

theorem orderedBoundaryTripleTails_two_support_subset_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    {z : V}
    (hz : z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support) :
    z ∈ P.pathSet := by
  have hzpath :
      z ∈ P.path.support := by
    simpa [orderedBoundaryTripleTails] using
      Walk.orderedThreeBoundaryTails_two_support_subset
        (oldBoundary := oldBoundary)
        (newBoundary := P.boundaryTriple a)
        P.path_isPath
        (fun i => by simpa [pathSet] using hold i)
        middle hz
  simpa [pathSet] using hzpath

theorem orderedBoundaryTripleTails_outer_disjoint
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    (h02 :
      Walk.supportIndex P.path (oldBoundary 0) <
        Walk.supportIndex P.path (oldBoundary 2)) :
    Disjoint
      {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support}
      {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support} := by
  simpa [orderedBoundaryTripleTails] using
    Walk.orderedThreeBoundaryTails_outer_disjoint
      (oldBoundary := oldBoundary)
      (newBoundary := P.boundaryTriple a)
      P.path_isPath
      (fun i => by simpa [pathSet] using hold i)
      middle h02

theorem orderedBoundaryTripleTails_zero_disjoint_middle_of_internal_avoids_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    {a : V}
    (middle : S.graph.Walk (oldBoundary 1) a)
    (ha_not_path : a ∉ P.pathSet)
    (h01 :
      Walk.supportIndex P.path (oldBoundary 0) <
        Walk.supportIndex P.path (oldBoundary 1))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅) :
    Disjoint
      {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support}
      {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support} := by
  rw [Set.disjoint_left]
  intro z hz0 hz1
  have hzpath : z ∈ P.pathSet :=
    P.orderedBoundaryTripleTails_zero_support_subset_pathSet hold a middle hz0
  have hzone : z ∈ middle.support := by
    simpa [orderedBoundaryTripleTails] using hz1
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := middle) hzone with hzint | hzend
  · have hbad : z ∈ Walk.InternalVertices middle ∩ P.pathSet :=
      ⟨hzint, hzpath⟩
    rw [hmiddle_internal] at hbad
    exact hbad
  · rcases hzend with hzstart | hzend
    · have hnot :
          oldBoundary 1 ∉
            (P.orderedBoundaryTripleTails hold a middle 0).support := by
        simpa [orderedBoundaryTripleTails] using
          Walk.orderedThreeBoundaryTails_one_not_mem_zero_of_order
            (oldBoundary := oldBoundary)
            (newBoundary := P.boundaryTriple a)
            P.path_isPath
            (fun i => by simpa [pathSet] using hold i)
            middle h01
      exact hnot (by simpa [hzstart] using hz0)
    · exact ha_not_path (by simpa [hzend] using hzpath)

theorem orderedBoundaryTripleTails_middle_disjoint_two_of_internal_avoids_pathSet
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    {a : V}
    (middle : S.graph.Walk (oldBoundary 1) a)
    (ha_not_path : a ∉ P.pathSet)
    (h12 :
      Walk.supportIndex P.path (oldBoundary 1) <
        Walk.supportIndex P.path (oldBoundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅) :
    Disjoint
      {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support}
      {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support} := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have hzpath : z ∈ P.pathSet :=
    P.orderedBoundaryTripleTails_two_support_subset_pathSet hold a middle hz2
  have hzone : z ∈ middle.support := by
    simpa [orderedBoundaryTripleTails] using hz1
  rcases
      Walk.mem_internalVertices_or_eq_start_or_eq_end_of_mem_support
        (p := middle) hzone with hzint | hzend
  · have hbad : z ∈ Walk.InternalVertices middle ∩ P.pathSet :=
      ⟨hzint, hzpath⟩
    rw [hmiddle_internal] at hbad
    exact hbad
  · rcases hzend with hzstart | hzend
    · have hnot :
          oldBoundary 1 ∉
            (P.orderedBoundaryTripleTails hold a middle 2).support := by
        simpa [orderedBoundaryTripleTails] using
          Walk.orderedThreeBoundaryTails_one_not_mem_two_of_order
            (oldBoundary := oldBoundary)
            (newBoundary := P.boundaryTriple a)
            P.path_isPath
            (fun i => by simpa [pathSet] using hold i)
            middle h12
      exact hnot (by simpa [hzstart] using hz2)
    · exact ha_not_path (by simpa [hzend] using hzpath)

/-- In the ordered `(s,a,t)` tail package, the middle old foot is not on the
tail from the first old foot back to `s`. -/
theorem orderedBoundaryTripleTails_one_not_mem_zero_of_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    (h01 :
      Walk.supportIndex P.path (oldBoundary 0) <
        Walk.supportIndex P.path (oldBoundary 1)) :
    oldBoundary 1 ∉
      (P.orderedBoundaryTripleTails hold a middle 0).support := by
  simpa [orderedBoundaryTripleTails] using
    Walk.orderedThreeBoundaryTails_one_not_mem_zero_of_order
      (oldBoundary := oldBoundary)
      (newBoundary := P.boundaryTriple a)
      P.path_isPath
      (fun i => by simpa [pathSet] using hold i)
      middle h01

/-- In the ordered `(s,a,t)` tail package, the third old foot is not on the
tail from the first old foot back to `s`. -/
theorem orderedBoundaryTripleTails_two_not_mem_zero_of_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    (h02 :
      Walk.supportIndex P.path (oldBoundary 0) <
        Walk.supportIndex P.path (oldBoundary 2)) :
    oldBoundary 2 ∉
      (P.orderedBoundaryTripleTails hold a middle 0).support := by
  simpa [orderedBoundaryTripleTails] using
    Walk.orderedThreeBoundaryTails_two_not_mem_zero_of_order
      (oldBoundary := oldBoundary)
      (newBoundary := P.boundaryTriple a)
      P.path_isPath
      (fun i => by simpa [pathSet] using hold i)
      middle h02

/-- In the ordered `(s,a,t)` tail package, the first old foot is not on the
tail from the third old foot forward to `t`. -/
theorem orderedBoundaryTripleTails_zero_not_mem_two_of_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    (h02 :
      Walk.supportIndex P.path (oldBoundary 0) <
        Walk.supportIndex P.path (oldBoundary 2)) :
    oldBoundary 0 ∉
      (P.orderedBoundaryTripleTails hold a middle 2).support := by
  simpa [orderedBoundaryTripleTails] using
    Walk.orderedThreeBoundaryTails_zero_not_mem_two_of_order
      (oldBoundary := oldBoundary)
      (newBoundary := P.boundaryTriple a)
      P.path_isPath
      (fun i => by simpa [pathSet] using hold i)
      middle h02

/-- In the ordered `(s,a,t)` tail package, the middle old foot is not on the
tail from the third old foot forward to `t`. -/
theorem orderedBoundaryTripleTails_one_not_mem_two_of_order
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    {oldBoundary : Fin 3 -> V}
    (hold : forall i : Fin 3, oldBoundary i ∈ P.pathSet)
    (a : V)
    (middle : S.graph.Walk (oldBoundary 1) a)
    (h12 :
      Walk.supportIndex P.path (oldBoundary 1) <
        Walk.supportIndex P.path (oldBoundary 2)) :
    oldBoundary 1 ∉
      (P.orderedBoundaryTripleTails hold a middle 2).support := by
  simpa [orderedBoundaryTripleTails] using
    Walk.orderedThreeBoundaryTails_one_not_mem_two_of_order
      (oldBoundary := oldBoundary)
      (newBoundary := P.boundaryTriple a)
      P.path_isPath
      (fun i => by simpa [pathSet] using hold i)
      middle h12

/-- The three boundary feet of a tripod that all lie on the cut path can be
sorted by their order on that path. -/
theorem exists_ordered_tripod_boundary_indices
    [DecidableEq V] {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet) :
    Exists fun i : Fin 3 =>
      Exists fun j : Fin 3 =>
        Exists fun k : Fin 3 =>
          i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
            Walk.supportIndex P.path (T.boundary i) <
              Walk.supportIndex P.path (T.boundary j) ∧
            Walk.supportIndex P.path (T.boundary j) <
              Walk.supportIndex P.path (T.boundary k) := by
  simpa [pathSet] using
    Walk.exists_ordered_three_support_indices
      (G := S.graph) (p := P.path)
      T.boundary_injective
      (fun i => by simpa [pathSet] using hold i)

end GMIX24CutPath

end GeneralSociety

end Schematic.Math.GraphTheory
