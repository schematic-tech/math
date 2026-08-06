import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.ResidualClassification

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Left-side mixed-foot side-tripod constructor.

If two side-tripod feet lie on the cut path and the remaining foot lies on
the left boundary arc, then the tripod lifts to the ambient society: route the
earlier path foot back to `s`, leave the arc foot fixed, and route the later
path foot forward to `t`.  The path-contact normalization is exactly the
source assertion that the old side tripod meets `P` only in its old feet. -/
theorem canonicalOfNoCross_left_tripod_lift_two_path_feet_one_arc_foot_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∉ P.pathSet)
    (hk : T.boundary k ∈ P.pathSet)
    (hik_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order i j k
  have he : Function.Injective e := fin3Order_injective hij hik hjk
  let Tre := T.reindex e he
  have ha : T.boundary j ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T j).mp hj
  let tail : forall r : Fin 3,
      S.graph.Walk (Tre.boundary r) (P.boundaryTriple (T.boundary j) r)
    | 0 => by
        simpa [Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using P.pathTailToStart hi
    | 1 => by
        simpa [Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using
          (SimpleGraph.Walk.nil : S.graph.Walk (T.boundary j) (T.boundary j))
    | 2 => by
        simpa [Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using P.pathTailToEnd hk
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails
      P hno_cross Tre ha tail ?_ ?_ ?_
  · intro r
    fin_cases r
    · simpa [tail, Tre, Tripod.reindex, e, fin3Order,
        GMIX24CutPath.boundaryTriple] using P.pathTailToStart_isPath hi
    · simp [tail, Tre, Tripod.reindex, e, fin3Order,
        GMIX24CutPath.boundaryTriple]
    · simpa [tail, Tre, Tripod.reindex, e, fin3Order,
        GMIX24CutPath.boundaryTriple] using P.pathTailToEnd_isPath hk
  · intro r z hz hzTre
    have hzT : z ∈ T.vertexSet := T.reindex_vertexSet_subset e he hzTre
    fin_cases r
    · have hz0 : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0
      have hnot_j_zero : T.boundary j ∉ (P.pathTailToStart hi).support := by
        intro hj0
        exact hj (P.pathTailToStart_support_subset_pathSet hi
          (T.boundary j) hj0)
      have hnot_k_zero : T.boundary k ∉ (P.pathTailToStart hi).support :=
        P.pathTailToStart_not_mem_of_supportIndex_lt hi hik_order
      rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
      rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm
      · rcases hmjk with hmj | hmk
        · exact False.elim
            (hnot_j_zero (by simpa [hmj, hm] using hz0))
        · exact False.elim
            (hnot_k_zero (by simpa [hmk, hm] using hz0))
    · have hz1 :
          z ∈ (SimpleGraph.Walk.nil :
            S.graph.Walk (T.boundary j) (T.boundary j)).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz
      simpa [Tre, Tripod.reindex, e, fin3Order] using hz1
    · have hz2 : z ∈ (P.pathTailToEnd hk).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hk z hz2
      have hnot_i_two : T.boundary i ∉ (P.pathTailToEnd hk).support :=
        P.pathTailToEnd_not_mem_of_supportIndex_lt hk hik_order
      have hnot_j_two : T.boundary j ∉ (P.pathTailToEnd hk).support := by
        intro hj2
        exact hj (P.pathTailToEnd_support_subset_pathSet hk
          (T.boundary j) hj2)
      rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
      rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
      · exact False.elim
          (hnot_i_two (by simpa [hmi, hm] using hz2))
      · rcases hmjk with hmj | hmk
        · exact False.elim
            (hnot_j_two (by simpa [hmj, hm] using hz2))
        · simpa [Tre, Tripod.reindex, e, fin3Order, hmk] using hm
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact False.elim (hrs rfl)
    · rw [Set.disjoint_left]
      intro z hz0 hz1
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz0
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0'
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz1
      exact hj (by simpa [hzj] using hzPath)
    · rw [Set.disjoint_left]
      intro z hz0 hz2
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz0
      have hz2' : z ∈ (P.pathTailToEnd hk).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz2
      exact
        (Set.disjoint_left.mp
          (P.pathTailToStart_support_disjoint_pathTailToEnd
            hi hk hik_order)) hz0' hz2'
    · rw [Set.disjoint_left]
      intro z hz1 hz0
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz0
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0'
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz1
      exact hj (by simpa [hzj] using hzPath)
    · exact False.elim (hrs rfl)
    · rw [Set.disjoint_left]
      intro z hz1 hz2
      have hz2' : z ∈ (P.pathTailToEnd hk).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz2
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hk z hz2'
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz1
      exact hj (by simpa [hzj] using hzPath)
    · rw [Set.disjoint_left]
      intro z hz2 hz0
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz0
      have hz2' : z ∈ (P.pathTailToEnd hk).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz2
      exact
        (Set.disjoint_left.mp
          (P.pathTailToStart_support_disjoint_pathTailToEnd
            hi hk hik_order).symm) hz2' hz0'
    · rw [Set.disjoint_left]
      intro z hz2 hz1
      have hz2' : z ∈ (P.pathTailToEnd hk).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz2
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToEnd_support_subset_pathSet hk z hz2'
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order,
          GMIX24CutPath.boundaryTriple] using hz1
      exact hj (by simpa [hzj] using hzPath)
    · exact False.elim (hrs rfl)

/-- Left-side mixed-foot side-tripod constructor with one cut-path foot and
two left-arc feet.

The sole path foot is routed back to `s`; the two arc feet are already
ambient boundary vertices and are left fixed.  This is the second mixed-foot
case needed to turn the source paragraph's "otherwise the original society
has a tripod" sentence into a local Lean theorem. -/
theorem canonicalOfNoCross_left_tripod_lift_one_path_foot_two_arc_feet_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : T.boundary i ∈ P.pathSet)
    (hj : T.boundary j ∉ P.pathSet)
    (hk : T.boundary k ∉ P.pathSet)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    Nonempty S.Tripod := by
  classical
  let e : Fin 3 -> Fin 3 := fin3Order i j k
  have he : Function.Injective e := fin3Order_injective hij hik hjk
  let Tre := T.reindex e he
  have hj_arc : T.boundary j ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T j).mp hj
  have hk_arc : T.boundary k ∈ P.leftBoundaryArc :=
    (GMIX24Split.canonicalOfNoCross_left_tripod_boundary_not_path_iff_arc
      P hno_cross T k).mp hk
  let newBoundary : Fin 3 -> V
    | 0 => P.s
    | 1 => T.boundary j
    | 2 => T.boundary k
  have hnew_boundary : forall r : Fin 3, newBoundary r ∈ S.boundarySet := by
    intro r
    fin_cases r
    · exact P.s_mem_boundary
    · exact P.leftBoundaryArc_subset hj_arc
    · exact P.leftBoundaryArc_subset hk_arc
  have hnew_injective : Function.Injective newBoundary := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp [newBoundary] at hrs ⊢
    · exact False.elim (P.leftBoundaryArc_ne_s hj_arc hrs.symm)
    · exact False.elim (P.leftBoundaryArc_ne_s hk_arc hrs.symm)
    · exact False.elim (P.leftBoundaryArc_ne_s hj_arc hrs)
    · exact False.elim (hjk (T.boundary_injective hrs))
    · exact False.elim (P.leftBoundaryArc_ne_s hk_arc hrs)
    · exact False.elim (hjk ((T.boundary_injective hrs).symm))
  let tail : forall r : Fin 3,
      S.graph.Walk (Tre.boundary r) (newBoundary r)
    | 0 => by
        simpa [Tre, Tripod.reindex, e, fin3Order, newBoundary] using
          P.pathTailToStart hi
    | 1 => by
        simpa [Tre, Tripod.reindex, e, fin3Order, newBoundary] using
          (SimpleGraph.Walk.nil : S.graph.Walk (T.boundary j) (T.boundary j))
    | 2 => by
        simpa [Tre, Tripod.reindex, e, fin3Order, newBoundary] using
          (SimpleGraph.Walk.nil : S.graph.Walk (T.boundary k) (T.boundary k))
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundary_tails
      P hno_cross Tre newBoundary hnew_boundary hnew_injective tail ?_ ?_ ?_
  · intro r
    fin_cases r
    · simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using
        P.pathTailToStart_isPath hi
    · simp [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary]
    · simp [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary]
  · intro r z hz hzTre
    have hzT : z ∈ T.vertexSet := T.reindex_vertexSet_subset e he hzTre
    fin_cases r
    · have hz0 : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0
      have hnot_j_zero : T.boundary j ∉ (P.pathTailToStart hi).support := by
        intro hj0
        exact hj (P.pathTailToStart_support_subset_pathSet hi
          (T.boundary j) hj0)
      have hnot_k_zero : T.boundary k ∉ (P.pathTailToStart hi).support := by
        intro hk0
        exact hk (P.pathTailToStart_support_subset_pathSet hi
          (T.boundary k) hk0)
      rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
      rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
      · simpa [Tre, Tripod.reindex, e, fin3Order, hmi] using hm
      · rcases hmjk with hmj | hmk
        · exact False.elim
            (hnot_j_zero (by simpa [hmj, hm] using hz0))
        · exact False.elim
            (hnot_k_zero (by simpa [hmk, hm] using hz0))
    · have hz1 :
          z ∈ (SimpleGraph.Walk.nil :
            S.graph.Walk (T.boundary j) (T.boundary j)).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz
      simpa [Tre, Tripod.reindex, e, fin3Order] using hz1
    · have hz2 :
          z ∈ (SimpleGraph.Walk.nil :
            S.graph.Walk (T.boundary k) (T.boundary k)).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz
      simpa [Tre, Tripod.reindex, e, fin3Order] using hz2
  · intro r s hrs
    fin_cases r <;> fin_cases s
    · exact False.elim (hrs rfl)
    · rw [Set.disjoint_left]
      intro z hz0 hz1
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz0
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0'
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz1
      exact hj (by simpa [hzj] using hzPath)
    · rw [Set.disjoint_left]
      intro z hz0 hz2
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz0
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0'
      have hzk : z = T.boundary k := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz2
      exact hk (by simpa [hzk] using hzPath)
    · rw [Set.disjoint_left]
      intro z hz1 hz0
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz0
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0'
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz1
      exact hj (by simpa [hzj] using hzPath)
    · exact False.elim (hrs rfl)
    · rw [Set.disjoint_left]
      intro z hz1 hz2
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz1
      have hzk : z = T.boundary k := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz2
      exact hjk (T.boundary_injective (hzj.symm.trans hzk))
    · rw [Set.disjoint_left]
      intro z hz2 hz0
      have hz0' : z ∈ (P.pathTailToStart hi).support := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz0
      have hzPath : z ∈ P.pathSet :=
        P.pathTailToStart_support_subset_pathSet hi z hz0'
      have hzk : z = T.boundary k := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz2
      exact hk (by simpa [hzk] using hzPath)
    · rw [Set.disjoint_left]
      intro z hz2 hz1
      have hzj : z = T.boundary j := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz1
      have hzk : z = T.boundary k := by
        simpa [tail, Tre, Tripod.reindex, e, fin3Order, newBoundary] using hz2
      exact hjk (T.boundary_injective (hzj.symm.trans hzk))
    · exact False.elim (hrs rfl)

/-- Under path-contact normalization, a left side-tripod cannot have an
off-path foot in a tripod-free ambient society.  This packages the three
mixed-foot constructors: all feet off lifts immediately; one path foot with
two arc feet lifts; and two path feet with one arc foot lifts after ordering
the two path feet along `P`. -/
theorem canonicalOfNoCross_left_tripod_off_path_foot_impossible_of_no_tripod_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi_off : T.boundary i ∉ P.pathSet)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    False := by
  classical
  by_cases hj_path : T.boundary j ∈ P.pathSet
  · by_cases hk_path : T.boundary k ∈ P.pathSet
    · by_cases hjk_order :
        Walk.supportIndex P.path (T.boundary j) <
          Walk.supportIndex P.path (T.boundary k)
      · exact hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_two_path_feet_one_arc_foot_path_contacts
            P hno_cross T (i := j) (j := i) (k := k)
            hij.symm hjk hik hj_path hi_off hk_path hjk_order
            hpath_contacts)
      · have hboundary_ne : T.boundary j ≠ T.boundary k := by
          intro h
          exact hjk (T.boundary_injective h)
        have hindex_ne :
            Walk.supportIndex P.path (T.boundary j) ≠
              Walk.supportIndex P.path (T.boundary k) :=
          Walk.supportIndex_ne_of_mem_of_ne
            (by simpa [GMIX24CutPath.pathSet] using hj_path)
            hboundary_ne
        have hkj_order :
            Walk.supportIndex P.path (T.boundary k) <
              Walk.supportIndex P.path (T.boundary j) :=
          lt_of_le_of_ne (Nat.le_of_not_gt hjk_order) hindex_ne.symm
        exact hno_tripod
          (GMIX24Split.canonicalOfNoCross_left_tripod_lift_two_path_feet_one_arc_foot_path_contacts
            P hno_cross T (i := k) (j := i) (k := j)
            hik.symm hjk.symm hij hk_path hi_off hj_path hkj_order
            hpath_contacts)
    · exact hno_tripod
        (GMIX24Split.canonicalOfNoCross_left_tripod_lift_one_path_foot_two_arc_feet_path_contacts
          P hno_cross T (i := j) (j := i) (k := k)
          hij.symm hjk hik hj_path hi_off hk_path hpath_contacts)
  · by_cases hk_path : T.boundary k ∈ P.pathSet
    · exact hno_tripod
        (GMIX24Split.canonicalOfNoCross_left_tripod_lift_one_path_foot_two_arc_feet_path_contacts
          P hno_cross T (i := k) (j := i) (k := j)
          hik.symm hjk.symm hij hk_path hi_off hj_path hpath_contacts)
    · have hall_off : forall m : Fin 3, T.boundary m ∉ P.pathSet := by
        intro m
        rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
        · simpa [hmi] using hi_off
        · rcases hmjk with hmj | hmk
          · simpa [hmj] using hj_path
          · simpa [hmk] using hk_path
      exact hno_tripod
        (GMIX24Split.canonicalOfNoCross_left_tripod_lift_of_all_feet_off_path
          P hno_cross T hall_off)

/-- Source-foot consequence for left side-tripods.

Once every cut-path contact of the side tripod is one of its feet, ambient
tripod-freeness forces all three feet onto the cut path. -/
theorem canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall i : Fin 3, T.boundary i ∈ P.pathSet := by
  intro i
  fin_cases i
  · by_contra h0
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_off_path_foot_impossible_of_no_tripod_path_contacts
        P hno_cross hno_tripod T (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) (by decide) h0 hpath_contacts
  · by_contra h1
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_off_path_foot_impossible_of_no_tripod_path_contacts
        P hno_cross hno_tripod T (i := 1) (j := 0) (k := 2)
        (by decide) (by decide) (by decide) h1 hpath_contacts
  · by_contra h2
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_off_path_foot_impossible_of_no_tripod_path_contacts
        P hno_cross hno_tripod T (i := 2) (j := 0) (k := 1)
        (by decide) (by decide) (by decide) h2 hpath_contacts

/-- Right-side version of
`canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts`,
obtained by reversing the canonical cut path. -/
theorem canonicalOfNoCross_right_tripod_all_feet_on_path_of_no_tripod_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) :
    forall i : Fin 3, T.boundary i ∈ P.pathSet := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  have hpath_contacts_rev :
      forall z : V, z ∈ P.reverse.pathSet -> z ∈ Trev.vertexSet ->
        Exists fun m : Fin 3 => z = Trev.boundary m := by
    intro z hzPath hzT
    have hzPathP : z ∈ P.pathSet := by simpa using hzPath
    have hzTorig : z ∈ T.vertexSet := by simpa [Trev] using hzT
    simpa [Trev] using hpath_contacts z hzPathP hzTorig
  have hall_rev :
      forall i : Fin 3, Trev.boundary i ∈ P.reverse.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P.reverse hno_cross hno_tripod Trev hpath_contacts_rev
  intro i
  simpa [Trev] using hall_rev i

/-- A hidden contact of a left side tripod with the left boundary arc is already
one of the two residual alternatives from the source side-tripod paragraph.

This is a direct local form of the GM IX `(2.4)` sentence that, after all
cut-path contacts have been normalized, a clean tail from the side boundary
cannot start on the median branch without producing an ambient tripod.  Thus an
unaccounted arc contact is forced to be either a common old rim end or the
collapsed non-median rim case. -/
theorem canonicalOfNoCross_left_tripod_arc_contact_common_endpoint_or_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x : V}
    (hxArc : x ∈ P.leftBoundaryArc)
    (hxT : x ∈ T.vertexSet) :
    (x = T.left ∨ x = T.right) ∨
      Exists fun r : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil := by
  classical
  have hall : forall r : Fin 3, T.boundary r ∈ P.pathSet :=
    GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
      P hno_cross hno_tripod T hpath_contacts
  rcases P.exists_ordered_tripod_boundary_indices T hall with
    ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩
  let q : S.graph.Walk x x := SimpleGraph.Walk.nil
  have hxPacked :
      Exists fun r : Fin 3 =>
        x ∈ (T.rim r).support ∨ x ∈ (T.leg r).support := by
    rcases hxT with hxRim | hxLeg
    · rcases hxRim with ⟨r, hr⟩
      exact ⟨r, Or.inl hr⟩
    · rcases hxLeg with ⟨r, hr⟩
      exact ⟨r, Or.inr hr⟩
  have hq_path : q.IsPath := by
    simp [q]
  have hq_outside : forall w : V, w ∈ q.support -> w ∈ P.outside := by
    intro w hw
    have hwx : w = x := by
      simpa [q] using hw
    simpa [hwx] using P.leftBoundaryArc_subset_outside hxArc
  have hq_clean :
      forall z : V, z ∈ q.support ->
        (Exists fun r : Fin 3 =>
          z ∈ (T.rim r).support ∨ z ∈ (T.leg r).support) ->
          z = x := by
    intro z hz _hzT
    simpa [q] using hz
  have hclass :=
    GMIX24Split.canonicalOfNoCross_left_tripod_clean_tail_all_path_feet_median_branch_or_leg_nil_residual
      P hno_cross hno_tripod T hij hik hjk q hxPacked hxArc
      (fun r : Fin 3 => hall (fin3Order i j k r))
      hq_path hij_order hjk_order hq_outside hpath_contacts hq_clean
  rcases hclass with hmedian | hresidual
  · exact False.elim
      (hno_tripod
        (GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_replace_ordered_leg_or_median_branch_path_contacts
          P hno_cross T hij hik hjk q (Or.inr (Or.inl hmedian)) hxArc
          (fun r : Fin 3 => hall (fin3Order i j k r))
          hq_path hij_order hjk_order hq_outside hpath_contacts
          (by
            intro z hz hzT
            exact hq_clean z hz (by
              rcases hzT with hzRim | hzLeg
              · rcases hzRim with ⟨r, hr⟩
                exact ⟨r, Or.inl hr⟩
              · rcases hzLeg with ⟨r, hr⟩
                exact ⟨r, Or.inr hr⟩))))
  · rcases hresidual with hend | hnil
    · exact Or.inl hend
    · rcases hnil with ⟨r, _hr, hxrim, hleg_nil⟩
      exact Or.inr ⟨r, hxrim, hleg_nil⟩

/-- Right-side version of
`canonicalOfNoCross_left_tripod_arc_contact_common_endpoint_or_leg_nil`,
obtained by applying the left-side statement to the reversed cut path. -/
theorem canonicalOfNoCross_right_tripod_arc_contact_common_endpoint_or_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    {x : V}
    (hxArc : x ∈ P.rightBoundaryArc)
    (hxT : x ∈ T.vertexSet) :
    (x = T.left ∨ x = T.right) ∨
      Exists fun r : Fin 3 =>
        x ∈ Walk.InternalVertices (T.rim r) ∧ (T.leg r).Nil := by
  classical
  have hSoc :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety =
        (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety :=
    GMIX24Split.canonicalOfNoCross_reverse_leftSociety P hno_cross
  let Trev :
      (GMIX24Split.canonicalOfNoCross P.reverse hno_cross).leftSociety.Tripod :=
    hSoc.symm ▸ T
  have hpath_contacts_rev :
      forall z : V, z ∈ P.reverse.pathSet -> z ∈ Trev.vertexSet ->
        Exists fun m : Fin 3 => z = Trev.boundary m := by
    intro z hzPath hzT
    have hzPathP : z ∈ P.pathSet := by
      simpa using hzPath
    have hzTorig : z ∈ T.vertexSet := by
      simpa [Trev] using hzT
    simpa [Trev] using hpath_contacts z hzPathP hzTorig
  have hres :=
    GMIX24Split.canonicalOfNoCross_left_tripod_arc_contact_common_endpoint_or_leg_nil
      P.reverse hno_cross hno_tripod Trev hpath_contacts_rev
      (by simpa using hxArc)
      (by simpa [Trev] using hxT)
  rcases hres with hend | hnil
  · exact Or.inl (by simpa [Trev] using hend)
  · rcases hnil with ⟨r, hxrim, hleg_nil⟩
    exact Or.inr
      ⟨r, by simpa [Trev] using hxrim,
        (Tripod.cast_leg_nil hSoc.symm T r).mp (by simpa [Trev] using hleg_nil)⟩

/-- Path-contact normalization for a boundary-clean left side tripod.

This is the formal version of the source proof's use of the induced cut path:
after the split, every vertex of `P` is a boundary vertex of the left society.
If the side tripod has no hidden boundary contacts, any contact with `P` is
one of its three boundary feet. -/
theorem canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m := by
  intro z hzPath hzT
  exact T.boundaryClean_vertexSet_boundary_eq_boundary hclean
    (by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact Or.inr hzPath)
    hzT

/-- Right-side version of
`canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean`. -/
theorem canonicalOfNoCross_right_tripod_path_contacts_of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m := by
  intro z hzPath hzT
  exact T.boundaryClean_vertexSet_boundary_eq_boundary hclean
    (by
      rw [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
      exact Or.inr hzPath)
    hzT

/-- Path-contact normalization after the source-clean leg condition has
reduced the problem to rim contacts.

For a left side tripod with genuine `X -> Ω` legs, every cut-path contact on a
leg is automatically the corresponding foot.  Thus the only remaining work is
to show the same conclusion for contacts on the three rim paths. -/
theorem canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_rim_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hleg_clean : T.LegBoundaryContactClean)
    (hrim_contacts :
      forall z : V, z ∈ P.pathSet ->
        (Exists fun i : Fin 3 => z ∈ (T.rim i).support) ->
          Exists fun m : Fin 3 => z = T.boundary m) :
    forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m := by
  intro z hzPath hzT
  rcases hzT with hzRim | hzLeg
  · exact hrim_contacts z hzPath hzRim
  · rcases hzLeg with ⟨i, hzLeg⟩
    exact ⟨i, hleg_clean i z hzLeg (by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact Or.inr hzPath)⟩

/-- Right-side version of
`canonicalOfNoCross_left_tripod_path_contacts_of_legBoundaryContactClean_and_rim_contacts`. -/
theorem canonicalOfNoCross_right_tripod_path_contacts_of_legBoundaryContactClean_and_rim_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hleg_clean : T.LegBoundaryContactClean)
    (hrim_contacts :
      forall z : V, z ∈ P.pathSet ->
        (Exists fun i : Fin 3 => z ∈ (T.rim i).support) ->
          Exists fun m : Fin 3 => z = T.boundary m) :
    forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m := by
  intro z hzPath hzT
  rcases hzT with hzRim | hzLeg
  · exact hrim_contacts z hzPath hzRim
  · rcases hzLeg with ⟨i, hzLeg⟩
    exact ⟨i, hleg_clean i z hzLeg (by
      rw [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
      exact Or.inr hzPath)⟩

/-- Boundary-arc contact normalization for a boundary-clean left side tripod. -/
theorem canonicalOfNoCross_left_tripod_arc_contacts_of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall z : V, z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m := by
  intro z hzArc hzT
  exact T.boundaryClean_vertexSet_boundary_eq_boundary hclean
    (by
      rw [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet P hno_cross]
      exact Or.inl hzArc)
    hzT

/-- Boundary-arc contact normalization for a boundary-clean right side
tripod. -/
theorem canonicalOfNoCross_right_tripod_arc_contacts_of_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall z : V, z ∈ P.rightBoundaryArc -> z ∈ T.vertexSet ->
      Exists fun m : Fin 3 => z = T.boundary m := by
  intro z hzArc hzT
  exact T.boundaryClean_vertexSet_boundary_eq_boundary hclean
    (by
      rw [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet P hno_cross]
      exact Or.inl hzArc)
    hzT

/-- Boundary-contact normalization for a left side-tripod gives the
`BoundaryClean` predicate used by the common-end constructor.

This is the non-circular direction: instead of assuming `BoundaryClean` and
deriving cut-path contact normalization, callers may prove directly that
every boundary vertex of the left cut society met by the tripod is one of its
three feet, plus that no leg is nil. -/
theorem canonicalOfNoCross_left_tripod_boundaryClean_of_cutBoundary_contacts_of_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hcontacts :
      forall z : V, z ∈ P.leftCutBoundarySet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    T.BoundaryClean := by
  exact
    T.boundaryClean_of_boundary_contacts_of_no_leg_nil
      (by
        intro z hzBoundary hzT
        exact hcontacts z (by
          simpa [GMIX24Split.canonicalOfNoCross_leftSociety_boundarySet
            P hno_cross] using hzBoundary) hzT)
      hleg_not_nil

/-- Right-side version of
`canonicalOfNoCross_left_tripod_boundaryClean_of_cutBoundary_contacts_of_no_leg_nil`. -/
theorem canonicalOfNoCross_right_tripod_boundaryClean_of_cutBoundary_contacts_of_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hcontacts :
      forall z : V, z ∈ P.rightCutBoundarySet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    T.BoundaryClean := by
  exact
    T.boundaryClean_of_boundary_contacts_of_no_leg_nil
      (by
        intro z hzBoundary hzT
        exact hcontacts z (by
          simpa [GMIX24Split.canonicalOfNoCross_rightSociety_boundarySet
            P hno_cross] using hzBoundary) hzT)
      hleg_not_nil

/-- Left side-tripod boundary cleanliness from separate arc-contact and
cut-path-contact normalizations. -/
theorem canonicalOfNoCross_left_tripod_boundaryClean_of_arc_path_contacts_of_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (harc_contacts :
      forall z : V, z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    T.BoundaryClean := by
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_boundaryClean_of_cutBoundary_contacts_of_no_leg_nil
      P hno_cross T ?_ hleg_not_nil
  intro z hzCut hzT
  rcases hzCut with hzArc | hzPath
  · exact harc_contacts z hzArc hzT
  · exact hpath_contacts z hzPath hzT

/-- Exact local normalization criterion for a left side tripod in the
canonical split. -/
theorem canonicalOfNoCross_left_tripod_boundaryClean_iff_arc_path_contacts_and_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod) :
    T.BoundaryClean ↔
      (forall z : V, z ∈ P.leftBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) ∧
      (forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) ∧
      (forall i : Fin 3, Not (T.leg i).Nil) := by
  constructor
  · intro hclean
    exact ⟨
      GMIX24Split.canonicalOfNoCross_left_tripod_arc_contacts_of_boundaryClean
        P hno_cross T hclean,
      GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean
        P hno_cross T hclean,
      T.boundaryClean_leg_not_nil hclean⟩
  · intro h
    exact
      GMIX24Split.canonicalOfNoCross_left_tripod_boundaryClean_of_arc_path_contacts_of_no_leg_nil
        P hno_cross T h.1 h.2.1 h.2.2

/-- Right side-tripod boundary cleanliness from separate arc-contact and
cut-path-contact normalizations. -/
theorem canonicalOfNoCross_right_tripod_boundaryClean_of_arc_path_contacts_of_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (harc_contacts :
      forall z : V, z ∈ P.rightBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hleg_not_nil : forall i : Fin 3, Not (T.leg i).Nil) :
    T.BoundaryClean := by
  refine
    GMIX24Split.canonicalOfNoCross_right_tripod_boundaryClean_of_cutBoundary_contacts_of_no_leg_nil
      P hno_cross T ?_ hleg_not_nil
  intro z hzCut hzT
  rcases hzCut with hzArc | hzPath
  · exact harc_contacts z hzArc hzT
  · exact hpath_contacts z hzPath hzT

/-- Exact local normalization criterion for a right side tripod in the
canonical split. -/
theorem canonicalOfNoCross_right_tripod_boundaryClean_iff_arc_path_contacts_and_no_leg_nil
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod) :
    T.BoundaryClean ↔
      (forall z : V, z ∈ P.rightBoundaryArc -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) ∧
      (forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m) ∧
      (forall i : Fin 3, Not (T.leg i).Nil) := by
  constructor
  · intro hclean
    exact ⟨
      GMIX24Split.canonicalOfNoCross_right_tripod_arc_contacts_of_boundaryClean
        P hno_cross T hclean,
      GMIX24Split.canonicalOfNoCross_right_tripod_path_contacts_of_boundaryClean
        P hno_cross T hclean,
      T.boundaryClean_leg_not_nil hclean⟩
  · intro h
    exact
      GMIX24Split.canonicalOfNoCross_right_tripod_boundaryClean_of_arc_path_contacts_of_no_leg_nil
        P hno_cross T h.1 h.2.1 h.2.2

/-- Boundary-clean left side-tripods have all three feet on the cut path in
an ambient tripod-free society. -/
theorem canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall i : Fin 3, T.boundary i ∈ P.pathSet :=
  GMIX24Split.canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_path_contacts
    P hno_cross hno_tripod T
    (GMIX24Split.canonicalOfNoCross_left_tripod_path_contacts_of_boundaryClean
      P hno_cross T hclean)

/-- Right-side version of
`canonicalOfNoCross_left_tripod_all_feet_on_path_of_no_tripod_boundaryClean`. -/
theorem canonicalOfNoCross_right_tripod_all_feet_on_path_of_no_tripod_boundaryClean
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (hno_tripod : Not (Nonempty S.Tripod))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (hclean : T.BoundaryClean) :
    forall i : Fin 3, T.boundary i ∈ P.pathSet :=
  GMIX24Split.canonicalOfNoCross_right_tripod_all_feet_on_path_of_no_tripod_path_contacts
    P hno_cross hno_tripod T
    (GMIX24Split.canonicalOfNoCross_right_tripod_path_contacts_of_boundaryClean
      P hno_cross T hclean)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
