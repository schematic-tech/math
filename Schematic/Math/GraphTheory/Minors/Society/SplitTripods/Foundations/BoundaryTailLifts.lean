import Schematic.Math.GraphTheory.Minors.Society.SplitTripods.Foundations.Symmetry

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Left-side multi-foot lift with the source ambient boundary triple
`(s, a, t)`. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (tail : forall i : Fin 3,
      S.graph.Walk (T.boundary i) (P.boundaryTriple a i))
    (htail_path : forall i : Fin 3, (tail i).IsPath)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (tail i).support -> z ∈ T.vertexSet -> z = T.boundary i)
    (htail_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint {z : V | z ∈ (tail i).support}
          {z : V | z ∈ (tail j).support}) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundary_tails
    P hno_cross T (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_leftArc ha)
    (P.boundaryTriple_injective_of_leftArc ha)
    tail htail_path htail_clean htail_disjoint

/-- Right-side multi-foot lift with the source ambient boundary triple
`(s, a, t)`. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (tail : forall i : Fin 3,
      S.graph.Walk (T.boundary i) (P.boundaryTriple a i))
    (htail_path : forall i : Fin 3, (tail i).IsPath)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (tail i).support -> z ∈ T.vertexSet -> z = T.boundary i)
    (htail_disjoint :
      forall i j : Fin 3, i ≠ j ->
        Disjoint {z : V | z ∈ (tail i).support}
          {z : V | z ∈ (tail j).support}) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_boundary_tails
    P hno_cross T (P.boundaryTriple a)
    (P.boundaryTriple_mem_of_rightArc ha)
    (P.boundaryTriple_injective_of_rightArc ha)
    tail htail_path htail_clean htail_disjoint

/-- Left-side ordered three-foot constructor.  The first and third side feet
are routed along the cut path to `s` and `t`; the middle foot is routed by the
given clean tail to `a`. -/
theorem canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path (T.boundary 0) <
        Walk.supportIndex P.path (T.boundary 1))
    (h12 :
      Walk.supportIndex P.path (T.boundary 1) <
        Walk.supportIndex P.path (T.boundary 2))
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle i).support ->
          z ∈ T.vertexSet -> z = T.boundary i)
    (hdisjoint01 :
      Disjoint
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support}
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support})
    (hdisjoint12 :
      Disjoint
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support}
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support}) :
    Nonempty S.Tripod := by
  let tail := P.orderedBoundaryTripleTails hold a middle
  have houter :
      Disjoint
        {z : V | z ∈ (tail 0).support}
        {z : V | z ∈ (tail 2).support} := by
    simpa [tail] using
      P.orderedBoundaryTripleTails_outer_disjoint hold a middle
        (lt_trans h01 h12)
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails
      P hno_cross T ha tail ?_ ?_ ?_
  · simpa [tail] using
      P.orderedBoundaryTripleTails_isPath hold a hmiddle_path
  · intro i z hz hT
    exact htail_clean i z (by simpa [tail] using hz) hT
  · intro i j hij
    exact fin3_pairwise_disjoint
      (s := fun i => {z : V | z ∈ (tail i).support})
      (by simpa [tail] using hdisjoint01) houter
      (by simpa [tail] using hdisjoint12) hij

/-- Right-side ordered three-foot constructor. -/
theorem canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path (T.boundary 0) <
        Walk.supportIndex P.path (T.boundary 1))
    (h12 :
      Walk.supportIndex P.path (T.boundary 1) <
        Walk.supportIndex P.path (T.boundary 2))
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle i).support ->
          z ∈ T.vertexSet -> z = T.boundary i)
    (hdisjoint01 :
      Disjoint
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support}
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support})
    (hdisjoint12 :
      Disjoint
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support}
        {z : V | z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support}) :
    Nonempty S.Tripod := by
  let tail := P.orderedBoundaryTripleTails hold a middle
  have houter :
      Disjoint
        {z : V | z ∈ (tail 0).support}
        {z : V | z ∈ (tail 2).support} := by
    simpa [tail] using
      P.orderedBoundaryTripleTails_outer_disjoint hold a middle
        (lt_trans h01 h12)
  refine
    GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails
      P hno_cross T ha tail ?_ ?_ ?_
  · simpa [tail] using
      P.orderedBoundaryTripleTails_isPath hold a hmiddle_path
  · intro i z hz hT
    exact htail_clean i z (by simpa [tail] using hz) hT
  · intro i j hij
    exact fin3_pairwise_disjoint
      (s := fun i => {z : V | z ∈ (tail i).support})
      (by simpa [tail] using hdisjoint01) houter
      (by simpa [tail] using hdisjoint12) hij

/-- Left-side ordered three-foot constructor with the middle-disjointness
obligations discharged from internal cut-path avoidance. -/
theorem canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails_of_middle_avoids_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path (T.boundary 0) <
        Walk.supportIndex P.path (T.boundary 1))
    (h12 :
      Walk.supportIndex P.path (T.boundary 1) <
        Walk.supportIndex P.path (T.boundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle i).support ->
          z ∈ T.vertexSet -> z = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails
    P hno_cross T ha hold middle hmiddle_path h01 h12 htail_clean
    (P.orderedBoundaryTripleTails_zero_disjoint_middle_of_internal_avoids_pathSet
      hold middle (P.leftBoundaryArc_not_mem_pathSet ha) h01 hmiddle_internal)
    (P.orderedBoundaryTripleTails_middle_disjoint_two_of_internal_avoids_pathSet
      hold middle (P.leftBoundaryArc_not_mem_pathSet ha) h12 hmiddle_internal)

/-- Right-side ordered three-foot constructor with middle internal cut-path
avoidance. -/
theorem canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails_of_middle_avoids_path
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path (T.boundary 0) <
        Walk.supportIndex P.path (T.boundary 1))
    (h12 :
      Walk.supportIndex P.path (T.boundary 1) <
        Walk.supportIndex P.path (T.boundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (htail_clean :
      forall i : Fin 3, forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle i).support ->
          z ∈ T.vertexSet -> z = T.boundary i) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails
    P hno_cross T ha hold middle hmiddle_path h01 h12 htail_clean
    (P.orderedBoundaryTripleTails_zero_disjoint_middle_of_internal_avoids_pathSet
      hold middle (P.rightBoundaryArc_not_mem_pathSet ha) h01 hmiddle_internal)
    (P.orderedBoundaryTripleTails_middle_disjoint_two_of_internal_avoids_pathSet
      hold middle (P.rightBoundaryArc_not_mem_pathSet ha) h12 hmiddle_internal)

/-- Left-side ordered constructor with the three clean-tail checks stated
separately. -/
theorem canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails_of_clean_parts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path (T.boundary 0) <
        Walk.supportIndex P.path (T.boundary 1))
    (h12 :
      Walk.supportIndex P.path (T.boundary 1) <
        Walk.supportIndex P.path (T.boundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hclean0 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support ->
          z ∈ T.vertexSet -> z = T.boundary 0)
    (hclean1 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support ->
          z ∈ T.vertexSet -> z = T.boundary 1)
    (hclean2 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support ->
          z ∈ T.vertexSet -> z = T.boundary 2) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails_of_middle_avoids_path
    P hno_cross T ha hold middle hmiddle_path h01 h12 hmiddle_internal
    (by
      intro i z hz hT
      fin_cases i
      · exact hclean0 z hz hT
      · exact hclean1 z hz hT
      · exact hclean2 z hz hT)

/-- Right-side ordered constructor with the three clean-tail checks stated
separately. -/
theorem canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails_of_clean_parts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hold : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path (T.boundary 0) <
        Walk.supportIndex P.path (T.boundary 1))
    (h12 :
      Walk.supportIndex P.path (T.boundary 1) <
        Walk.supportIndex P.path (T.boundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hclean0 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support ->
          z ∈ T.vertexSet -> z = T.boundary 0)
    (hclean1 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support ->
          z ∈ T.vertexSet -> z = T.boundary 1)
    (hclean2 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support ->
          z ∈ T.vertexSet -> z = T.boundary 2) :
    Nonempty S.Tripod :=
  GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails_of_middle_avoids_path
    P hno_cross T ha hold middle hmiddle_path h01 h12 hmiddle_internal
    (by
      intro i z hz hT
      fin_cases i
      · exact hclean0 z hz hT
      · exact hclean1 z hz hT
      · exact hclean2 z hz hT)

/-- Left-side ordered constructor after reindexing the side tripod.  The
clean-tail checks may be proved against the original tripod; the reindexed
tripod has no new vertices. -/
theorem canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails_of_reindex_clean_parts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (e : Fin 3 -> Fin 3)
    (he : Function.Injective e)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall i : Fin 3, (T.reindex e he).boundary i ∈ P.pathSet)
    (middle : S.graph.Walk ((T.reindex e he).boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path ((T.reindex e he).boundary 0) <
        Walk.supportIndex P.path ((T.reindex e he).boundary 1))
    (h12 :
      Walk.supportIndex P.path ((T.reindex e he).boundary 1) <
        Walk.supportIndex P.path ((T.reindex e he).boundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hclean0 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support ->
          z ∈ T.vertexSet -> z = (T.reindex e he).boundary 0)
    (hclean1 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support ->
          z ∈ T.vertexSet -> z = (T.reindex e he).boundary 1)
    (hclean2 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support ->
          z ∈ T.vertexSet -> z = (T.reindex e he).boundary 2) :
    Nonempty S.Tripod := by
  let Tre := T.reindex e he
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails_of_clean_parts
      P hno_cross Tre ha hold middle hmiddle_path h01 h12 hmiddle_internal
      ?_ ?_ ?_
  · intro z hz hzTre
    exact hclean0 z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    exact hclean1 z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    exact hclean2 z hz (T.reindex_vertexSet_subset e he hzTre)

/-- Right-side ordered constructor after reindexing the side tripod. -/
theorem canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails_of_reindex_clean_parts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (e : Fin 3 -> Fin 3)
    (he : Function.Injective e)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall i : Fin 3, (T.reindex e he).boundary i ∈ P.pathSet)
    (middle : S.graph.Walk ((T.reindex e he).boundary 1) a)
    (hmiddle_path : middle.IsPath)
    (h01 :
      Walk.supportIndex P.path ((T.reindex e he).boundary 0) <
        Walk.supportIndex P.path ((T.reindex e he).boundary 1))
    (h12 :
      Walk.supportIndex P.path ((T.reindex e he).boundary 1) <
        Walk.supportIndex P.path ((T.reindex e he).boundary 2))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hclean0 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 0).support ->
          z ∈ T.vertexSet -> z = (T.reindex e he).boundary 0)
    (hclean1 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 1).support ->
          z ∈ T.vertexSet -> z = (T.reindex e he).boundary 1)
    (hclean2 :
      forall z : V,
        z ∈ (P.orderedBoundaryTripleTails hold a middle 2).support ->
          z ∈ T.vertexSet -> z = (T.reindex e he).boundary 2) :
    Nonempty S.Tripod := by
  let Tre := T.reindex e he
  refine
    GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails_of_clean_parts
      P hno_cross Tre ha hold middle hmiddle_path h01 h12 hmiddle_internal
      ?_ ?_ ?_
  · intro z hz hzTre
    exact hclean0 z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    exact hclean1 z hz (T.reindex_vertexSet_subset e he hzTre)
  · intro z hz hzTre
    exact hclean2 z hz (T.reindex_vertexSet_subset e he hzTre)

/-- Left-side all-path-foot ordered constructor with the order stated in the
original branch labels. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_clean_parts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary j) a)
    (hmiddle_path : middle.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hclean0 :
      forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 0).support ->
          z ∈ T.vertexSet -> z = T.boundary i)
    (hclean1 :
      forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 1).support ->
          z ∈ T.vertexSet -> z = T.boundary j)
    (hclean2 :
      forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 2).support ->
          z ∈ T.vertexSet -> z = T.boundary k) :
    Nonempty S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order i j k
  have he : Function.Injective e :=
    fin3Order_injective hij hik hjk
  let Tre := T.reindex e he
  have holdRe : forall r : Fin 3, Tre.boundary r ∈ P.pathSet := by
    intro r
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold r
  let middleRe : S.graph.Walk (Tre.boundary 1) a := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using middle
  refine
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_ordered_boundaryTriple_tails_of_reindex_clean_parts
      P hno_cross T e he ha holdRe middleRe ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hmiddle_path
  · simpa [Tre, Tripod.reindex, e, fin3Order] using hij_order
  · simpa [Tre, Tripod.reindex, e, fin3Order] using hjk_order
  · simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hmiddle_internal
  · intro z hz hzT
    have hz0 :
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 0).support := by
      simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hz
    simpa [Tre, Tripod.reindex, e, fin3Order] using hclean0 z hz0 hzT
  · intro z hz hzT
    have hz1 :
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 1).support := by
      simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hz
    simpa [Tre, Tripod.reindex, e, fin3Order] using hclean1 z hz1 hzT
  · intro z hz hzT
    have hz2 :
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 2).support := by
      simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hz
    simpa [Tre, Tripod.reindex, e, fin3Order] using hclean2 z hz2 hzT

/-- Right-side all-path-foot ordered constructor with the order stated in the
original branch labels. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_clean_parts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary j) a)
    (hmiddle_path : middle.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hclean0 :
      forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 0).support ->
          z ∈ T.vertexSet -> z = T.boundary i)
    (hclean1 :
      forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 1).support ->
          z ∈ T.vertexSet -> z = T.boundary j)
    (hclean2 :
      forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 2).support ->
          z ∈ T.vertexSet -> z = T.boundary k) :
    Nonempty S.Tripod := by
  let e : Fin 3 -> Fin 3 := fin3Order i j k
  have he : Function.Injective e :=
    fin3Order_injective hij hik hjk
  let Tre := T.reindex e he
  have holdRe : forall r : Fin 3, Tre.boundary r ∈ P.pathSet := by
    intro r
    simpa [Tre, Tripod.reindex, e, fin3Order] using hold r
  let middleRe : S.graph.Walk (Tre.boundary 1) a := by
    simpa [Tre, Tripod.reindex, e, fin3Order] using middle
  refine
    GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_ordered_boundaryTriple_tails_of_reindex_clean_parts
      P hno_cross T e he ha holdRe middleRe ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hmiddle_path
  · simpa [Tre, Tripod.reindex, e, fin3Order] using hij_order
  · simpa [Tre, Tripod.reindex, e, fin3Order] using hjk_order
  · simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hmiddle_internal
  · intro z hz hzT
    have hz0 :
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 0).support := by
      simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hz
    simpa [Tre, Tripod.reindex, e, fin3Order] using hclean0 z hz0 hzT
  · intro z hz hzT
    have hz1 :
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 1).support := by
      simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hz
    simpa [Tre, Tripod.reindex, e, fin3Order] using hclean1 z hz1 hzT
  · intro z hz hzT
    have hz2 :
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 2).support := by
      simpa [middleRe, Tre, Tripod.reindex, e, fin3Order] using hz
    simpa [Tre, Tripod.reindex, e, fin3Order] using hclean2 z hz2 hzT

/-- Cleanliness of the ordered `(s,a,t)` tripod tails from a path-contact
normalization theorem.

This is the local combinatorial heart of the side-tripod all-path-foot case:
if the old tripod meets the cut path only in its three feet, then the two
outer ordered tails meet the old tripod only at their own starting feet; the
middle tail is handled by its supplied clean-tail hypothesis. -/
theorem orderedBoundaryTripleTails_clean_of_path_contacts
    [DecidableEq V] {S H : GeneralSociety V}
    (P : GMIX24CutPath S)
    (T : H.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {a : V}
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary j) a)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmiddle_clean :
      forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
        z = T.boundary j) :
    (forall z : V,
      z ∈
        (P.orderedBoundaryTripleTails
          (oldBoundary := fun r : Fin 3 =>
            T.boundary (fin3Order i j k r))
          hold a middle 0).support ->
        z ∈ T.vertexSet -> z = T.boundary i) ∧
      (forall z : V,
        z ∈
          (P.orderedBoundaryTripleTails
            (oldBoundary := fun r : Fin 3 =>
              T.boundary (fin3Order i j k r))
            hold a middle 1).support ->
          z ∈ T.vertexSet -> z = T.boundary j) ∧
        (forall z : V,
          z ∈
            (P.orderedBoundaryTripleTails
              (oldBoundary := fun r : Fin 3 =>
                T.boundary (fin3Order i j k r))
              hold a middle 2).support ->
            z ∈ T.vertexSet -> z = T.boundary k) := by
  classical
  have hnot_j_zero :
      T.boundary j ∉
        (P.orderedBoundaryTripleTails
          (oldBoundary := fun r : Fin 3 =>
            T.boundary (fin3Order i j k r))
          hold a middle 0).support := by
    simpa [fin3Order] using
      P.orderedBoundaryTripleTails_one_not_mem_zero_of_order
        (oldBoundary := fun r : Fin 3 =>
          T.boundary (fin3Order i j k r))
        hold a middle hij_order
  have hnot_k_zero :
      T.boundary k ∉
        (P.orderedBoundaryTripleTails
          (oldBoundary := fun r : Fin 3 =>
            T.boundary (fin3Order i j k r))
          hold a middle 0).support := by
    simpa [fin3Order] using
      P.orderedBoundaryTripleTails_two_not_mem_zero_of_order
        (oldBoundary := fun r : Fin 3 =>
          T.boundary (fin3Order i j k r))
        hold a middle (lt_trans hij_order hjk_order)
  have hnot_i_two :
      T.boundary i ∉
        (P.orderedBoundaryTripleTails
          (oldBoundary := fun r : Fin 3 =>
            T.boundary (fin3Order i j k r))
          hold a middle 2).support := by
    simpa [fin3Order] using
      P.orderedBoundaryTripleTails_zero_not_mem_two_of_order
        (oldBoundary := fun r : Fin 3 =>
          T.boundary (fin3Order i j k r))
        hold a middle (lt_trans hij_order hjk_order)
  have hnot_j_two :
      T.boundary j ∉
        (P.orderedBoundaryTripleTails
          (oldBoundary := fun r : Fin 3 =>
            T.boundary (fin3Order i j k r))
          hold a middle 2).support := by
    simpa [fin3Order] using
      P.orderedBoundaryTripleTails_one_not_mem_two_of_order
        (oldBoundary := fun r : Fin 3 =>
          T.boundary (fin3Order i j k r))
        hold a middle hjk_order
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hzT
    have hzPath : z ∈ P.pathSet :=
      P.orderedBoundaryTripleTails_zero_support_subset_pathSet
        (oldBoundary := fun r : Fin 3 =>
          T.boundary (fin3Order i j k r))
        hold a middle hz
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · simpa [hmi] using hm
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_zero (by simpa [hmj, hm] using hz))
      · exact False.elim (hnot_k_zero (by simpa [hmk, hm] using hz))
  · intro z hz hzT
    have hzMiddle : z ∈ middle.support := by
      simpa [GMIX24CutPath.orderedBoundaryTripleTails, fin3Order] using hz
    exact hmiddle_clean z hzMiddle hzT
  · intro z hz hzT
    have hzPath : z ∈ P.pathSet :=
      P.orderedBoundaryTripleTails_two_support_subset_pathSet
        (oldBoundary := fun r : Fin 3 =>
          T.boundary (fin3Order i j k r))
        hold a middle hz
    rcases hpath_contacts z hzPath hzT with ⟨m, hm⟩
    rcases fin3_eq_of_pairwise (m := m) hij hik hjk with hmi | hmjk
    · exact False.elim (hnot_i_two (by simpa [hmi, hm] using hz))
    · rcases hmjk with hmj | hmk
      · exact False.elim (hnot_j_two (by simpa [hmj, hm] using hz))
      · simpa [hmk] using hm

/-- Left-side ordered all-path-foot constructor using the natural path-contact
normalization condition instead of a fully expanded dependent clean-tail
family. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary j) a)
    (hmiddle_path : middle.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmiddle_clean :
      forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
        z = T.boundary j) :
    Nonempty S.Tripod := by
  rcases
      orderedBoundaryTripleTails_clean_of_path_contacts
        P
        T hij hik hjk hold middle hij_order hjk_order
        hpath_contacts hmiddle_clean with
    ⟨hclean0, hclean1, hclean2⟩
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_clean_parts
      P hno_cross T hij hik hjk ha hold middle hmiddle_path
      hij_order hjk_order hmiddle_internal hclean0 hclean1 hclean2

/-- Right-side ordered all-path-foot constructor using path-contact
normalization. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hold :
      forall r : Fin 3, T.boundary (fin3Order i j k r) ∈ P.pathSet)
    (middle : S.graph.Walk (T.boundary j) a)
    (hmiddle_path : middle.IsPath)
    (hij_order :
      Walk.supportIndex P.path (T.boundary i) <
        Walk.supportIndex P.path (T.boundary j))
    (hjk_order :
      Walk.supportIndex P.path (T.boundary j) <
        Walk.supportIndex P.path (T.boundary k))
    (hmiddle_internal :
      Walk.InternalVertices middle ∩ P.pathSet = ∅)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (hmiddle_clean :
      forall z : V, z ∈ middle.support -> z ∈ T.vertexSet ->
        z = T.boundary j) :
    Nonempty S.Tripod := by
  rcases
      orderedBoundaryTripleTails_clean_of_path_contacts
        P
        T hij hik hjk hold middle hij_order hjk_order
        hpath_contacts hmiddle_clean with
    ⟨hclean0, hclean1, hclean2⟩
  exact
    GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_clean_parts
      P hno_cross T hij hik hjk ha hold middle hmiddle_path
      hij_order hjk_order hmiddle_internal hclean0 hclean1 hclean2

/-- Left-side all-path-foot constructor with the branch order chosen
internally from the cut path.  The supplied family gives a candidate clean
tail from every old boundary foot to the arc vertex; the proof uses the one
whose foot is median along `P`. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_all_path_feet_clean_family
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (middle : forall j : Fin 3, S.graph.Walk (T.boundary j) a)
    (hmiddle_path : forall j : Fin 3, (middle j).IsPath)
    (hmiddle_internal :
      forall j : Fin 3, Walk.InternalVertices (middle j) ∩ P.pathSet = ∅)
    (hclean :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          forall r : Fin 3, forall z : V,
            z ∈
              (P.orderedBoundaryTripleTails
                (oldBoundary := fun t : Fin 3 =>
                  T.boundary (fin3Order i j k t))
                (fun t : Fin 3 => holdAll (fin3Order i j k t))
                a (middle j) r).support ->
              z ∈ T.vertexSet ->
                z = T.boundary (fin3Order i j k r)) :
    Nonempty S.Tripod := by
  obtain ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩ :=
    P.exists_ordered_tripod_boundary_indices T holdAll
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_clean_parts
      P hno_cross T hij hik hjk ha
      (fun r : Fin 3 => holdAll (fin3Order i j k r))
      (middle j) (hmiddle_path j) hij_order hjk_order
      (hmiddle_internal j)
      (by
        intro z hz hzT
        simpa [fin3Order] using
          hclean hij hik hjk hij_order hjk_order 0 z hz hzT)
      (by
        intro z hz hzT
        simpa [fin3Order] using
          hclean hij hik hjk hij_order hjk_order 1 z hz hzT)
      (by
        intro z hz hzT
        simpa [fin3Order] using
          hclean hij hik hjk hij_order hjk_order 2 z hz hzT)

/-- Right-side all-path-foot constructor with the branch order chosen
internally from the cut path. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_all_path_feet_clean_family
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (middle : forall j : Fin 3, S.graph.Walk (T.boundary j) a)
    (hmiddle_path : forall j : Fin 3, (middle j).IsPath)
    (hmiddle_internal :
      forall j : Fin 3, Walk.InternalVertices (middle j) ∩ P.pathSet = ∅)
    (hclean :
      forall {i j k : Fin 3},
        i ≠ j -> i ≠ k -> j ≠ k ->
          Walk.supportIndex P.path (T.boundary i) <
            Walk.supportIndex P.path (T.boundary j) ->
          Walk.supportIndex P.path (T.boundary j) <
            Walk.supportIndex P.path (T.boundary k) ->
          forall r : Fin 3, forall z : V,
            z ∈
              (P.orderedBoundaryTripleTails
                (oldBoundary := fun t : Fin 3 =>
                  T.boundary (fin3Order i j k t))
                (fun t : Fin 3 => holdAll (fin3Order i j k t))
                a (middle j) r).support ->
              z ∈ T.vertexSet ->
                z = T.boundary (fin3Order i j k r)) :
    Nonempty S.Tripod := by
  obtain ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩ :=
    P.exists_ordered_tripod_boundary_indices T holdAll
  exact
    GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_clean_parts
      P hno_cross T hij hik hjk ha
      (fun r : Fin 3 => holdAll (fin3Order i j k r))
      (middle j) (hmiddle_path j) hij_order hjk_order
      (hmiddle_internal j)
      (by
        intro z hz hzT
        simpa [fin3Order] using
          hclean hij hik hjk hij_order hjk_order 0 z hz hzT)
      (by
        intro z hz hzT
        simpa [fin3Order] using
          hclean hij hik hjk hij_order hjk_order 1 z hz hzT)
      (by
        intro z hz hzT
        simpa [fin3Order] using
          hclean hij hik hjk hij_order hjk_order 2 z hz hzT)

/-- Left-side all-path-foot constructor from the source-shaped
path-contact normalization.

The remaining proof obligation is now the mathematically meaningful one:
every point where the old side tripod meets the cut path is one of its three
feet.  Together with clean middle tails from each possible median foot to the
side boundary arc, this produces the ambient tripod. -/
theorem canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_all_path_feet_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).leftSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {a : V} (ha : a ∈ P.leftBoundaryArc)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (middle : forall j : Fin 3, S.graph.Walk (T.boundary j) a)
    (hmiddle_path : forall j : Fin 3, (middle j).IsPath)
    (hmiddle_internal :
      forall j : Fin 3, Walk.InternalVertices (middle j) ∩ P.pathSet = ∅)
    (hmiddle_clean :
      forall j : Fin 3, forall z : V,
        z ∈ (middle j).support -> z ∈ T.vertexSet ->
          z = T.boundary j) :
    Nonempty S.Tripod := by
  obtain ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩ :=
    P.exists_ordered_tripod_boundary_indices T holdAll
  exact
    GMIX24Split.canonicalOfNoCross_left_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk ha
      (fun r : Fin 3 => holdAll (fin3Order i j k r))
      (middle j) (hmiddle_path j) hij_order hjk_order
      (hmiddle_internal j) hpath_contacts (hmiddle_clean j)

/-- Right-side all-path-foot constructor from path-contact normalization. -/
theorem canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_all_path_feet_path_contacts
    [DecidableEq V] {S : GeneralSociety V}
    (P : GMIX24CutPath S)
    (hno_cross : Not (Nonempty S.Cross))
    (T : (GMIX24Split.canonicalOfNoCross P hno_cross).rightSociety.Tripod)
    (holdAll : forall i : Fin 3, T.boundary i ∈ P.pathSet)
    {a : V} (ha : a ∈ P.rightBoundaryArc)
    (hpath_contacts :
      forall z : V, z ∈ P.pathSet -> z ∈ T.vertexSet ->
        Exists fun m : Fin 3 => z = T.boundary m)
    (middle : forall j : Fin 3, S.graph.Walk (T.boundary j) a)
    (hmiddle_path : forall j : Fin 3, (middle j).IsPath)
    (hmiddle_internal :
      forall j : Fin 3, Walk.InternalVertices (middle j) ∩ P.pathSet = ∅)
    (hmiddle_clean :
      forall j : Fin 3, forall z : V,
        z ∈ (middle j).support -> z ∈ T.vertexSet ->
          z = T.boundary j) :
    Nonempty S.Tripod := by
  obtain ⟨i, j, k, hij, hik, hjk, hij_order, hjk_order⟩ :=
    P.exists_ordered_tripod_boundary_indices T holdAll
  exact
    GMIX24Split.canonicalOfNoCross_right_tripod_lift_append_boundaryTriple_tails_of_ordered_indices_path_contacts
      P hno_cross T hij hik hjk ha
      (fun r : Fin 3 => holdAll (fin3Order i j k r))
      (middle j) (hmiddle_path j) hij_order hjk_order
      (hmiddle_internal j) hpath_contacts (hmiddle_clean j)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
