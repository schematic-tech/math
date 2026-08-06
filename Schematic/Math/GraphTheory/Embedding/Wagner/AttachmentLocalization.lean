import Schematic.Math.GraphTheory.Embedding.Wagner.K33Extraction
import Schematic.Math.GraphTheory.Embedding.Wagner.ThreeJoined
import Schematic.Math.GraphTheory.Embedding.Wagner.ArcRestriction
import Schematic.Math.GraphTheory.Embedding.Wagner.OppositeArcSplit
import Schematic.Math.GraphTheory.Embedding.Wagner.TwoArcSplit
import Schematic.Math.GraphTheory.Planarity.Basic

/-! Localization of planar cycle attachments to one complementary arc. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace Wagner
/-- Once one `y`-attachment lies internally on one of two complementary
`x1`--`x2` cycle arcs, planarity forces every other `y`-attachment onto that
same closed arc.  Otherwise the two arcs split at the two attachments and
give the alternating strict `K3,3` obstruction. -/
theorem IsPlanar.second_neighbors_subset_arc
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hplanar : IsPlanar G)
    {r x y x1 x2 y1 : V}
    (C : G.Walk r r)
    (p q : G.Walk x1 x2)
    (hp : p.IsPath)
    (hq : q.IsPath)
    (hp_support : forall z, z ∈ p.support -> z ∈ C.support)
    (hq_support : forall z, z ∈ q.support -> z ∈ C.support)
    (hcover : forall z, z ∈ C.support -> z ∈ p.support ∨ z ∈ q.support)
    (hd : Disjoint (Walk.InternalVertices p) (Walk.InternalVertices q))
    (hy1 : y1 ∈ Walk.InternalVertices q)
    (hxy : G.Adj x y)
    (hxx1 : G.Adj x x1) (hxx2 : G.Adj x x2)
    (hyy1 : G.Adj y y1)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    forall z, z ∈ C.support -> G.Adj y z -> z ∈ q.support := by
  intro z hzC hyz
  by_contra hzq
  have hzp : z ∈ p.support := (hcover z hzC).resolve_right hzq
  have hzx1 : z ≠ x1 := by
    intro h
    exact hzq (by simp [h])
  have hzx2 : z ≠ x2 := by
    intro h
    exact hzq (by simp [h])
  have hzInternal : z ∈ Walk.InternalVertices p :=
    ⟨hzp, hzx1, hzx2⟩
  let S : AlternatingCycleSplit C (x1 := x1) (y1 := y1)
      (x2 := x2) (y2 := z) :=
    alternatingCycleSplitOfTwoArcs C q p hq hp
      hq_support hp_support hy1 hzInternal hd.symm
  exact hplanar.no_K33_subdivision
    (containsStrictSubdivision_K33_of_alternating_cycle_split
      C S hxy hxx1 hxx2 hyy1 hyz hxC hyC)

/-- If a `y`-attachment of the cycle is not an `x`-attachment, the two
consecutive `x`-attachments surrounding it cut out an arc that contains every
`y`-attachment.  Its interior contains no `x`-attachment. -/
theorem IsPlanar.exists_attachment_arc_of_second_not_first
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hplanar : IsPlanar G)
    {r x y a b y1 : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (haC : a ∈ C.support) (hbC : b ∈ C.support)
    (hab : a ≠ b)
    (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hy1C : y1 ∈ C.support)
    (hyy1 : G.Adj y y1)
    (hnxy1 : ¬ G.Adj x y1)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    Exists fun u : V =>
      Exists fun v : V =>
        Exists fun A : CycleTwoArcs C (x1 := u) (x2 := v) =>
          G.Adj x u ∧ G.Adj x v ∧
            y1 ∈ Walk.InternalVertices A.first ∧
              (forall z, z ∈ C.support -> G.Adj y z ->
                z ∈ A.first.support) ∧
                (forall z, z ∈ Walk.InternalVertices A.first ->
                  ¬ G.Adj x z) := by
  classical
  let A0 : CycleTwoArcs C (x1 := a) (x2 := b) :=
    cycleTwoArcs C hC haC hbC hab
  have hy1_ne_a : y1 ≠ a := by
    intro h
    subst y1
    exact hnxy1 hxa
  have hy1_ne_b : y1 ≠ b := by
    intro h
    subst y1
    exact hnxy1 hxb
  have hbuild :
      forall A : CycleTwoArcs C (x1 := a) (x2 := b),
        y1 ∈ Walk.InternalVertices A.first ->
          Exists fun u : V =>
            Exists fun v : V =>
              Exists fun B : CycleTwoArcs C (x1 := u) (x2 := v) =>
                G.Adj x u ∧ G.Adj x v ∧
                  y1 ∈ Walk.InternalVertices B.first ∧
                    (forall z, z ∈ C.support -> G.Adj y z ->
                      z ∈ B.first.support) ∧
                      (forall z, z ∈ Walk.InternalVertices B.first ->
                        ¬ G.Adj x z) := by
    intro A hy1A
    let X : Set V := {z | G.Adj x z}
    have haX : a ∈ X := hxa
    have hbX : b ∈ X := hxb
    have hy1_not_X : y1 ∉ X := hnxy1
    rcases Walk.IsPath.exists_consecutive_attachment_interval
        A.first_isPath X haX hbX hy1A.1 hy1_not_X with
      ⟨u, v, huA, huX, hvA, hvX, hy1Open, hnoX⟩
    have huv :
        Walk.supportIndex A.first u < Walk.supportIndex A.first v :=
      lt_trans hy1Open.2.1 hy1Open.2.2
    let B : CycleTwoArcs C (x1 := u) (x2 := v) :=
      A.subarcs huA hvA huv
    have hy1Bsupport : y1 ∈ B.first.support := by
      rw [CycleTwoArcs.subarcs_first]
      exact Walk.mem_support_segmentBetween_of_supportIndex_between
        huA hy1A.1 hvA (Nat.le_of_lt hy1Open.2.1)
          (Nat.le_of_lt hy1Open.2.2)
    have hy1_ne_u : y1 ≠ u := by
      intro h
      subst y1
      exact Walk.left_not_mem_openSupportInterval A.first hy1Open
    have hy1_ne_v : y1 ≠ v := by
      intro h
      subst y1
      exact Walk.right_not_mem_openSupportInterval A.first hy1Open
    have hy1B : y1 ∈ Walk.InternalVertices B.first :=
      ⟨hy1Bsupport, hy1_ne_u, hy1_ne_v⟩
    have hallY :
        forall z, z ∈ C.support -> G.Adj y z -> z ∈ B.first.support :=
      IsPlanar.second_neighbors_subset_arc hplanar C B.second B.first
        B.second_isPath B.first_isPath B.second_support B.first_support
        (by
          intro z hzC
          rcases B.cover z hzC with hzFirst | hzSecond
          · exact Or.inr hzFirst
          · exact Or.inl hzSecond)
        B.internally_disjoint.symm hy1B hxy huX hvX hyy1 hxC hyC
    have hnoXInterior :
        forall z, z ∈ Walk.InternalVertices B.first -> ¬ G.Adj x z := by
      intro z hzB hzx
      have hzSegment : z ∈
          (Walk.segmentBetween A.first huA hvA (Nat.le_of_lt huv)).support := by
        simpa [B] using hzB.1
      have hzA : z ∈ A.first.support :=
        Walk.segmentBetween_support_subset huA hvA (Nat.le_of_lt huv)
          hzSegment
      have hu_le_z :
          Walk.supportIndex A.first u ≤ Walk.supportIndex A.first z :=
        Walk.segmentBetween_supportIndex_left_le A.first_isPath
          huA hvA (Nat.le_of_lt huv) hzSegment
      have hz_le_v :
          Walk.supportIndex A.first z ≤ Walk.supportIndex A.first v :=
        Walk.segmentBetween_supportIndex_right_le huA hvA
          (Nat.le_of_lt huv) hzSegment
      have hzInterval : z ∈ Walk.SupportInterval A.first u v :=
        ⟨hzA, hu_le_z, hz_le_v⟩
      rcases Walk.mem_supportInterval_eq_endpoint_or_mem_open
          A.first hzInterval with hzu | hzv | hzOpen
      · exact False.elim (hzB.2.1 hzu)
      · exact False.elim (hzB.2.2 hzv)
      · exact hnoX z hzOpen hzx
    exact ⟨u, v, B, huX, hvX, hy1B, hallY, hnoXInterior⟩
  rcases A0.cover y1 hy1C with hy1First | hy1Second
  · exact hbuild A0 ⟨hy1First, hy1_ne_a, hy1_ne_b⟩
  · exact hbuild A0.swap ⟨hy1Second, hy1_ne_a, hy1_ne_b⟩

theorem IsPlanar.not_cycle_three_joined_pair
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hplanar : IsPlanar G)
    {r x y a b c : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (ha : a ∈ C.support)
    (hb : b ∈ C.support)
    (hc : c ∈ C.support)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : G.Adj x y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    False :=
  hplanar.no_K5_subdivision
    (containsStrictSubdivision_K5_of_cycle_three_joined_pair
      C hC ha hb hc hab hac hbc hxy
      hxa hxb hxc hya hyb hyc hxC hyC)

/-- If every `y`-attachment is also an `x`-attachment, two distinct
`y`-attachments bound a complementary cycle arc containing all
`y`-attachments and no interior `x`-attachment.  Three common attachments
would give a strict `K5`; interior `x`-attachments on both sides would give a
strict `K3,3`. -/
theorem IsPlanar.exists_attachment_arc_of_second_subset_first
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (hplanar : IsPlanar G)
    {r x y y1 y2 : V}
    (C : G.Walk r r)
    (hC : C.IsCycle)
    (hy1C : y1 ∈ C.support) (hy2C : y2 ∈ C.support)
    (hy1y2 : y1 ≠ y2)
    (hxy : G.Adj x y)
    (hyy1 : G.Adj y y1) (hyy2 : G.Adj y y2)
    (hYX : forall z, z ∈ C.support -> G.Adj y z -> G.Adj x z)
    (hxC : x ∉ C.support)
    (hyC : y ∉ C.support) :
    Exists fun A : CycleTwoArcs C (x1 := y2) (x2 := y1) =>
      G.Adj x y1 ∧ G.Adj x y2 ∧
        (forall z, z ∈ C.support -> G.Adj y z ->
          z ∈ A.first.support) ∧
          (forall z, z ∈ Walk.InternalVertices A.first ->
            ¬ G.Adj x z) := by
  classical
  have hxy1 : G.Adj x y1 := hYX y1 hy1C hyy1
  have hxy2 : G.Adj x y2 := hYX y2 hy2C hyy2
  have hYtwo :
      forall z, z ∈ C.support -> G.Adj y z -> z = y1 ∨ z = y2 := by
    intro z hzC hyz
    by_cases hzy1 : z = y1
    · exact Or.inl hzy1
    by_cases hzy2 : z = y2
    · exact Or.inr hzy2
    have hxz : G.Adj x z := hYX z hzC hyz
    exact False.elim
      (IsPlanar.not_cycle_three_joined_pair hplanar C hC
        hy1C hy2C hzC hy1y2 (Ne.symm hzy1) (Ne.symm hzy2) hxy
        hxy1 hxy2 hxz hyy1 hyy2 hyz hxC hyC)
  let A0 : CycleTwoArcs C (x1 := y2) (x2 := y1) :=
    cycleTwoArcs C hC hy2C hy1C hy1y2.symm
  have hallY :
      forall A : CycleTwoArcs C (x1 := y2) (x2 := y1),
        forall z, z ∈ C.support -> G.Adj y z -> z ∈ A.first.support := by
    intro A z hzC hyz
    rcases hYtwo z hzC hyz with rfl | rfl
    · exact A.first.end_mem_support
    · exact A.first.start_mem_support
  by_cases hFirst :
      Exists fun x1 : V =>
        x1 ∈ Walk.InternalVertices A0.first ∧ G.Adj x x1
  · rcases hFirst with ⟨x1, hx1A, hxx1⟩
    by_cases hSecond :
        Exists fun x2 : V =>
          x2 ∈ Walk.InternalVertices A0.second ∧ G.Adj x x2
    · rcases hSecond with ⟨x2, hx2A, hxx2⟩
      let S : AlternatingCycleSplit C (x1 := x1) (y1 := y1)
          (x2 := x2) (y2 := y2) :=
        alternatingCycleSplitOfOppositeArcInteriors A0 hx1A hx2A
      exact False.elim
        (hplanar.no_K33_subdivision
          (containsStrictSubdivision_K33_of_alternating_cycle_split
            C S hxy hxx1 hxx2 hyy1 hyy2 hxC hyC))
    · have hnoSecond :
          forall z, z ∈ Walk.InternalVertices A0.second ->
            ¬ G.Adj x z := by
        intro z hz hzx
        exact hSecond ⟨z, hz, hzx⟩
      exact ⟨A0.swap, hxy1, hxy2, hallY A0.swap, hnoSecond⟩
  · have hnoFirst :
        forall z, z ∈ Walk.InternalVertices A0.first ->
          ¬ G.Adj x z := by
      intro z hz hzx
      exact hFirst ⟨z, hz, hzx⟩
    exact ⟨A0, hxy1, hxy2, hallY A0, hnoFirst⟩


end Wagner

end FourColor

end Schematic.Math.GraphTheory
