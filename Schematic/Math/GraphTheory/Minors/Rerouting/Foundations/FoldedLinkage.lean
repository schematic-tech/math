import Schematic.Math.GraphTheory.Minors.Rerouting.Foundations.DuplicateVertex

/-! Folded duplicate-vertex linkage data and replacement paths. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

structure FoldedDuplicateLinkageData
    {V : Type u} (G : SimpleGraph V) (root v1 x y z : V) where
  pathX : G.Walk v1 x
  pathX_isPath : pathX.IsPath
  pathYZ : G.Walk y z
  pathYZ_isPath : pathYZ.IsPath
  pathX_pathYZ_disjoint :
    Disjoint {a : V | a ∈ pathX.support} {a : V | a ∈ pathYZ.support}

def FoldedDuplicateLinkageData.replacePathYZ
    {root v1 x y z : V}
    (F : FoldedDuplicateLinkageData G root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hq_support_subset :
      forall a : V, a ∈ q.support -> a ∈ F.pathYZ.support) :
    FoldedDuplicateLinkageData G root v1 x y z where
  pathX := F.pathX
  pathX_isPath := F.pathX_isPath
  pathYZ := q
  pathYZ_isPath := hq_path
  pathX_pathYZ_disjoint := by
    rw [Set.disjoint_left]
    intro a haX haq
    exact Set.disjoint_left.mp F.pathX_pathYZ_disjoint haX
      (hq_support_subset a haq)

/--
Replace the `yz` path by an arbitrary path disjoint from the fixed `x` path.
This is the constructor needed for the KNTW/Tutte rerouting step, where the
new `yz` path may leave the old `yz` path and run through a noncore component.
-/
def FoldedDuplicateLinkageData.replacePathYZAny
    {root v1 x y z : V}
    (F : FoldedDuplicateLinkageData G root v1 x y z)
    (q : G.Walk y z)
    (hq_path : q.IsPath)
    (hdisj :
      Disjoint {a : V | a ∈ F.pathX.support} {a : V | a ∈ q.support}) :
    FoldedDuplicateLinkageData G root v1 x y z where
  pathX := F.pathX
  pathX_isPath := F.pathX_isPath
  pathYZ := q
  pathYZ_isPath := hq_path
  pathX_pathYZ_disjoint := hdisj

theorem FoldedDuplicateLinkageData.pathYZ_chordless_of_shortest_under_replacement
    [DecidableEq V]
    {root v1 x y z : V}
    (F : FoldedDuplicateLinkageData G root v1 x y z)
    (hmin :
      forall (q : G.Walk y z), q.IsPath ->
        (forall a : V, a ∈ q.support -> a ∈ F.pathYZ.support) ->
          F.pathYZ.length <= q.length) :
    F.pathYZ.IsChordless := by
  by_contra hnot
  rcases Schematic.Math.GraphTheory.Walk.exists_shorter_path_of_not_chordless (G := G) (p := F.pathYZ) hnot with
    ⟨q, hq_path, hq_shorter, hq_support_subset⟩
  have hle := hmin q hq_path hq_support_subset
  omega

noncomputable def FoldedDuplicateLinkageData.ofDuplicatePaths
    {root v1 x y z : V}
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some x))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some z))
    (hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support})
    (hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support}) :
    FoldedDuplicateLinkageData G root v1 x y z := by
  classical
  let fold := duplicateVertexFoldHom G root
  let wX : G.Walk v1 x := pXdup.map fold
  let wYZ : G.Walk y z := (pYdup.map fold).reverse.append (pZdup.map fold)
  refine {
    pathX := (wX.toPath : G.Walk v1 x)
    pathX_isPath := wX.toPath.property
    pathYZ := (wYZ.toPath : G.Walk y z)
    pathYZ_isPath := wYZ.toPath.property
    pathX_pathYZ_disjoint := ?_
  }
  have hsome_root_not_X : some root ∉ pXdup.support := by
    intro hrootX
    exact Set.disjoint_left.mp hXY hrootX pYdup.start_mem_support
  have hnone_not_X : none ∉ pXdup.support := by
    intro hnoneX
    exact Set.disjoint_left.mp hXZ hnoneX pZdup.start_mem_support
  have hnone_not_Y : none ∉ pYdup.support := by
    intro hnoneY
    exact Set.disjoint_left.mp hYZ hnoneY pZdup.start_mem_support
  rw [Set.disjoint_left]
  intro a haX haYZ
  have haX_wX : a ∈ wX.support :=
    SimpleGraph.Walk.support_toPath_subset wX haX
  have haYZ_wYZ : a ∈ wYZ.support :=
    SimpleGraph.Walk.support_toPath_subset wYZ haYZ
  have hsome_a_X : some a ∈ pXdup.support := by
    change a ∈ (pXdup.map fold).support at haX_wX
    have hfold := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pXdup) (x := a)).mp haX_wX
    rcases hfold with hsome | ⟨haroot, hnone⟩
    · exact hsome
    · exact False.elim (hnone_not_X (by simpa [haroot] using hnone))
  have haYZ_split :
      a ∈ (pYdup.map fold).support ∨ a ∈ (pZdup.map fold).support := by
    have h := haYZ_wYZ
    change a ∈ ((pYdup.map fold).reverse.append (pZdup.map fold)).support at h
    rw [SimpleGraph.Walk.mem_support_append_iff] at h
    rcases h with hY | hZ
    · left
      simpa [SimpleGraph.Walk.support_reverse] using hY
    · exact Or.inr hZ
  rcases haYZ_split with haY | haZ
  · have hfoldY := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pYdup) (x := a)).mp
      (by simpa [fold] using haY)
    rcases hfoldY with hsomeY | ⟨haroot, hnoneY⟩
    · exact Set.disjoint_left.mp hXY hsome_a_X hsomeY
    · exact hnone_not_Y (by simpa [haroot] using hnoneY)
  · have hfoldZ := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pZdup) (x := a)).mp
      (by simpa [fold] using haZ)
    rcases hfoldZ with hsomeZ | ⟨haroot, _hnoneZ⟩
    · exact Set.disjoint_left.mp hXZ hsome_a_X hsomeZ
    · exact hsome_root_not_X (by simpa [haroot] using hsome_a_X)

noncomputable def FoldedDuplicateLinkageData.ofDuplicatePathsExact
    {root v1 x y z : V}
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some x))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some z))
    (hpXdup : pXdup.IsPath)
    (hpYdup : pYdup.IsPath)
    (hpZdup : pZdup.IsPath)
    (hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support})
    (hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support}) :
    FoldedDuplicateLinkageData G root v1 x y z := by
  classical
  let fold := duplicateVertexFoldHom G root
  let wX : G.Walk v1 x := pXdup.map fold
  let wYZ : G.Walk y z := (pYdup.map fold).reverse.append (pZdup.map fold)
  have hsome_root_not_X : some root ∉ pXdup.support := by
    intro hrootX
    exact Set.disjoint_left.mp hXY hrootX pYdup.start_mem_support
  have hnone_not_X : none ∉ pXdup.support := by
    intro hnoneX
    exact Set.disjoint_left.mp hXZ hnoneX pZdup.start_mem_support
  have hnone_not_Y : none ∉ pYdup.support := by
    intro hnoneY
    exact Set.disjoint_left.mp hYZ hnoneY pZdup.start_mem_support
  have hwX_path : wX.IsPath := by
    simpa [wX, fold] using
      duplicateVertexFoldHom_map_isPath_of_not_none
        (G := G) (root := root) hpXdup hnone_not_X
  have hwYZ_path : wYZ.IsPath := by
    simpa [wYZ, fold] using
      duplicateVertexFoldHom_reverse_append_isPath
        (G := G) (root := root) hpYdup hpZdup hYZ
  refine {
    pathX := wX
    pathX_isPath := hwX_path
    pathYZ := wYZ
    pathYZ_isPath := hwYZ_path
    pathX_pathYZ_disjoint := ?_
  }
  rw [Set.disjoint_left]
  intro a haX haYZ
  have hsome_a_X : some a ∈ pXdup.support := by
    change a ∈ (pXdup.map (duplicateVertexFoldHom G root)).support at haX
    have hfold := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pXdup) (x := a)).mp haX
    rcases hfold with hsome | ⟨haroot, hnone⟩
    · exact hsome
    · exact False.elim (hnone_not_X (by simpa [haroot] using hnone))
  have haYZ_split :
      a ∈ (pYdup.map fold).support ∨ a ∈ (pZdup.map fold).support := by
    have h := haYZ
    change a ∈ ((pYdup.map fold).reverse.append (pZdup.map fold)).support at h
    rw [SimpleGraph.Walk.mem_support_append_iff] at h
    rcases h with hY | hZ
    · left
      simpa [SimpleGraph.Walk.support_reverse] using hY
    · exact Or.inr hZ
  rcases haYZ_split with haY | haZ
  · have hfoldY := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pYdup) (x := a)).mp
      (by simpa [fold] using haY)
    rcases hfoldY with hsomeY | ⟨haroot, hnoneY⟩
    · exact Set.disjoint_left.mp hXY hsome_a_X hsomeY
    · exact hnone_not_Y (by simpa [haroot] using hnoneY)
  · have hfoldZ := (duplicateVertexFoldHom_mem_support_iff
      (G := G) (root := root) (p := pZdup) (x := a)).mp
      (by simpa [fold] using haZ)
    rcases hfoldZ with hsomeZ | ⟨haroot, _hnoneZ⟩
    · exact Set.disjoint_left.mp hXZ hsome_a_X hsomeZ
    · exact hsome_root_not_X (by simpa [haroot] using hsome_a_X)

theorem FoldedDuplicateLinkageData.ofDuplicatePathsExact_root_mem_pathYZ
    {root v1 x y z : V}
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some x))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some z))
    (hpXdup : pXdup.IsPath)
    (hpYdup : pYdup.IsPath)
    (hpZdup : pZdup.IsPath)
    (hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support})
    (hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support})
    (hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support}) :
    root ∈
      (FoldedDuplicateLinkageData.ofDuplicatePathsExact
        (G := G) (root := root) pXdup pYdup pZdup
        hpXdup hpYdup hpZdup hXY hXZ hYZ).pathYZ.support := by
  classical
  let fold := duplicateVertexFoldHom G root
  change root ∈ ((pYdup.map fold).reverse.append (pZdup.map fold)).support
  rw [SimpleGraph.Walk.mem_support_append_iff]
  left
  rw [SimpleGraph.Walk.support_reverse]
  exact List.mem_reverse.mpr (by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨some root, pYdup.start_mem_support, by simp [fold, duplicateVertexFoldHom]⟩)


end Schematic.Math.GraphTheory
