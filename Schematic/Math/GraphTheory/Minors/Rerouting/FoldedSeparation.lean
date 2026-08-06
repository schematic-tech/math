import Schematic.Math.GraphTheory.Minors.Rerouting.TargetSetMenger

/-! Folding a three-linkage through a separation. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

def ThreeVertexLinkage.toInternallyDisjointLinkage
    {left right : Fin 3 -> V}
    (L : ThreeVertexLinkage G left right) :
    VertexDisjointLinkage G left (fun i => right (L.targetEquiv i)) where
  path := L.path
  isPath := L.isPath
  pairwise_internally_vertex_disjoint := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.mp (L.pairwise_vertex_disjoint i j hij) hxi.1 hxj.1

noncomputable def ThreeVertexLinkage.foldDuplicateNormalized
    {root v1 x y z : V}
    (L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z)))
    (h0 : L.targetEquiv 0 = 0)
    (h1 : L.targetEquiv 1 = 1)
    (h2 : L.targetEquiv 2 = 2) :
    FoldedDuplicateLinkageData G root v1 x y z := by
  classical
  let pXdup :
      (duplicateVertexGraph G root).Walk (some v1) (some x) :=
    (L.path 0).copy rfl (by simp [vertexTriple, h0])
  let pYdup :
      (duplicateVertexGraph G root).Walk (some root) (some y) :=
    (L.path 1).copy rfl (by simp [vertexTriple, h1])
  let pZdup :
      (duplicateVertexGraph G root).Walk none (some z) :=
    (L.path 2).copy rfl (by simp [vertexTriple, h2])
  have hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support} := by
    simpa [pXdup, pYdup] using
      L.pairwise_vertex_disjoint 0 1 (by decide)
  have hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pXdup, pZdup] using
      L.pairwise_vertex_disjoint 0 2 (by decide)
  have hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pYdup, pZdup] using
      L.pairwise_vertex_disjoint 1 2 (by decide)
  exact FoldedDuplicateLinkageData.ofDuplicatePaths
    (G := G) (root := root) pXdup pYdup pZdup hXY hXZ hYZ

/-- The common separation argument for exact duplicate-vertex paths.  Besides
constructing the folded linkage, it retains the root-on-`yz` fact needed by
the companion membership theorem, so callers do not have to replay the
separation and support bookkeeping. -/
private noncomputable def
    FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExactInSeparation
    [DecidableEq V]
    (S : Separation G) {root v1 X Y Z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({X, Y, Z} : Set V))
    (pXdup : (duplicateVertexGraph G root).Walk (some v1) (some X))
    (pYdup : (duplicateVertexGraph G root).Walk (some root) (some Y))
    (pZdup : (duplicateVertexGraph G root).Walk none (some Z))
    (hpXdup : pXdup.IsPath)
    (hpYdup : pYdup.IsPath)
    (hpZdup : pZdup.IsPath)
    (hXY : Disjoint {a : Option V | a ∈ pXdup.support}
      {a : Option V | a ∈ pYdup.support})
    (hXZ : Disjoint {a : Option V | a ∈ pXdup.support}
      {a : Option V | a ∈ pZdup.support})
    (hYZ : Disjoint {a : Option V | a ∈ pYdup.support}
      {a : Option V | a ∈ pZdup.support}) :
    {F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z //
      root ∈ F.toLinkage.pathYZ.support} := by
  classical
  let Dsep : Separation (duplicateVertexGraph G root) :=
    duplicateVertexSeparation S hroot_left hroot_not_right
  have hDseparator :
      Dsep.separator = ({some X, some Y, some Z} : Set (Option V)) := by
    simpa [Dsep] using
      duplicateVertexSeparation_separator_triple
        (G := G) S hroot_left hroot_not_right hseparator
  have hY_not_pX : some Y ∉ pXdup.support := by
    intro hY
    exact Set.disjoint_left.mp hXY hY pYdup.end_mem_support
  have hZ_not_pX : some Z ∉ pXdup.support := by
    intro hZ
    exact Set.disjoint_left.mp hXZ hZ pZdup.end_mem_support
  have hX_not_pY : some X ∉ pYdup.support := by
    intro hX
    exact Set.disjoint_left.mp hXY pXdup.end_mem_support hX
  have hZ_not_pY : some Z ∉ pYdup.support := by
    intro hZ
    exact Set.disjoint_left.mp hYZ hZ pZdup.end_mem_support
  have hX_not_pZ : some X ∉ pZdup.support := by
    intro hX
    exact Set.disjoint_left.mp hXZ pXdup.end_mem_support hX
  have hY_not_pZ : some Y ∉ pZdup.support := by
    intro hY
    exact Set.disjoint_left.mp hYZ pYdup.end_mem_support hY
  have hDseparator_YXZ :
      Dsep.separator = ({some Y, some X, some Z} : Set (Option V)) := by
    rw [hDseparator]
    ext o
    constructor <;> intro h <;> simp [Set.mem_insert_iff] at h ⊢ <;> tauto
  have hDseparator_ZXY :
      Dsep.separator = ({some Z, some X, some Y} : Set (Option V)) := by
    rw [hDseparator]
    ext o
    constructor <;> intro h <;> simp [Set.mem_insert_iff] at h ⊢ <;> tauto
  have hX_left :
      forall o : Option V, o ∈ pXdup.support ->
        o ∈ duplicateVertexSeparationLeft S := by
    intro o ho
    have hleft : o ∈ Dsep.left :=
      Separation.Walk.IsPath.support_subset_left_of_triple_endpoint
        Dsep hpXdup hDseparator (by simpa [Dsep] using hv1_left)
        hY_not_pX hZ_not_pX o ho
    simpa [Dsep, duplicateVertexSeparation] using hleft
  have hY_left :
      forall o : Option V, o ∈ pYdup.support ->
        o ∈ duplicateVertexSeparationLeft S := by
    intro o ho
    have hleft : o ∈ Dsep.left :=
      Separation.Walk.IsPath.support_subset_left_of_triple_endpoint
        Dsep hpYdup hDseparator_YXZ (by simpa [Dsep] using hroot_left)
        hX_not_pY hZ_not_pY o ho
    simpa [Dsep, duplicateVertexSeparation] using hleft
  have hZ_left :
      forall o : Option V, o ∈ pZdup.support ->
        o ∈ duplicateVertexSeparationLeft S := by
    intro o ho
    have hleft : o ∈ Dsep.left :=
      Separation.Walk.IsPath.support_subset_left_of_triple_endpoint
        Dsep hpZdup hDseparator_ZXY
        (by change none ∈ duplicateVertexSeparationLeft S; exact trivial)
        hX_not_pZ hY_not_pZ o ho
    simpa [Dsep, duplicateVertexSeparation] using hleft
  refine ⟨?_, ?_⟩
  · exact FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExact
      (G := G) S hroot_left pXdup pYdup pZdup
      hpXdup hpYdup hpZdup hXY hXZ hYZ hX_left hY_left hZ_left
  · exact FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExact_root_mem_pathYZ
      (G := G) S hroot_left pXdup pYdup pZdup
      hpXdup hpYdup hpZdup hXY hXZ hYZ hX_left hY_left hZ_left

noncomputable def ThreeVertexLinkage.foldDuplicateNormalizedInSeparation
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z)))
    (h0 : L.targetEquiv 0 = 0)
    (h1 : L.targetEquiv 1 = 1)
    (h2 : L.targetEquiv 2 = 2) :
    FoldedDuplicateLinkageDataInSet G S.left root v1 x y z := by
  classical
  let pXdup :
      (duplicateVertexGraph G root).Walk (some v1) (some x) :=
    (L.path 0).copy rfl (by simp [vertexTriple, h0])
  let pYdup :
      (duplicateVertexGraph G root).Walk (some root) (some y) :=
    (L.path 1).copy rfl (by simp [vertexTriple, h1])
  let pZdup :
      (duplicateVertexGraph G root).Walk none (some z) :=
    (L.path 2).copy rfl (by simp [vertexTriple, h2])
  have hpXdup : pXdup.IsPath := by
    simpa [pXdup] using L.isPath 0
  have hpYdup : pYdup.IsPath := by
    simpa [pYdup] using L.isPath 1
  have hpZdup : pZdup.IsPath := by
    simpa [pZdup] using L.isPath 2
  have hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support} := by
    simpa [pXdup, pYdup] using
      L.pairwise_vertex_disjoint 0 1 (by decide)
  have hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pXdup, pZdup] using
      L.pairwise_vertex_disjoint 0 2 (by decide)
  have hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pYdup, pZdup] using
      L.pairwise_vertex_disjoint 1 2 (by decide)
  exact
    (FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExactInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparator
      pXdup pYdup pZdup hpXdup hpYdup hpZdup hXY hXZ hYZ).1

private noncomputable def ThreeVertexLinkage.foldDuplicateInSeparationWithRoot
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z))) :
    {F : FoldedDuplicateLinkageDataInSet G S.left root v1
      (vertexTriple x y z (L.targetEquiv 0))
      (vertexTriple x y z (L.targetEquiv 1))
      (vertexTriple x y z (L.targetEquiv 2)) //
        root ∈ F.toLinkage.pathYZ.support} := by
  classical
  let X : V := vertexTriple x y z (L.targetEquiv 0)
  let Y : V := vertexTriple x y z (L.targetEquiv 1)
  let Z : V := vertexTriple x y z (L.targetEquiv 2)
  have hXYZ : ({X, Y, Z} : Set V) = ({x, y, z} : Set V) := by
    simpa [X, Y, Z] using vertexTriple_equiv_set x y z L.targetEquiv
  have hseparatorXYZ : S.separator = ({X, Y, Z} : Set V) :=
    hseparator.trans hXYZ.symm
  let pXdup :
      (duplicateVertexGraph G root).Walk (some v1) (some X) :=
    (L.path 0).copy rfl (by simp [X, vertexTriple_some_apply])
  let pYdup :
      (duplicateVertexGraph G root).Walk (some root) (some Y) :=
    (L.path 1).copy rfl (by simp [Y, vertexTriple_some_apply])
  let pZdup :
      (duplicateVertexGraph G root).Walk none (some Z) :=
    (L.path 2).copy rfl (by simp [Z, vertexTriple_some_apply])
  have hpXdup : pXdup.IsPath := by
    simpa [pXdup] using L.isPath 0
  have hpYdup : pYdup.IsPath := by
    simpa [pYdup] using L.isPath 1
  have hpZdup : pZdup.IsPath := by
    simpa [pZdup] using L.isPath 2
  have hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support} := by
    simpa [pXdup, pYdup] using
      L.pairwise_vertex_disjoint 0 1 (by decide)
  have hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pXdup, pZdup] using
      L.pairwise_vertex_disjoint 0 2 (by decide)
  have hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pYdup, pZdup] using
      L.pairwise_vertex_disjoint 1 2 (by decide)
  simpa [X, Y, Z] using
    FoldedDuplicateLinkageDataInSet.ofDuplicatePathsExactInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparatorXYZ
      pXdup pYdup pZdup hpXdup hpYdup hpZdup hXY hXZ hYZ

noncomputable def ThreeVertexLinkage.foldDuplicateInSeparation
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z))) :
    FoldedDuplicateLinkageDataInSet G S.left root v1
      (vertexTriple x y z (L.targetEquiv 0))
      (vertexTriple x y z (L.targetEquiv 1))
      (vertexTriple x y z (L.targetEquiv 2)) :=
  (L.foldDuplicateInSeparationWithRoot
    (G := G) S hroot_left hroot_not_right hv1_left hseparator).1

theorem ThreeVertexLinkage.foldDuplicateInSeparation_root_mem_pathYZ
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z))) :
    root ∈
      (L.foldDuplicateInSeparation
        (G := G) S hroot_left hroot_not_right hv1_left hseparator).toLinkage.pathYZ.support := by
  exact
    (L.foldDuplicateInSeparationWithRoot
      (G := G) S hroot_left hroot_not_right hv1_left hseparator).2

noncomputable def ThreeVertexLinkage.foldDuplicate
    {root v1 x y z : V}
    (L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z))) :
    FoldedDuplicateLinkageData G root v1
      (vertexTriple x y z (L.targetEquiv 0))
      (vertexTriple x y z (L.targetEquiv 1))
      (vertexTriple x y z (L.targetEquiv 2)) := by
  classical
  let X : V := vertexTriple x y z (L.targetEquiv 0)
  let Y : V := vertexTriple x y z (L.targetEquiv 1)
  let Z : V := vertexTriple x y z (L.targetEquiv 2)
  let pXdup :
      (duplicateVertexGraph G root).Walk (some v1) (some X) :=
    (L.path 0).copy rfl (by simp [X, vertexTriple_some_apply])
  let pYdup :
      (duplicateVertexGraph G root).Walk (some root) (some Y) :=
    (L.path 1).copy rfl (by simp [Y, vertexTriple_some_apply])
  let pZdup :
      (duplicateVertexGraph G root).Walk none (some Z) :=
    (L.path 2).copy rfl (by simp [Z, vertexTriple_some_apply])
  have hpXdup : pXdup.IsPath := by
    simpa [pXdup] using L.isPath 0
  have hpYdup : pYdup.IsPath := by
    simpa [pYdup] using L.isPath 1
  have hpZdup : pZdup.IsPath := by
    simpa [pZdup] using L.isPath 2
  have hXY :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pYdup.support} := by
    simpa [pXdup, pYdup] using
      L.pairwise_vertex_disjoint 0 1 (by decide)
  have hXZ :
      Disjoint {a : Option V | a ∈ pXdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pXdup, pZdup] using
      L.pairwise_vertex_disjoint 0 2 (by decide)
  have hYZ :
      Disjoint {a : Option V | a ∈ pYdup.support}
        {a : Option V | a ∈ pZdup.support} := by
    simpa [pYdup, pZdup] using
      L.pairwise_vertex_disjoint 1 2 (by decide)
  simpa [X, Y, Z] using
    FoldedDuplicateLinkageData.ofDuplicatePathsExact
      (G := G) (root := root) pXdup pYdup pZdup
      hpXdup hpYdup hpZdup hXY hXZ hYZ

noncomputable def HasThreeVertexLinkage.foldedDuplicateInSeparation
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z))) :
    Sigma fun X : V =>
      Sigma fun Y : V =>
        Sigma fun Z : V =>
          PLift (({X, Y, Z} : Set V) = ({x, y, z} : Set V)) ×
            FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z := by
  classical
  let L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z)) :=
    Classical.choice hlink
  let X : V := vertexTriple x y z (L.targetEquiv 0)
  let Y : V := vertexTriple x y z (L.targetEquiv 1)
  let Z : V := vertexTriple x y z (L.targetEquiv 2)
  have hXYZ : ({X, Y, Z} : Set V) = ({x, y, z} : Set V) := by
    simpa [X, Y, Z] using vertexTriple_equiv_set x y z L.targetEquiv
  refine ⟨X, Y, Z, ⟨PLift.up hXYZ, ?_⟩⟩
  exact
    (by
      simpa [X, Y, Z] using
        L.foldDuplicateInSeparation
          (G := G) S hroot_left hroot_not_right hv1_left hseparator)

theorem HasThreeVertexLinkage.exists_foldedDuplicateInSeparation
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z))) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun _F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) := by
  classical
  let P :=
    hlink.foldedDuplicateInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparator
  exact ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.2, P.2.2.2.1.down⟩

theorem HasThreeVertexLinkage.exists_chordless_foldedDuplicateInSeparation
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z))) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless := by
  classical
  have hfolded :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun _F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) :=
    hlink.exists_foldedDuplicateInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparator
  rcases exists_foldedDuplicateLinkageDataInSet_tripleSet_max_core_min_path_chordless
      (G := G) (A := S.left) (root := root) (v1 := v1) hfolded with
    ⟨X, Y, Z, F, hXYZ, hchordless, _hmax, _hmin⟩
  exact ⟨X, Y, Z, F, hXYZ, hchordless⟩

theorem HasThreeVertexLinkage.exists_optimized_foldedDuplicateInSeparation
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z))) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard <=
                        F.pathXComponentCore.verts.ncard) ∧
                  (forall X' Y' Z' : V,
                    forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                      ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                        F'.pathXComponentCore.verts.ncard =
                          F.pathXComponentCore.verts.ncard ->
                            F.toLinkage.pathYZ.length <=
                              F'.toLinkage.pathYZ.length) := by
  classical
  have hfolded :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun _F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) :=
    hlink.exists_foldedDuplicateInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparator
  exact exists_foldedDuplicateLinkageDataInSet_tripleSet_max_core_min_path_chordless
    (G := G) (A := S.left) (root := root) (v1 := v1) hfolded

/-- Transfer any property proved from the canonical maximal-core,
minimal-chordless folded linkage to a witness in the separation.  This keeps
the finite optimization and existential bookkeeping independent of the
downstream property being established. -/
theorem HasThreeVertexLinkage.exists_optimized_foldedDuplicateInSeparation_satisfying
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (Q : ∀ X Y Z : V,
      FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z → Prop)
    (hQ :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  Q X Y Z F) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
            Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
              ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
                F.toLinkage.pathYZ.IsChordless ∧ Q X Y Z F := by
  rcases hlink.exists_optimized_foldedDuplicateInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparator with
    ⟨X, Y, Z, F, hXYZ, hchordless, hmax, hmin⟩
  exact ⟨X, Y, Z, F, hXYZ, hchordless,
    hQ X Y Z F hXYZ hchordless hmax hmin⟩

theorem HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_component_boundaries_pair
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hG : IsThreeConnected G)
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hcomponent_boundary_pair :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
                    Exists fun u : V =>
                      Exists fun v : V =>
                        u ∈ F.toLinkage.pathYZ.support ∧
                          v ∈ F.toLinkage.pathYZ.support ∧
                            forall b : V,
                              b ∈ F.noncorePathBoundaryOfSet
                                (F.noncoreComponent hc) ->
                                b = u ∨ b = v) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (G.induce F.deletedPathSet).Connected := by
  refine hlink.exists_optimized_foldedDuplicateInSeparation_satisfying
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
    (Q := fun _ _ _ F => (G.induce F.deletedPathSet).Connected) ?_
  intro X Y Z F hXYZ hchordless hmax hmin
  have hseparatorXYZ : S.separator = ({X, Y, Z} : Set V) :=
    hseparator.trans hXYZ.symm
  exact F.deletedPathSet_connected_of_all_component_boundaries_pair
    hG hseparatorXYZ
    (hcomponent_boundary_pair X Y Z F hXYZ hchordless hmax hmin)

theorem HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_optimized_noncore_empty
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hnoncore_empty :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  F.noncoreDeletedSet = ∅) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (G.induce F.deletedPathSet).Connected := by
  refine hlink.exists_optimized_foldedDuplicateInSeparation_satisfying
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
    (Q := fun _ _ _ F => (G.induce F.deletedPathSet).Connected) ?_
  intro X Y Z F hXYZ hchordless hmax hmin
  exact (F.deletedPathSet_connected_iff_noncoreDeletedSet_eq_empty).mpr
    (hnoncore_empty X Y Z F hXYZ hchordless hmax hmin)

theorem HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_optimized_openInterval_boundaries
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hG : IsThreeConnected G)
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hoptimized_open_interval_boundary :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
                    Exists fun C : Set V =>
                      Exists fun u : V =>
                        Exists fun v : V =>
                          F.noncoreComponent hc ⊆ C ∧
                            C ⊆ F.noncoreDeletedSet ∧
                              C.Nonempty ∧
                                u ∈ F.toLinkage.pathYZ.support ∧
                                  v ∈ F.toLinkage.pathYZ.support ∧
                                    (forall {a b : V},
                                      a ∈ C ∪
                                          Walk.OpenSupportInterval
                                            F.toLinkage.pathYZ u v ->
                                        b ∉ C ∪
                                          Walk.OpenSupportInterval
                                            F.toLinkage.pathYZ u v ->
                                        G.Adj a b -> b = u ∨ b = v)) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (G.induce F.deletedPathSet).Connected := by
  refine hlink.exists_optimized_foldedDuplicateInSeparation_satisfying
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
    (Q := fun _ _ _ F => (G.induce F.deletedPathSet).Connected) ?_
  intro X Y Z F hXYZ hchordless hmax hmin
  exact F.deletedPathSet_connected_of_component_openInterval_boundaries hG
    (hoptimized_open_interval_boundary X Y Z F hXYZ hchordless hmax hmin)

theorem HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_optimized_stable_openIntervals
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hG : IsThreeConnected G)
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hoptimized_stable_intervals :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
                    Exists fun u : V =>
                      Exists fun v : V =>
                        Exists fun b : V =>
                          u ∈ F.pathYZCoreAttachmentSet ∧
                            v ∈ F.pathYZCoreAttachmentSet ∧
                              b ∈ Walk.OpenSupportInterval
                                  F.toLinkage.pathYZ u v ∧
                                b ∈ F.noncorePathBoundaryOfSet
                                  (F.noncoreComponent hc) ∧
                                  (forall a : V,
                                    a ∈ Walk.OpenSupportInterval
                                        F.toLinkage.pathYZ u v ->
                                      a ∉ F.pathYZCoreAttachmentSet) ∧
                                    (forall {a d : V},
                                      a ∈ F.noncoreComponentsAttachedToOpenInterval
                                          u v ->
                                        d ∈ F.toLinkage.pathYZ.support ->
                                          G.Adj a d ->
                                            d ∈ Walk.OpenSupportInterval
                                                F.toLinkage.pathYZ u v ∨
                                              d = u ∨ d = v)) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (G.induce F.deletedPathSet).Connected := by
  refine hlink.exists_optimized_foldedDuplicateInSeparation_satisfying
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
    (Q := fun _ _ _ F => (G.induce F.deletedPathSet).Connected) ?_
  intro X Y Z F hXYZ hchordless hmax hmin
  have hseparatorXYZ : S.separator = ({X, Y, Z} : Set V) :=
    hseparator.trans hXYZ.symm
  exact F.deletedPathSet_connected_of_attached_stable_openIntervals
    hG hseparatorXYZ hchordless
    (hoptimized_stable_intervals X Y Z F hXYZ hchordless hmax hmin)

theorem HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_optimized_stable_openIntervals_boundary_subset
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hG : IsThreeConnected G)
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hoptimized_stable_intervals :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
                    Exists fun u : V =>
                      Exists fun v : V =>
                        Exists fun b : V =>
                          u ∈ F.pathYZCoreAttachmentSet ∧
                            v ∈ F.pathYZCoreAttachmentSet ∧
                              b ∈ Walk.OpenSupportInterval
                                  F.toLinkage.pathYZ u v ∧
                                b ∈ F.noncorePathBoundaryOfSet
                                  (F.noncoreComponent hc) ∧
                                  (forall a : V,
                                    a ∈ Walk.OpenSupportInterval
                                        F.toLinkage.pathYZ u v ->
                                      a ∉ F.pathYZCoreAttachmentSet) ∧
                                    (F.noncorePathBoundaryOfSet
                                        (F.noncoreComponentsAttachedToOpenInterval
                                          u v) ⊆
                                      Walk.SupportInterval
                                        F.toLinkage.pathYZ u v)) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (G.induce F.deletedPathSet).Connected := by
  refine hlink.exists_optimized_foldedDuplicateInSeparation_satisfying
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
    (Q := fun _ _ _ F => (G.induce F.deletedPathSet).Connected) ?_
  intro X Y Z F hXYZ hchordless hmax hmin
  have hseparatorXYZ : S.separator = ({X, Y, Z} : Set V) :=
    hseparator.trans hXYZ.symm
  exact F.deletedPathSet_connected_of_attached_stable_openIntervals_boundary_subset
    hG hseparatorXYZ hchordless
    (hoptimized_stable_intervals X Y Z F hXYZ hchordless hmax hmin)

theorem HasThreeVertexLinkage.exists_connected_foldedDuplicateInSeparation_of_optimized_nonattachment_boundary_stable
    [Fintype V] [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hG : IsThreeConnected G)
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z)))
    (hoptimized_stable :
      forall X Y Z : V,
        forall F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z,
          ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ->
            F.toLinkage.pathYZ.IsChordless ->
              (forall X' Y' Z' : V,
                forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                  ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                    F'.pathXComponentCore.verts.ncard <=
                      F.pathXComponentCore.verts.ncard) ->
                (forall X' Y' Z' : V,
                  forall F' : FoldedDuplicateLinkageDataInSet G S.left root v1 X' Y' Z',
                    ({X', Y', Z'} : Set V) = ({x, y, z} : Set V) ->
                      F'.pathXComponentCore.verts.ncard =
                        F.pathXComponentCore.verts.ncard ->
                          F.toLinkage.pathYZ.length <=
                            F'.toLinkage.pathYZ.length) ->
                  forall c : V, forall hc : c ∈ F.noncoreDeletedSet,
                    Exists fun b : V =>
                      b ∈ F.noncorePathBoundaryOfSet
                          (F.noncoreComponent hc) ∧
                        b ∉ F.pathYZCoreAttachmentSet ∧
                          forall u v : V,
                            u ∈ F.pathYZCoreAttachmentSet ->
                              v ∈ F.pathYZCoreAttachmentSet ->
                                b ∈ Walk.OpenSupportInterval
                                    F.toLinkage.pathYZ u v ->
                                  (forall a : V,
                                    a ∈ Walk.OpenSupportInterval
                                        F.toLinkage.pathYZ u v ->
                                      a ∉ F.pathYZCoreAttachmentSet) ->
                                    F.noncorePathBoundaryOfSet
                                        (F.noncoreComponentsAttachedToOpenInterval
                                          u v) ⊆
                                      Walk.SupportInterval
                                        F.toLinkage.pathYZ u v) :
      Exists fun X : V =>
        Exists fun Y : V =>
          Exists fun Z : V =>
          Exists fun F : FoldedDuplicateLinkageDataInSet G S.left root v1 X Y Z =>
            ({X, Y, Z} : Set V) = ({x, y, z} : Set V) ∧
              F.toLinkage.pathYZ.IsChordless ∧
                (G.induce F.deletedPathSet).Connected := by
  refine hlink.exists_optimized_foldedDuplicateInSeparation_satisfying
    (G := G) S hroot_left hroot_not_right hv1_left hseparator
    (Q := fun _ _ _ F => (G.induce F.deletedPathSet).Connected) ?_
  intro X Y Z F hXYZ hchordless hmax hmin
  have hseparatorXYZ : S.separator = ({X, Y, Z} : Set V) :=
    hseparator.trans hXYZ.symm
  exact F.deletedPathSet_connected_of_nonattachment_boundary_stable
    hG hseparatorXYZ hchordless
    (hoptimized_stable X Y Z F hXYZ hchordless hmax hmin)

theorem HasThreeVertexLinkage.foldedDuplicateInSeparation_root_mem_pathYZ
    [DecidableEq V]
    (S : Separation G) {root v1 x y z : V}
    (hroot_left : root ∈ S.left)
    (hroot_not_right : root ∉ S.right)
    (hv1_left : v1 ∈ S.left)
    (hseparator : S.separator = ({x, y, z} : Set V))
    (hlink :
      HasThreeVertexLinkage (duplicateVertexGraph G root)
        (vertexTriple (some v1) (some root) none)
        (vertexTriple (some x) (some y) (some z))) :
    let P := hlink.foldedDuplicateInSeparation
      (G := G) S hroot_left hroot_not_right hv1_left hseparator
    root ∈ P.2.2.2.2.toLinkage.pathYZ.support := by
  classical
  let L : ThreeVertexLinkage (duplicateVertexGraph G root)
      (vertexTriple (some v1) (some root) none)
      (vertexTriple (some x) (some y) (some z)) :=
    Classical.choice hlink
  simpa [HasThreeVertexLinkage.foldedDuplicateInSeparation, L] using
    L.foldDuplicateInSeparation_root_mem_pathYZ
      (G := G) S hroot_left hroot_not_right hv1_left hseparator

end Schematic.Math.GraphTheory
