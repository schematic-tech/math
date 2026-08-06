import Schematic.Math.GraphTheory.Minors.Society.SplitGeometry.K5SourcePaths

namespace Schematic.Math.GraphTheory

open SimpleGraph

universe u

variable {V : Type u}

namespace GeneralSociety

namespace GMIX24Split
/-- Named, path-equipped version of the `K_5` triangle-source cover branch for
one mixed Kuratowski package.

The finite source-graph split says that the three selected mixed source edges
may all be covered by three `K_5` source vertices.  In that case the two unused
source vertices and their six incident edge paths are the extra data needed to
turn the cover into a geometric contradiction. -/
structure MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    (D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5) : Type _ where
  x : Fin 5
  y : Fin 5
  z : Fin 5
  right_x_cover :
    D.right_or_path.x = x ∨ D.right_or_path.x = y ∨ D.right_or_path.x = z
  right_y_cover :
    D.right_or_path.y = x ∨ D.right_or_path.y = y ∨ D.right_or_path.y = z
  left_x_cover :
    D.left_or_path.x = x ∨ D.left_or_path.x = y ∨ D.left_or_path.x = z
  left_y_cover :
    D.left_or_path.y = x ∨ D.left_or_path.y = y ∨ D.left_or_path.y = z
  side_x_cover :
    D.left_or_right.x = x ∨ D.left_or_right.x = y ∨ D.left_or_right.x = z
  side_y_cover :
    D.left_or_right.y = x ∨ D.left_or_right.y = y ∨ D.left_or_right.y = z
  extra_paths :
    (Classical.choice hK5).K5TriangleExtraPaths x y z

noncomputable def MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.of_cover
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (hcover : D.K5ThreeSourceCover) :
    D.K5TriangleCoverExtraPaths := by
  classical
  let x : Fin 5 := Classical.choose hcover
  let Hy := Classical.choose_spec hcover
  let y : Fin 5 := Classical.choose Hy
  let Hz := Classical.choose_spec Hy
  let z : Fin 5 := Classical.choose Hz
  have hxyz := Classical.choose_spec Hz
  exact {
    x := x
    y := y
    z := z
    right_x_cover := hxyz.1
    right_y_cover := hxyz.2.1
    left_x_cover := hxyz.2.2.1
    left_y_cover := hxyz.2.2.2.1
    side_x_cover := hxyz.2.2.2.2.1
    side_y_cover := hxyz.2.2.2.2.2
    extra_paths :=
      StrictSubdivisionModel.K5TriangleExtraPaths.of_sources
        (Classical.choice hK5) x y z
  }

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_x_inter_e_x_eq_x
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    {w : V}
    (hwd : w ∈ E.extra_paths.d_a_path.support)
    (hwe : w ∈ E.extra_paths.e_a_path.support) :
    w = (Classical.choice hK5).branchVertex E.x :=
  E.extra_paths.d_a_inter_e_a_eq_a hwd hwe

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_y_inter_e_y_eq_y
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    {w : V}
    (hwd : w ∈ E.extra_paths.d_b_path.support)
    (hwe : w ∈ E.extra_paths.e_b_path.support) :
    w = (Classical.choice hK5).branchVertex E.y :=
  E.extra_paths.d_b_inter_e_b_eq_b hwd hwe

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_z_inter_e_z_eq_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    {w : V}
    (hwd : w ∈ E.extra_paths.d_c_path.support)
    (hwe : w ∈ E.extra_paths.e_c_path.support) :
    w = (Classical.choice hK5).branchVertex E.z :=
  E.extra_paths.d_c_inter_e_c_eq_c hwd hwe

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_x_inter_d_y_eq_d
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxy : E.x ≠ E.y)
    {w : V}
    (hwx : w ∈ E.extra_paths.d_a_path.support)
    (hwy : w ∈ E.extra_paths.d_b_path.support) :
    w = (Classical.choice hK5).branchVertex E.extra_paths.d :=
  E.extra_paths.d_a_inter_d_b_eq_d hxy hwx hwy

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_x_inter_d_z_eq_d
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxz : E.x ≠ E.z)
    {w : V}
    (hwx : w ∈ E.extra_paths.d_a_path.support)
    (hwz : w ∈ E.extra_paths.d_c_path.support) :
    w = (Classical.choice hK5).branchVertex E.extra_paths.d :=
  E.extra_paths.d_a_inter_d_c_eq_d hxz hwx hwz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_y_inter_d_z_eq_d
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hyz : E.y ≠ E.z)
    {w : V}
    (hwy : w ∈ E.extra_paths.d_b_path.support)
    (hwz : w ∈ E.extra_paths.d_c_path.support) :
    w = (Classical.choice hK5).branchVertex E.extra_paths.d :=
  E.extra_paths.d_b_inter_d_c_eq_d hyz hwy hwz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.e_x_inter_e_y_eq_e
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxy : E.x ≠ E.y)
    {w : V}
    (hwx : w ∈ E.extra_paths.e_a_path.support)
    (hwy : w ∈ E.extra_paths.e_b_path.support) :
    w = (Classical.choice hK5).branchVertex E.extra_paths.e :=
  E.extra_paths.e_a_inter_e_b_eq_e hxy hwx hwy

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.e_x_inter_e_z_eq_e
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxz : E.x ≠ E.z)
    {w : V}
    (hwx : w ∈ E.extra_paths.e_a_path.support)
    (hwz : w ∈ E.extra_paths.e_c_path.support) :
    w = (Classical.choice hK5).branchVertex E.extra_paths.e :=
  E.extra_paths.e_a_inter_e_c_eq_e hxz hwx hwz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.e_y_inter_e_z_eq_e
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hyz : E.y ≠ E.z)
    {w : V}
    (hwy : w ∈ E.extra_paths.e_b_path.support)
    (hwz : w ∈ E.extra_paths.e_c_path.support) :
    w = (Classical.choice hK5).branchVertex E.extra_paths.e :=
  E.extra_paths.e_b_inter_e_c_eq_e hyz hwy hwz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_x_disjoint_e_y
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxy : E.x ≠ E.y) :
    Disjoint
      {w : V | w ∈ E.extra_paths.d_a_path.support}
      {w : V | w ∈ E.extra_paths.e_b_path.support} :=
  E.extra_paths.d_a_disjoint_e_b hxy

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_x_disjoint_e_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxz : E.x ≠ E.z) :
    Disjoint
      {w : V | w ∈ E.extra_paths.d_a_path.support}
      {w : V | w ∈ E.extra_paths.e_c_path.support} :=
  E.extra_paths.d_a_disjoint_e_c hxz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_y_disjoint_e_x
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxy : E.x ≠ E.y) :
    Disjoint
      {w : V | w ∈ E.extra_paths.d_b_path.support}
      {w : V | w ∈ E.extra_paths.e_a_path.support} :=
  E.extra_paths.d_b_disjoint_e_a hxy

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_y_disjoint_e_z
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hyz : E.y ≠ E.z) :
    Disjoint
      {w : V | w ∈ E.extra_paths.d_b_path.support}
      {w : V | w ∈ E.extra_paths.e_c_path.support} :=
  E.extra_paths.d_b_disjoint_e_c hyz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_z_disjoint_e_x
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hxz : E.x ≠ E.z) :
    Disjoint
      {w : V | w ∈ E.extra_paths.d_c_path.support}
      {w : V | w ∈ E.extra_paths.e_a_path.support} :=
  E.extra_paths.d_c_disjoint_e_a hxz

theorem MixedEdgeTaggedSupportData.K5TriangleCoverExtraPaths.d_z_disjoint_e_y
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {hK5 : ContainsStrictSubdivision K5Graph S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK5}
    (E : D.K5TriangleCoverExtraPaths)
    (hyz : E.y ≠ E.z) :
    Disjoint
      {w : V | w ∈ E.extra_paths.d_c_path.support}
      {w : V | w ∈ E.extra_paths.e_b_path.support} :=
  E.extra_paths.d_c_disjoint_e_b hyz

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_fst_mem_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    D.right_or_path.e.out.1 ∈ P.rightSide ∪ P.pathSet := by
  rcases C.right_or_path_regions with hright | hpath
  · exact hright.2.1
  · exact Or.inr hpath.2.1

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_snd_mem_right_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    D.right_or_path.e.out.2 ∈ P.rightSide ∪ P.pathSet := by
  rcases C.right_or_path_regions with hright | hpath
  · exact hright.2.2
  · exact Or.inr hpath.2.2

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.left_fst_mem_left_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    D.left_or_path.e.out.1 ∈ P.leftSide ∪ P.pathSet := by
  rcases C.left_or_path_regions with hleft | hpath
  · exact hleft.2.1
  · exact Or.inr hpath.2.1

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.left_snd_mem_left_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    D.left_or_path.e.out.2 ∈ P.leftSide ∪ P.pathSet := by
  rcases C.left_or_path_regions with hleft | hpath
  · exact hleft.2.2
  · exact Or.inr hpath.2.2

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.side_fst_mem_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    D.left_or_right.e.out.1 ∈ (P.leftSide ∪ P.rightSide) ∪ P.pathSet := by
  rcases C.left_or_right_regions with hleft | hright
  · rcases hleft.2.1 with hside | hpath
    · exact Or.inl (Or.inl hside)
    · exact Or.inr hpath
  · rcases hright.2.1 with hside | hpath
    · exact Or.inl (Or.inr hside)
    · exact Or.inr hpath

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.side_snd_mem_side_or_path
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    D.left_or_right.e.out.2 ∈ (P.leftSide ∪ P.rightSide) ∪ P.pathSet := by
  rcases C.left_or_right_regions with hleft | hright
  · rcases hleft.2.2 with hside | hpath
    · exact Or.inl (Or.inl hside)
    · exact Or.inr hpath
  · rcases hright.2.2 with hside | hpath
    · exact Or.inl (Or.inr hside)
    · exact Or.inr hpath

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_fst_path_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    forall w : V, w ∈ C.right_paths.fst_path.support ->
      w ∈ D.right_or_path.supportSet :=
  C.right_paths.fst_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.right_snd_path_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    forall w : V, w ∈ C.right_paths.snd_path.support ->
      w ∈ D.right_or_path.supportSet :=
  C.right_paths.snd_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.left_fst_path_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    forall w : V, w ∈ C.left_paths.fst_path.support ->
      w ∈ D.left_or_path.supportSet :=
  C.left_paths.fst_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.left_snd_path_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    forall w : V, w ∈ C.left_paths.snd_path.support ->
      w ∈ D.left_or_path.supportSet :=
  C.left_paths.snd_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.side_fst_path_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    forall w : V, w ∈ C.side_paths.fst_path.support ->
      w ∈ D.left_or_right.supportSet :=
  C.side_paths.fst_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.side_snd_path_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    (C : D.CommonSupportEndpointPaths) :
    forall w : V, w ∈ C.side_paths.snd_path.support ->
      w ∈ D.left_or_right.supportSet :=
  C.side_paths.snd_support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_arm_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    forall w : V, w ∈ A.right_arm.path.support ->
      w ∈ D.right_or_path.supportSet :=
  A.right_arm.support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_arm_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    forall w : V, w ∈ A.left_arm.path.support ->
      w ∈ D.left_or_path.supportSet :=
  A.left_arm.support_subset

theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.side_arm_support_subset
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    forall w : V, w ∈ A.side_arm.path.support ->
      w ∈ D.left_or_right.supportSet :=
  A.side_arm.support_subset

/-- In a common-branch arm package, the right/path and left/path selected
source edges are not the same unordered edge. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.not_rightLeftSame
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Not D.rightLeftSame := by
  intro hsame
  exact A.right_left_other_ne
    (two_pair_other_endpoints_eq_of_same
      A.c_right A.c_left A.right_arm.other_ne A.right_arm.other_endpoint
      A.left_arm.other_ne A.left_arm.other_endpoint
      (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightLeftSame] using hsame))

/-- In a common-branch arm package, the right/path and left/right selected
source edges are not the same unordered edge. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.not_rightSideSame
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Not D.rightSideSame := by
  intro hsame
  exact A.right_side_other_ne
    (two_pair_other_endpoints_eq_of_same
      A.c_right A.c_side A.right_arm.other_ne A.right_arm.other_endpoint
      A.side_arm.other_ne A.side_arm.other_endpoint
      (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightSideSame] using hsame))

/-- In a common-branch arm package, the left/path and left/right selected
source edges are not the same unordered edge. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.not_leftSideSame
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    Not D.leftSideSame := by
  intro hsame
  exact A.left_side_other_ne
    (two_pair_other_endpoints_eq_of_same
      A.c_left A.c_side A.left_arm.other_ne A.left_arm.other_endpoint
      A.side_arm.other_ne A.side_arm.other_endpoint
      (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.leftSideSame] using hsame))

/-- The common source vertex is the unique common endpoint of the right/path and
left/path selected source edges in a common-branch arm package. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_left_unique_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    forall u : W,
      (u = D.right_or_path.x ∨ u = D.right_or_path.y) ->
        (u = D.left_or_path.x ∨ u = D.left_or_path.y) ->
          u = c :=
  two_pair_unique_common_endpoint_of_not_same
    D.right_or_path.hxy.ne D.left_or_path.hxy.ne
    A.c_right A.c_left
    (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightLeftSame] using
      A.not_rightLeftSame)

/-- The common source vertex is the unique common endpoint of the right/path and
left/right selected source edges in a common-branch arm package. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_side_unique_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    forall u : W,
      (u = D.right_or_path.x ∨ u = D.right_or_path.y) ->
        (u = D.left_or_right.x ∨ u = D.left_or_right.y) ->
          u = c :=
  two_pair_unique_common_endpoint_of_not_same
    D.right_or_path.hxy.ne D.left_or_right.hxy.ne
    A.c_right A.c_side
    (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightSideSame] using
      A.not_rightSideSame)

/-- The common source vertex is the unique common endpoint of the left/path and
left/right selected source edges in a common-branch arm package. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_side_unique_common_endpoint
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c) :
    forall u : W,
      (u = D.left_or_path.x ∨ u = D.left_or_path.y) ->
        (u = D.left_or_right.x ∨ u = D.left_or_right.y) ->
          u = c :=
  two_pair_unique_common_endpoint_of_not_same
    D.left_or_path.hxy.ne D.left_or_right.hxy.ne
    A.c_left A.c_side
    (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.leftSideSame] using
      A.not_leftSideSame)

/-- The right and left common-branch arms of a mixed Kuratowski package meet
only at the common strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_left_arm_inter_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    {w : V}
    (hwRight : w ∈ A.right_arm.path.support)
    (hwLeft : w ∈ A.left_arm.path.support) :
    w = (Classical.choice hK).branchVertex c := by
  classical
  exact
    D.right_or_path.support_inter_eq_common_branchVertex
      D.left_or_path
      (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightLeftSame] using
        A.not_rightLeftSame)
      A.right_left_unique_common_endpoint
      (A.right_arm_support_subset w hwRight)
      (A.left_arm_support_subset w hwLeft)

/-- The right and side common-branch arms of a mixed Kuratowski package meet
only at the common strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_side_arm_inter_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    {w : V}
    (hwRight : w ∈ A.right_arm.path.support)
    (hwSide : w ∈ A.side_arm.path.support) :
    w = (Classical.choice hK).branchVertex c := by
  classical
  exact
    D.right_or_path.support_inter_eq_common_branchVertex
      D.left_or_right
      (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightSideSame] using
        A.not_rightSideSame)
      A.right_side_unique_common_endpoint
      (A.right_arm_support_subset w hwRight)
      (A.side_arm_support_subset w hwSide)

/-- The left and side common-branch arms of a mixed Kuratowski package meet
only at the common strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_side_arm_inter_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    {w : V}
    (hwLeft : w ∈ A.left_arm.path.support)
    (hwSide : w ∈ A.side_arm.path.support) :
    w = (Classical.choice hK).branchVertex c := by
  classical
  exact
    D.left_or_path.support_inter_eq_common_branchVertex
      D.left_or_right
      (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.leftSideSame] using
        A.not_leftSideSame)
      A.left_side_unique_common_endpoint
      (A.left_arm_support_subset w hwLeft)
      (A.side_arm_support_subset w hwSide)

/-- Any right-support subpath and left-support subpath in a common-branch arm
package meet only at the common strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_left_support_paths_inter_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    {r₀ r₁ l₀ l₁ w : V}
    {qR : S.graph.Walk r₀ r₁} {qL : S.graph.Walk l₀ l₁}
    (hR : forall z : V, z ∈ qR.support -> z ∈ D.right_or_path.supportSet)
    (hL : forall z : V, z ∈ qL.support -> z ∈ D.left_or_path.supportSet)
    (hwR : w ∈ qR.support)
    (hwL : w ∈ qL.support) :
    w = (Classical.choice hK).branchVertex c :=
  D.right_or_path.support_inter_eq_common_branchVertex
    D.left_or_path
    (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightLeftSame] using
      A.not_rightLeftSame)
    A.right_left_unique_common_endpoint
    (hR w hwR) (hL w hwL)

/-- Any right-support subpath and side-support subpath in a common-branch arm
package meet only at the common strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.right_side_support_paths_inter_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    {r₀ r₁ s₀ s₁ w : V}
    {qR : S.graph.Walk r₀ r₁} {qS : S.graph.Walk s₀ s₁}
    (hR : forall z : V, z ∈ qR.support -> z ∈ D.right_or_path.supportSet)
    (hS : forall z : V, z ∈ qS.support -> z ∈ D.left_or_right.supportSet)
    (hwR : w ∈ qR.support)
    (hwS : w ∈ qS.support) :
    w = (Classical.choice hK).branchVertex c :=
  D.right_or_path.support_inter_eq_common_branchVertex
    D.left_or_right
    (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.rightSideSame] using
      A.not_rightSideSame)
    A.right_side_unique_common_endpoint
    (hR w hwR) (hS w hwS)

/-- Any left-support subpath and side-support subpath in a common-branch arm
package meet only at the common strict-subdivision branch vertex. -/
theorem MixedEdgeTaggedSupportData.CommonSupportEndpointPaths.CommonBranchArmPaths.left_side_support_paths_inter_eq_common
    [DecidableEq V] {S : GeneralSociety V}
    {P : GMIX24CutPath S}
    {hno_cross : Not (Nonempty S.Cross)}
    {W : Type*} {K : SimpleGraph W}
    {hK : ContainsStrictSubdivision K S.graph}
    {D : GMIX24Split.MixedEdgeTaggedSupportData P hno_cross hK}
    {C : D.CommonSupportEndpointPaths} {c : W}
    (A : C.CommonBranchArmPaths c)
    {l₀ l₁ s₀ s₁ w : V}
    {qL : S.graph.Walk l₀ l₁} {qS : S.graph.Walk s₀ s₁}
    (hL : forall z : V, z ∈ qL.support -> z ∈ D.left_or_path.supportSet)
    (hS : forall z : V, z ∈ qS.support -> z ∈ D.left_or_right.supportSet)
    (hwL : w ∈ qL.support)
    (hwS : w ∈ qS.support) :
    w = (Classical.choice hK).branchVertex c :=
  D.left_or_path.support_inter_eq_common_branchVertex
    D.left_or_right
    (by simpa [GMIX24Split.MixedEdgeTaggedSupportData.leftSideSame] using
      A.not_leftSideSame)
    A.left_side_unique_common_endpoint
    (hL w hwL) (hS w hwS)


end GMIX24Split

end GeneralSociety

end Schematic.Math.GraphTheory
