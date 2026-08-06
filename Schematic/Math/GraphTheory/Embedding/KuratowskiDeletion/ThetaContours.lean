import Schematic.Math.GraphTheory.Embedding.KuratowskiDeletion.FaceOrbitSubgraph
import Schematic.Math.GraphTheory.Embedding.RotationSystemFaceCrossing


namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

namespace EdgeDeletion

/-- Presentation-independent theta data after transport from the canonical
face-orbit subgraph to the ambient rotation graph.  Each port is the canonical
outgoing dart at the branch; the selected face contains one of its two
orientations, and the three opposite endpoints remain pairwise connected by
walks avoiding the branch. -/
structure FaceOrbitThetaBranchPorts
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H) where
  branch : W
  first : OrientedEdge H
  second : OrientedEdge H
  third : OrientedEdge H
  first_tail : first.tail = branch
  second_tail : second.tail = branch
  third_tail : third.tail = branch
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third
  first_face :
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) first ∨
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) first.symm
  second_face :
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) second ∨
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) second.symm
  third_face :
    (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) third ∨
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) third.symm
  firstSecond : H.Walk first.head second.head
  firstThird : H.Walk first.head third.head
  secondThird : H.Walk second.head third.head
  branch_not_mem_firstSecond : branch ∉ firstSecond.support
  branch_not_mem_firstThird : branch ∉ firstThird.support
  branch_not_mem_secondThird : branch ∉ secondThird.support

def faceOrbitSubgraph_thetaBranchPaths_to_ports
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (T : ThetaBranchPaths (faceOrbitSubgraph R e).coe) :
    FaceOrbitThetaBranchPorts R e := by
  let S : H.Subgraph := faceOrbitSubgraph R e
  let d₁ : OrientedEdge H :=
    ⟨((T.branch : W), (T.first : W)),
      S.coe_adj_sub T.branch T.first T.adj_first⟩
  let d₂ : OrientedEdge H :=
    ⟨((T.branch : W), (T.second : W)),
      S.coe_adj_sub T.branch T.second T.adj_second⟩
  let d₃ : OrientedEdge H :=
    ⟨((T.branch : W), (T.third : W)),
      S.coe_adj_sub T.branch T.third T.adj_third⟩
  let p₁₂ : H.Walk (T.first : W) (T.second : W) :=
    T.firstSecond.map S.hom
  let p₁₃ : H.Walk (T.first : W) (T.third : W) :=
    T.firstThird.map S.hom
  let p₂₃ : H.Walk (T.second : W) (T.third : W) :=
    T.secondThird.map S.hom
  have avoid_map
      {a b : S.verts}
      (p : S.coe.Walk a b)
      (havoid : T.branch ∉ p.support) :
      (T.branch : W) ∉ (p.map S.hom).support := by
    intro hmem
    rcases (Walk.mem_support_map_subgraph_hom_iff p).mp hmem with
      ⟨z, hz, hzval⟩
    have hz_eq : z = T.branch := Subtype.ext hzval
    exact havoid (by simpa [hz_eq] using hz)
  refine {
    branch := (T.branch : W)
    first := d₁
    second := d₂
    third := d₃
    first_tail := rfl
    second_tail := rfl
    third_tail := rfl
    first_ne_second := ?_
    first_ne_third := ?_
    second_ne_third := ?_
    first_face := ?_
    second_face := ?_
    third_face := ?_
    firstSecond := p₁₂
    firstThird := p₁₃
    secondThird := p₂₃
    branch_not_mem_firstSecond := by
      exact avoid_map T.firstSecond T.branch_not_mem_firstSecond
    branch_not_mem_firstThird := by
      exact avoid_map T.firstThird T.branch_not_mem_firstThird
    branch_not_mem_secondThird := by
      exact avoid_map T.secondThird T.branch_not_mem_secondThird
  }
  · intro h
    exact T.first_ne_second (Subtype.ext
      (congrArg OrientedEdge.head h))
  · intro h
    exact T.first_ne_third (Subtype.ext
      (congrArg OrientedEdge.head h))
  · intro h
    exact T.second_ne_third (Subtype.ext
      (congrArg OrientedEdge.head h))
  · exact faceOrbitSubgraph_coe_adj_faceBand_or_symm R e T.adj_first
  · exact faceOrbitSubgraph_coe_adj_faceBand_or_symm R e T.adj_second
  · exact faceOrbitSubgraph_coe_adj_faceBand_or_symm R e T.adj_third

theorem faceOrbitSubgraph_containsHomeomorphicTheta_branchPorts
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsHomeomorphicTheta (faceOrbitSubgraph R e).coe) :
    Nonempty (FaceOrbitThetaBranchPorts R e) := by
  rcases hθ.exists_thetaBranchPaths with ⟨T⟩
  exact ⟨faceOrbitSubgraph_thetaBranchPaths_to_ports R e T⟩

/-- Two of the three theta ports whose selected-face orientations agree,
together with the retained alternate walk between their opposite endpoints. -/
structure FaceOrbitSameOrientationBranchPair
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H) where
  branch : W
  left : OrientedEdge H
  right : OrientedEdge H
  left_tail : left.tail = branch
  right_tail : right.tail = branch
  left_ne_right : left ≠ right
  same_orientation :
    ((R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) left ∧
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) right) ∨
    ((R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) left.symm ∧
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) right.symm)
  alternate : H.Walk left.head right.head
  branch_not_mem_alternate : branch ∉ alternate.support

noncomputable def FaceOrbitThetaBranchPorts.sameOrientationPair
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (T : FaceOrbitThetaBranchPorts R e) :
    FaceOrbitSameOrientationBranchPair R e := by
  classical
  by_cases h₁ :
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) T.first
  · by_cases h₂ :
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) T.second
    · exact {
        branch := T.branch
        left := T.first
        right := T.second
        left_tail := T.first_tail
        right_tail := T.second_tail
        left_ne_right := T.first_ne_second
        same_orientation := Or.inl ⟨h₁, h₂⟩
        alternate := T.firstSecond
        branch_not_mem_alternate := T.branch_not_mem_firstSecond
      }
    · have h₂' :
          (R.toHypermap).FaceBand
            ((R.toHypermap).faceOrbitList e) T.second.symm :=
        T.second_face.resolve_left h₂
      by_cases h₃ :
          (R.toHypermap).FaceBand
            ((R.toHypermap).faceOrbitList e) T.third
      · exact {
          branch := T.branch
          left := T.first
          right := T.third
          left_tail := T.first_tail
          right_tail := T.third_tail
          left_ne_right := T.first_ne_third
          same_orientation := Or.inl ⟨h₁, h₃⟩
          alternate := T.firstThird
          branch_not_mem_alternate := T.branch_not_mem_firstThird
        }
      · have h₃' :
            (R.toHypermap).FaceBand
              ((R.toHypermap).faceOrbitList e) T.third.symm :=
          T.third_face.resolve_left h₃
        exact {
          branch := T.branch
          left := T.second
          right := T.third
          left_tail := T.second_tail
          right_tail := T.third_tail
          left_ne_right := T.second_ne_third
          same_orientation := Or.inr ⟨h₂', h₃'⟩
          alternate := T.secondThird
          branch_not_mem_alternate := T.branch_not_mem_secondThird
        }
  · have h₁' :
        (R.toHypermap).FaceBand
          ((R.toHypermap).faceOrbitList e) T.first.symm :=
      T.first_face.resolve_left h₁
    by_cases h₂ :
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) T.second
    · by_cases h₃ :
          (R.toHypermap).FaceBand
            ((R.toHypermap).faceOrbitList e) T.third
      · exact {
          branch := T.branch
          left := T.second
          right := T.third
          left_tail := T.second_tail
          right_tail := T.third_tail
          left_ne_right := T.second_ne_third
          same_orientation := Or.inl ⟨h₂, h₃⟩
          alternate := T.secondThird
          branch_not_mem_alternate := T.branch_not_mem_secondThird
        }
      · have h₃' :
            (R.toHypermap).FaceBand
              ((R.toHypermap).faceOrbitList e) T.third.symm :=
          T.third_face.resolve_left h₃
        exact {
          branch := T.branch
          left := T.first
          right := T.third
          left_tail := T.first_tail
          right_tail := T.third_tail
          left_ne_right := T.first_ne_third
          same_orientation := Or.inr ⟨h₁', h₃'⟩
          alternate := T.firstThird
          branch_not_mem_alternate := T.branch_not_mem_firstThird
        }
    · have h₂' :
          (R.toHypermap).FaceBand
            ((R.toHypermap).faceOrbitList e) T.second.symm :=
        T.second_face.resolve_left h₂
      exact {
        branch := T.branch
        left := T.first
        right := T.second
        left_tail := T.first_tail
        right_tail := T.second_tail
        left_ne_right := T.first_ne_second
        same_orientation := Or.inr ⟨h₁', h₂'⟩
        alternate := T.firstSecond
        branch_not_mem_alternate := T.branch_not_mem_firstSecond
      }

theorem faceOrbitSubgraph_containsHomeomorphicTheta_sameOrientationPair
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsHomeomorphicTheta (faceOrbitSubgraph R e).coe) :
    Nonempty (FaceOrbitSameOrientationBranchPair R e) := by
  rcases faceOrbitSubgraph_containsHomeomorphicTheta_branchPorts R e hθ with
    ⟨T⟩
  exact ⟨T.sameOrientationPair⟩

/-- Controlled contour attached to a same-oriented theta-port pair.  It runs
between the reverse darts at the far endpoints and every dart tail avoids the
common branch vertex. -/
theorem FaceOrbitSameOrientationBranchPair.exists_short_alternate_cPath
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (T : FaceOrbitSameOrientationBranchPair R e) :
    ∃ p : List (OrientedEdge H),
      (R.toHypermap).CPath T.left.symm p ∧
        (T.left.symm :: p).getLastD T.left.symm = T.right.symm ∧
          (T.left.symm :: p).Nodup ∧
            ∀ d : OrientedEdge H, d ∈ T.left.symm :: p →
              d.tail ≠ T.branch := by
  exact R.toHypermap_exists_short_cPath_of_walk_avoiding_vertex
    T.alternate T.branch_not_mem_alternate rfl rfl

/-- Normalize the two same-orientation cases.  In the outgoing case the
reverse alternate walk is lifted between the face successors; in the incoming
case it is lifted between the predecessor darts themselves. -/
theorem FaceOrbitSameOrientationBranchPair.exists_crossingData
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    (T : FaceOrbitSameOrientationBranchPair R e) :
    Nonempty (FaceOrbitCrossingData R e) := by
  have hreverseAvoid :
      T.branch ∉ T.alternate.reverse.support := by
    simpa using T.branch_not_mem_alternate
  rcases T.same_orientation with hout | hin
  · rcases R.toHypermap_exists_short_cPath_of_walk_avoiding_vertex
        T.alternate.reverse hreverseAvoid
        (e := (R.toHypermap).face T.right)
        (f := (R.toHypermap).face T.left)
        (by
          rw [RotationSystem.toHypermap_face_tail])
        (by
          rw [RotationSystem.toHypermap_face_tail]) with
      ⟨q, hq, hlast, hnodup, havoid⟩
    exact ⟨{
      branch := T.branch
      x := T.left
      y := T.right
      u := (R.toHypermap).face T.right
      v := (R.toHypermap).face T.left
      x_tail := T.left_tail
      y_tail := T.right_tail
      x_ne_y := T.left_ne_right
      x_face := hout.1
      y_face := hout.2
      connector := q
      connector_path := hq
      connector_last := hlast
      connector_nodup := hnodup
      connector_avoids_branch := havoid
      endpoint_orientation := Or.inl ⟨rfl, rfl⟩
    }⟩
  · have hxFace :
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e)
          ((R.toHypermap).face T.left.symm) :=
      Hypermap.FaceBand.of_faceReachable
        (G := R.toHypermap) hin.1
        (PermReachable.forward (R.toHypermap).face T.left.symm)
    have hyFace :
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e)
          ((R.toHypermap).face T.right.symm) :=
      Hypermap.FaceBand.of_faceReachable
        (G := R.toHypermap) hin.2
        (PermReachable.forward (R.toHypermap).face T.right.symm)
    have hxy :
        (R.toHypermap).face T.left.symm ≠
          (R.toHypermap).face T.right.symm := by
      intro h
      apply T.left_ne_right
      have hs : T.left.symm = T.right.symm :=
        (R.toHypermap).face.injective h
      simpa using congrArg OrientedEdge.symm hs
    rcases R.toHypermap_exists_short_cPath_of_walk_avoiding_vertex
        T.alternate.reverse hreverseAvoid
        (e := T.right.symm)
        (f := T.left.symm) rfl rfl with
      ⟨q, hq, hlast, hnodup, havoid⟩
    exact ⟨{
      branch := T.branch
      x := (R.toHypermap).face T.right.symm
      y := (R.toHypermap).face T.left.symm
      u := T.right.symm
      v := T.left.symm
      x_tail := by
        rw [RotationSystem.toHypermap_face_tail]
        simpa using T.right_tail
      y_tail := by
        rw [RotationSystem.toHypermap_face_tail]
        simpa using T.left_tail
      x_ne_y := hxy.symm
      x_face := hyFace
      y_face := hxFace
      connector := q
      connector_path := hq
      connector_last := hlast
      connector_nodup := hnodup
      connector_avoids_branch := havoid
      endpoint_orientation := Or.inr ⟨by simp, by simp⟩
    }⟩


theorem faceOrbit_exists_short_facePath_of_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : OrientedEdge H}
    (hx : (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) x)
    (hy : (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) y) :
    ∃ p : List (OrientedEdge H),
      (R.toHypermap).FacePath x p ∧
        (x :: p).getLastD x = y ∧
          (x :: p).Nodup := by
  have hxReach :
      PermReachable (R.toHypermap).face e x :=
    (faceOrbitSubgraph_faceBand_iff R e x).mp hx
  have hyReach :
      PermReachable (R.toHypermap).face e y :=
    (faceOrbitSubgraph_faceBand_iff R e y).mp hy
  have hxy :
      PermReachable (R.toHypermap).face x y :=
    PermReachable.trans (R.toHypermap).face
      (PermReachable.symm (R.toHypermap).face hxReach) hyReach
  exact (R.toHypermap).exists_short_facePath_of_faceReachable hxy

theorem faceOrbit_exists_short_facePath_of_mem_faceOrbitList
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : OrientedEdge H}
    (hx : x ∈ (R.toHypermap).faceOrbitList e)
    (hy : y ∈ (R.toHypermap).faceOrbitList e) :
    ∃ p : List (OrientedEdge H),
      (R.toHypermap).FacePath x p ∧
        (x :: p).getLastD x = y ∧
          (x :: p).Nodup := by
  exact faceOrbit_exists_short_facePath_of_faceBand R e
    (Hypermap.FaceBand.of_mem (G := R.toHypermap) hx
      (PermReachable.refl (R.toHypermap).face x))
    (Hypermap.FaceBand.of_mem (G := R.toHypermap) hy
      (PermReachable.refl (R.toHypermap).face y))

theorem faceOrbit_rLink_of_mem_faceOrbitList
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : OrientedEdge H}
    (hx : (R.toHypermap).edge x ∈ (R.toHypermap).faceOrbitList e)
    (hy : y ∈ (R.toHypermap).faceOrbitList e) :
    (R.toHypermap).RLink x y := by
  have hxReach :
      PermReachable (R.toHypermap).face e ((R.toHypermap).edge x) :=
    (Hypermap.mem_faceOrbitList (G := R.toHypermap)
      (x := e) (y := (R.toHypermap).edge x)).mp hx
  have hyReach :
      PermReachable (R.toHypermap).face e y :=
    (Hypermap.mem_faceOrbitList (G := R.toHypermap)
      (x := e) (y := y)).mp hy
  exact
    PermReachable.trans (R.toHypermap).face
      (PermReachable.symm (R.toHypermap).face hxReach) hyReach

theorem faceOrbit_rLink_of_faceReachable
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : OrientedEdge H}
    (hx : PermReachable (R.toHypermap).face e ((R.toHypermap).edge x))
    (hy : PermReachable (R.toHypermap).face e y) :
    (R.toHypermap).RLink x y :=
  PermReachable.trans (R.toHypermap).face
    (PermReachable.symm (R.toHypermap).face hx) hy

/-- Face-band form of `faceOrbit_rLink_of_faceReachable`: if the reverse of
`x` and the target dart `y` are carried by the selected face orbit, then the
hypermap has the corresponding `rlink`. -/
theorem faceOrbit_rLink_of_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : OrientedEdge H}
    (hx : (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e)
      ((R.toHypermap).edge x))
    (hy : (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) y) :
    (R.toHypermap).RLink x y :=
  faceOrbit_rLink_of_faceReachable R e
    ((faceOrbitSubgraph_faceBand_iff R e ((R.toHypermap).edge x)).mp hx)
    ((faceOrbitSubgraph_faceBand_iff R e y).mp hy)

/-- A finite dart list whose darts and edge-reverses all lie in one selected
face band is automatically an `rlink` cycle.  This packages the repeated
face-orbit-to-`rlink` step needed when a graph cycle has been lifted to
oriented hypermap darts. -/
theorem faceOrbit_rLinkCycle_of_forall_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {r : List (OrientedEdge H)}
    (hr : r ≠ [])
    (hedge :
      ∀ x : OrientedEdge H, x ∈ r →
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e)
          ((R.toHypermap).edge x))
    (hdart :
      ∀ x : OrientedEdge H, x ∈ r →
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) x) :
    (R.toHypermap).RLinkCycle r := by
  classical
  cases r with
  | nil =>
      exact False.elim (hr rfl)
  | cons x p =>
      have hpath :
          (R.toHypermap).RLinkPath x p := by
        induction p generalizing x with
        | nil =>
            exact Hypermap.RLinkPath.nil R.toHypermap x
        | cons y p ih =>
            have hxy : (R.toHypermap).RLink x y :=
              faceOrbit_rLink_of_faceBand R e
                (hedge x (by simp))
                (hdart y (by simp))
            have htail :
                (R.toHypermap).RLinkPath y p := by
              exact ih y (by simp)
                (fun z hz => hedge z (by simp [hz]))
                (fun z hz => hdart z (by simp [hz]))
            exact ⟨hxy, htail⟩
      have hclose :
          (R.toHypermap).RLink ((x :: p).getLastD x) x := by
        exact
          faceOrbit_rLink_of_faceBand R e
            (hedge ((x :: p).getLastD x)
              (by simp [List.getLastD]))
            (hdart x (by simp))
      exact ⟨hpath, hclose⟩

/-- Face-simple version of `faceOrbit_rLinkCycle_of_forall_faceBand`, ready
for the Jordan disk API. -/
theorem faceOrbit_simpleRLinkCycle_of_forall_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {r : List (OrientedEdge H)}
    (hr : r ≠ [])
    (hedge :
      ∀ x : OrientedEdge H, x ∈ r →
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e)
          ((R.toHypermap).edge x))
    (hdart :
      ∀ x : OrientedEdge H, x ∈ r →
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) x)
    (hsimple : (R.toHypermap).FaceSimple r) :
    (R.toHypermap).SimpleRLinkCycle r :=
  ⟨faceOrbit_rLinkCycle_of_forall_faceBand R e hr hedge hdart, hsimple⟩

theorem SubgraphCarriedByFaceOrbit.vert_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    {x : W}
    (hx : x ∈ S.verts) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        (d.tail = x ∨ d.head = x) := by
  rcases hS.1 hx with ⟨d, hd, hdx⟩
  exact
    ⟨d,
      (faceOrbitSubgraph_faceBand_iff R e d).mpr hd,
      hdx⟩

theorem SubgraphCarriedByFaceOrbit.edge_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    {x y : W}
    (hxy : S.Adj x y) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        ((d.tail = x ∧ d.head = y) ∨
          (d.tail = y ∧ d.head = x)) := by
  rcases hS.2 hxy with ⟨d, hd, hdxy⟩
  exact
    ⟨d,
      (faceOrbitSubgraph_faceBand_iff R e d).mpr hd,
      hdxy⟩

theorem SubgraphCarriedByFaceOrbit.coe_vert_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    (x : S.verts) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        (d.tail = (x : W) ∨ d.head = (x : W)) :=
  hS.vert_faceBand x.property

theorem SubgraphCarriedByFaceOrbit.coe_edge_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    {x y : S.verts}
    (hxy : S.coe.Adj x y) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        ((d.tail = (x : W) ∧ d.head = (y : W)) ∨
          (d.tail = (y : W) ∧ d.head = (x : W))) := by
  have hxyS : S.Adj (x : W) (y : W) := by
    simpa [SimpleGraph.Subgraph.coe] using hxy
  exact hS.edge_faceBand hxyS

/-- If a carried subgraph edge is incident with `x`, then the selected face
band contains a dart whose tail is exactly `x`.  If the edge witness is
oriented into `x`, take the next face dart. -/
theorem SubgraphCarriedByFaceOrbit.coe_edge_tail_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    {x y : S.verts}
    (hxy : S.coe.Adj x y) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        d.tail = (x : W) := by
  rcases hS.coe_edge_faceBand hxy with ⟨d, hd, hdir⟩
  rcases hdir with hxyDir | hyxDir
  · exact ⟨d, hd, hxyDir.1⟩
  · refine ⟨(R.toHypermap).face d, ?_, ?_⟩
    · exact Hypermap.FaceBand.of_faceReachable
        (G := R.toHypermap) hd
        (PermReachable.forward (R.toHypermap).face d)
    · rw [RotationSystem.toHypermap_face_tail]
      exact hyxDir.2

/-- Two carried subgraph edges incident with the same vertex determine
face-band darts based at that vertex and a short contour path between those
darts. -/
theorem SubgraphCarriedByFaceOrbit.coe_incident_edges_cPath
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    {x y z : S.verts}
    (hxy : S.coe.Adj x y)
    (hxz : S.coe.Adj x z) :
    Exists fun dxy : OrientedEdge H =>
      Exists fun dxz : OrientedEdge H =>
        Exists fun p : List (OrientedEdge H) =>
          (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) dxy ∧
            (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) dxz ∧
              dxy.tail = (x : W) ∧
                dxz.tail = (x : W) ∧
                  (R.toHypermap).CPath dxy p ∧
                    (dxy :: p).getLastD dxy = dxz ∧
                      (dxy :: p).Nodup := by
  rcases hS.coe_edge_tail_faceBand hxy with ⟨dxy, hdxy, hdxy_tail⟩
  rcases hS.coe_edge_tail_faceBand hxz with ⟨dxz, hdxz, hdxz_tail⟩
  rcases R.toHypermap_exists_short_cPath_of_same_tail
      (e := dxy) (f := dxz)
      (by rw [hdxy_tail, hdxz_tail]) with
    ⟨p, hp, hlast, hnodup⟩
  exact
    ⟨dxy, dxz, p, hdxy, hdxz, hdxy_tail, hdxz_tail,
      hp, hlast, hnodup⟩

theorem SubgraphCarriedByFaceOrbit.coe_dart_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    (d : S.coe.Dart) :
    Exists fun f : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) f ∧
        ((f.tail = (d.fst : W) ∧ f.head = (d.snd : W)) ∨
          (f.tail = (d.snd : W) ∧ f.head = (d.fst : W))) := by
  exact hS.coe_edge_faceBand d.adj

theorem SubgraphCarriedByFaceOrbit.walk_edge_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    {x y a b : S.verts}
    (p : S.coe.Walk x y)
    (hab : s(a, b) ∈ p.edges) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        ((d.tail = (a : W) ∧ d.head = (b : W)) ∨
          (d.tail = (b : W) ∧ d.head = (a : W))) := by
  exact hS.coe_edge_faceBand (p.adj_of_mem_edges hab)

theorem faceOrbitSubgraph_coe_dart_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (d : (faceOrbitSubgraph R e).coe.Dart) :
    Exists fun f : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) f ∧
        ((f.tail = (d.fst : W) ∧ f.head = (d.snd : W)) ∨
          (f.tail = (d.snd : W) ∧ f.head = (d.fst : W))) :=
  (faceOrbitSubgraph_carriedByFaceOrbit R e).coe_dart_faceBand d

theorem faceOrbitSubgraph_coe_edge_tail_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y : (faceOrbitSubgraph R e).verts}
    (hxy : (faceOrbitSubgraph R e).coe.Adj x y) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        d.tail = (x : W) :=
  (faceOrbitSubgraph_carriedByFaceOrbit R e).coe_edge_tail_faceBand hxy

theorem faceOrbitSubgraph_coe_incident_edges_cPath
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y z : (faceOrbitSubgraph R e).verts}
    (hxy : (faceOrbitSubgraph R e).coe.Adj x y)
    (hxz : (faceOrbitSubgraph R e).coe.Adj x z) :
    Exists fun dxy : OrientedEdge H =>
      Exists fun dxz : OrientedEdge H =>
        Exists fun p : List (OrientedEdge H) =>
          (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) dxy ∧
            (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) dxz ∧
              dxy.tail = (x : W) ∧
                dxz.tail = (x : W) ∧
                  (R.toHypermap).CPath dxy p ∧
                    (dxy :: p).getLastD dxy = dxz ∧
                      (dxy :: p).Nodup :=
  (faceOrbitSubgraph_carriedByFaceOrbit R e).coe_incident_edges_cPath hxy hxz

/-- Compact form of the endpoint contour data extracted from two face-orbit
edges incident with the same graph vertex. -/
def FaceOrbitEndpointCPath
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (x : W) : Prop :=
  Exists fun d₁ : OrientedEdge H =>
    Exists fun d₂ : OrientedEdge H =>
      Exists fun p : List (OrientedEdge H) =>
        (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d₁ ∧
          (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d₂ ∧
            d₁.tail = x ∧
              d₂.tail = x ∧
                (R.toHypermap).CPath d₁ p ∧
                  (d₁ :: p).getLastD d₁ = d₂ ∧
                    (d₁ :: p).Nodup

/-- Presentation-independent endpoint contour package for a theta cycle
carried by one face orbit.  The four vertices should be read as the branch
vertices of a selected theta cycle; this predicate deliberately records only
the contour-contact data needed by the Jordan layer. -/
def FaceOrbitThetaCycleEndpointCPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H) : Prop :=
  Exists fun x : W =>
    Exists fun y : W =>
      Exists fun u : W =>
        Exists fun v : W =>
          FaceOrbitEndpointCPath R e x ∧
            FaceOrbitEndpointCPath R e y ∧
              FaceOrbitEndpointCPath R e u ∧
                FaceOrbitEndpointCPath R e v

theorem faceOrbitSubgraph_coe_incident_edges_endpointCPath
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y z : (faceOrbitSubgraph R e).verts}
    (hxy : (faceOrbitSubgraph R e).coe.Adj x y)
    (hxz : (faceOrbitSubgraph R e).coe.Adj x z) :
    FaceOrbitEndpointCPath R e (x : W) :=
  faceOrbitSubgraph_coe_incident_edges_cPath R e hxy hxz

theorem faceOrbitSubgraph_walk_edge_faceBand
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    {x y a b : (faceOrbitSubgraph R e).verts}
    (p : (faceOrbitSubgraph R e).coe.Walk x y)
    (hab : s(a, b) ∈ p.edges) :
    Exists fun d : OrientedEdge H =>
      (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) d ∧
        ((d.tail = (a : W) ∧ d.head = (b : W)) ∨
          (d.tail = (b : W) ∧ d.head = (a : W))) :=
  (faceOrbitSubgraph_carriedByFaceOrbit R e).walk_edge_faceBand p hab

theorem SubgraphCarriedByFaceOrbit.containsEdgeTheta_faceBand_witnesses
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {S : H.Subgraph}
    (hS : SubgraphCarriedByFaceOrbit R e S)
    (hθ : ContainsEdgeTheta S.coe) :
    Exists fun x : S.verts =>
      Exists fun y : S.verts =>
        Exists fun u : S.verts =>
          Exists fun v : S.verts =>
            S.coe.Adj x y ∧
              S.coe.Adj x u ∧
                S.coe.Adj y u ∧
                  S.coe.Adj x v ∧
                    S.coe.Adj y v ∧
                      u ≠ v ∧
                        (Exists fun dxy : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dxy ∧
                            ((dxy.tail = (x : W) ∧ dxy.head = (y : W)) ∨
                              (dxy.tail = (y : W) ∧ dxy.head = (x : W)))) ∧
                        (Exists fun dxu : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dxu ∧
                            ((dxu.tail = (x : W) ∧ dxu.head = (u : W)) ∨
                              (dxu.tail = (u : W) ∧ dxu.head = (x : W)))) ∧
                        (Exists fun dyu : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dyu ∧
                            ((dyu.tail = (y : W) ∧ dyu.head = (u : W)) ∨
                              (dyu.tail = (u : W) ∧ dyu.head = (y : W)))) ∧
                        (Exists fun dxv : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dxv ∧
                            ((dxv.tail = (x : W) ∧ dxv.head = (v : W)) ∨
                              (dxv.tail = (v : W) ∧ dxv.head = (x : W)))) ∧
                        (Exists fun dyv : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dyv ∧
                            ((dyv.tail = (y : W) ∧ dyv.head = (v : W)) ∨
                              (dyv.tail = (v : W) ∧ dyv.head = (y : W)))) := by
  rcases hθ with ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv⟩
  exact
    ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv,
      hS.coe_edge_faceBand hxy,
      hS.coe_edge_faceBand hxu,
      hS.coe_edge_faceBand hyu,
      hS.coe_edge_faceBand hxv,
      hS.coe_edge_faceBand hyv⟩

theorem faceOrbitSubgraph_containsEdgeTheta_faceBand_witnesses
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsEdgeTheta (faceOrbitSubgraph R e).coe) :
    Exists fun x : (faceOrbitSubgraph R e).verts =>
      Exists fun y : (faceOrbitSubgraph R e).verts =>
        Exists fun u : (faceOrbitSubgraph R e).verts =>
          Exists fun v : (faceOrbitSubgraph R e).verts =>
            (faceOrbitSubgraph R e).coe.Adj x y ∧
              (faceOrbitSubgraph R e).coe.Adj x u ∧
                (faceOrbitSubgraph R e).coe.Adj y u ∧
                  (faceOrbitSubgraph R e).coe.Adj x v ∧
                    (faceOrbitSubgraph R e).coe.Adj y v ∧
                      u ≠ v ∧
                        (Exists fun dxy : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dxy ∧
                            ((dxy.tail = (x : W) ∧ dxy.head = (y : W)) ∨
                              (dxy.tail = (y : W) ∧ dxy.head = (x : W)))) ∧
                        (Exists fun dxu : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dxu ∧
                            ((dxu.tail = (x : W) ∧ dxu.head = (u : W)) ∨
                              (dxu.tail = (u : W) ∧ dxu.head = (x : W)))) ∧
                        (Exists fun dyu : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dyu ∧
                            ((dyu.tail = (y : W) ∧ dyu.head = (u : W)) ∨
                              (dyu.tail = (u : W) ∧ dyu.head = (y : W)))) ∧
                        (Exists fun dxv : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dxv ∧
                            ((dxv.tail = (x : W) ∧ dxv.head = (v : W)) ∨
                              (dxv.tail = (v : W) ∧ dxv.head = (x : W)))) ∧
                        (Exists fun dyv : OrientedEdge H =>
                          (R.toHypermap).FaceBand
                              ((R.toHypermap).faceOrbitList e) dyv ∧
                            ((dyv.tail = (y : W) ∧ dyv.head = (v : W)) ∨
                              (dyv.tail = (v : W) ∧ dyv.head = (y : W)))) :=
  (faceOrbitSubgraph_carriedByFaceOrbit R e).containsEdgeTheta_faceBand_witnesses hθ

/-- The direct four-vertex theta case already yields the contour contacts
needed at the two degree-three endpoints: from the two incident boundary edges
at `x`, and from the two incident boundary edges at `y`, we get short contour
paths between face-band darts based at those endpoints. -/
theorem faceOrbitSubgraph_containsEdgeTheta_endpoint_cPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsEdgeTheta (faceOrbitSubgraph R e).coe) :
    Exists fun x : (faceOrbitSubgraph R e).verts =>
      Exists fun y : (faceOrbitSubgraph R e).verts =>
        Exists fun u : (faceOrbitSubgraph R e).verts =>
          Exists fun v : (faceOrbitSubgraph R e).verts =>
            (faceOrbitSubgraph R e).coe.Adj x y ∧
              (faceOrbitSubgraph R e).coe.Adj x u ∧
                (faceOrbitSubgraph R e).coe.Adj y u ∧
                  (faceOrbitSubgraph R e).coe.Adj x v ∧
                    (faceOrbitSubgraph R e).coe.Adj y v ∧
                      u ≠ v ∧
                        (Exists fun dxu : OrientedEdge H =>
                          Exists fun dxv : OrientedEdge H =>
                            Exists fun px : List (OrientedEdge H) =>
                              (R.toHypermap).FaceBand
                                  ((R.toHypermap).faceOrbitList e) dxu ∧
                                (R.toHypermap).FaceBand
                                  ((R.toHypermap).faceOrbitList e) dxv ∧
                                  dxu.tail = (x : W) ∧
                                    dxv.tail = (x : W) ∧
                                      (R.toHypermap).CPath dxu px ∧
                                        (dxu :: px).getLastD dxu = dxv ∧
                                          (dxu :: px).Nodup) ∧
                        (Exists fun dyu : OrientedEdge H =>
                          Exists fun dyv : OrientedEdge H =>
                            Exists fun py : List (OrientedEdge H) =>
                              (R.toHypermap).FaceBand
                                  ((R.toHypermap).faceOrbitList e) dyu ∧
                                (R.toHypermap).FaceBand
                                  ((R.toHypermap).faceOrbitList e) dyv ∧
                                  dyu.tail = (y : W) ∧
                                    dyv.tail = (y : W) ∧
                                      (R.toHypermap).CPath dyu py ∧
                                        (dyu :: py).getLastD dyu = dyv ∧
                                          (dyu :: py).Nodup) := by
  rcases hθ with ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv⟩
  exact
    ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv,
      faceOrbitSubgraph_coe_incident_edges_cPath R e hxu hxv,
      faceOrbitSubgraph_coe_incident_edges_cPath R e hyu hyv⟩

/-- Direct theta case with endpoint contour contacts at all four displayed
vertices.  This is the compact package used by the Jordan step when it chooses
one theta cycle and treats the other branch as a contact/chord. -/
theorem faceOrbitSubgraph_containsEdgeTheta_all_endpointCPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsEdgeTheta (faceOrbitSubgraph R e).coe) :
    Exists fun x : (faceOrbitSubgraph R e).verts =>
      Exists fun y : (faceOrbitSubgraph R e).verts =>
        Exists fun u : (faceOrbitSubgraph R e).verts =>
          Exists fun v : (faceOrbitSubgraph R e).verts =>
            (faceOrbitSubgraph R e).coe.Adj x y ∧
              (faceOrbitSubgraph R e).coe.Adj x u ∧
                (faceOrbitSubgraph R e).coe.Adj y u ∧
                  (faceOrbitSubgraph R e).coe.Adj x v ∧
                    (faceOrbitSubgraph R e).coe.Adj y v ∧
                      u ≠ v ∧
                        FaceOrbitEndpointCPath R e (x : W) ∧
                          FaceOrbitEndpointCPath R e (y : W) ∧
                            FaceOrbitEndpointCPath R e (u : W) ∧
                              FaceOrbitEndpointCPath R e (v : W) := by
  rcases hθ with ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv⟩
  exact
    ⟨x, y, u, v, hxy, hxu, hyu, hxv, hyv, huv,
      faceOrbitSubgraph_coe_incident_edges_endpointCPath R e hxu hxv,
      faceOrbitSubgraph_coe_incident_edges_endpointCPath R e hyu hyv,
      faceOrbitSubgraph_coe_incident_edges_endpointCPath R e hxu.symm hyu.symm,
      faceOrbitSubgraph_coe_incident_edges_endpointCPath R e hxv.symm hyv.symm⟩

/-- First-step endpoint extraction for a strict subdivision carried by one
face orbit.  Two source edges incident with `x` give two first host edges
incident with the branch vertex for `x`; the face-orbit machinery then turns
those host edges into face-band darts joined by a short contour path. -/
theorem faceOrbitSubgraph_strictSubdivision_source_incident_cPath
    {X : Type v} {W : Type u} [Fintype W] [DecidableEq W]
    {K : SimpleGraph X}
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (M : StrictSubdivisionModel K (faceOrbitSubgraph R e).coe)
    {x y z : X}
    (hxy : K.Adj x y)
    (hxz : K.Adj x z) :
    Exists fun dxy : OrientedEdge H =>
      Exists fun dxz : OrientedEdge H =>
        Exists fun p : List (OrientedEdge H) =>
          (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) dxy ∧
            (R.toHypermap).FaceBand ((R.toHypermap).faceOrbitList e) dxz ∧
              dxy.tail = (M.branchVertex x : W) ∧
                dxz.tail = (M.branchVertex x : W) ∧
                  (R.toHypermap).CPath dxy p ∧
                    (dxy :: p).getLastD dxy = dxz ∧
                      (dxy :: p).Nodup := by
  let pxy :
      (faceOrbitSubgraph R e).coe.Walk
        (M.branchVertex x) (M.branchVertex y) :=
    M.edgePath hxy
  let pxz :
      (faceOrbitSubgraph R e).coe.Walk
        (M.branchVertex x) (M.branchVertex z) :=
    M.edgePath hxz
  have hpxy_not_nil : Not pxy.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pxy)
      (M.branchVertex_ne_of_adj hxy)
  have hpxz_not_nil : Not pxz.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (p := pxz)
      (M.branchVertex_ne_of_adj hxz)
  have hxy_first :
      (faceOrbitSubgraph R e).coe.Adj (M.branchVertex x) pxy.snd :=
    pxy.adj_snd hpxy_not_nil
  have hxz_first :
      (faceOrbitSubgraph R e).coe.Adj (M.branchVertex x) pxz.snd :=
    pxz.adj_snd hpxz_not_nil
  exact
    faceOrbitSubgraph_coe_incident_edges_cPath
      R e hxy_first hxz_first

theorem faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
    {X : Type v} {W : Type u} [Fintype W] [DecidableEq W]
    {K : SimpleGraph X}
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (M : StrictSubdivisionModel K (faceOrbitSubgraph R e).coe)
    {x y z : X}
    (hxy : K.Adj x y)
    (hxz : K.Adj x z) :
    FaceOrbitEndpointCPath R e (M.branchVertex x : W) :=
  faceOrbitSubgraph_strictSubdivision_source_incident_cPath
    R e M hxy hxz

/-- A strict `K_{2,3}` theta subdivision inside a face-orbit graph supplies
the same endpoint contour contacts as the direct four-vertex theta case, by
taking the first host edge on two arms at each degree-three branch vertex. -/
theorem faceOrbitSubgraph_containsThetaSubdivision_endpoint_cPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsThetaSubdivision (faceOrbitSubgraph R e).coe) :
    let x : K23Vertex := Sum.inl (0 : Fin 2)
    let y : K23Vertex := Sum.inl (1 : Fin 2)
    Exists fun M : StrictSubdivisionModel K23Graph (faceOrbitSubgraph R e).coe =>
      (Exists fun dxu : OrientedEdge H =>
        Exists fun dxv : OrientedEdge H =>
          Exists fun px : List (OrientedEdge H) =>
            (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dxu ∧
              (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dxv ∧
                dxu.tail = (M.branchVertex x : W) ∧
                  dxv.tail = (M.branchVertex x : W) ∧
                    (R.toHypermap).CPath dxu px ∧
                      (dxu :: px).getLastD dxu = dxv ∧
                        (dxu :: px).Nodup) ∧
      (Exists fun dyu : OrientedEdge H =>
        Exists fun dyv : OrientedEdge H =>
          Exists fun py : List (OrientedEdge H) =>
            (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dyu ∧
              (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dyv ∧
                dyu.tail = (M.branchVertex y : W) ∧
                  dyv.tail = (M.branchVertex y : W) ∧
                    (R.toHypermap).CPath dyu py ∧
                      (dyu :: py).getLastD dyu = dyv ∧
                        (dyu :: py).Nodup) := by
  classical
  rcases hθ with ⟨M⟩
  let x : K23Vertex := Sum.inl (0 : Fin 2)
  let y : K23Vertex := Sum.inl (1 : Fin 2)
  let u : K23Vertex := Sum.inr (0 : Fin 3)
  let v : K23Vertex := Sum.inr (1 : Fin 3)
  have hxu : K23Graph.Adj x u := by
    simp [K23Graph, x, u]
  have hxv : K23Graph.Adj x v := by
    simp [K23Graph, x, v]
  have hyu : K23Graph.Adj y u := by
    simp [K23Graph, y, u]
  have hyv : K23Graph.Adj y v := by
    simp [K23Graph, y, v]
  exact
    ⟨M,
      faceOrbitSubgraph_strictSubdivision_source_incident_cPath
        R e M hxu hxv,
      faceOrbitSubgraph_strictSubdivision_source_incident_cPath
        R e M hyu hyv⟩

/-- Strict `K_{2,3}` subdivision case with the compact endpoint-contact
package at the two degree-three branch vertices and two selected degree-two
branch vertices. -/
theorem faceOrbitSubgraph_containsThetaSubdivision_cycle_endpointCPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsThetaSubdivision (faceOrbitSubgraph R e).coe) :
    let x : K23Vertex := Sum.inl (0 : Fin 2)
    let y : K23Vertex := Sum.inl (1 : Fin 2)
    let u : K23Vertex := Sum.inr (0 : Fin 3)
    let v : K23Vertex := Sum.inr (1 : Fin 3)
    Exists fun M : StrictSubdivisionModel K23Graph (faceOrbitSubgraph R e).coe =>
      FaceOrbitEndpointCPath R e (M.branchVertex x : W) ∧
        FaceOrbitEndpointCPath R e (M.branchVertex y : W) ∧
          FaceOrbitEndpointCPath R e (M.branchVertex u : W) ∧
            FaceOrbitEndpointCPath R e (M.branchVertex v : W) := by
  classical
  rcases hθ with ⟨M⟩
  let x : K23Vertex := Sum.inl (0 : Fin 2)
  let y : K23Vertex := Sum.inl (1 : Fin 2)
  let u : K23Vertex := Sum.inr (0 : Fin 3)
  let v : K23Vertex := Sum.inr (1 : Fin 3)
  have hxu : K23Graph.Adj x u := by
    simp [K23Graph, x, u]
  have hxv : K23Graph.Adj x v := by
    simp [K23Graph, x, v]
  have hyu : K23Graph.Adj y u := by
    simp [K23Graph, y, u]
  have hyv : K23Graph.Adj y v := by
    simp [K23Graph, y, v]
  exact
    ⟨M,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hxu hxv,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hyu hyv,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hxu.symm hyu.symm,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hxv.symm hyv.symm⟩

/-- The suppressed-edge theta subdivision case is handled in the same
first-step way as the strict `K_{2,3}` subdivision.  The direct source edge
between the two degree-three vertices is intentionally not used here; the
two length-positive arms through the degree-two source vertices already give
the endpoint contour contacts needed by the face-orbit obstruction. -/
theorem faceOrbitSubgraph_containsEdgeThetaSubdivision_endpoint_cPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsEdgeThetaSubdivision (faceOrbitSubgraph R e).coe) :
    let x : EdgeThetaVertex := Sum.inl (0 : Fin 2)
    let y : EdgeThetaVertex := Sum.inl (1 : Fin 2)
    Exists fun M :
        StrictSubdivisionModel EdgeThetaGraph (faceOrbitSubgraph R e).coe =>
      (Exists fun dxu : OrientedEdge H =>
        Exists fun dxv : OrientedEdge H =>
          Exists fun px : List (OrientedEdge H) =>
            (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dxu ∧
              (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dxv ∧
                dxu.tail = (M.branchVertex x : W) ∧
                  dxv.tail = (M.branchVertex x : W) ∧
                    (R.toHypermap).CPath dxu px ∧
                      (dxu :: px).getLastD dxu = dxv ∧
                        (dxu :: px).Nodup) ∧
      (Exists fun dyu : OrientedEdge H =>
        Exists fun dyv : OrientedEdge H =>
          Exists fun py : List (OrientedEdge H) =>
            (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dyu ∧
              (R.toHypermap).FaceBand
                ((R.toHypermap).faceOrbitList e) dyv ∧
                dyu.tail = (M.branchVertex y : W) ∧
                  dyv.tail = (M.branchVertex y : W) ∧
                    (R.toHypermap).CPath dyu py ∧
                      (dyu :: py).getLastD dyu = dyv ∧
                        (dyu :: py).Nodup) := by
  classical
  rcases hθ with ⟨M⟩
  let x : EdgeThetaVertex := Sum.inl (0 : Fin 2)
  let y : EdgeThetaVertex := Sum.inl (1 : Fin 2)
  let u : EdgeThetaVertex := Sum.inr (0 : Fin 2)
  let v : EdgeThetaVertex := Sum.inr (1 : Fin 2)
  have hxu : EdgeThetaGraph.Adj x u := by
    simp [EdgeThetaGraph, x, u]
  have hxv : EdgeThetaGraph.Adj x v := by
    simp [EdgeThetaGraph, x, v]
  have hyu : EdgeThetaGraph.Adj y u := by
    simp [EdgeThetaGraph, y, u]
  have hyv : EdgeThetaGraph.Adj y v := by
    simp [EdgeThetaGraph, y, v]
  exact
    ⟨M,
      faceOrbitSubgraph_strictSubdivision_source_incident_cPath
        R e M hxu hxv,
      faceOrbitSubgraph_strictSubdivision_source_incident_cPath
        R e M hyu hyv⟩

/-- Suppressed-edge theta subdivision case with compact endpoint contacts at
the four displayed source vertices of the theta cycle
`x - u - y - v - x`. -/
theorem faceOrbitSubgraph_containsEdgeThetaSubdivision_cycle_endpointCPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsEdgeThetaSubdivision (faceOrbitSubgraph R e).coe) :
    let x : EdgeThetaVertex := Sum.inl (0 : Fin 2)
    let y : EdgeThetaVertex := Sum.inl (1 : Fin 2)
    let u : EdgeThetaVertex := Sum.inr (0 : Fin 2)
    let v : EdgeThetaVertex := Sum.inr (1 : Fin 2)
    Exists fun M :
        StrictSubdivisionModel EdgeThetaGraph (faceOrbitSubgraph R e).coe =>
      FaceOrbitEndpointCPath R e (M.branchVertex x : W) ∧
        FaceOrbitEndpointCPath R e (M.branchVertex y : W) ∧
          FaceOrbitEndpointCPath R e (M.branchVertex u : W) ∧
            FaceOrbitEndpointCPath R e (M.branchVertex v : W) := by
  classical
  rcases hθ with ⟨M⟩
  let x : EdgeThetaVertex := Sum.inl (0 : Fin 2)
  let y : EdgeThetaVertex := Sum.inl (1 : Fin 2)
  let u : EdgeThetaVertex := Sum.inr (0 : Fin 2)
  let v : EdgeThetaVertex := Sum.inr (1 : Fin 2)
  have hxu : EdgeThetaGraph.Adj x u := by
    simp [EdgeThetaGraph, x, u]
  have hxv : EdgeThetaGraph.Adj x v := by
    simp [EdgeThetaGraph, x, v]
  have hyu : EdgeThetaGraph.Adj y u := by
    simp [EdgeThetaGraph, y, u]
  have hyv : EdgeThetaGraph.Adj y v := by
    simp [EdgeThetaGraph, y, v]
  exact
    ⟨M,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hxu hxv,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hyu hyv,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hxu.symm hyu.symm,
      faceOrbitSubgraph_strictSubdivision_source_incident_endpointCPath
        R e M hxv.symm hyv.symm⟩

/-- Any of the three local homeomorphic-theta presentations in the canonical
face-orbit subgraph yields the same compact four-vertex contour-contact
package. -/
theorem faceOrbitSubgraph_containsHomeomorphicTheta_cycle_endpointCPaths
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (R : RotationSystem H)
    (e : OrientedEdge H)
    (hθ : ContainsHomeomorphicTheta (faceOrbitSubgraph R e).coe) :
    FaceOrbitThetaCycleEndpointCPaths R e := by
  rcases hθ with hstrict | hedgeOrDirect
  · rcases faceOrbitSubgraph_containsThetaSubdivision_cycle_endpointCPaths
        R e hstrict with
      ⟨M, hx, hy, hu, hv⟩
    exact
      ⟨M.branchVertex (Sum.inl (0 : Fin 2)),
        M.branchVertex (Sum.inl (1 : Fin 2)),
        M.branchVertex (Sum.inr (0 : Fin 3)),
        M.branchVertex (Sum.inr (1 : Fin 3)),
        hx, hy, hu, hv⟩
  · rcases hedgeOrDirect with hedge | hdirect
    · rcases
          faceOrbitSubgraph_containsEdgeThetaSubdivision_cycle_endpointCPaths
            R e hedge with
        ⟨M, hx, hy, hu, hv⟩
      exact
        ⟨M.branchVertex (Sum.inl (0 : Fin 2)),
          M.branchVertex (Sum.inl (1 : Fin 2)),
          M.branchVertex (Sum.inr (0 : Fin 2)),
          M.branchVertex (Sum.inr (1 : Fin 2)),
          hx, hy, hu, hv⟩
    · rcases faceOrbitSubgraph_containsEdgeTheta_all_endpointCPaths
          R e hdirect with
        ⟨x, y, u, v, _hxy, _hxu, _hyu, _hxv, _hyv, _huv,
          hx, hy, hu, hv⟩
      exact ⟨(x : W), (y : W), (u : W), (v : W), hx, hy, hu, hv⟩


end EdgeDeletion

end FourColor

end Schematic.Math.GraphTheory
