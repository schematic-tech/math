import Schematic.Math.GraphTheory.Embedding.WalkupGeometry

/-!
Euler-characteristic and planarity preservation for Walkup transforms.

This file contains only generic finite-hypermap results.  The
minimal-counterexample and coloring consequences remain in `WalkupCubicity`.
-/

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Unavoidability

universe u

open Hypermap

/-- Coq `le_genus_WalkupE`, isolated as the remaining reusable Walkup
planarity theorem. -/
def WalkupEGenusNonincreasing : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    (G.walkupE z).genus ≤ G.genus

/-- Difference form below Coq `le_genus_WalkupE`. -/
def WalkupEEulerDiffNonincreasing : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    (G.walkupE z).eulerLeft - (G.walkupE z).eulerRight ≤
      G.eulerLeft - G.eulerRight

/-- Coq-style count form below `le_genus_WalkupE`.  This abstracts the two
equations named `Euler_lhs_WalkupE` and `Euler_rhs_WalkupE`: the hidden
coefficients are arranged so that the right-side coefficient is no larger than
the left-side coefficient, exactly the inequality used in the nontrivial
cross-edge branch of the Coq proof. -/
def WalkupEStepCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    ∃ a b : Nat,
      b ≤ a ∧
        2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 ∧
          2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1

/-- Remaining count form after the edge-fixed branch has been closed in Lean. -/
def WalkupEStepCountNonEdgeFixedFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart), G.edge z ≠ z →
    ∃ a b : Nat,
      b ≤ a ∧
        2 * a + (G.walkupE z).eulerLeft = G.eulerLeft + 1 ∧
          2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1

/-- Lower count form for the remaining non-edge-fixed Walkup branch.  This
matches the two Coq equations `n_comp_glink_Walkup` and `fcard_skip_edge`:
`a` is the component-count coefficient, `e` is the edge-orbit coefficient,
and the node/face coefficients are already supplied by the generic skip
lemmas. -/
def WalkupENonEdgeFixedCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart), G.edge z ≠ z →
    ∃ a e b : Nat,
      b ≤ a ∧
        a + (G.walkupE z).componentCount = G.componentCount + 1 ∧
          e + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 ∧
            e + (if G.node z = z then 1 else 0) +
              (if G.face z = z then 1 else 0) = 2 * b

/-- Remaining count form after both the edge-fixed branch and the self-link
non-edge branch have been closed in Lean. -/
def WalkupENonEdgeNonSelfCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z →
      ∃ a e b : Nat,
        b ≤ a ∧
          a + (G.walkupE z).componentCount = G.componentCount + 1 ∧
            e + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 ∧
              e + (if G.node z = z then 1 else 0) +
                (if G.face z = z then 1 else 0) = 2 * b

/-- Indicator-free form of the remaining non-edge, non-self count branch.
Under `not Link z z`, both the node and face fixed-point indicators vanish,
so the parity side of `WalkupENonEdgeNonSelfCountFormula` is just
`e = 2 * b`. -/
def WalkupENonEdgeNonSelfCoreCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z →
      ∃ a e b : Nat,
        b ≤ a ∧
          a + (G.walkupE z).componentCount = G.componentCount + 1 ∧
            e + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 ∧
              e = 2 * b

/-- Cross-edge half of the remaining count branch: `node z` lies in the edge
cycle of `z`. -/
def WalkupENonEdgeNonSelfCrossCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → G.CrossEdge z →
      ∃ a e b : Nat,
        b ≤ a ∧
          a + (G.walkupE z).componentCount = G.componentCount + 1 ∧
            e + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 ∧
              e = 2 * b

/-- Non-cross-edge half of the remaining count branch: `node z` lies outside
the edge cycle of `z`. -/
def WalkupENonEdgeNonSelfNonCrossCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → ¬ G.CrossEdge z →
      ∃ a e b : Nat,
        b ≤ a ∧
          a + (G.walkupE z).componentCount = G.componentCount + 1 ∧
            e + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 ∧
              e = 2 * b

/-- Component-count half of the cross-edge branch.  Coq packages this through
`n_comp_z disconnected`; in the cross branch the coefficient may be either
`0` or `1`, so the Lean boundary only asks for existence of the coefficient. -/
def WalkupENonEdgeNonSelfCrossComponentCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → G.CrossEdge z →
      ∃ a : Nat,
        a + (G.walkupE z).componentCount = G.componentCount + 1

/-- Inequality form of the remaining cross component-count branch. -/
def WalkupENonEdgeNonSelfCrossComponentCountLe : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → G.CrossEdge z →
      (G.walkupE z).componentCount ≤ G.componentCount + 1

/-- Component-count half of the non-cross branch.  Coq
`not_cross_connected` forces the coefficient to be at least `1`. -/
def WalkupENonEdgeNonSelfNonCrossComponentCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → ¬ G.CrossEdge z →
      ∃ a : Nat,
        1 ≤ a ∧
          a + (G.walkupE z).componentCount = G.componentCount + 1

/-- Edge-orbit half of Coq `fcard_skip_edge` in the cross-edge, non-self
branch: the original edge cycle is split, so the Walkup map has one more edge
orbit. -/
def WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → G.CrossEdge z →
      0 + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1

/-- The remaining local classification needed for the cross-edge count: the
single affected original edge orbit splits into exactly the two canonical
Walkup edge orbits represented by `edge z` and `edge.symm z`. -/
def WalkupENonEdgeNonSelfCrossAffectedFiberExhaustive : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    ∀ (hself : ¬ G.Link z z) (hcross : G.CrossEdge z),
      ∀ q : G.CrossAffectedEdgeFiber hself hcross,
        q = G.crossAffectedEdgeFiberEdgeZ hself hcross ∨
          q = G.crossAffectedEdgeFiberEdgeSymm hself hcross

/-- Edge-orbit half of Coq `fcard_skip_edge` in the non-cross, non-self
branch: the two affected edge cycles are merged. -/
def WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula : Prop :=
  ∀ (G : Hypermap.{u}) (z : G.Dart),
    G.edge z ≠ z → ¬ G.Link z z → ¬ G.CrossEdge z →
      2 + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1

theorem walkupENonEdgeNonSelfCrossCountFormula_of_component_edgeOrbit
    (hcomp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hedge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCrossCountFormula.{u} := by
  intro G z he hself hcross
  rcases hcomp G z he hself hcross with ⟨a, hcomp⟩
  exact ⟨a, 0, 0, Nat.zero_le a, hcomp,
    hedge G z he hself hcross, by omega⟩

theorem walkupENonEdgeNonSelfNonCrossCountFormula_of_component_edgeOrbit
    (hcomp : WalkupENonEdgeNonSelfNonCrossComponentCountFormula.{u})
    (hedge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfNonCrossCountFormula.{u} := by
  intro G z he hself hcross
  rcases hcomp G z he hself hcross with ⟨a, ha, hcomp⟩
  exact ⟨a, 2, 1, ha, hcomp,
    hedge G z he hself hcross, by omega⟩

theorem walkupENonEdgeNonSelfNonCrossComponentCountFormula_proved :
    WalkupENonEdgeNonSelfNonCrossComponentCountFormula.{u} := by
  intro G z _he hself hnoncross
  exact ⟨1, le_rfl,
    G.walkupE_componentCount_step_of_not_cross hself hnoncross⟩

theorem walkupENonEdgeNonSelfCrossComponentCountFormula_of_le
    (hle : WalkupENonEdgeNonSelfCrossComponentCountLe.{u}) :
    WalkupENonEdgeNonSelfCrossComponentCountFormula.{u} := by
  intro G z he hself hcross
  refine ⟨G.componentCount + 1 - (G.walkupE z).componentCount, ?_⟩
  exact Nat.sub_add_cancel (hle G z he hself hcross)

theorem walkupENonEdgeNonSelfCrossComponentCountLe_proved :
    WalkupENonEdgeNonSelfCrossComponentCountLe.{u} := by
  intro G z _he hself hcross
  exact G.walkupE_cross_componentCount_le hself hcross

theorem walkupENonEdgeNonSelfCrossComponentCountFormula_proved :
    WalkupENonEdgeNonSelfCrossComponentCountFormula.{u} :=
  walkupENonEdgeNonSelfCrossComponentCountFormula_of_le
    walkupENonEdgeNonSelfCrossComponentCountLe_proved

theorem walkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula_proved :
    WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u} := by
  intro G z _he hself hnoncross
  have h := G.walkupE_nonCross_edgeOrbitCount_add_one_eq hself hnoncross
  omega

theorem walkupENonEdgeNonSelfCrossEdgeOrbitCountFormula_of_fiberExhaustive
    (hfiber : WalkupENonEdgeNonSelfCrossAffectedFiberExhaustive.{u}) :
    WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u} := by
  intro G z _he hself hcross
  have h := G.walkupE_cross_edgeOrbitCount_add_one_eq_of_fiberExhaustive
    hself hcross (hfiber G z hself hcross)
  omega

theorem walkupENonEdgeNonSelfCrossEdgeOrbitCountFormula_proved :
    WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u} := by
  intro G z _he hself hcross
  have h := G.walkupE_cross_edgeOrbitCount_add_one_eq hself hcross
  omega

theorem walkupENonEdgeNonSelfCoreCountFormula_of_countFormula
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u}) :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} := by
  intro G z he hself
  rcases hcounts G z he hself with
    ⟨a, e, b, hba, hcomp, hedge, hsum⟩
  have hn : G.node z ≠ z := G.node_ne_self_of_not_link_self hself
  have hf : G.face z ≠ z := G.face_ne_self_of_not_link_self hself
  exact ⟨a, e, b, hba, hcomp, hedge, by
    simpa [hn, hf] using hsum⟩

theorem walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    (hcounts : WalkupENonEdgeNonSelfCoreCountFormula.{u}) :
    WalkupENonEdgeNonSelfCountFormula.{u} := by
  intro G z he hself
  rcases hcounts G z he hself with
    ⟨a, e, b, hba, hcomp, hedge, hsum⟩
  have hn : G.node z ≠ z := G.node_ne_self_of_not_link_self hself
  have hf : G.face z ≠ z := G.face_ne_self_of_not_link_self hself
  exact ⟨a, e, b, hba, hcomp, hedge, by
    simpa [hn, hf] using hsum⟩

theorem walkupENonEdgeNonSelfCoreCountFormula_of_crossSplit
    (hcross : WalkupENonEdgeNonSelfCrossCountFormula.{u})
    (hnoncross : WalkupENonEdgeNonSelfNonCrossCountFormula.{u}) :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} := by
  intro G z he hself
  by_cases hcz : G.CrossEdge z
  · exact hcross G z he hself hcz
  · exact hnoncross G z he hself hcz

theorem walkupENonEdgeNonSelfCountFormula_of_crossSplit
    (hcross : WalkupENonEdgeNonSelfCrossCountFormula.{u})
    (hnoncross : WalkupENonEdgeNonSelfNonCrossCountFormula.{u}) :
    WalkupENonEdgeNonSelfCountFormula.{u} :=
  walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    (walkupENonEdgeNonSelfCoreCountFormula_of_crossSplit hcross hnoncross)

theorem walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossComp : WalkupENonEdgeNonSelfNonCrossComponentCountFormula.{u})
    (hnoncrossEdge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} :=
  walkupENonEdgeNonSelfCoreCountFormula_of_crossSplit
    (walkupENonEdgeNonSelfCrossCountFormula_of_component_edgeOrbit
      hcrossComp hcrossEdge)
    (walkupENonEdgeNonSelfNonCrossCountFormula_of_component_edgeOrbit
      hnoncrossComp hnoncrossEdge)

theorem walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossEdge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} :=
  walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit
    hcrossComp hcrossEdge
    walkupENonEdgeNonSelfNonCrossComponentCountFormula_proved
    hnoncrossEdge

theorem walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} :=
  walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
    hcrossComp hcrossEdge
    walkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula_proved

theorem walkupENonEdgeNonSelfCoreCountFormula_of_crossComponent
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u}) :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} :=
  walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
    hcrossComp
    walkupENonEdgeNonSelfCrossEdgeOrbitCountFormula_proved

theorem walkupENonEdgeNonSelfCoreCountFormula_proved :
    WalkupENonEdgeNonSelfCoreCountFormula.{u} :=
  walkupENonEdgeNonSelfCoreCountFormula_of_crossComponent
    walkupENonEdgeNonSelfCrossComponentCountFormula_proved

theorem walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossComp : WalkupENonEdgeNonSelfNonCrossComponentCountFormula.{u})
    (hnoncrossEdge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCountFormula.{u} :=
  walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    (walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit
      hcrossComp hcrossEdge hnoncrossComp hnoncrossEdge)

theorem walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u})
    (hnoncrossEdge : WalkupENonEdgeNonSelfNonCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCountFormula.{u} :=
  walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    (walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit_nonCrossComponent
      hcrossComp hcrossEdge hnoncrossEdge)

theorem walkupENonEdgeNonSelfCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u})
    (hcrossEdge : WalkupENonEdgeNonSelfCrossEdgeOrbitCountFormula.{u}) :
    WalkupENonEdgeNonSelfCountFormula.{u} :=
  walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    (walkupENonEdgeNonSelfCoreCountFormula_of_component_edgeOrbitSplit_nonCrossSolved
      hcrossComp hcrossEdge)

theorem walkupENonEdgeNonSelfCountFormula_of_crossComponent
    (hcrossComp : WalkupENonEdgeNonSelfCrossComponentCountFormula.{u}) :
    WalkupENonEdgeNonSelfCountFormula.{u} :=
  walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    (walkupENonEdgeNonSelfCoreCountFormula_of_crossComponent hcrossComp)

theorem walkupENonEdgeNonSelfCountFormula_proved :
    WalkupENonEdgeNonSelfCountFormula.{u} :=
  walkupENonEdgeNonSelfCountFormula_of_coreCountFormula
    walkupENonEdgeNonSelfCoreCountFormula_proved

theorem walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula
    (hcounts : WalkupENonEdgeNonSelfCountFormula.{u}) :
    WalkupENonEdgeFixedCountFormula.{u} := by
  intro G z he
  by_cases hz : G.Link z z
  · exact G.walkupE_nonEdgeFixedCount_of_link_self hz he
  · exact hcounts G z he hz

theorem walkupENonEdgeFixedCountFormula_proved :
    WalkupENonEdgeFixedCountFormula.{u} :=
  walkupENonEdgeFixedCountFormula_of_nonSelfCountFormula
    walkupENonEdgeNonSelfCountFormula_proved

theorem walkupEStepCountNonEdgeFixedFormula_of_countFormula
    (hcounts : WalkupENonEdgeFixedCountFormula.{u}) :
    WalkupEStepCountNonEdgeFixedFormula.{u} := by
  intro G z he
  rcases hcounts G z he with ⟨a, e, b, hba, hcomp, hedge, hsum⟩
  exact G.walkupE_stepCount_of_count_steps hba hcomp hedge hsum

theorem walkupEStepCountNonEdgeFixedFormula_proved :
    WalkupEStepCountNonEdgeFixedFormula.{u} :=
  walkupEStepCountNonEdgeFixedFormula_of_countFormula
    walkupENonEdgeFixedCountFormula_proved

theorem walkupEStepCountFormula_of_nonEdgeFixedFormula
    (hcounts : WalkupEStepCountNonEdgeFixedFormula.{u}) :
    WalkupEStepCountFormula.{u} := by
  intro G z
  by_cases he : G.edge z = z
  · exact G.walkupE_stepCount_of_edge_fixed he
  · exact hcounts G z he

theorem walkupEStepCountFormula_proved :
    WalkupEStepCountFormula.{u} :=
  walkupEStepCountFormula_of_nonEdgeFixedFormula
    walkupEStepCountNonEdgeFixedFormula_proved

theorem walkupEEulerDiffNonincreasing_of_stepCountFormula
    (hcounts : WalkupEStepCountFormula.{u}) :
    WalkupEEulerDiffNonincreasing.{u} := by
  intro G z
  rcases hcounts G z with ⟨a, b, hba, hleft, hright⟩
  exact G.eulerDiff_le_of_walkup_step_counts (G.walkupE z)
    hba hleft hright

theorem walkupEEulerDiffNonincreasing_proved :
    WalkupEEulerDiffNonincreasing.{u} :=
  walkupEEulerDiffNonincreasing_of_stepCountFormula
    walkupEStepCountFormula_proved

theorem walkupEGenusNonincreasing_of_eulerDiffNonincreasing
    (hdiff : WalkupEEulerDiffNonincreasing.{u}) :
    WalkupEGenusNonincreasing.{u} := by
  intro G z
  exact G.genus_le_of_eulerDiff_le (G.walkupE z) (hdiff G z)

theorem walkupEGenusNonincreasing_of_stepCountFormula
    (hcounts : WalkupEStepCountFormula.{u}) :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_eulerDiffNonincreasing
    (walkupEEulerDiffNonincreasing_of_stepCountFormula hcounts)

theorem walkupEGenusNonincreasing_proved :
    WalkupEGenusNonincreasing.{u} :=
  walkupEGenusNonincreasing_of_stepCountFormula
    walkupEStepCountFormula_proved

/-- Coq `planar_WalkupE`: deleting one dart with `WalkupE` preserves
Euler-planarity. -/
theorem walkupE_eulerPlanar_of_eulerPlanar
    (G : Hypermap.{u}) (z : G.Dart)
    (hplanar : G.EulerPlanar) :
    (G.walkupE z).EulerPlanar :=
  G.walkupE_eulerPlanar_of_genus_le
    (walkupEGenusNonincreasing_proved G z) hplanar

/-- Coq `planar_WalkupN`, obtained from `planar_WalkupE` by cyclic
permutation of the hypermap structure. -/
theorem walkupN_eulerPlanar_of_eulerPlanar
    (G : Hypermap.{u}) (z : G.Dart)
    (hplanar : G.EulerPlanar) :
    (G.walkupN z).EulerPlanar := by
  change ((G.permNode.walkupE z).permFace).EulerPlanar
  have hperm : G.permNode.EulerPlanar :=
    (G.permNode_eulerPlanar_iff).mpr hplanar
  have hE : (G.permNode.walkupE z).EulerPlanar :=
    walkupE_eulerPlanar_of_eulerPlanar G.permNode z hperm
  exact ((G.permNode.walkupE z).permFace_eulerPlanar_iff).mpr hE

/-- Coq `planar_WalkupF`, obtained from `planar_WalkupE` by cyclic
permutation of the hypermap structure. -/
theorem walkupF_eulerPlanar_of_eulerPlanar
    (G : Hypermap.{u}) (z : G.Dart)
    (hplanar : G.EulerPlanar) :
    (G.walkupF z).EulerPlanar := by
  change ((G.permFace.walkupE z).permNode).EulerPlanar
  have hperm : G.permFace.EulerPlanar :=
    (G.permFace_eulerPlanar_iff).mpr hplanar
  have hE : (G.permFace.walkupE z).EulerPlanar :=
    walkupE_eulerPlanar_of_eulerPlanar G.permFace z hperm
  exact ((G.permFace.walkupE z).permNode_eulerPlanar_iff).mpr hE

/-- Coq `planar_Jordan`: Euler-planar finite hypermaps satisfy Jordan. -/
theorem eulerPlanar_jordan
    (G : Hypermap.{u})
    (hplanar : G.EulerPlanar) :
    G.Jordan := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ H : Hypermap.{u},
      Fintype.card H.Dart = n →
        H.EulerPlanar →
          H.Jordan
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro H hcard hplanarH
        have hE : ∀ z : H.Dart, (H.walkupE z).Jordan := by
          intro z
          exact ih (Fintype.card (H.walkupE z).Dart)
            (by
              have hlt := H.walkupE_dart_card_lt z
              simpa [hcard] using hlt)
            (H.walkupE z) rfl
            (walkupE_eulerPlanar_of_eulerPlanar H z hplanarH)
        have hN : ∀ z : H.Dart, (H.walkupN z).Jordan := by
          intro z
          exact ih (Fintype.card (H.walkupN z).Dart)
            (by
              have hlt : Fintype.card (H.walkupN z).Dart <
                  Fintype.card H.Dart := by
                change Fintype.card (H.permNode.walkupE z).Dart <
                  Fintype.card H.Dart
                exact H.permNode.walkupE_dart_card_lt z
              simpa [hcard] using hlt)
            (H.walkupN z) rfl
            (walkupN_eulerPlanar_of_eulerPlanar H z hplanarH)
        have hF : ∀ z : H.Dart, (H.walkupF z).Jordan := by
          intro z
          exact ih (Fintype.card (H.walkupF z).Dart)
            (by
              have hlt : Fintype.card (H.walkupF z).Dart <
                  Fintype.card H.Dart := by
                change Fintype.card (H.permFace.walkupE z).Dart <
                  Fintype.card H.Dart
                exact H.permFace.walkupE_dart_card_lt z
              simpa [hcard] using hlt)
            (H.walkupF z) rfl
            (walkupF_eulerPlanar_of_eulerPlanar H z hplanarH)
        exact H.jordan_of_walkup_jordan_and_eulerPlanar hE hN hF hplanarH
  exact hP (Fintype.card G.Dart) G rfl hplanar

end Unavoidability

end FourColor

end Schematic.Math.GraphTheory
