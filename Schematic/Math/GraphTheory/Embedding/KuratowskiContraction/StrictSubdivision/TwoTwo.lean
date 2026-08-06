import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.StrictSubdivision.BranchRoot

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

theorem containsStrictSubdivision_K33_of_collapseEdge_K5_two_two
    {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K5Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c p q r s : Fin 5}
    {hcp : K5Graph.Adj c p}
    {hcq : K5Graph.Adj c q}
    {hcr : K5Graph.Adj c r}
    {hcs : K5Graph.Adj c s}
    {hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)}
    (Tp : CollapseEdgeBranchIncidentTail hab M hcp hc)
    (Tq : CollapseEdgeBranchIncidentTail hab M hcq hc)
    (Tr : CollapseEdgeBranchIncidentTail hab M hcr hc)
    (Ts : CollapseEdgeBranchIncidentTail hab M hcs hc)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hpa : G.Adj a Tp.v) (hqa : G.Adj a Tq.v)
    (hrb : G.Adj b Tr.v) (hsb : G.Adj b Ts.v) :
    ContainsStrictSubdivision K33Graph G := by
  classical
  let bp :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex p) Tp.hy
  let bq :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex q) Tq.hy
  let brv :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex r) Tr.hy
  let bsv :=
    GraphContraction.collapseEdgeUncollapse G hab
      (M.branchVertex s) Ts.hy
  let abPath : G.Walk a b := hab.toWalk
  let apPath : G.Walk a bp :=
    Walk.branchAttachmentPath hab (Or.inl hpa) Tp.q
  let aqPath : G.Walk a bq :=
    Walk.branchAttachmentPath hab (Or.inl hqa) Tq.q
  let brPath : G.Walk b brv :=
    Walk.branchAttachmentPath hab.symm (Or.inl hrb) Tr.q
  let bsPath : G.Walk b bsv :=
    Walk.branchAttachmentPath hab.symm (Or.inl hsb) Ts.q
  have hrpAdj : K5Graph.Adj r p :=
    K5Graph.adj_of_ne (fun h => hpr h.symm)
  have hrqAdj : K5Graph.Adj r q :=
    K5Graph.adj_of_ne (fun h => hqr h.symm)
  have hspAdj : K5Graph.Adj s p :=
    K5Graph.adj_of_ne (fun h => hps h.symm)
  have hsqAdj : K5Graph.Adj s q :=
    K5Graph.adj_of_ne (fun h => hqs h.symm)
  let havoid_rp :=
    strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
      hab M hrpAdj hc hcr.ne.symm hcp.ne.symm
  let havoid_rq :=
    strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
      hab M hrqAdj hc hcr.ne.symm hcq.ne.symm
  let havoid_sp :=
    strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
      hab M hspAdj hc hcs.ne.symm hcp.ne.symm
  let havoid_sq :=
    strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
      hab M hsqAdj hc hcs.ne.symm hcq.ne.symm
  let rpPath : G.Walk brv bp :=
    GraphContraction.collapseEdgeWalkOutside G hab
      Tr.hy Tp.hy (M.edgePath hrpAdj) havoid_rp
  let rqPath : G.Walk brv bq :=
    GraphContraction.collapseEdgeWalkOutside G hab
      Tr.hy Tq.hy (M.edgePath hrqAdj) havoid_rq
  let spPath : G.Walk bsv bp :=
    GraphContraction.collapseEdgeWalkOutside G hab
      Ts.hy Tp.hy (M.edgePath hspAdj) havoid_sp
  let sqPath : G.Walk bsv bq :=
    GraphContraction.collapseEdgeWalkOutside G hab
      Ts.hy Tq.hy (M.edgePath hsqAdj) havoid_sq
  have hbranch :
      Function.Injective
        (k5TieK33Branch a b bp bq brv bsv) := by
    simpa [bp, bq, brv, bsv] using
      k5TieK33Branch_injective_of_collapseEdge_K5_two_two
        hab M Tp Tq Tr Ts hpq hpr hps hqr hqs hrs
  have hcases_ab :
      forall w : K33Vertex,
        k5TieK33Branch a b bp bq brv bsv w = a ∨
        k5TieK33Branch a b bp bq brv bsv w = b ∨
          Exists fun x : Fin 5 =>
            x ≠ c ∧
              Exists fun hx :
                M.branchVertex x ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                k5TieK33Branch a b bp bq brv bsv w =
                  GraphContraction.collapseEdgeUncollapse G hab
                    (M.branchVertex x) hx := by
    simpa [bp, bq, brv, bsv] using
      k5TieK33Branch_cases_of_collapseEdge_K5_two_two_ab
        hab M Tp Tq Tr Ts
  have hcases_ba :
      forall w : K33Vertex,
        k5TieK33Branch a b bp bq brv bsv w = b ∨
        k5TieK33Branch a b bp bq brv bsv w = a ∨
          Exists fun x : Fin 5 =>
            x ≠ c ∧
              Exists fun hx :
                M.branchVertex x ≠
                  (none : (GraphContraction.collapseEdge G hab).Target) =>
                k5TieK33Branch a b bp bq brv bsv w =
                  GraphContraction.collapseEdgeUncollapse G hab
                    (M.branchVertex x) hx := by
    simpa [bp, bq, brv, bsv] using
      k5TieK33Branch_cases_of_collapseEdge_K5_two_two_ba
        hab M Tp Tq Tr Ts
  have hcases_clean :
      forall w : K33Vertex,
        k5TieK33Branch a b bp bq brv bsv w = a ∨
        k5TieK33Branch a b bp bq brv bsv w = b ∨
          Exists fun x : Fin 5 =>
            Exists fun hx :
              M.branchVertex x ≠
                (none : (GraphContraction.collapseEdge G hab).Target) =>
              k5TieK33Branch a b bp bq brv bsv w =
                GraphContraction.collapseEdgeUncollapse G hab
                  (M.branchVertex x) hx := by
    intro w
    rcases hcases_ab w with ha | hb | h
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · rcases h with ⟨x, _hxc, hx, hbranch_eq⟩
      exact Or.inr (Or.inr ⟨x, hx, hbranch_eq⟩)
  have habPath_isPath : abPath.IsPath := by
    simpa [abPath] using SimpleGraph.Walk.IsPath.of_adj hab
  have hapPath_isPath : apPath.IsPath := by
    have ha_not : a ∉ Tp.q.support := by
      intro hmem
      exact Tp.q_outside a hmem (by simp)
    have hb_not : b ∉ Tp.q.support := by
      intro hmem
      exact Tp.q_outside b hmem (by simp)
    simpa [apPath] using
      Walk.branchAttachmentPath_isPath hab (Or.inl hpa)
        Tp.q_isPath ha_not hb_not
  have haqPath_isPath : aqPath.IsPath := by
    have ha_not : a ∉ Tq.q.support := by
      intro hmem
      exact Tq.q_outside a hmem (by simp)
    have hb_not : b ∉ Tq.q.support := by
      intro hmem
      exact Tq.q_outside b hmem (by simp)
    simpa [aqPath] using
      Walk.branchAttachmentPath_isPath hab (Or.inl hqa)
        Tq.q_isPath ha_not hb_not
  have hbrPath_isPath : brPath.IsPath := by
    have hb_not : b ∉ Tr.q.support := by
      intro hmem
      exact Tr.q_outside b hmem (by simp)
    have ha_not : a ∉ Tr.q.support := by
      intro hmem
      exact Tr.q_outside a hmem (by simp)
    simpa [brPath] using
      Walk.branchAttachmentPath_isPath hab.symm (Or.inl hrb)
        Tr.q_isPath hb_not ha_not
  have hbsPath_isPath : bsPath.IsPath := by
    have hb_not : b ∉ Ts.q.support := by
      intro hmem
      exact Ts.q_outside b hmem (by simp)
    have ha_not : a ∉ Ts.q.support := by
      intro hmem
      exact Ts.q_outside a hmem (by simp)
    simpa [bsPath] using
      Walk.branchAttachmentPath_isPath hab.symm (Or.inl hsb)
        Ts.q_isPath hb_not ha_not
  have hrpPath_isPath : rpPath.IsPath := by
    simpa [rpPath] using
      GraphContraction.collapseEdgeWalkOutside_isPath G hab
        Tr.hy Tp.hy (M.edgePath hrpAdj) havoid_rp
        (M.edgePath_isPath hrpAdj)
  have hrqPath_isPath : rqPath.IsPath := by
    simpa [rqPath] using
      GraphContraction.collapseEdgeWalkOutside_isPath G hab
        Tr.hy Tq.hy (M.edgePath hrqAdj) havoid_rq
        (M.edgePath_isPath hrqAdj)
  have hspPath_isPath : spPath.IsPath := by
    simpa [spPath] using
      GraphContraction.collapseEdgeWalkOutside_isPath G hab
        Ts.hy Tp.hy (M.edgePath hspAdj) havoid_sp
        (M.edgePath_isPath hspAdj)
  have hsqPath_isPath : sqPath.IsPath := by
    simpa [sqPath] using
      GraphContraction.collapseEdgeWalkOutside_isPath G hab
        Ts.hy Tq.hy (M.edgePath hsqAdj) havoid_sq
        (M.edgePath_isPath hsqAdj)
  have habPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices abPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact False.elim (Walk.not_mem_internalVertices_toWalk hab (by
      simpa [abPath] using hz))
  have hapPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices apPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_listed_branches
        hab (by simp) (by simp) hab M hcp hc hpa
        Tp.q_outside Tp.q_reflect
        (k5TieK33Branch a b bp bq brv bsv) hcases_ab
        (by simpa [apPath] using hz) w
  have haqPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices aqPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_listed_branches
        hab (by simp) (by simp) hab M hcq hc hqa
        Tq.q_outside Tq.q_reflect
        (k5TieK33Branch a b bp bq brv bsv) hcases_ab
        (by simpa [aqPath] using hz) w
  have hbrPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices brPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_listed_branches
        hab (by simp) (by simp) hab.symm M hcr hc hrb
        Tr.q_outside Tr.q_reflect
        (k5TieK33Branch a b bp bq brv bsv) hcases_ba
        (by simpa [brPath] using hz) w
  have hbsPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices bsPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_no_listed_branches
        hab (by simp) (by simp) hab.symm M hcs hc hsb
        Ts.q_outside Ts.q_reflect
        (k5TieK33Branch a b bp bq brv bsv) hcases_ba
        (by simpa [bsPath] using hz) w
  have hrpPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices rpPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_clean_lift_no_listed_branches
        hab M hrpAdj Tr.hy Tp.hy havoid_rp
        (k5TieK33Branch a b bp bq brv bsv) hcases_clean
        (by simpa [rpPath] using hz) w
  have hrqPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices rqPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_clean_lift_no_listed_branches
        hab M hrqAdj Tr.hy Tq.hy havoid_rq
        (k5TieK33Branch a b bp bq brv bsv) hcases_clean
        (by simpa [rqPath] using hz) w
  have hspPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices spPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_clean_lift_no_listed_branches
        hab M hspAdj Ts.hy Tp.hy havoid_sp
        (k5TieK33Branch a b bp bq brv bsv) hcases_clean
        (by simpa [spPath] using hz) w
  have hsqPath_no :
      forall {z : V}, z ∈ Walk.InternalVertices sqPath ->
        forall w : K33Vertex, z ≠ k5TieK33Branch a b bp bq brv bsv w := by
    intro z hz w
    exact
      strictSubdivisionModel_collapseEdge_clean_lift_no_listed_branches
        hab M hsqAdj Ts.hy Tq.hy havoid_sq
        (k5TieK33Branch a b bp bq brv bsv) hcases_clean
        (by simpa [sqPath] using hz) w
  have htail_pq :
      Disjoint {z : V | z ∈ Tp.q.support} {z : V | z ∈ Tq.q.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcp hcq hpq hc Tp.q_reflect Tq.q_reflect
  have htail_pr :
      Disjoint {z : V | z ∈ Tp.q.support} {z : V | z ∈ Tr.q.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcp hcr hpr hc Tp.q_reflect Tr.q_reflect
  have htail_ps :
      Disjoint {z : V | z ∈ Tp.q.support} {z : V | z ∈ Ts.q.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcp hcs hps hc Tp.q_reflect Ts.q_reflect
  have htail_qr :
      Disjoint {z : V | z ∈ Tq.q.support} {z : V | z ∈ Tr.q.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcq hcr hqr hc Tq.q_reflect Tr.q_reflect
  have htail_qs :
      Disjoint {z : V | z ∈ Tq.q.support} {z : V | z ∈ Ts.q.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcq hcs hqs hc Tq.q_reflect Ts.q_reflect
  have htail_rs :
      Disjoint {z : V | z ∈ Tr.q.support} {z : V | z ∈ Ts.q.support} :=
    strictSubdivisionModel_collapseEdge_branch_tail_lifts_support_disjoint
      hab M hcr hcs hrs hc Tr.q_reflect Ts.q_reflect
  have hab_disjoint_left (S : Set V) :
      Disjoint (Walk.InternalVertices abPath) S := by
    rw [Set.disjoint_left]
    intro z hz _hzS
    exact Walk.not_mem_internalVertices_toWalk hab (by
      simpa [abPath] using hz)
  have hab_disjoint_right (S : Set V) :
      Disjoint S (Walk.InternalVertices abPath) :=
    (hab_disjoint_left S).symm
  have h_ab_ap :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices apPath) :=
    hab_disjoint_left _
  have h_ap_ab :
      Disjoint (Walk.InternalVertices apPath)
        (Walk.InternalVertices abPath) :=
    h_ab_ap.symm
  have h_ab_aq :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices aqPath) :=
    hab_disjoint_left _
  have h_aq_ab :
      Disjoint (Walk.InternalVertices aqPath)
        (Walk.InternalVertices abPath) :=
    h_ab_aq.symm
  have h_ab_br :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices brPath) :=
    hab_disjoint_left _
  have h_br_ab :
      Disjoint (Walk.InternalVertices brPath)
        (Walk.InternalVertices abPath) :=
    h_ab_br.symm
  have h_ab_bs :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices bsPath) :=
    hab_disjoint_left _
  have h_bs_ab :
      Disjoint (Walk.InternalVertices bsPath)
        (Walk.InternalVertices abPath) :=
    h_ab_bs.symm
  have h_ab_rp :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices rpPath) :=
    hab_disjoint_left _
  have h_rp_ab :
      Disjoint (Walk.InternalVertices rpPath)
        (Walk.InternalVertices abPath) :=
    h_ab_rp.symm
  have h_ab_rq :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices rqPath) :=
    hab_disjoint_left _
  have h_rq_ab :
      Disjoint (Walk.InternalVertices rqPath)
        (Walk.InternalVertices abPath) :=
    h_ab_rq.symm
  have h_ab_sp :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices spPath) :=
    hab_disjoint_left _
  have h_sp_ab :
      Disjoint (Walk.InternalVertices spPath)
        (Walk.InternalVertices abPath) :=
    h_ab_sp.symm
  have h_ab_sq :
      Disjoint (Walk.InternalVertices abPath)
        (Walk.InternalVertices sqPath) :=
    hab_disjoint_left _
  have h_sq_ab :
      Disjoint (Walk.InternalVertices sqPath)
        (Walk.InternalVertices abPath) :=
    h_ab_sq.symm
  have h_ap_aq :
      Disjoint (Walk.InternalVertices apPath)
        (Walk.InternalVertices aqPath) := by
    simpa [apPath, aqPath] using
      Walk.branchAttachmentPath_direct_direct_internally_disjoint
        hab hpa hab hqa htail_pq
  have h_ap_br :
      Disjoint (Walk.InternalVertices apPath)
        (Walk.InternalVertices brPath) := by
    simpa [apPath, brPath] using
      Walk.branchAttachmentPath_direct_direct_internally_disjoint
        hab hpa hab.symm hrb htail_pr
  have h_ap_bs :
      Disjoint (Walk.InternalVertices apPath)
        (Walk.InternalVertices bsPath) := by
    simpa [apPath, bsPath] using
      Walk.branchAttachmentPath_direct_direct_internally_disjoint
        hab hpa hab.symm hsb htail_ps
  have h_aq_br :
      Disjoint (Walk.InternalVertices aqPath)
        (Walk.InternalVertices brPath) := by
    simpa [aqPath, brPath] using
      Walk.branchAttachmentPath_direct_direct_internally_disjoint
        hab hqa hab.symm hrb htail_qr
  have h_aq_bs :
      Disjoint (Walk.InternalVertices aqPath)
        (Walk.InternalVertices bsPath) := by
    simpa [aqPath, bsPath] using
      Walk.branchAttachmentPath_direct_direct_internally_disjoint
        hab hqa hab.symm hsb htail_qs
  have h_br_bs :
      Disjoint (Walk.InternalVertices brPath)
        (Walk.InternalVertices bsPath) := by
    simpa [brPath, bsPath] using
      Walk.branchAttachmentPath_direct_direct_internally_disjoint
        hab.symm hrb hab.symm hsb htail_rs
  have h_ap_rp :
      Disjoint (Walk.InternalVertices apPath) (Walk.InternalVertices rpPath) := by
    simpa [apPath, rpPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcp hrpAdj hc hcr.ne.symm hcp.ne.symm
        havoid_rp hpa Tp.q_reflect
  have h_ap_rq :
      Disjoint (Walk.InternalVertices apPath) (Walk.InternalVertices rqPath) := by
    simpa [apPath, rqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcp hrqAdj hc hcr.ne.symm hcq.ne.symm
        havoid_rq hpa Tp.q_reflect
  have h_ap_sp :
      Disjoint (Walk.InternalVertices apPath) (Walk.InternalVertices spPath) := by
    simpa [apPath, spPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcp hspAdj hc hcs.ne.symm hcp.ne.symm
        havoid_sp hpa Tp.q_reflect
  have h_ap_sq :
      Disjoint (Walk.InternalVertices apPath) (Walk.InternalVertices sqPath) := by
    simpa [apPath, sqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcp hsqAdj hc hcs.ne.symm hcq.ne.symm
        havoid_sq hpa Tp.q_reflect
  have h_aq_rp :
      Disjoint (Walk.InternalVertices aqPath) (Walk.InternalVertices rpPath) := by
    simpa [aqPath, rpPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcq hrpAdj hc hcr.ne.symm hcp.ne.symm
        havoid_rp hqa Tq.q_reflect
  have h_aq_rq :
      Disjoint (Walk.InternalVertices aqPath) (Walk.InternalVertices rqPath) := by
    simpa [aqPath, rqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcq hrqAdj hc hcr.ne.symm hcq.ne.symm
        havoid_rq hqa Tq.q_reflect
  have h_aq_sp :
      Disjoint (Walk.InternalVertices aqPath) (Walk.InternalVertices spPath) := by
    simpa [aqPath, spPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcq hspAdj hc hcs.ne.symm hcp.ne.symm
        havoid_sp hqa Tq.q_reflect
  have h_aq_sq :
      Disjoint (Walk.InternalVertices aqPath) (Walk.InternalVertices sqPath) := by
    simpa [aqPath, sqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab M hcq hsqAdj hc hcs.ne.symm hcq.ne.symm
        havoid_sq hqa Tq.q_reflect
  have h_br_rp :
      Disjoint (Walk.InternalVertices brPath) (Walk.InternalVertices rpPath) := by
    simpa [brPath, rpPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcr hrpAdj hc hcr.ne.symm hcp.ne.symm
        havoid_rp hrb Tr.q_reflect
  have h_br_rq :
      Disjoint (Walk.InternalVertices brPath) (Walk.InternalVertices rqPath) := by
    simpa [brPath, rqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcr hrqAdj hc hcr.ne.symm hcq.ne.symm
        havoid_rq hrb Tr.q_reflect
  have h_br_sp :
      Disjoint (Walk.InternalVertices brPath) (Walk.InternalVertices spPath) := by
    simpa [brPath, spPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcr hspAdj hc hcs.ne.symm hcp.ne.symm
        havoid_sp hrb Tr.q_reflect
  have h_br_sq :
      Disjoint (Walk.InternalVertices brPath) (Walk.InternalVertices sqPath) := by
    simpa [brPath, sqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcr hsqAdj hc hcs.ne.symm hcq.ne.symm
        havoid_sq hrb Tr.q_reflect
  have h_bs_rp :
      Disjoint (Walk.InternalVertices bsPath) (Walk.InternalVertices rpPath) := by
    simpa [bsPath, rpPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcs hrpAdj hc hcr.ne.symm hcp.ne.symm
        havoid_rp hsb Ts.q_reflect
  have h_bs_rq :
      Disjoint (Walk.InternalVertices bsPath) (Walk.InternalVertices rqPath) := by
    simpa [bsPath, rqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcs hrqAdj hc hcr.ne.symm hcq.ne.symm
        havoid_rq hsb Ts.q_reflect
  have h_bs_sp :
      Disjoint (Walk.InternalVertices bsPath) (Walk.InternalVertices spPath) := by
    simpa [bsPath, spPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcs hspAdj hc hcs.ne.symm hcp.ne.symm
        havoid_sp hsb Ts.q_reflect
  have h_bs_sq :
      Disjoint (Walk.InternalVertices bsPath) (Walk.InternalVertices sqPath) := by
    simpa [bsPath, sqPath] using
      strictSubdivisionModel_collapseEdge_branch_attachment_direct_disjoint_clean_lift
        hab (by simp) hab.symm M hcs hsqAdj hc hcs.ne.symm hcq.ne.symm
        havoid_sq hsb Ts.q_reflect
  have hne_rp_rq :
      Not ((r = r ∧ p = q) ∨ (r = q ∧ p = r)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hpq hsame.2
    · exact hqr hsame.1.symm
  have hne_rp_sp :
      Not ((r = s ∧ p = p) ∨ (r = p ∧ p = s)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hrs hsame.1
    · exact hpr hsame.1.symm
  have hne_rp_sq :
      Not ((r = s ∧ p = q) ∨ (r = q ∧ p = s)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hrs hsame.1
    · exact hqr hsame.1.symm
  have hne_rq_sp :
      Not ((r = s ∧ q = p) ∨ (r = p ∧ q = s)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hrs hsame.1
    · exact hpr hsame.1.symm
  have hne_rq_sq :
      Not ((r = s ∧ q = q) ∨ (r = q ∧ q = s)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hrs hsame.1
    · exact hqr hsame.1.symm
  have hne_sp_sq :
      Not ((s = s ∧ p = q) ∨ (s = q ∧ p = s)) := by
    intro hsame
    rcases hsame with hsame | hsame
    · exact hpq hsame.2
    · exact hqs hsame.1.symm
  have h_rp_rq :
      Disjoint (Walk.InternalVertices rpPath) (Walk.InternalVertices rqPath) := by
    simpa [rpPath, rqPath] using
      strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
        hab M hrpAdj hrqAdj hne_rp_rq Tr.hy Tp.hy Tr.hy Tq.hy
        havoid_rp havoid_rq
  have h_rp_sp :
      Disjoint (Walk.InternalVertices rpPath) (Walk.InternalVertices spPath) := by
    simpa [rpPath, spPath] using
      strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
        hab M hrpAdj hspAdj hne_rp_sp Tr.hy Tp.hy Ts.hy Tp.hy
        havoid_rp havoid_sp
  have h_rp_sq :
      Disjoint (Walk.InternalVertices rpPath) (Walk.InternalVertices sqPath) := by
    simpa [rpPath, sqPath] using
      strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
        hab M hrpAdj hsqAdj hne_rp_sq Tr.hy Tp.hy Ts.hy Tq.hy
        havoid_rp havoid_sq
  have h_rq_sp :
      Disjoint (Walk.InternalVertices rqPath) (Walk.InternalVertices spPath) := by
    simpa [rqPath, spPath] using
      strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
        hab M hrqAdj hspAdj hne_rq_sp Tr.hy Tq.hy Ts.hy Tp.hy
        havoid_rq havoid_sp
  have h_rq_sq :
      Disjoint (Walk.InternalVertices rqPath) (Walk.InternalVertices sqPath) := by
    simpa [rqPath, sqPath] using
      strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
        hab M hrqAdj hsqAdj hne_rq_sq Tr.hy Tq.hy Ts.hy Tq.hy
        havoid_rq havoid_sq
  have h_sp_sq :
      Disjoint (Walk.InternalVertices spPath) (Walk.InternalVertices sqPath) := by
    simpa [spPath, sqPath] using
      strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
        hab M hspAdj hsqAdj hne_sp_sq Ts.hy Tp.hy Ts.hy Tq.hy
        havoid_sp havoid_sq
  have hpair :
      forall i j : Fin 9, i ≠ j ->
        Disjoint
          (k5TieK33PathSet abPath apPath aqPath brPath bsPath
            rpPath rqPath spPath sqPath i)
          (k5TieK33PathSet abPath apPath aqPath brPath bsPath
            rpPath rqPath spPath sqPath j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [k5TieK33PathSet] at hij ⊢
    · exact h_ab_ap
    · exact h_ab_aq
    · exact h_ab_br
    · exact h_ab_bs
    · exact h_ab_rp
    · exact h_ab_rq
    · exact h_ab_sp
    · exact h_ab_sq
    · exact h_ap_ab
    · exact h_ap_aq
    · exact h_ap_br
    · exact h_ap_bs
    · exact h_ap_rp
    · exact h_ap_rq
    · exact h_ap_sp
    · exact h_ap_sq
    · exact h_aq_ab
    · exact h_ap_aq.symm
    · exact h_aq_br
    · exact h_aq_bs
    · exact h_aq_rp
    · exact h_aq_rq
    · exact h_aq_sp
    · exact h_aq_sq
    · exact h_br_ab
    · exact h_ap_br.symm
    · exact h_aq_br.symm
    · exact h_br_bs
    · exact h_br_rp
    · exact h_br_rq
    · exact h_br_sp
    · exact h_br_sq
    · exact h_bs_ab
    · exact h_ap_bs.symm
    · exact h_aq_bs.symm
    · exact h_br_bs.symm
    · exact h_bs_rp
    · exact h_bs_rq
    · exact h_bs_sp
    · exact h_bs_sq
    · exact h_rp_ab
    · exact h_ap_rp.symm
    · exact h_aq_rp.symm
    · exact h_br_rp.symm
    · exact h_bs_rp.symm
    · exact h_rp_rq
    · exact h_rp_sp
    · exact h_rp_sq
    · exact h_rq_ab
    · exact h_ap_rq.symm
    · exact h_aq_rq.symm
    · exact h_br_rq.symm
    · exact h_bs_rq.symm
    · exact h_rp_rq.symm
    · exact h_rq_sp
    · exact h_rq_sq
    · exact h_sp_ab
    · exact h_ap_sp.symm
    · exact h_aq_sp.symm
    · exact h_br_sp.symm
    · exact h_bs_sp.symm
    · exact h_rp_sp.symm
    · exact h_rq_sp.symm
    · exact h_sp_sq
    · exact h_sq_ab
    · exact h_ap_sq.symm
    · exact h_aq_sq.symm
    · exact h_br_sq.symm
    · exact h_bs_sq.symm
    · exact h_rp_sq.symm
    · exact h_rq_sq.symm
    · exact h_sp_sq.symm
  exact
    containsStrictSubdivision_K33_of_k5TieK33_paths
      hbranch
      habPath_isPath hapPath_isPath haqPath_isPath hbrPath_isPath
      hbsPath_isPath hrpPath_isPath hrqPath_isPath hspPath_isPath
      hsqPath_isPath
      habPath_no hapPath_no haqPath_no hbrPath_no hbsPath_no
      hrpPath_no hrqPath_no hspPath_no hsqPath_no hpair

theorem strictSubdivisionModel_collapseEdge_branch_root_edgePath_no_internal_branch_vertices
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (D : CollapseEdgeBranchRootData hab M hc root other)
    {s t : W}
    (hst : K.Adj s t)
    {z : V}
    (hz : z ∈ Walk.InternalVertices
      (strictSubdivisionModel_collapseEdge_branch_root_edgePath
        hab M hc D hst))
    (w : W) :
    z ≠
      strictSubdivisionModel_collapseEdge_branch_root_branchVertex
        hab M hc (root := root) w := by
  classical
  unfold strictSubdivisionModel_collapseEdge_branch_root_edgePath at hz
  split_ifs at hz with hsc htc
  · subst s
    have htc : t ≠ c := fun htc => hst.ne htc.symm
    have hzarm :
        z ∈ Walk.InternalVertices
          (Walk.branchAttachmentPath D.hroot_other
            (D.hside hst) (D.q hst)) := by
      simpa [Walk.internalVertices_copy] using hz
    by_cases hwc : w = c
    · subst w
      intro hzc
      exact hzarm.2.1
        (by
          simpa [strictSubdivisionModel_collapseEdge_branch_root_branchVertex]
            using hzc)
    · have hz_ne :=
        strictSubdivisionModel_collapseEdge_branch_attachment_root_no_uncollapsed_branch
          hab D.hroot_pair D.hother_pair D.hroot_other M hst hc hwc
          (D.hside hst) (D.q_reflect hst) hzarm
      intro hzw
      exact hz_ne
        (hzw.trans
          (strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
            (root := root) hab M hc hwc))
  · subst t
    have hcs : K.Adj c s := hst.symm
    have hzrev :
        z ∈ Walk.InternalVertices
          (Walk.branchAttachmentPath D.hroot_other
            (D.hside hcs) (D.q hcs)).reverse := by
      simpa [Walk.internalVertices_copy] using hz
    have hzarm :
        z ∈ Walk.InternalVertices
          (Walk.branchAttachmentPath D.hroot_other
            (D.hside hcs) (D.q hcs)) := by
      simpa [Walk.internalVertices_reverse] using hzrev
    by_cases hwc : w = c
    · subst w
      intro hzc
      exact hzarm.2.1
        (by
          simpa [strictSubdivisionModel_collapseEdge_branch_root_branchVertex]
            using hzc)
    · have hz_ne :=
        strictSubdivisionModel_collapseEdge_branch_attachment_root_no_uncollapsed_branch
          hab D.hroot_pair D.hother_pair D.hroot_other M hcs hc hwc
          (D.hside hcs) (D.q_reflect hcs) hzarm
      intro hzw
      exact hz_ne
        (hzw.trans
          (strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
            (root := root) hab M hc hwc))
  · have hs_ne :
        M.branchVertex s ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      intro hs_none
      exact hsc (M.branchVertex_injective (hs_none.trans hc.symm))
    have ht_ne :
        M.branchVertex t ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      intro ht_none
      exact htc (M.branchVertex_injective (ht_none.trans hc.symm))
    let havoid :=
      strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
        hab M hst hc hsc htc
    have hzclean :
        z ∈ Walk.InternalVertices
          (GraphContraction.collapseEdgeWalkOutside G hab
            hs_ne ht_ne (M.edgePath hst) havoid) := by
      simpa [Walk.internalVertices_copy] using hz
    by_cases hwc : w = c
    · subst w
      have hzout :
          z ∉ ({a, b} : Set V) :=
        GraphContraction.collapseEdgeWalkOutside_support_outside G hab
          hs_ne ht_ne (M.edgePath hst) havoid hzclean.1
      intro hzc
      exact hzout
        (by
          have hzr : z = root := by
            simpa
              [strictSubdivisionModel_collapseEdge_branch_root_branchVertex]
              using hzc
          simpa [hzr] using D.hroot_pair)
    · have hw_ne :
          M.branchVertex w ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hw_none
        exact hwc (M.branchVertex_injective (hw_none.trans hc.symm))
      have hz_ne :=
        strictSubdivisionModel_collapseEdge_clean_lift_no_internal_branch_vertex_local
          hab M hst hs_ne ht_ne hw_ne havoid hzclean
      intro hzw
      exact hz_ne
        (hzw.trans
          (strictSubdivisionModel_collapseEdge_branch_root_branchVertex_of_ne
            (root := root) hab M hc hwc))

theorem strictSubdivisionModel_collapseEdge_branch_root_edgePaths_internally_disjoint
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (D : CollapseEdgeBranchRootData hab M hc root other)
    {s t s' t' : W}
    (hst : K.Adj s t)
    (hs't' : K.Adj s' t')
    (hne : Not ((s = s' ∧ t = t') ∨ (s = t' ∧ t = s'))) :
    Disjoint
      (Walk.InternalVertices
        (strictSubdivisionModel_collapseEdge_branch_root_edgePath
          hab M hc D hst))
      (Walk.InternalVertices
        (strictSubdivisionModel_collapseEdge_branch_root_edgePath
          hab M hc D hs't')) := by
  classical
  rw [Set.disjoint_left]
  intro z hz hz'
  unfold strictSubdivisionModel_collapseEdge_branch_root_edgePath at hz hz'
  split_ifs at hz with hsc htc
  · subst s
    have hzarm :
        z ∈ Walk.InternalVertices
          (Walk.branchAttachmentPath D.hroot_other
            (D.hside hst) (D.q hst)) := by
      simpa [Walk.internalVertices_copy] using hz
    split_ifs at hz' with hs2c ht2c
    · subst s'
      have hzarm' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hs't') (D.q hs't')) := by
        simpa [Walk.internalVertices_copy] using hz'
      have htt' : t ≠ t' := by
        intro htt'
        exact hne (Or.inl ⟨rfl, htt'⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_pair_direct_arms_internally_disjoint
          D.hroot_pair D.hother_pair D.hroot_other
          (D.hside hst) (D.hside hs't')
          (D.pair_direct hst hs't' htt')
          (D.q_outside hst) (D.q_outside hs't')
          (D.q_disjoint hst hs't' htt'))
        hzarm hzarm'
    · subst t'
      have hcs' : K.Adj c s' := hs't'.symm
      have hzrev' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hcs') (D.q hcs')).reverse := by
        simpa [Walk.internalVertices_copy] using hz'
      have hzarm' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hcs') (D.q hcs')) := by
        simpa [Walk.internalVertices_reverse] using hzrev'
      have hts' : t ≠ s' := by
        intro hts'
        exact hne (Or.inr ⟨rfl, hts'⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_pair_direct_arms_internally_disjoint
          D.hroot_pair D.hother_pair D.hroot_other
          (D.hside hst) (D.hside hcs')
          (D.pair_direct hst hcs' hts')
          (D.q_outside hst) (D.q_outside hcs')
          (D.q_disjoint hst hcs' hts'))
        hzarm hzarm'
    · have hs'_ne :
          M.branchVertex s' ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hs'_none
        exact hs2c (M.branchVertex_injective (hs'_none.trans hc.symm))
      have ht'_ne :
          M.branchVertex t' ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro ht'_none
        exact ht2c (M.branchVertex_injective (ht'_none.trans hc.symm))
      let havoid' :=
        strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
          hab M hs't' hc hs2c ht2c
      have hzclean' :
          z ∈ Walk.InternalVertices
            (GraphContraction.collapseEdgeWalkOutside G hab
              hs'_ne ht'_ne (M.edgePath hs't') havoid') := by
        simpa [Walk.internalVertices_copy] using hz'
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_root_disjoint_clean_lift
          hab D.hroot_pair D.hother_pair D.hroot_other M hst hs't' hc
          hs2c ht2c havoid' (D.hside hst) (D.q_reflect hst))
        hzarm hzclean'
  · subst t
    have hcs : K.Adj c s := hst.symm
    have hzrev :
        z ∈ Walk.InternalVertices
          (Walk.branchAttachmentPath D.hroot_other
            (D.hside hcs) (D.q hcs)).reverse := by
      simpa [Walk.internalVertices_copy] using hz
    have hzarm :
        z ∈ Walk.InternalVertices
          (Walk.branchAttachmentPath D.hroot_other
            (D.hside hcs) (D.q hcs)) := by
      simpa [Walk.internalVertices_reverse] using hzrev
    split_ifs at hz' with hs2c ht2c
    · subst s'
      have hzarm' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hs't') (D.q hs't')) := by
        simpa [Walk.internalVertices_copy] using hz'
      have hst' : s ≠ t' := by
        intro hst'
        exact hne (Or.inr ⟨hst', rfl⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_pair_direct_arms_internally_disjoint
          D.hroot_pair D.hother_pair D.hroot_other
          (D.hside hcs) (D.hside hs't')
          (D.pair_direct hcs hs't' hst')
          (D.q_outside hcs) (D.q_outside hs't')
          (D.q_disjoint hcs hs't' hst'))
        hzarm hzarm'
    · subst t'
      have hcs' : K.Adj c s' := hs't'.symm
      have hzrev' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hcs') (D.q hcs')).reverse := by
        simpa [Walk.internalVertices_copy] using hz'
      have hzarm' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hcs') (D.q hcs')) := by
        simpa [Walk.internalVertices_reverse] using hzrev'
      have hss' : s ≠ s' := by
        intro hss'
        exact hne (Or.inl ⟨hss', rfl⟩)
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_pair_direct_arms_internally_disjoint
          D.hroot_pair D.hother_pair D.hroot_other
          (D.hside hcs) (D.hside hcs')
          (D.pair_direct hcs hcs' hss')
          (D.q_outside hcs) (D.q_outside hcs')
          (D.q_disjoint hcs hcs' hss'))
        hzarm hzarm'
    · have hs'_ne :
          M.branchVertex s' ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hs'_none
        exact hs2c (M.branchVertex_injective (hs'_none.trans hc.symm))
      have ht'_ne :
          M.branchVertex t' ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro ht'_none
        exact ht2c (M.branchVertex_injective (ht'_none.trans hc.symm))
      let havoid' :=
        strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
          hab M hs't' hc hs2c ht2c
      have hzclean' :
          z ∈ Walk.InternalVertices
            (GraphContraction.collapseEdgeWalkOutside G hab
              hs'_ne ht'_ne (M.edgePath hs't') havoid') := by
        simpa [Walk.internalVertices_copy] using hz'
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_root_disjoint_clean_lift
          hab D.hroot_pair D.hother_pair D.hroot_other M hcs hs't' hc
          hs2c ht2c havoid' (D.hside hcs) (D.q_reflect hcs))
        hzarm hzclean'
  · have hs_ne :
        M.branchVertex s ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      intro hs_none
      exact hsc (M.branchVertex_injective (hs_none.trans hc.symm))
    have ht_ne :
        M.branchVertex t ≠
          (none : (GraphContraction.collapseEdge G hab).Target) := by
      intro ht_none
      exact htc (M.branchVertex_injective (ht_none.trans hc.symm))
    let havoid :=
      strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
        hab M hst hc hsc htc
    have hzclean :
        z ∈ Walk.InternalVertices
          (GraphContraction.collapseEdgeWalkOutside G hab
            hs_ne ht_ne (M.edgePath hst) havoid) := by
      simpa [Walk.internalVertices_copy] using hz
    split_ifs at hz' with hs2c ht2c
    · subst s'
      have hzarm' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hs't') (D.q hs't')) := by
        simpa [Walk.internalVertices_copy] using hz'
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_root_disjoint_clean_lift
          hab D.hroot_pair D.hother_pair D.hroot_other M hs't' hst hc
          hsc htc havoid (D.hside hs't') (D.q_reflect hs't')).symm
        hzclean hzarm'
    · subst t'
      have hcs' : K.Adj c s' := hs't'.symm
      have hzrev' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hcs') (D.q hcs')).reverse := by
        simpa [Walk.internalVertices_copy] using hz'
      have hzarm' :
          z ∈ Walk.InternalVertices
            (Walk.branchAttachmentPath D.hroot_other
              (D.hside hcs') (D.q hcs')) := by
        simpa [Walk.internalVertices_reverse] using hzrev'
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_branch_attachment_root_disjoint_clean_lift
          hab D.hroot_pair D.hother_pair D.hroot_other M hcs' hst hc
          hsc htc havoid (D.hside hcs') (D.q_reflect hcs')).symm
        hzclean hzarm'
    · have hs'_ne :
          M.branchVertex s' ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro hs'_none
        exact hs2c (M.branchVertex_injective (hs'_none.trans hc.symm))
      have ht'_ne :
          M.branchVertex t' ≠
            (none : (GraphContraction.collapseEdge G hab).Target) := by
        intro ht'_none
        exact ht2c (M.branchVertex_injective (ht'_none.trans hc.symm))
      let havoid' :=
        strictSubdivisionModel_collapseEdge_branch_other_edgePath_avoids_collapsed
          hab M hs't' hc hs2c ht2c
      have hzclean' :
          z ∈ Walk.InternalVertices
            (GraphContraction.collapseEdgeWalkOutside G hab
              hs'_ne ht'_ne (M.edgePath hs't') havoid') := by
        simpa [Walk.internalVertices_copy] using hz'
      exact Set.disjoint_left.mp
        (strictSubdivisionModel_collapseEdge_clean_lifts_internally_disjoint_local
          hab M hst hs't' hne hs_ne ht_ne hs'_ne ht'_ne havoid havoid')
        hzclean hzclean'

theorem containsStrictSubdivision_of_collapseEdge_branch_root_data
    {W : Type*} {V : Type u} [DecidableEq W]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (D : CollapseEdgeBranchRootData hab M hc root other) :
    ContainsStrictSubdivision K G := by
  classical
  exact ⟨{
    toSubdivisionModel := {
      branchVertex :=
        strictSubdivisionModel_collapseEdge_branch_root_branchVertex
          hab M hc (root := root)
      branchVertex_injective :=
        strictSubdivisionModel_collapseEdge_branch_root_branchVertex_injective
          hab D.hroot_pair M hc
      edgePath := fun {s t} hst =>
        strictSubdivisionModel_collapseEdge_branch_root_edgePath
          hab M hc D hst
      edgePath_isPath := by
        intro s t hst
        exact
          strictSubdivisionModel_collapseEdge_branch_root_edgePath_isPath
            hab M hc D hst
      no_internal_branch_vertices :=
        forall {s t : W} (hst : K.Adj s t) {z : V},
          z ∈ Walk.InternalVertices
            (strictSubdivisionModel_collapseEdge_branch_root_edgePath
              hab M hc D hst) ->
          forall w : W,
            z ≠
              strictSubdivisionModel_collapseEdge_branch_root_branchVertex
                hab M hc (root := root) w
      internally_disjoint_edge_paths :=
        forall {s t s' t' : W}
          (hst : K.Adj s t) (hs't' : K.Adj s' t'),
            Not ((s = s' ∧ t = t') ∨ (s = t' ∧ t = s')) ->
              Disjoint
                (Walk.InternalVertices
                  (strictSubdivisionModel_collapseEdge_branch_root_edgePath
                    hab M hc D hst))
                (Walk.InternalVertices
                  (strictSubdivisionModel_collapseEdge_branch_root_edgePath
                    hab M hc D hs't')) }
    no_internal_branch_vertices' := by
      intro s t hst z hz w hzw
      exact
        strictSubdivisionModel_collapseEdge_branch_root_edgePath_no_internal_branch_vertices
          hab M hc D hst hz w hzw
    internally_disjoint_edge_paths' := by
      intro s t s' t' hst hs't' hne
      exact
        strictSubdivisionModel_collapseEdge_branch_root_edgePaths_internally_disjoint
          hab M hc D hst hs't' hne }⟩

theorem containsStrictSubdivision_of_collapseEdge_branch_root_pair_direct
    {W : Type*} {V : Type u} [DecidableEq W] [DecidableEq V]
    {K : SimpleGraph W} {G : SimpleGraph V}
    {a b root other : V}
    (hab : G.Adj a b)
    (M : StrictSubdivisionModel K
      (GraphContraction.collapseEdge G hab).graph)
    {c : W}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target))
    (hroot_pair : root ∈ ({a, b} : Set V))
    (hother_pair : other ∈ ({a, b} : Set V))
    (hroot_other : G.Adj root other)
    (hpair_direct :
      forall {y z : W} (hcy : K.Adj c y) (hcz : K.Adj c z),
        y ≠ z ->
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) ∨
          G.Adj root
            ((CollapseEdgeBranchIncidentTail.ofModel hab M hcz hc).v)) :
    ContainsStrictSubdivision K G :=
  containsStrictSubdivision_of_collapseEdge_branch_root_data hab M hc
    (CollapseEdgeBranchRootData.ofModel hab M hc hroot_pair hother_pair
      hroot_other hpair_direct)

theorem containsStrictSubdivision_K33_of_collapseEdge_collapsed_branch
    {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    {a b : V}
    (hab : G.Adj a b)
    (M :
      StrictSubdivisionModel K33Graph
        (GraphContraction.collapseEdge G hab).graph)
    {c : K33Vertex}
    (hc :
      M.branchVertex c =
        (none : (GraphContraction.collapseEdge G hab).Target)) :
    ContainsStrictSubdivision K33Graph G := by
  classical
  let side : K33Vertex -> Bool := fun y =>
    if hcy : K33Graph.Adj c y then
      if G.Adj a
          ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) then
        true
      else
        false
    else
      false
  rcases K33Graph.exists_bool_pair_majority c side with ⟨r, hr⟩
  cases r
  · refine
      containsStrictSubdivision_of_collapseEdge_branch_root_pair_direct
        hab M hc (root := b) (other := a) ?_ ?_ hab.symm ?_
    · simp
    · simp
    · intro y z hcy hcz hyz
      obtain hy_major | hz_major := hr (y := y) (z := z) hcy hcz hyz
      · left
        have hnot_a :
            ¬ G.Adj a
              ((CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).v) := by
          intro ha
          have hside_true : side y = true := by
            simp [side, hcy, ha]
          rw [hside_true] at hy_major
          contradiction
        exact
          (CollapseEdgeBranchIncidentTail.ofModel hab M hcy hc).hside.resolve_left
            hnot_a
      · right
        have hnot_a :
            ¬ G.Adj a
              ((CollapseEdgeBranchIncidentTail.ofModel hab M hcz hc).v) := by
          intro ha
          have hside_true : side z = true := by
            simp [side, hcz, ha]
          rw [hside_true] at hz_major
          contradiction
        exact
          (CollapseEdgeBranchIncidentTail.ofModel hab M hcz hc).hside.resolve_left
            hnot_a
  · refine
      containsStrictSubdivision_of_collapseEdge_branch_root_pair_direct
        hab M hc (root := a) (other := b) ?_ ?_ hab ?_
    · simp
    · simp
    · intro y z hcy hcz hyz
      obtain hy_major | hz_major := hr (y := y) (z := z) hcy hcz hyz
      · left
        by_contra hnot
        have hside_false : side y = false := by
          simp [side, hcy, hnot]
        simp [hside_false] at hy_major
      · right
        by_contra hnot
        have hside_false : side z = false := by
          simp [side, hcz, hnot]
        simp [hside_false] at hz_major
end FourColor

end Schematic.Math.GraphTheory
