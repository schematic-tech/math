import Schematic.Math.GraphTheory.Embedding.Walkup.CrossEdgeReachability

/-! Edge orbits and components in the non-cross branch. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

/-- Representative of an original dart in the non-self Walkup edge-orbit
quotient.  The deleted dart `z` is represented by `edge z`; all other darts
are represented by themselves. -/
def walkupENonSelfEdgeRepresentative
    {z : G.Dart} (hz : ¬ G.Link z z) (x : G.Dart) :
    (G.walkupE z).Dart :=
  G.walkupI
    (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
      (G.walkupE z).Dart) x

theorem walkupENonSelfEdgeRepresentative_deleted
    {z : G.Dart} (hz : ¬ G.Link z z) :
    G.walkupENonSelfEdgeRepresentative hz z =
      (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart) := by
  apply Subtype.ext
  simp [walkupENonSelfEdgeRepresentative]

theorem walkupENonSelfEdgeRepresentative_of_ne
    {z x : G.Dart} (hz : ¬ G.Link z z) (hx : x ≠ z) :
    G.walkupENonSelfEdgeRepresentative hz x =
      (⟨x, hx⟩ : (G.walkupE z).Dart) := by
  apply Subtype.ext
  simp [walkupENonSelfEdgeRepresentative, hx]

theorem walkupE_edgePermReachable_representatives_of_edge_step_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (x : G.Dart) :
    PermReachable (G.walkupE z).edge
      (G.walkupENonSelfEdgeRepresentative hz x)
      (G.walkupENonSelfEdgeRepresentative hz (G.edge x)) := by
  by_cases hxz : x = z
  · subst x
    rw [G.walkupENonSelfEdgeRepresentative_deleted]
    rw [G.walkupENonSelfEdgeRepresentative_of_ne hz
      (G.edge_ne_self_of_not_link_self hz)]
    exact PermReachable.refl (G.walkupE z).edge
      (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart)
  · by_cases hxnode : x = G.node z
    · have hedge_node_ne :
          G.edge (G.node z) ≠ z :=
        G.edge_node_ne_self_of_not_link_self hz
      subst x
      rw [G.walkupENonSelfEdgeRepresentative_of_ne hz
        (G.node_ne_self_of_not_link_self hz)]
      rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hedge_node_ne]
      exact PermReachable.trans (G.walkupE z).edge
        (G.walkupE_edgePermReachable_node_to_edge_of_not_link_self hz)
        (PermReachable.trans (G.walkupE z).edge
          (G.walkupE_edgePermReachable_edge_to_edge_symm_of_not_cross
            hz hncross)
          (G.walkupE_edgePermReachable_edge_symm_to_edge_node_of_not_link_self
            hz))
    · by_cases hxpred : x = G.edge.symm z
      · have hedge_x : G.edge x = z := by
          rw [hxpred]
          simp
        rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz]
        rw [hedge_x, G.walkupENonSelfEdgeRepresentative_deleted]
        subst x
        exact PermReachable.symm (G.walkupE z).edge
          (G.walkupE_edgePermReachable_edge_to_edge_symm_of_not_cross
            hz hncross)
      · have hedge_ne_z : G.edge x ≠ z := by
          intro hxedge
          exact hxpred ((G.edge_eq_iff_eq_edge_symm).mp hxedge)
        rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz]
        rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hedge_ne_z]
        exact G.walkupE_edgePermReachable_of_original_edge_regular
          hz rfl hxnode hxpred

theorem walkupE_edgePermReachable_representatives_of_edgeReachable_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {x y : G.Dart} (hxy : PermReachable G.edge x y) :
    PermReachable (G.walkupE z).edge
      (G.walkupENonSelfEdgeRepresentative hz x)
      (G.walkupENonSelfEdgeRepresentative hz y) := by
  induction hxy with
  | refl =>
      exact PermReachable.refl (G.walkupE z).edge
        (G.walkupENonSelfEdgeRepresentative hz x)
  | @tail b c hxb hbc ih =>
      exact PermReachable.trans (G.walkupE z).edge ih (by
        cases hbc with
        | forward =>
            exact G.walkupE_edgePermReachable_representatives_of_edge_step_not_cross
              hz hncross b
        | backward =>
            exact PermReachable.symm (G.walkupE z).edge
              (by
                simpa using
                G.walkupE_edgePermReachable_representatives_of_edge_step_not_cross
                    hz hncross (G.edge.symm b)))

/-- Non-cross edge-orbit map induced by representing the deleted dart `z` by
`edge z`.  In the non-cross branch this map merges exactly the original edge
orbits of `z` and `node z`. -/
noncomputable def walkupENonCrossEdgeOrbitLift
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    G.EdgeOrbit → (G.walkupE z).EdgeOrbit :=
  Quotient.lift
    (fun x : G.Dart =>
      PermOrbit.of (G.walkupE z).edge
        (G.walkupENonSelfEdgeRepresentative hz x))
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of (G.walkupE z).edge
        (G.walkupE_edgePermReachable_representatives_of_edgeReachable_not_cross
          hz hncross hxy))

theorem walkupENonCrossEdgeOrbitLift_of
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (x : G.Dart) :
    G.walkupENonCrossEdgeOrbitLift hz hncross (PermOrbit.of G.edge x) =
      PermOrbit.of (G.walkupE z).edge
        (G.walkupENonSelfEdgeRepresentative hz x) :=
  rfl

theorem walkupENonCrossEdgeOrbitLift_z_eq_node
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    G.walkupENonCrossEdgeOrbitLift hz hncross (PermOrbit.of G.edge z) =
      G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge (G.node z)) := by
  rw [G.walkupENonCrossEdgeOrbitLift_of,
    G.walkupENonCrossEdgeOrbitLift_of,
    G.walkupENonSelfEdgeRepresentative_deleted,
    G.walkupENonSelfEdgeRepresentative_of_ne hz
      (G.node_ne_self_of_not_link_self hz)]
  exact PermOrbit.of_eq_of (G.walkupE z).edge
    (PermReachable.symm (G.walkupE z).edge
      (G.walkupE_edgePermReachable_node_to_edge_of_not_link_self hz))

theorem walkupENonCrossEdgeOrbitLift_eq_of_affected
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (o : G.AffectedEdgeOrbit z) :
    G.walkupENonCrossEdgeOrbitLift hz hncross o.1 =
      G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge z) := by
  rcases o with ⟨o, ho⟩
  change G.walkupENonCrossEdgeOrbitLift hz hncross o =
    G.walkupENonCrossEdgeOrbitLift hz hncross
      (PermOrbit.of G.edge z)
  rcases ho with ho | ho
  · rw [ho]
  · rw [ho]
    exact (G.walkupENonCrossEdgeOrbitLift_z_eq_node hz hncross).symm

theorem walkupENonCrossEdgeOrbitLift_eq_of_edgeDomain
    {z x : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (hx : G.EdgeDomain z x) :
    G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge x) =
      G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge z) := by
  rcases G.edgeOrbit_eq_left_or_right_of_edgeDomain hx with hxz | hxnode
  · rw [hxz]
  · rw [hxnode]
    exact (G.walkupENonCrossEdgeOrbitLift_z_eq_node hz hncross).symm

/-- Coq `same_cskip_edge` and `cskip_edge_merge`, combined: in the
non-self, non-cross branch, `WalkupE` leaves every unaffected edge orbit
unchanged and merges all darts in the two affected edge orbits. -/
theorem walkupE_edgePermReachable_iff_of_not_link_self_of_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {x y : (G.walkupE z).Dart}
    [Decidable (G.EdgeDomain z x.1)] :
    PermReachable (G.walkupE z).edge x y ↔
      if G.EdgeDomain z x.1 then G.EdgeDomain z y.1
      else PermReachable G.edge x.1 y.1 := by
  classical
  constructor
  · intro hxy
    by_cases hxdom : G.EdgeDomain z x.1
    · simp only [hxdom, if_pos]
      rcases G.walkupE_edgePermReachable_sameEdgeOrbitOrAffected_of_not_link_self
          hz hxy with hsame | haffected
      · exact G.edgeDomain_of_permReachable hxdom
          (PermReachable.symm G.edge hsame)
      · exact haffected.2
    · simp only [hxdom]
      exact Quotient.exact
        (G.edgeOrbit_eq_of_walkupE_edgeOrbit_eq_of_not_edgeDomain
          hz hxdom (PermOrbit.of_eq_of (G.walkupE z).edge hxy))
  · by_cases hxdom : G.EdgeDomain z x.1
    · simp only [hxdom, if_pos]
      intro hydom
      have hxLift := G.walkupENonCrossEdgeOrbitLift_eq_of_edgeDomain
        hz hncross hxdom
      have hyLift := G.walkupENonCrossEdgeOrbitLift_eq_of_edgeDomain
        hz hncross hydom
      rw [G.walkupENonCrossEdgeOrbitLift_of,
        G.walkupENonCrossEdgeOrbitLift_of] at hxLift hyLift
      rw [G.walkupENonSelfEdgeRepresentative_of_ne hz x.2] at hxLift
      rw [G.walkupENonSelfEdgeRepresentative_of_ne hz y.2] at hyLift
      exact Quotient.exact (hxLift.trans hyLift.symm)
    · simp only [hxdom]
      intro hxy
      exact G.walkupE_edgePermReachable_of_original_edgeReachable_not_edgeDomain
        hz hxdom hxy

theorem walkupENonCrossEdgeOrbitLift_injective_of_not_edgeDomain
    {z x y : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (hxdom : ¬ G.EdgeDomain z x)
    (hydom : ¬ G.EdgeDomain z y)
    (hxy :
      G.walkupENonCrossEdgeOrbitLift hz hncross
          (PermOrbit.of G.edge x) =
        G.walkupENonCrossEdgeOrbitLift hz hncross
          (PermOrbit.of G.edge y)) :
    PermOrbit.of G.edge x = PermOrbit.of G.edge y := by
  have hxz : x ≠ z := by
    intro hxz
    exact hxdom (by simpa [hxz] using G.edgeDomain_self z)
  have hyz : y ≠ z := by
    intro hyz
    exact hydom (by simpa [hyz] using G.edgeDomain_self z)
  rw [G.walkupENonCrossEdgeOrbitLift_of,
    G.walkupENonCrossEdgeOrbitLift_of] at hxy
  rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz,
    G.walkupENonSelfEdgeRepresentative_of_ne hz hyz] at hxy
  exact G.edgeOrbit_eq_of_walkupE_edgeOrbit_eq_of_not_edgeDomain
    hz hxdom hxy

theorem walkupENonCrossEdgeOrbitLift_ne_z_of_not_edgeDomain
    {z x : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (hxdom : ¬ G.EdgeDomain z x) :
    G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge x) ≠
      G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge z) := by
  intro hx
  have hxz : x ≠ z := by
    intro hxz
    exact hxdom (by simpa [hxz] using G.edgeDomain_self z)
  rw [G.walkupENonCrossEdgeOrbitLift_of,
    G.walkupENonCrossEdgeOrbitLift_of] at hx
  rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz,
    G.walkupENonSelfEdgeRepresentative_deleted] at hx
  have horbit :
      PermOrbit.of G.edge x = PermOrbit.of G.edge (G.edge z) :=
    G.edgeOrbit_eq_of_walkupE_edgeOrbit_eq_of_not_edgeDomain hz hxdom hx
  rw [PermOrbit.of_apply G.edge z] at horbit
  exact hxdom (G.edgeDomain_of_edgeOrbit_eq_left horbit)

theorem walkupENonCrossEdgeOrbitLift_ne_node_of_not_edgeDomain
    {z x : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    (hxdom : ¬ G.EdgeDomain z x) :
    G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge x) ≠
      G.walkupENonCrossEdgeOrbitLift hz hncross
        (PermOrbit.of G.edge (G.node z)) := by
  intro hx
  exact G.walkupENonCrossEdgeOrbitLift_ne_z_of_not_edgeDomain
    hz hncross hxdom
    (hx.trans
      (G.walkupENonCrossEdgeOrbitLift_z_eq_node hz hncross).symm)

theorem walkupENonCrossEdgeOrbitLift_surjective
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    Function.Surjective (G.walkupENonCrossEdgeOrbitLift hz hncross) := by
  intro o
  let x : (G.walkupE z).Dart := Quotient.out o
  refine ⟨PermOrbit.of G.edge x.1, ?_⟩
  rw [G.walkupENonCrossEdgeOrbitLift_of]
  rw [G.walkupENonSelfEdgeRepresentative_of_ne hz x.2]
  exact Quotient.out_eq o

/-- In the non-cross, non-self branch, deleting `z` merges exactly the two
affected original edge orbits.  Equivalently, the original edge-orbit quotient
is obtained from the Walkup edge-orbit quotient by adding one extra point. -/
noncomputable def walkupENonCrossEdgeOrbitOptionEquiv
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    G.EdgeOrbit ≃ Option (G.walkupE z).EdgeOrbit := by
  classical
  let az : G.EdgeOrbit := PermOrbit.of G.edge z
  let an : G.EdgeOrbit := PermOrbit.of G.edge (G.node z)
  let f : G.EdgeOrbit → (G.walkupE z).EdgeOrbit :=
    G.walkupENonCrossEdgeOrbitLift hz hncross
  let F : G.EdgeOrbit → Option (G.walkupE z).EdgeOrbit :=
    fun q => if q = az then none else some (f q)
  have hazne : az ≠ an := by
    exact G.edgeOrbit_z_ne_node_of_not_cross hncross
  have hfan : f az = f an := by
    simpa [f, az, an] using
      G.walkupENonCrossEdgeOrbitLift_z_eq_node hz hncross
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro q r hqr
    by_cases hqz : q = az
    · subst q
      by_cases hrz : r = az
      · exact hrz.symm
      · simp [F, hrz] at hqr
    · by_cases hrz : r = az
      · subst r
        simp [F, hqz] at hqr
      · have hfqr : f q = f r := by
          simpa [F, hqz, hrz] using hqr
        by_cases hqn : q = an
        · subst q
          by_cases hrn : r = an
          · exact hrn.symm
          · have hrdom :
                ¬ G.EdgeDomain z (Quotient.out r) :=
              G.not_edgeDomain_quotient_out_of_not_affected hrz hrn
            have hr_ne :
                f r ≠ f an := by
              have hne :=
                G.walkupENonCrossEdgeOrbitLift_ne_node_of_not_edgeDomain
                  hz hncross hrdom
              change f (PermOrbit.of G.edge (Quotient.out r)) ≠ f an at hne
              have hout :
                  PermOrbit.of G.edge (Quotient.out r) = r :=
                Quotient.out_eq r
              rw [hout] at hne
              exact hne
            exact False.elim (hr_ne hfqr.symm)
        · by_cases hrn : r = an
          · subst r
            have hqdom :
                ¬ G.EdgeDomain z (Quotient.out q) :=
              G.not_edgeDomain_quotient_out_of_not_affected hqz hqn
            have hq_ne :
                f q ≠ f an := by
              have hne :=
                G.walkupENonCrossEdgeOrbitLift_ne_node_of_not_edgeDomain
                  hz hncross hqdom
              change f (PermOrbit.of G.edge (Quotient.out q)) ≠ f an at hne
              have hout :
                  PermOrbit.of G.edge (Quotient.out q) = q :=
                Quotient.out_eq q
              rw [hout] at hne
              exact hne
            exact False.elim (hq_ne hfqr)
          · have hqdom :
                ¬ G.EdgeDomain z (Quotient.out q) :=
              G.not_edgeDomain_quotient_out_of_not_affected hqz hqn
            have hrdom :
                ¬ G.EdgeDomain z (Quotient.out r) :=
              G.not_edgeDomain_quotient_out_of_not_affected hrz hrn
            have hout_eq :
                PermOrbit.of G.edge (Quotient.out q) =
                  PermOrbit.of G.edge (Quotient.out r) := by
              exact
                G.walkupENonCrossEdgeOrbitLift_injective_of_not_edgeDomain
                  hz hncross hqdom hrdom (by
                    change
                      f (PermOrbit.of G.edge (Quotient.out q)) =
                        f (PermOrbit.of G.edge (Quotient.out r))
                    have houtq :
                        PermOrbit.of G.edge (Quotient.out q) = q :=
                      Quotient.out_eq q
                    have houtr :
                        PermOrbit.of G.edge (Quotient.out r) = r :=
                      Quotient.out_eq r
                    rw [houtq, houtr]
                    exact hfqr)
            have houtq :
                PermOrbit.of G.edge (Quotient.out q) = q :=
              Quotient.out_eq q
            have houtr :
                PermOrbit.of G.edge (Quotient.out r) = r :=
              Quotient.out_eq r
            rw [houtq, houtr] at hout_eq
            exact hout_eq
  · intro o
    cases o with
    | none =>
        exact ⟨az, by simp [F]⟩
    | some b =>
        by_cases hb : b = f az
        · refine ⟨an, ?_⟩
          have hanz : an ≠ az := hazne.symm
          have hfb : f an = b := hfan.symm.trans hb.symm
          simp [F, hanz, hfb]
        · rcases G.walkupENonCrossEdgeOrbitLift_surjective hz hncross b with
            ⟨q, hq⟩
          refine ⟨q, ?_⟩
          have hqz : q ≠ az := by
            intro hqz
            apply hb
            rw [← hq]
            rw [hqz]
          simp [F, hqz, f, hq]

theorem walkupE_nonCross_edgeOrbitCount_add_one_eq
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).edgeOrbitCount + 1 = G.edgeOrbitCount := by
  have hcard :
      G.edgeOrbitCount =
        Nat.card (Option (G.walkupE z).EdgeOrbit) := by
    change Nat.card G.EdgeOrbit =
      Nat.card (Option (G.walkupE z).EdgeOrbit)
    exact Nat.card_congr
      (G.walkupENonCrossEdgeOrbitOptionEquiv hz hncross)
  rw [Finite.card_option] at hcard
  unfold edgeOrbitCount at hcard ⊢
  omega

theorem walkupE_nonCross_edgeOrbitCount_lt
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).edgeOrbitCount < G.edgeOrbitCount := by
  unfold edgeOrbitCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_surjective_not_injective
    (G.walkupENonCrossEdgeOrbitLift hz hncross)
    (G.walkupENonCrossEdgeOrbitLift_surjective hz hncross) ?_
  intro hinj
  apply hncross
  have horbit :
      PermOrbit.of G.edge z = PermOrbit.of G.edge (G.node z) :=
    hinj (G.walkupENonCrossEdgeOrbitLift_z_eq_node hz hncross)
  exact Quotient.exact horbit

theorem walkupE_nonCross_edgeOrbitCount_add_one_le
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).edgeOrbitCount + 1 ≤ G.edgeOrbitCount :=
  Nat.succ_le_of_lt (G.walkupE_nonCross_edgeOrbitCount_lt hz hncross)

theorem walkupE_reachable_node_to_edge_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    (G.walkupE z).Reachable
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  rw [← G.walkupE_edge_apply_node_of_not_link_self hz]
  exact (G.walkupE z).reachable_edge
    (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
      (G.walkupE z).Dart)

theorem walkupE_reachable_face_to_edge_node_of_not_link_self
    {z : G.Dart} (hz : ¬ G.Link z z) :
    (G.walkupE z).Reachable
        (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  exact ((G.walkupE z).reachable_node
      (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart)).trans (by
    rw [G.walkupE_node_apply_face_of_not_link_self hz,
      ← G.walkupE_edge_apply_edge_symm_of_not_link_self hz]
    exact (G.walkupE z).reachable_edge
      (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart))

theorem walkupE_reachable_edge_to_face_of_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).Reachable
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) := by
  exact ((G.walkupE z).edgePermReachable_reachable
      (G.walkupE_edgePermReachable_edge_to_edge_symm_of_not_cross
        hz hncross)).trans
    (((G.walkupE z).edgePermReachable_reachable
      (G.walkupE_edgePermReachable_edge_symm_to_edge_node_of_not_link_self
        hz)).trans
      ((G.walkupE z).reachable_symm
        (G.walkupE_reachable_face_to_edge_node_of_not_link_self hz)))

theorem walkupE_reachable_face_to_edge_of_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).Reachable
        (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart)
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) :=
  (G.walkupE z).reachable_symm
    (G.walkupE_reachable_edge_to_face_of_not_cross hz hncross)

theorem walkupE_reachable_representatives_of_link_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {x y : G.Dart} (hxy : G.Link x y) :
    (G.walkupE z).Reachable
      (G.walkupENonSelfEdgeRepresentative hz x)
      (G.walkupENonSelfEdgeRepresentative hz y) := by
  rcases hxy with hy | hy | hy
  · subst y
    exact (G.walkupE z).edgePermReachable_reachable
      (G.walkupE_edgePermReachable_representatives_of_edge_step_not_cross
        hz hncross x)
  · subst y
    by_cases hxz : x = z
    · subst x
      rw [G.walkupENonSelfEdgeRepresentative_deleted]
      rw [G.walkupENonSelfEdgeRepresentative_of_ne hz
        (G.node_ne_self_of_not_link_self hz)]
      exact (G.walkupE z).reachable_symm
        (G.walkupE_reachable_node_to_edge_of_not_link_self hz)
    · by_cases hnodez : G.node x = z
      · rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz]
        rw [hnodez, G.walkupENonSelfEdgeRepresentative_deleted]
        let ux : (G.walkupE z).Dart := ⟨x, hxz⟩
        have hnode :
            (G.walkupE z).node ux =
              (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
                (G.walkupE z).Dart) := by
          apply Subtype.ext
          exact G.walkupE_node_apply_coe_of_eq ux hnodez
        have hstep : (G.walkupE z).Reachable ux
            (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
              (G.walkupE z).Dart) := by
          rw [← hnode]
          exact (G.walkupE z).reachable_node ux
        exact hstep.trans
          (G.walkupE_reachable_node_to_edge_of_not_link_self hz)
      · rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz]
        rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hnodez]
        let ux : (G.walkupE z).Dart := ⟨x, hxz⟩
        let uy : (G.walkupE z).Dart := ⟨G.node x, hnodez⟩
        have hnode : (G.walkupE z).node ux = uy := by
          apply Subtype.ext
          exact G.walkupE_node_apply_coe_of_ne ux hnodez
        have hstep := (G.walkupE z).reachable_node ux
        rw [hnode] at hstep
        simpa [ux, uy] using hstep
  · subst y
    by_cases hxz : x = z
    · subst x
      rw [G.walkupENonSelfEdgeRepresentative_deleted]
      rw [G.walkupENonSelfEdgeRepresentative_of_ne hz
        (G.face_ne_self_of_not_link_self hz)]
      exact G.walkupE_reachable_edge_to_face_of_not_cross hz hncross
    · by_cases hfacez : G.face x = z
      · rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz]
        rw [hfacez, G.walkupENonSelfEdgeRepresentative_deleted]
        let ux : (G.walkupE z).Dart := ⟨x, hxz⟩
        have hface :
            (G.walkupE z).face ux =
              (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
                (G.walkupE z).Dart) := by
          apply Subtype.ext
          exact G.walkupE_face_apply_coe_of_eq ux hfacez
        have hstep : (G.walkupE z).Reachable ux
            (⟨G.face z, G.face_ne_self_of_not_link_self hz⟩ :
              (G.walkupE z).Dart) := by
          rw [← hface]
          exact (G.walkupE z).reachable_face ux
        exact hstep.trans
          (G.walkupE_reachable_face_to_edge_of_not_cross hz hncross)
      · rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hxz]
        rw [G.walkupENonSelfEdgeRepresentative_of_ne hz hfacez]
        let ux : (G.walkupE z).Dart := ⟨x, hxz⟩
        let uy : (G.walkupE z).Dart := ⟨G.face x, hfacez⟩
        have hface : (G.walkupE z).face ux = uy := by
          apply Subtype.ext
          exact G.walkupE_face_apply_coe_of_ne ux hfacez
        have hstep := (G.walkupE z).reachable_face ux
        rw [hface] at hstep
        simpa [ux, uy] using hstep

theorem walkupE_componentOf_representatives_eq_of_link_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {x y : G.Dart} (hxy : G.Link x y) :
    (G.walkupE z).componentOf
        (G.walkupENonSelfEdgeRepresentative hz x) =
      (G.walkupE z).componentOf
        (G.walkupENonSelfEdgeRepresentative hz y) :=
  (G.walkupE z).componentOf_eq_componentOf
    (G.walkupE_reachable_representatives_of_link_not_cross
      hz hncross hxy)

theorem walkupE_componentOf_representatives_eq_of_reachable_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z)
    {x y : G.Dart} (hxy : G.Reachable x y) :
    (G.walkupE z).componentOf
        (G.walkupENonSelfEdgeRepresentative hz x) =
      (G.walkupE z).componentOf
        (G.walkupENonSelfEdgeRepresentative hz y) :=
  hxy.apply_eq
    (fun x => (G.walkupE z).componentOf
      (G.walkupENonSelfEdgeRepresentative hz x))
    (fun {_ _} h =>
      G.walkupE_componentOf_representatives_eq_of_link_not_cross
        hz hncross h)

noncomputable def walkupEComponentEquivOfNonCross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).Component ≃ G.Component where
  toFun :=
    Quotient.map
      (fun x : G.DeletedDart z => x.1)
      (by
        intro x y hxy
        exact G.walkupE_reachable_reachable hxy)
  invFun :=
    Quotient.lift
      (fun x : G.Dart =>
        (G.walkupE z).componentOf
          (G.walkupENonSelfEdgeRepresentative hz x))
      (by
        intro x y hxy
        exact
          G.walkupE_componentOf_representatives_eq_of_reachable_not_cross
            hz hncross hxy)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    have hrep_x : G.walkupENonSelfEdgeRepresentative hz x.1 = x :=
      G.walkupENonSelfEdgeRepresentative_of_ne hz x.2
    change
      (G.walkupE z).componentOf
          (G.walkupENonSelfEdgeRepresentative hz x.1) =
        Quot.mk (G.walkupE z).reachableSetoid x
    rw [hrep_x]
    rfl
  right_inv c := by
    refine Quotient.inductionOn c ?_
    intro x
    change G.componentOf
        (G.walkupENonSelfEdgeRepresentative hz x).1 = G.componentOf x
    by_cases hx : x = z
    · subst x
      have hrep :
          (G.walkupENonSelfEdgeRepresentative hz z).1 = G.edge z := by
        exact congrArg Subtype.val
          (G.walkupENonSelfEdgeRepresentative_deleted hz)
      rw [hrep]
      exact G.componentOf_edge z
    · have hrep :
          (G.walkupENonSelfEdgeRepresentative hz x).1 = x := by
        exact congrArg Subtype.val
          (G.walkupENonSelfEdgeRepresentative_of_ne hz hx)
      rw [hrep]

theorem walkupE_componentCount_eq_of_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    (G.walkupE z).componentCount = G.componentCount := by
  change Nat.card (G.walkupE z).Component = Nat.card G.Component
  exact Nat.card_congr (G.walkupEComponentEquivOfNonCross hz hncross)

theorem walkupE_componentCount_step_of_not_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hncross : ¬ G.CrossEdge z) :
    1 + (G.walkupE z).componentCount = G.componentCount + 1 := by
  have h := G.walkupE_componentCount_eq_of_not_cross hz hncross
  omega


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
