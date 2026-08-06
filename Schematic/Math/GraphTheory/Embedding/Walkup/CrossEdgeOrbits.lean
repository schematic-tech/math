import Schematic.Math.GraphTheory.Embedding.Walkup.CrossComponents

/-! Edge orbits in the cross-edge branch of Walkup deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

theorem walkupE_edge_step_project_of_not_link_self_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (x : (G.walkupE z).Dart) :
    PermReachable G.edge x.1 (((G.walkupE z).edge x).1) := by
  by_cases hxnode : x.1 = G.node z
  · have hval : (((G.walkupE z).edge x).1 : G.Dart) = G.edge z := by
      rw [G.walkupE_edge_apply_coe, hxnode]
      exact G.walkupSkipEdgeAux_node_of_not_link_self hz
    rw [hxnode, hval]
    exact PermReachable.trans G.edge
      (PermReachable.symm G.edge hcross)
      (PermReachable.forward G.edge z)
  · by_cases hxpred : x.1 = G.edge.symm z
    · have hval :
          (((G.walkupE z).edge x).1 : G.Dart) =
            G.edge (G.node z) := by
        rw [G.walkupE_edge_apply_coe, hxpred]
        exact G.walkupSkipEdgeAux_edge_symm_of_not_link_self hz
      rw [hxpred, hval]
      exact PermReachable.trans G.edge
        (by simpa using PermReachable.forward G.edge (G.edge.symm z))
        (PermReachable.trans G.edge hcross
          (PermReachable.forward G.edge (G.node z)))
    · have hval : (((G.walkupE z).edge x).1 : G.Dart) = G.edge x.1 :=
        G.walkupE_edge_apply_of_not_link_self_of_regular hz x hxnode hxpred
      rw [hval]
      exact PermReachable.forward G.edge x.1

theorem walkupE_edgePermReachable_project_of_not_link_self_of_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {x y : (G.walkupE z).Dart}
    (hxy : PermReachable (G.walkupE z).edge x y) :
    PermReachable G.edge x.1 y.1 :=
  PermReachable.map_of_forward_simulation (G.walkupE z).edge G.edge
    Subtype.val
    (G.walkupE_edge_step_project_of_not_link_self_of_cross hz hcross) hxy

/-- Cross-edge projection from Walkup edge orbits to original edge orbits. -/
noncomputable def walkupECrossEdgeOrbitProjection
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    (G.walkupE z).EdgeOrbit → G.EdgeOrbit :=
  Quotient.lift
    (fun x : (G.walkupE z).Dart => PermOrbit.of G.edge x.1)
    (by
      intro x y hxy
      exact PermOrbit.of_eq_of G.edge
        (G.walkupE_edgePermReachable_project_of_not_link_self_of_cross
          hz hcross hxy))

theorem walkupECrossEdgeOrbitProjection_of
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (x : (G.walkupE z).Dart) :
    G.walkupECrossEdgeOrbitProjection hz hcross
        (PermOrbit.of (G.walkupE z).edge x) =
      PermOrbit.of G.edge x.1 :=
  rfl

theorem walkupECrossEdgeOrbitProjection_surjective
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    Function.Surjective (G.walkupECrossEdgeOrbitProjection hz hcross) := by
  intro o
  let x : G.Dart := Quotient.out o
  by_cases hxz : x = z
  · have hquote : PermOrbit.of G.edge z = o := by
      simpa [x, hxz] using Quotient.out_eq o
    refine ⟨PermOrbit.of (G.walkupE z).edge
        (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart), ?_⟩
    rw [G.walkupECrossEdgeOrbitProjection_of]
    calc
      PermOrbit.of G.edge (G.edge z) = PermOrbit.of G.edge z :=
        PermOrbit.of_eq_of G.edge
          (PermReachable.symm G.edge (PermReachable.forward G.edge z))
      _ = o := hquote
  · refine ⟨PermOrbit.of (G.walkupE z).edge
        (⟨x, hxz⟩ : (G.walkupE z).Dart), ?_⟩
    rw [G.walkupECrossEdgeOrbitProjection_of]
    exact Quotient.out_eq o

theorem walkupECrossEdgeOrbitProjection_injective_of_not_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {x y : (G.walkupE z).Dart}
    (hxdom : ¬ G.EdgeDomain z x.1)
    (hxy :
      G.walkupECrossEdgeOrbitProjection hz hcross
          (PermOrbit.of (G.walkupE z).edge x) =
        G.walkupECrossEdgeOrbitProjection hz hcross
          (PermOrbit.of (G.walkupE z).edge y)) :
    PermOrbit.of (G.walkupE z).edge x =
      PermOrbit.of (G.walkupE z).edge y := by
  rw [G.walkupECrossEdgeOrbitProjection_of,
    G.walkupECrossEdgeOrbitProjection_of] at hxy
  exact G.walkupE_edgeOrbit_eq_of_original_edgeOrbit_eq_not_edgeDomain
    hz hxdom hxy

theorem walkupECrossEdgeOrbitProjection_eq_affected_of_edgeDomain
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {x : (G.walkupE z).Dart}
    (hxdom : G.EdgeDomain z x.1) :
    G.walkupECrossEdgeOrbitProjection hz hcross
        (PermOrbit.of (G.walkupE z).edge x) =
      PermOrbit.of G.edge z := by
  rw [G.walkupECrossEdgeOrbitProjection_of]
  rcases G.edgeOrbit_eq_left_or_right_of_edgeDomain hxdom with hx | hx
  · exact hx
  · exact hx.trans (G.edgeOrbit_z_eq_node_of_cross hcross).symm

theorem walkupECrossEdgeOrbitProjection_edge_z
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    G.walkupECrossEdgeOrbitProjection hz hcross
        (PermOrbit.of (G.walkupE z).edge
          (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart)) =
      PermOrbit.of G.edge z := by
  rw [G.walkupECrossEdgeOrbitProjection_of]
  exact PermOrbit.of_apply G.edge z

theorem walkupECrossEdgeOrbitProjection_edge_symm
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    G.walkupECrossEdgeOrbitProjection hz hcross
        (PermOrbit.of (G.walkupE z).edge
          (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart)) =
      PermOrbit.of G.edge z := by
  rw [G.walkupECrossEdgeOrbitProjection_of]
  exact PermOrbit.of_eq_of G.edge
    (by simpa using PermReachable.forward G.edge (G.edge.symm z))

/-- The single original edge orbit whose cross-branch fiber must split. -/
def CrossAffectedEdgeFiber
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) : Type u :=
  {q : (G.walkupE z).EdgeOrbit //
    G.walkupECrossEdgeOrbitProjection hz hcross q =
      PermOrbit.of G.edge z}

noncomputable def crossAffectedEdgeFiberEdgeZ
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    G.CrossAffectedEdgeFiber hz hcross :=
  ⟨PermOrbit.of (G.walkupE z).edge
      (⟨G.edge z, G.edge_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart),
    G.walkupECrossEdgeOrbitProjection_edge_z hz hcross⟩

noncomputable def crossAffectedEdgeFiberEdgeSymm
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    G.CrossAffectedEdgeFiber hz hcross :=
  ⟨PermOrbit.of (G.walkupE z).edge
      (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
        (G.walkupE z).Dart),
    G.walkupECrossEdgeOrbitProjection_edge_symm hz hcross⟩

theorem crossAffectedEdgeFiber_node_orbit_eq_edgeZ
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermOrbit.of (G.walkupE z).edge
        (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      (G.crossAffectedEdgeFiberEdgeZ hz hcross).1 := by
  exact (G.walkupE_edgeOrbit_edge_z_eq_node_of_cross hz hcross).symm

theorem crossAffectedEdgeFiber_edge_node_orbit_eq_edgeSymm
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    PermOrbit.of (G.walkupE z).edge
        (⟨G.edge (G.node z), G.edge_node_ne_self_of_not_link_self hz⟩ :
          (G.walkupE z).Dart) =
      (G.crossAffectedEdgeFiberEdgeSymm hz hcross).1 := by
  exact G.walkupE_edgeOrbit_edge_node_eq_edge_symm_of_cross hz hcross

theorem crossAffectedEdgeFiberEdgeZ_ne_edgeSymm
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    G.crossAffectedEdgeFiberEdgeZ hz hcross ≠
      G.crossAffectedEdgeFiberEdgeSymm hz hcross := by
  intro h
  exact G.walkupE_edgeOrbit_edge_z_ne_edge_symm_of_cross hz hcross
    (congrArg Subtype.val h)

theorem walkupE_edgeOrbit_eq_edgeZ_or_edgeSymm_of_edgeDomain_cross
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (x : (G.walkupE z).Dart) (hxdom : G.EdgeDomain z x.1) :
    PermOrbit.of (G.walkupE z).edge x =
        (G.crossAffectedEdgeFiberEdgeZ hz hcross).1 ∨
      PermOrbit.of (G.walkupE z).edge x =
        (G.crossAffectedEdgeFiberEdgeSymm hz hcross).1 := by
  classical
  let σ : Equiv.Perm G.Dart := G.edge
  let Target : Nat → Prop := fun k =>
    (σ : G.Dart → G.Dart)^[k] x.1 = z ∨
      (σ : G.Dart → G.Dart)^[k] x.1 = G.node z
  have hex : ∃ k : Nat, Target k := by
    rcases hxdom with hxz | hxnode
    · rcases permReachable_exists_iterate σ hxz with ⟨k, hk⟩
      exact ⟨k, Or.inl hk⟩
    · rcases permReachable_exists_iterate σ hxnode with ⟨k, hk⟩
      exact ⟨k, Or.inr hk⟩
  let m : Nat := Nat.find hex
  have hm : Target m := Nat.find_spec hex
  have hmin : ∀ k : Nat, k < m → ¬ Target k := by
    intro k hk
    exact Nat.find_min hex hk
  rcases hm with hmz | hmnode
  · have hmpos : 0 < m := by
      by_contra hmnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hmnot
      exact x.2 (by simpa [m, Target, hm0] using hmz)
    rcases Nat.exists_eq_add_of_lt hmpos with ⟨j, hm_eq⟩
    have hm_eq_succ : m = j + 1 := by
      simpa [Nat.zero_add, Nat.add_assoc] using hm_eq
    have htarget_pred :
        (σ : G.Dart → G.Dart)^[j] x.1 = G.edge.symm z := by
      apply G.edge.injective
      calc
        G.edge ((σ : G.Dart → G.Dart)^[j] x.1) =
            (σ : G.Dart → G.Dart)^[j + 1] x.1 := by
          simp [σ, Function.iterate_succ_apply']
        _ = z := by
          simpa [hm_eq_succ] using hmz
        _ = G.edge (G.edge.symm z) := by simp
    have hiter_ne_z :
        ∀ k : Nat, k ≤ j →
          (σ : G.Dart → G.Dart)^[k] x.1 ≠ z := by
      intro k hk hkz
      exact hmin k (by omega) (Or.inl hkz)
    let dart (k : Nat) (hk : k ≤ j) : (G.walkupE z).Dart :=
      ⟨(σ : G.Dart → G.Dart)^[k] x.1, hiter_ne_z k hk⟩
    have hpath :
        ∀ k : Nat, ∀ hk : k ≤ j,
          PermReachable (G.walkupE z).edge
            (dart 0 (Nat.zero_le j)) (dart k hk) := by
      intro k hk
      induction k with
      | zero =>
          exact PermReachable.refl (G.walkupE z).edge
            (dart 0 (Nat.zero_le j))
      | succ k ih =>
          have hk_le : k ≤ j := Nat.le_of_succ_le hk
          have hk_lt : k < j := Nat.lt_of_succ_le hk
          have ihpath := ih hk_le
          have hxnode : (dart k hk_le).1 ≠ G.node z := by
            intro hnode
            exact hmin k (by omega) (Or.inr hnode)
          have hxpred : (dart k hk_le).1 ≠ G.edge.symm z := by
            intro hpred
            have hhit_z :
                (σ : G.Dart → G.Dart)^[k + 1] x.1 = z := by
              have hcongr := congrArg (fun y => σ y) hpred
              simpa [dart, σ, Function.iterate_succ_apply',
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcongr
            exact hmin (k + 1) (by omega) (Or.inl hhit_z)
          have hstep :
              PermReachable (G.walkupE z).edge
                (dart k hk_le) (dart k.succ hk) := by
            exact G.walkupE_edgePermReachable_of_original_edge_regular
              hz (by simp [dart, σ, Function.iterate_succ_apply'])
              hxnode hxpred
          exact PermReachable.trans (G.walkupE z).edge ihpath hstep
    have hsource : dart 0 (Nat.zero_le j) = x := by
      apply Subtype.ext
      simp [dart]
    have htarget :
        dart j le_rfl =
          (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart) := by
      apply Subtype.ext
      exact htarget_pred
    have hreach :
        PermReachable (G.walkupE z).edge x
          (⟨G.edge.symm z, G.edge_symm_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart) := by
      simpa [hsource, htarget] using hpath j le_rfl
    right
    exact PermOrbit.of_eq_of (G.walkupE z).edge hreach
  · have hiter_ne_z :
        ∀ k : Nat, k ≤ m →
          (σ : G.Dart → G.Dart)^[k] x.1 ≠ z := by
      intro k hk hkz
      by_cases hkm : k = m
      · subst k
        exact G.node_ne_self_of_not_link_self hz (hmnode.symm.trans hkz)
      · exact hmin k (Nat.lt_of_le_of_ne hk hkm) (Or.inl hkz)
    let dart (k : Nat) (hk : k ≤ m) : (G.walkupE z).Dart :=
      ⟨(σ : G.Dart → G.Dart)^[k] x.1, hiter_ne_z k hk⟩
    have hpath :
        ∀ k : Nat, ∀ hk : k ≤ m,
          PermReachable (G.walkupE z).edge
            (dart 0 (Nat.zero_le m)) (dart k hk) := by
      intro k hk
      induction k with
      | zero =>
          exact PermReachable.refl (G.walkupE z).edge
            (dart 0 (Nat.zero_le m))
      | succ k ih =>
          have hk_le : k ≤ m := Nat.le_of_succ_le hk
          have hk_lt : k < m := Nat.lt_of_succ_le hk
          have ihpath := ih hk_le
          have hxnode : (dart k hk_le).1 ≠ G.node z := by
            intro hnode
            exact hmin k hk_lt (Or.inr hnode)
          have hxpred : (dart k hk_le).1 ≠ G.edge.symm z := by
            intro hpred
            have hhit_z :
                (σ : G.Dart → G.Dart)^[k + 1] x.1 = z := by
              have hcongr := congrArg (fun y => σ y) hpred
              simpa [dart, σ, Function.iterate_succ_apply',
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcongr
            by_cases hks : k + 1 = m
            · have hnode_z : G.node z = z := by
                rw [← hmnode, ← hks]
                exact hhit_z
              exact G.node_ne_self_of_not_link_self hz hnode_z
            · exact hmin (k + 1) (Nat.lt_of_le_of_ne hk hks)
                (Or.inl hhit_z)
          have hstep :
              PermReachable (G.walkupE z).edge
                (dart k hk_le) (dart k.succ hk) := by
            exact G.walkupE_edgePermReachable_of_original_edge_regular
              hz (by simp [dart, σ, Function.iterate_succ_apply'])
              hxnode hxpred
          exact PermReachable.trans (G.walkupE z).edge ihpath hstep
    have hsource : dart 0 (Nat.zero_le m) = x := by
      apply Subtype.ext
      simp [dart]
    have htarget :
        dart m le_rfl =
          (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart) := by
      apply Subtype.ext
      exact hmnode
    have hreach :
        PermReachable (G.walkupE z).edge x
          (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
            (G.walkupE z).Dart) := by
      simpa [hsource, htarget] using hpath m le_rfl
    left
    calc
      PermOrbit.of (G.walkupE z).edge x =
          PermOrbit.of (G.walkupE z).edge
            (⟨G.node z, G.node_ne_self_of_not_link_self hz⟩ :
              (G.walkupE z).Dart) :=
        PermOrbit.of_eq_of (G.walkupE z).edge hreach
      _ = (G.crossAffectedEdgeFiberEdgeZ hz hcross).1 :=
        G.crossAffectedEdgeFiber_node_orbit_eq_edgeZ hz hcross

theorem walkupECrossEdgeOrbitProjection_eq_affected_iff
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (q : (G.walkupE z).EdgeOrbit) :
    G.walkupECrossEdgeOrbitProjection hz hcross q =
        PermOrbit.of G.edge z ↔
      G.EdgeDomain z (Quotient.out q).1 := by
  constructor
  · intro hq
    have hqout :
        G.walkupECrossEdgeOrbitProjection hz hcross
            (PermOrbit.of (G.walkupE z).edge (Quotient.out q)) =
          PermOrbit.of G.edge z := by
      have hout :
          PermOrbit.of (G.walkupE z).edge (Quotient.out q) = q :=
        Quotient.out_eq q
      rw [hout]
      exact hq
    rw [G.walkupECrossEdgeOrbitProjection_of] at hqout
    exact G.edgeDomain_of_edgeOrbit_eq_left hqout
  · intro hdom
    have hqout :=
      G.walkupECrossEdgeOrbitProjection_eq_affected_of_edgeDomain
        hz hcross hdom
    have hout :
        PermOrbit.of (G.walkupE z).edge (Quotient.out q) = q :=
      Quotient.out_eq q
    rw [hout] at hqout
    exact hqout

theorem crossAffectedEdgeFiber_exhaustive
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    ∀ q : G.CrossAffectedEdgeFiber hz hcross,
      q = G.crossAffectedEdgeFiberEdgeZ hz hcross ∨
        q = G.crossAffectedEdgeFiberEdgeSymm hz hcross := by
  intro q
  let x : (G.walkupE z).Dart := Quotient.out q.1
  have hxdom : G.EdgeDomain z x.1 := by
    have hq := q.2
    exact (G.walkupECrossEdgeOrbitProjection_eq_affected_iff
      hz hcross q.1).mp hq
  have hout :
      PermOrbit.of (G.walkupE z).edge x = q.1 :=
    Quotient.out_eq q.1
  rcases G.walkupE_edgeOrbit_eq_edgeZ_or_edgeSymm_of_edgeDomain_cross
      hz hcross x hxdom with hqz | hqs
  · left
    apply Subtype.ext
    exact hout.symm.trans hqz
  · right
    apply Subtype.ext
    exact hout.symm.trans hqs

theorem walkupECrossEdgeOrbitProjection_ne_affected_iff
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (q : (G.walkupE z).EdgeOrbit) :
    G.walkupECrossEdgeOrbitProjection hz hcross q ≠
        PermOrbit.of G.edge z ↔
      ¬ G.EdgeDomain z (Quotient.out q).1 := by
  rw [← G.walkupECrossEdgeOrbitProjection_eq_affected_iff hz hcross q]

theorem walkupECrossEdgeOrbitProjection_injective_of_ne_affected
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    {q r : (G.walkupE z).EdgeOrbit}
    (hq :
      G.walkupECrossEdgeOrbitProjection hz hcross q ≠
        PermOrbit.of G.edge z)
    (hqr :
      G.walkupECrossEdgeOrbitProjection hz hcross q =
        G.walkupECrossEdgeOrbitProjection hz hcross r) :
    q = r := by
  have hqdom :
      ¬ G.EdgeDomain z (Quotient.out q).1 :=
    (G.walkupECrossEdgeOrbitProjection_ne_affected_iff
      hz hcross q).mp hq
  have houtq :
      PermOrbit.of (G.walkupE z).edge (Quotient.out q) = q :=
    Quotient.out_eq q
  have houtr :
      PermOrbit.of (G.walkupE z).edge (Quotient.out r) = r :=
    Quotient.out_eq r
  have hqr' :
      G.walkupECrossEdgeOrbitProjection hz hcross
          (PermOrbit.of (G.walkupE z).edge (Quotient.out q)) =
        G.walkupECrossEdgeOrbitProjection hz hcross
          (PermOrbit.of (G.walkupE z).edge (Quotient.out r)) := by
    rw [houtq, houtr]
    exact hqr
  have horbit :
      PermOrbit.of (G.walkupE z).edge (Quotient.out q) =
        PermOrbit.of (G.walkupE z).edge (Quotient.out r) :=
    G.walkupECrossEdgeOrbitProjection_injective_of_not_edgeDomain
      hz hcross hqdom hqr'
  rw [houtq, houtr] at horbit
  exact horbit

/-- If the affected cross fiber consists only of the two canonical split
orbits, then Walkup edge orbits are original edge orbits plus one new point. -/
noncomputable def walkupECrossEdgeOrbitOptionEquivOfFiberExhaustive
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (hfiber : ∀ q : G.CrossAffectedEdgeFiber hz hcross,
      q = G.crossAffectedEdgeFiberEdgeZ hz hcross ∨
        q = G.crossAffectedEdgeFiberEdgeSymm hz hcross) :
    (G.walkupE z).EdgeOrbit ≃ Option G.EdgeOrbit := by
  classical
  let az : (G.walkupE z).EdgeOrbit :=
    (G.crossAffectedEdgeFiberEdgeZ hz hcross).1
  let as : (G.walkupE z).EdgeOrbit :=
    (G.crossAffectedEdgeFiberEdgeSymm hz hcross).1
  let a : G.EdgeOrbit := PermOrbit.of G.edge z
  let f : (G.walkupE z).EdgeOrbit → G.EdgeOrbit :=
    G.walkupECrossEdgeOrbitProjection hz hcross
  let F : (G.walkupE z).EdgeOrbit → Option G.EdgeOrbit :=
    fun q => if q = az then none else some (f q)
  have haz_as : az ≠ as := by
    intro h
    exact G.crossAffectedEdgeFiberEdgeZ_ne_edgeSymm hz hcross (by
      apply Subtype.ext
      exact h)
  have hfaz : f az = a := by
    simpa [f, az, a] using G.walkupECrossEdgeOrbitProjection_edge_z hz hcross
  have hfas : f as = a := by
    simpa [f, as, a] using
      G.walkupECrossEdgeOrbitProjection_edge_symm hz hcross
  have affected_eq_as_of_ne_az :
      ∀ {q : (G.walkupE z).EdgeOrbit}, q ≠ az → f q = a → q = as := by
    intro q hqaz hqa
    let qfiber : G.CrossAffectedEdgeFiber hz hcross := ⟨q, by
      simpa [f, a] using hqa⟩
    rcases hfiber qfiber with hq | hq
    · exact False.elim (hqaz (by
        simpa [qfiber, az] using congrArg Subtype.val hq))
    · simpa [qfiber, as] using congrArg Subtype.val hq
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · intro q r hqr
    by_cases hqaz : q = az
    · subst q
      by_cases hraz : r = az
      · exact hraz.symm
      · simp [F, hraz] at hqr
    · by_cases hraz : r = az
      · subst r
        simp [F, hqaz] at hqr
      · have hfqr : f q = f r := by
          simpa [F, hqaz, hraz] using hqr
        by_cases hqa : f q = a
        · have hq_as : q = as :=
            affected_eq_as_of_ne_az hqaz hqa
          have hra : f r = a := hfqr ▸ hqa
          have hr_as : r = as :=
            affected_eq_as_of_ne_az hraz hra
          exact hq_as.trans hr_as.symm
        · exact G.walkupECrossEdgeOrbitProjection_injective_of_ne_affected
            hz hcross (by simpa [f, a] using hqa) (by
              simpa [f] using hfqr)
  · intro o
    cases o with
    | none =>
        exact ⟨az, by simp [F]⟩
    | some b =>
        by_cases hb : b = a
        · refine ⟨as, ?_⟩
          have has_ne : as ≠ az := haz_as.symm
          simpa [F, has_ne, hb] using hfas
        · rcases G.walkupECrossEdgeOrbitProjection_surjective hz hcross b with
            ⟨q, hq⟩
          refine ⟨q, ?_⟩
          have hqaz : q ≠ az := by
            intro hqaz
            apply hb
            rw [← hq, hqaz]
            exact hfaz
          simp [F, hqaz, f, hq]

theorem walkupE_cross_edgeOrbitCount_add_one_eq_of_fiberExhaustive
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z)
    (hfiber : ∀ q : G.CrossAffectedEdgeFiber hz hcross,
      q = G.crossAffectedEdgeFiberEdgeZ hz hcross ∨
        q = G.crossAffectedEdgeFiberEdgeSymm hz hcross) :
    (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 := by
  have hcard :
      (G.walkupE z).edgeOrbitCount =
        Nat.card (Option G.EdgeOrbit) := by
    change Nat.card (G.walkupE z).EdgeOrbit =
      Nat.card (Option G.EdgeOrbit)
    exact Nat.card_congr
      (G.walkupECrossEdgeOrbitOptionEquivOfFiberExhaustive
        hz hcross hfiber)
  rw [Finite.card_option] at hcard
  unfold edgeOrbitCount at hcard ⊢
  omega

theorem walkupE_cross_edgeOrbitCount_add_one_eq
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 :=
  G.walkupE_cross_edgeOrbitCount_add_one_eq_of_fiberExhaustive
    hz hcross (G.crossAffectedEdgeFiber_exhaustive hz hcross)

theorem walkupE_cross_edgeOrbitCount_le
    {z : G.Dart} (hz : ¬ G.Link z z) (hcross : G.CrossEdge z) :
    G.edgeOrbitCount ≤ (G.walkupE z).edgeOrbitCount := by
  unfold edgeOrbitCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_surjective
    (G.walkupECrossEdgeOrbitProjection hz hcross)
    (G.walkupECrossEdgeOrbitProjection_surjective hz hcross)


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
