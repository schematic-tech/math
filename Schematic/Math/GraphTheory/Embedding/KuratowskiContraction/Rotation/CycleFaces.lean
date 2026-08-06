import Schematic.Math.GraphTheory.Embedding.KuratowskiContraction.Rotation.DegreeTwoLocal
import Schematic.Math.GraphTheory.Embedding.RotationSystemCycleGluing

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The wrap-around face step on a simple cycle for the canonical
degree-at-most-two rotation system.  The internal path-step lemma handles all
non-final edges; this theorem handles the final edge returning to the first
edge of the cycle. -/
theorem degreeLeTwoRotationSystem_toHypermap_face_eq_cycle_last_to_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (⟨(c.getVert (c.length - 1), c.getVert ((c.length - 1) + 1)),
          c.adj_getVert_succ (i := c.length - 1) (by
            have hlen := hc.three_le_length
            omega)⟩ : OrientedEdge G) =
      (⟨(c.getVert 0, c.getVert 1),
          c.adj_getVert_succ (by
            have hlen := hc.three_le_length
            omega)⟩ : OrientedEdge G) := by
  have hne : c.getVert (c.length - 1) ≠ c.getVert 1 := by
    intro h
    exact hc.snd_ne_penultimate h.symm
  have hlast_idx : (c.length - 1) + 1 = c.length := by
    have hlen := hc.three_le_length
    omega
  have hfirst_adj :
      G.Adj (c.getVert ((c.length - 1) + 1)) (c.getVert 1) := by
    rw [hlast_idx, SimpleGraph.Walk.getVert_length]
    simpa using
      c.adj_getVert_succ (i := 0) (by
        have hlen := hc.three_le_length
        omega)
  have hstep :
      ((degreeLeTwoRotationSystem hdegree).toHypermap).face
          (⟨(c.getVert (c.length - 1),
              c.getVert ((c.length - 1) + 1)),
            c.adj_getVert_succ (i := c.length - 1) (by
              have hlen := hc.three_le_length
              omega)⟩ : OrientedEdge G) =
        (⟨(c.getVert ((c.length - 1) + 1), c.getVert 1),
            hfirst_adj⟩ : OrientedEdge G) := by
    exact degreeLeTwoRotationSystem_toHypermap_face_eq_path_step
      hdegree
      (c.adj_getVert_succ (i := c.length - 1) (by
        have hlen := hc.three_le_length
        omega))
      hfirst_adj
      hne
  simpa [hlast_idx, SimpleGraph.Walk.getVert_length] using hstep

/-- The canonical degree-two face permutation preserves the forward-directed
darts of a simple cycle. -/
theorem degreeLeTwoRotationSystem_cycleForwardDart_face
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    {e : OrientedEdge G}
    (he : CycleForwardDart c e) :
    CycleForwardDart c
      (((degreeLeTwoRotationSystem hdegree).toHypermap).face e) := by
  rcases he with ⟨i, hi, htail, hhead⟩
  by_cases hnext : i + 1 < c.length
  · have hi2 : i + 2 <= c.length := by omega
    have hne : c.getVert i ≠ c.getVert (i + 2) := by
      have h :=
        hc.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
      simpa [Nat.add_sub_cancel] using h
    let curr : OrientedEdge G :=
      ⟨(c.getVert i, c.getVert (i + 1)),
        c.adj_getVert_succ (i := i) (by omega)⟩
    let nxt : OrientedEdge G :=
      ⟨(c.getVert (i + 1), c.getVert (i + 2)),
        c.adj_getVert_succ (i := i + 1) (by omega)⟩
    have heq : e = curr :=
      orientedEdge_eq_of_tail_head htail hhead
    have hface :
        ((degreeLeTwoRotationSystem hdegree).toHypermap).face e = nxt := by
      rw [heq]
      exact degreeLeTwoRotationSystem_toHypermap_face_eq_path_step
        hdegree
        (c.adj_getVert_succ (i := i) (by omega))
        (c.adj_getVert_succ (i := i + 1) (by omega))
        hne
    refine ⟨i + 1, hnext, ?_, ?_⟩
    · rw [hface]
      rfl
    · rw [hface]
      rfl
  · have hi_last : i = c.length - 1 := by omega
    have hlast_idx : (c.length - 1) + 1 = c.length := by
      have hlen := hc.three_le_length
      omega
    let last : OrientedEdge G :=
      ⟨(c.getVert (c.length - 1), c.getVert ((c.length - 1) + 1)),
        c.adj_getVert_succ (i := c.length - 1) (by
          have hlen := hc.three_le_length
          omega)⟩
    have heq : e = last := by
      apply orientedEdge_eq_of_tail_head
      · simpa [last, hi_last, OrientedEdge.tail] using htail
      · simpa [last, hi_last, OrientedEdge.head] using hhead
    have hface :
        ((degreeLeTwoRotationSystem hdegree).toHypermap).face e =
          (⟨(c.getVert 0, c.getVert 1),
            c.adj_getVert_succ (by
              have hlen := hc.three_le_length
              omega)⟩ : OrientedEdge G) := by
      rw [heq]
      exact degreeLeTwoRotationSystem_toHypermap_face_eq_cycle_last_to_first
        hdegree c hc
    refine ⟨0, by
      have hlen := hc.three_le_length
      omega, ?_, ?_⟩
    · rw [hface]
      rfl
    · rw [hface]
      rfl

/-- The canonical degree-two rotation system exposes either orientation of a
simple cycle as a face.  This is the face-marked form of the elementary
embedding of a cycle and is used by the rural-society edgeless base case. -/
theorem degreeLeTwoRotationSystem_isFacialCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
    RotationSystemGluing.IsFacialCycle
      (degreeLeTwoRotationSystem hdegree) c hc := by
  intro e
  constructor
  · intro he
    rcases he with ⟨i, hi, htail, hhead⟩
    have hreach_at : forall (j : Nat) (hj : j < c.length),
        PermReachable
          (degreeLeTwoRotationSystem hdegree).toHypermap.face
          (cycleFirstDart c hc) (cycleDartAt c j hj) := by
      intro j
      induction j with
      | zero =>
          intro _hj
          exact PermReachable.refl _ _
      | succ j ih =>
          intro hsj
          have hj : j < c.length := by omega
          have hprev := ih hj
          let d := cycleDartAt c j hj
          have hd_forward : CycleForwardDart c d :=
            cycleDartAt_forward c j hj
          have hface_forward :
              CycleForwardDart c
                ((degreeLeTwoRotationSystem hdegree).toHypermap.face d) :=
            degreeLeTwoRotationSystem_cycleForwardDart_face
              hdegree c hc hd_forward
          have hnext_forward :
              CycleForwardDart c (cycleDartAt c (j + 1) hsj) :=
            cycleDartAt_forward c (j + 1) hsj
          have htail_eq :
              ((degreeLeTwoRotationSystem hdegree).toHypermap.face d).tail =
                (cycleDartAt c (j + 1) hsj).tail := by
            rw [RotationSystem.toHypermap_face_tail, cycleDartAt_tail]
            simp [d, cycleDartAt_head c j hj]
          have hface_eq :
              (degreeLeTwoRotationSystem hdegree).toHypermap.face d =
                cycleDartAt c (j + 1) hsj :=
            cycleForwardDart_eq_of_tail_eq hc hface_forward hnext_forward htail_eq
          exact PermReachable.trans _ hprev (by
            rw [← hface_eq]
            exact PermReachable.forward _ d)
    have hreach := hreach_at i hi
    have heq : cycleDartAt c i hi = e := by
      apply orientedEdge_eq_of_tail_head
      · simpa [cycleDartAt_tail] using htail.symm
      · simpa [cycleDartAt_head] using hhead.symm
    simpa [heq] using hreach
  · intro hreach
    rcases permReachable_exists_iterate _ hreach with ⟨n, hn⟩
    have hforward : forall m : Nat,
        CycleForwardDart c
          (((degreeLeTwoRotationSystem hdegree).toHypermap.face :
            OrientedEdge G -> OrientedEdge G)^[m] (cycleFirstDart c hc)) := by
      intro m
      induction m with
      | zero => simpa using cycleForwardDart_first c hc
      | succ m ih =>
          simpa [Function.iterate_succ_apply'] using
            degreeLeTwoRotationSystem_cycleForwardDart_face
              hdegree c hc ih
    have hforward_n := hforward n
    rw [hn] at hforward_n
    exact hforward_n

/-- On a simple cycle, the first directed edge and its reverse do not lie in
the same face orbit of the canonical degree-two rotation system. -/
theorem not_degreeLeTwoRotationSystem_face_reachable_cycle_first_to_reverse_first
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    ¬ PermReachable ((degreeLeTwoRotationSystem hdegree).toHypermap).face
      (⟨(c.getVert 0, c.getVert 1),
        c.adj_getVert_succ (by
          have hlen := hc.three_le_length
          omega)⟩ : OrientedEdge G)
      (OrientedEdge.symm
        (⟨(c.getVert 0, c.getVert 1),
          c.adj_getVert_succ (by
            have hlen := hc.three_le_length
            omega)⟩ : OrientedEdge G)) := by
  intro hreach
  let H := (degreeLeTwoRotationSystem hdegree).toHypermap
  let first : OrientedEdge G := cycleFirstDart c hc
  have hforward_iter :
      forall n : ℕ, CycleForwardDart c ((H.face : OrientedEdge G -> OrientedEdge G)^[n] first) := by
    intro n
    induction n with
    | zero =>
        simpa [first] using cycleForwardDart_first c hc
    | succ n ih =>
        simpa [Function.iterate_succ_apply'] using
          degreeLeTwoRotationSystem_cycleForwardDart_face
            hdegree c hc ih
  have hreachFirst : PermReachable H.face first first.symm := by
    simpa [H, first, cycleFirstDart] using hreach
  rcases permReachable_exists_iterate H.face hreachFirst with ⟨n, hn⟩
  have hforward :
      CycleForwardDart c
        (((H.face : OrientedEdge G -> OrientedEdge G)^[n]) first) :=
    hforward_iter n
  rw [hn] at hforward
  exact not_cycleForwardDart_first_symm c hc
    (by simpa [first] using hforward)

/-- A simple cycle contributes at least two face orbits to the canonical
degree-two rotation system: the two orientations of the first cycle edge are
separated by the directed-cycle invariant. -/
theorem degreeLeTwoRotationSystem_cycle_two_le_faceOrbitCount
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    2 <= ((degreeLeTwoRotationSystem hdegree).toHypermap).faceOrbitCount := by
  classical
  let H := (degreeLeTwoRotationSystem hdegree).toHypermap
  let first : OrientedEdge G :=
    ⟨(u, c.getVert 1),
      by
        simpa using c.adj_getVert_succ (i := 0) (by
          have hlen := hc.three_le_length
          omega)⟩
  have hnot :
      ¬ PermReachable H.face first first.symm := by
    simpa [H, first, SimpleGraph.Walk.getVert_zero] using
      not_degreeLeTwoRotationSystem_face_reachable_cycle_first_to_reverse_first
        hdegree c hc
  have horbit_ne :
      PermOrbit.of H.face first ≠ PermOrbit.of H.face first.symm := by
    intro h
    exact hnot (Quotient.exact h)
  let f : Fin 2 -> H.FaceOrbit := fun i =>
    if i = 0 then PermOrbit.of H.face first
    else PermOrbit.of H.face first.symm
  have hinj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
    · exact False.elim (horbit_ne hab)
    · exact False.elim (horbit_ne hab.symm)
  have hcard : Fintype.card (Fin 2) <= Fintype.card H.FaceOrbit :=
    Fintype.card_le_of_injective f hinj
  rw [Hypermap.faceOrbitCount, Nat.card_eq_fintype_card]
  simpa using hcard

/-- Face orbits of the canonical maximum-degree-two rotation system remain in
one graph component.  This is the disconnected-support half of the embedding
count: different graph components must contribute distinct face orbits. -/
theorem degreeLeTwoRotationSystem_faceOrbit_ne_of_not_reachable_tail
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {e f : OrientedEdge G}
    (hnot : ¬ G.Reachable e.tail f.tail) :
    PermOrbit.of ((degreeLeTwoRotationSystem hdegree).toHypermap).face e ≠
      PermOrbit.of ((degreeLeTwoRotationSystem hdegree).toHypermap).face f := by
  intro horbit
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  let H : Hypermap := R.toHypermap
  have hface : PermReachable H.face e f := by
    simpa [H, R] using Quotient.exact horbit
  have hH : H.Reachable e f :=
    H.facePermReachable_reachable hface
  exact hnot (R.toHypermap_reachable_tail_reachable hH)

/-- Cycle-face representatives from graph-disconnected cycle starts determine
distinct face orbits in the canonical degree-two rotation system. -/
theorem degreeLeTwoRotationSystem_cycleFaceDart_faceOrbit_ne_of_not_reachable_start
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    {u v : V}
    (c : G.Walk u u) (hc : c.IsCycle)
    (d : G.Walk v v) (hd : d.IsCycle)
    (hnot : ¬ G.Reachable u v)
    (i j : Fin 2) :
    PermOrbit.of ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (cycleFaceDart c hc i) ≠
      PermOrbit.of ((degreeLeTwoRotationSystem hdegree).toHypermap).face
        (cycleFaceDart d hd j) := by
  refine
    degreeLeTwoRotationSystem_faceOrbit_ne_of_not_reachable_tail
      (G := G) hdegree ?_
  intro htail
  exact hnot
    ((cycleFaceDart_start_reachable_tail c hc i).trans
      (htail.trans (cycleFaceDart_tail_reachable_start d hd j)))

/-- If every non-isolated support component of a maximum-degree-two graph is
represented by a simple cycle, then the canonical rotation system has at least
two face orbits per support component.  The proof is the componentwise version
of `degreeLeTwoRotationSystem_cycle_two_le_faceOrbitCount`: the two directed
cycle-face representatives are distinct inside one component, and the previous
lemma separates representatives belonging to different graph components. -/
theorem degreeLeTwoRotationSystem_two_mul_supportComponent_card_le_faceOrbitCount_of_component_cycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hcycle :
      forall C : (G.induce G.support).ConnectedComponent,
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle) :
    2 * Nat.card (G.induce G.support).ConnectedComponent <=
      ((degreeLeTwoRotationSystem hdegree).toHypermap).faceOrbitCount := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  let H : Hypermap := R.toHypermap
  let Comp := (G.induce G.support).ConnectedComponent
  let chosenVertex : Comp -> V := fun C => (hcycle C).choose
  let chosenSupport : forall C : Comp, chosenVertex C ∈ G.support := fun C =>
    (hcycle C).choose_spec.choose
  let chosenMem : forall C : Comp,
      (⟨chosenVertex C, chosenSupport C⟩ : G.support) ∈ C.supp := fun C =>
    (hcycle C).choose_spec.choose_spec.1
  let chosenCycle : forall C : Comp, G.Walk (chosenVertex C) (chosenVertex C) :=
    fun C => (hcycle C).choose_spec.choose_spec.2.choose
  let chosenCycle_isCycle : forall C : Comp, (chosenCycle C).IsCycle := fun C =>
    (hcycle C).choose_spec.choose_spec.2.choose_spec
  let faceOf : Comp × Fin 2 -> H.FaceOrbit := fun ci =>
    PermOrbit.of H.face
      (cycleFaceDart (chosenCycle ci.1) (chosenCycle_isCycle ci.1) ci.2)
  have hinj : Function.Injective faceOf := by
    intro a b hab
    rcases a with ⟨C, i⟩
    rcases b with ⟨D, j⟩
    dsimp [faceOf] at hab
    have hCD : C = D := by
      by_contra hne
      have hnotReach :
          ¬ G.Reachable (chosenVertex C) (chosenVertex D) := by
        intro hreach
        have hreach_support :
            (G.induce G.support).Reachable
              (⟨chosenVertex C, chosenSupport C⟩ : G.support)
              (⟨chosenVertex D, chosenSupport D⟩ : G.support) :=
          RotationSystem.reachable_induce_support_of_reachable
            (G := G) hreach
        have hmk :
            (G.induce G.support).connectedComponentMk
                (⟨chosenVertex C, chosenSupport C⟩ : G.support) =
              (G.induce G.support).connectedComponentMk
                (⟨chosenVertex D, chosenSupport D⟩ : G.support) :=
          SimpleGraph.ConnectedComponent.sound hreach_support
        have hCmk :
            (G.induce G.support).connectedComponentMk
                (⟨chosenVertex C, chosenSupport C⟩ : G.support) = C :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff C
            (⟨chosenVertex C, chosenSupport C⟩ : G.support)).mp
              (chosenMem C)
        have hDmk :
            (G.induce G.support).connectedComponentMk
                (⟨chosenVertex D, chosenSupport D⟩ : G.support) = D :=
          (SimpleGraph.ConnectedComponent.mem_supp_iff D
            (⟨chosenVertex D, chosenSupport D⟩ : G.support)).mp
              (chosenMem D)
        exact hne (hCmk.symm.trans (hmk.trans hDmk))
      exact
        (degreeLeTwoRotationSystem_cycleFaceDart_faceOrbit_ne_of_not_reachable_start
          (G := G) hdegree
          (chosenCycle C) (chosenCycle_isCycle C)
          (chosenCycle D) (chosenCycle_isCycle D)
          hnotReach i j) hab
    subst D
    have hij : i = j := by
      fin_cases i <;> fin_cases j
      · rfl
      · have hreach :
            PermReachable H.face
              (cycleFirstDart (chosenCycle C) (chosenCycle_isCycle C))
              (cycleFirstDart (chosenCycle C) (chosenCycle_isCycle C)).symm := by
          simpa [H, faceOf, cycleFaceDart] using Quotient.exact hab
        exact False.elim
          ((not_degreeLeTwoRotationSystem_face_reachable_cycle_first_to_reverse_first
            (G := G) hdegree (chosenCycle C) (chosenCycle_isCycle C))
            (by simpa [cycleFirstDart] using hreach))
      · have hreach :
            PermReachable H.face
              (cycleFirstDart (chosenCycle C) (chosenCycle_isCycle C)).symm
              (cycleFirstDart (chosenCycle C) (chosenCycle_isCycle C)) := by
          simpa [H, faceOf, cycleFaceDart] using Quotient.exact hab
        have hreach' :
            PermReachable H.face
              (cycleFirstDart (chosenCycle C) (chosenCycle_isCycle C))
              (cycleFirstDart (chosenCycle C) (chosenCycle_isCycle C)).symm :=
          PermReachable.symm H.face hreach
        exact False.elim
          ((not_degreeLeTwoRotationSystem_face_reachable_cycle_first_to_reverse_first
            (G := G) hdegree (chosenCycle C) (chosenCycle_isCycle C))
            (by simpa [cycleFirstDart] using hreach'))
      · rfl
    subst j
    rfl
  have hcard :
      Fintype.card (Comp × Fin 2) <= Fintype.card H.FaceOrbit :=
    Fintype.card_le_of_injective faceOf hinj
  have hcard_nat :
      2 * Nat.card Comp <= H.faceOrbitCount := by
    rw [Hypermap.faceOrbitCount, Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card]
    simpa [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using hcard
  simpa [H, R, Comp] using hcard_nat

/-- Mixed path/cycle face count for the canonical maximum-degree-two rotation
system.  A support component always contributes at least one face orbit; a
component with an explicit simple cycle contributes one further orbit, namely
the reverse orientation of the first cycle edge.  Components are separated by
tail reachability, and the two cycle orientations in one component are
separated by the directed-cycle invariant. -/
theorem degreeLeTwoRotationSystem_supportComponent_card_add_cyclic_card_le_faceOrbitCount
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (Cyc : Finset (G.induce G.support).ConnectedComponent)
    (hcycle :
      forall C : (G.induce G.support).ConnectedComponent, C ∈ Cyc ->
        Exists fun u : V =>
          Exists fun hu : u ∈ G.support =>
            (⟨u, hu⟩ : G.support) ∈ C.supp ∧
              Exists fun c : G.Walk u u => c.IsCycle) :
    Nat.card (G.induce G.support).ConnectedComponent + Cyc.card <=
      ((degreeLeTwoRotationSystem hdegree).toHypermap).faceOrbitCount := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  let H : Hypermap := R.toHypermap
  let Comp := (G.induce G.support).ConnectedComponent
  let Extra := {C : Comp // C ∈ Cyc}
  let supportVertex : Comp -> G.support := fun C => (C.nonempty_supp).choose
  have supportVertex_mem :
      forall C : Comp, supportVertex C ∈ C.supp := fun C =>
    (C.nonempty_supp).choose_spec
  let supportNeighbor : Comp -> V := fun C =>
    (SimpleGraph.mem_support (G := G)).mp (supportVertex C).property |>.choose
  have supportNeighbor_adj :
      forall C : Comp, G.Adj (supportVertex C : V) (supportNeighbor C) := fun C =>
    (SimpleGraph.mem_support (G := G)).mp (supportVertex C).property |>.choose_spec
  let supportDart : Comp -> OrientedEdge G := fun C =>
    ⟨((supportVertex C : V), supportNeighbor C), supportNeighbor_adj C⟩
  let cycVertex : forall C : Comp, C ∈ Cyc -> V := fun C hC =>
    (hcycle C hC).choose
  let cycSupport : forall C : Comp, forall hC : C ∈ Cyc,
      cycVertex C hC ∈ G.support := fun C hC =>
    (hcycle C hC).choose_spec.choose
  have cycVertex_mem :
      forall C : Comp, forall hC : C ∈ Cyc,
        (⟨cycVertex C hC, cycSupport C hC⟩ : G.support) ∈ C.supp := fun C hC =>
    (hcycle C hC).choose_spec.choose_spec.1
  let cycWalk : forall C : Comp, forall hC : C ∈ Cyc,
      G.Walk (cycVertex C hC) (cycVertex C hC) := fun C hC =>
    (hcycle C hC).choose_spec.choose_spec.2.choose
  have cycWalk_isCycle :
      forall C : Comp, forall hC : C ∈ Cyc,
        (cycWalk C hC).IsCycle := fun C hC =>
    (hcycle C hC).choose_spec.choose_spec.2.choose_spec
  let cycleDart (C : Comp) (hC : C ∈ Cyc) (i : Fin 2) : OrientedEdge G :=
    cycleFaceDart (cycWalk C hC) (cycWalk_isCycle C hC) i
  let baseDart : Comp -> OrientedEdge G := fun C =>
    if hC : C ∈ Cyc then cycleDart C hC 0 else supportDart C
  have supportDart_tail_mem :
      forall C : Comp,
        (⟨(supportDart C).tail, (supportDart C).adj.left_mem_support⟩ :
          G.support) ∈ C.supp := by
    intro C
    simpa [supportDart, OrientedEdge.tail] using supportVertex_mem C
  have cycleDart_tail_mem :
      forall C : Comp, forall hC : C ∈ Cyc, forall i : Fin 2,
        (⟨(cycleDart C hC i).tail,
            (cycleDart C hC i).adj.left_mem_support⟩ : G.support) ∈
          C.supp := by
    intro C hC i
    let tailSupport : G.support :=
      ⟨(cycleDart C hC i).tail,
        (cycleDart C hC i).adj.left_mem_support⟩
    let rootSupport : G.support := ⟨cycVertex C hC, cycSupport C hC⟩
    have hreachG :
        G.Reachable (cycleDart C hC i).tail (cycVertex C hC) := by
      simpa [cycleDart] using
        cycleFaceDart_tail_reachable_start
          (cycWalk C hC) (cycWalk_isCycle C hC) i
    have hreachSupport :
        (G.induce G.support).Reachable tailSupport rootSupport :=
      RotationSystem.reachable_induce_support_of_reachable
        (G := G) hreachG
    have hmk :
        (G.induce G.support).connectedComponentMk tailSupport =
          (G.induce G.support).connectedComponentMk rootSupport :=
      SimpleGraph.ConnectedComponent.sound hreachSupport
    have hCmk :
        (G.induce G.support).connectedComponentMk rootSupport = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C rootSupport).mp
        (cycVertex_mem C hC)
    exact
      (SimpleGraph.ConnectedComponent.mem_supp_iff C tailSupport).mpr (hmk.trans hCmk)
  have baseDart_tail_mem :
      forall C : Comp,
        (⟨(baseDart C).tail, (baseDart C).adj.left_mem_support⟩ :
          G.support) ∈ C.supp := by
    intro C
    unfold baseDart
    split_ifs with hC
    · exact cycleDart_tail_mem C hC 0
    · exact supportDart_tail_mem C
  have orbit_ne_of_component_ne :
      forall {C D : Comp} {e f : OrientedEdge G},
        (⟨e.tail, e.adj.left_mem_support⟩ : G.support) ∈ C.supp ->
        (⟨f.tail, f.adj.left_mem_support⟩ : G.support) ∈ D.supp ->
        C ≠ D ->
          PermOrbit.of H.face e ≠ PermOrbit.of H.face f := by
    intro C D e f heC hfD hCD
    exact
      degreeLeTwoRotationSystem_faceOrbit_ne_of_not_reachable_tail
        (G := G) hdegree (e := e) (f := f)
        (by
          intro hreach
          have hreach_support :
              (G.induce G.support).Reachable
                (⟨e.tail, e.adj.left_mem_support⟩ : G.support)
                (⟨f.tail, f.adj.left_mem_support⟩ : G.support) :=
            RotationSystem.reachable_induce_support_of_reachable
              (G := G) hreach
          have hmk :
              (G.induce G.support).connectedComponentMk
                  (⟨e.tail, e.adj.left_mem_support⟩ : G.support) =
                (G.induce G.support).connectedComponentMk
                  (⟨f.tail, f.adj.left_mem_support⟩ : G.support) :=
            SimpleGraph.ConnectedComponent.sound hreach_support
          have hCmk :
              (G.induce G.support).connectedComponentMk
                  (⟨e.tail, e.adj.left_mem_support⟩ : G.support) = C :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff C
              (⟨e.tail, e.adj.left_mem_support⟩ : G.support)).mp heC
          have hDmk :
              (G.induce G.support).connectedComponentMk
                  (⟨f.tail, f.adj.left_mem_support⟩ : G.support) = D :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff D
              (⟨f.tail, f.adj.left_mem_support⟩ : G.support)).mp hfD
          exact hCD (hCmk.symm.trans (hmk.trans hDmk)))
  let faceOf : Comp ⊕ Extra -> H.FaceOrbit
    | Sum.inl C => PermOrbit.of H.face (baseDart C)
    | Sum.inr E => PermOrbit.of H.face (cycleDart E.1 E.2 1)
  have hinj : Function.Injective faceOf := by
    intro a b hab
    cases a with
    | inl C =>
        cases b with
        | inl D =>
            by_cases hCD : C = D
            · subst D
              rfl
            · exact False.elim
                ((orbit_ne_of_component_ne
                  (baseDart_tail_mem C) (baseDart_tail_mem D) hCD) hab)
        | inr E =>
            by_cases hCE : C = E.1
            · subst C
              have hreach :
                  PermReachable H.face
                    (cycleFirstDart (cycWalk E.1 E.2)
                      (cycWalk_isCycle E.1 E.2))
                    (cycleFirstDart (cycWalk E.1 E.2)
                      (cycWalk_isCycle E.1 E.2)).symm := by
                simpa [H, faceOf, baseDart, cycleDart, cycleFaceDart, E.2]
                  using Quotient.exact hab
              exact False.elim
                ((not_degreeLeTwoRotationSystem_face_reachable_cycle_first_to_reverse_first
                  (G := G) hdegree (cycWalk E.1 E.2)
                  (cycWalk_isCycle E.1 E.2))
                  (by simpa [cycleFirstDart] using hreach))
            · exact False.elim
                ((orbit_ne_of_component_ne
                  (baseDart_tail_mem C)
                  (cycleDart_tail_mem E.1 E.2 1)
                  hCE) hab)
    | inr E =>
        cases b with
        | inl C =>
            by_cases hEC : E.1 = C
            · subst C
              have hreach :
                  PermReachable H.face
                    (cycleFirstDart (cycWalk E.1 E.2)
                      (cycWalk_isCycle E.1 E.2)).symm
                    (cycleFirstDart (cycWalk E.1 E.2)
                      (cycWalk_isCycle E.1 E.2)) := by
                simpa [H, faceOf, baseDart, cycleDart, cycleFaceDart, E.2]
                  using Quotient.exact hab
              have hreach' :
                  PermReachable H.face
                    (cycleFirstDart (cycWalk E.1 E.2)
                      (cycWalk_isCycle E.1 E.2))
                    (cycleFirstDart (cycWalk E.1 E.2)
                      (cycWalk_isCycle E.1 E.2)).symm :=
                PermReachable.symm H.face hreach
              exact False.elim
                ((not_degreeLeTwoRotationSystem_face_reachable_cycle_first_to_reverse_first
                  (G := G) hdegree (cycWalk E.1 E.2)
                  (cycWalk_isCycle E.1 E.2))
                  (by simpa [cycleFirstDart] using hreach'))
            · exact False.elim
                ((orbit_ne_of_component_ne
                  (cycleDart_tail_mem E.1 E.2 1)
                  (baseDart_tail_mem C)
                  hEC) hab)
        | inr F =>
            by_cases hEF : E.1 = F.1
            · have hsub : E = F := Subtype.ext hEF
              subst F
              rfl
            · exact False.elim
                ((orbit_ne_of_component_ne
                  (cycleDart_tail_mem E.1 E.2 1)
                  (cycleDart_tail_mem F.1 F.2 1)
                  hEF) hab)
  have hcard :
      Fintype.card (Comp ⊕ Extra) <= Fintype.card H.FaceOrbit :=
    Fintype.card_le_of_injective faceOf hinj
  have hcard_nat :
      Nat.card Comp + Cyc.card <= H.faceOrbitCount := by
    rw [Hypermap.faceOrbitCount, Nat.card_eq_fintype_card]
    rw [Nat.card_eq_fintype_card]
    have hExtra : Fintype.card Extra = Cyc.card := by
      change Fintype.card {C : Comp // C ∈ Cyc} = Cyc.card
      rw [Fintype.card_subtype]
      simp
    simpa [Extra, Fintype.card_sum, hExtra] using hcard
  simpa [H, R, Comp] using hcard_nat

/-- The connected cycle-witness case of the degree-at-most-two Kuratowski
bridge.  A simple cycle supplies two face orbits; together with `m <= n` and a
single support component this proves Euler-planarity for the canonical
degree-two rotation system. -/
theorem degreeLeTwoRotationSystem_dual_eulerPlanar_of_support_preconnected_cycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hsupport : (G.induce G.support).Preconnected)
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    ((degreeLeTwoRotationSystem hdegree).toHypermap).dual.EulerPlanar := by
  classical
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  let x : G.support :=
    ⟨u, by
      have hadj : G.Adj (c.getVert 0) (c.getVert 1) :=
        c.adj_getVert_succ (i := 0) (by
          have hlen := hc.three_le_length
          omega)
      simpa using hadj.left_mem_support⟩
  have hcomponent_count : (R.toHypermap).componentCount = 1 := by
    rw [R.componentCount_eq_supportComponent_card]
    haveI : Subsingleton (G.induce G.support).ConnectedComponent :=
      SimpleGraph.Preconnected.subsingleton_connectedComponent hsupport
    haveI : Nonempty (G.induce G.support).ConnectedComponent :=
      ⟨(G.induce G.support).connectedComponentMk x⟩
    exact Nat.card_unique
  have hface_two : 2 <= (R.toHypermap).faceOrbitCount := by
    simpa [R] using
      degreeLeTwoRotationSystem_cycle_two_le_faceOrbitCount hdegree c hc
  have hedge_support :
      G.edgeFinset.card <= Fintype.card G.support :=
    edgeFinset_card_le_support_card_of_degree_le_two (G := G) hdegree
  have hleft_le :
      (R.toHypermap).eulerLeft <= (R.toHypermap).eulerRight := by
    have hdart :
        Fintype.card (R.toHypermap).Dart = 2 * G.edgeFinset.card :=
      orientedEdge_card_eq_twice_card_edges (G := G)
    rw [Hypermap.eulerLeft, Hypermap.eulerRight,
      hcomponent_count, R.edgeOrbitCount_eq_edgeFinset_card,
      R.nodeOrbitCount_eq_support_card, hdart]
    omega
  have hplanar : (R.toHypermap).EulerPlanar :=
    Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight
      (G := R.toHypermap) hleft_le
  simpa [R] using
    (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mpr hplanar

/-- Existential packaging of the canonical cycle rotation system. -/
theorem exists_eulerRotationSystem_of_degree_le_two_support_preconnected_cycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hsupport : (G.induce G.support).Preconnected)
    {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar :=
  ⟨degreeLeTwoRotationSystem hdegree,
    degreeLeTwoRotationSystem_dual_eulerPlanar_of_support_preconnected_cycle
      hdegree hsupport c hc⟩

/-- The connected pathlike case of the degree-at-most-two Kuratowski bridge.
If the non-isolated support is connected and contains a degree-at-most-one
vertex, the canonical degree-two rotation system has Euler-planar dual.  The
proof is the source handshaking argument at the rotation-system boundary:
`m + 1 <= n`, one support component, and at least one face orbit. -/
theorem exists_eulerRotationSystem_of_degree_le_two_support_preconnected_exists_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hsupport : (G.induce G.support).Preconnected)
    (hexists : Exists fun x : G.support => G.degree (x : V) <= 1) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  rcases hexists with ⟨x, hxdegree⟩
  let R : RotationSystem G := degreeLeTwoRotationSystem hdegree
  have hcomponent_count : (R.toHypermap).componentCount = 1 := by
    rw [R.componentCount_eq_supportComponent_card]
    haveI : Subsingleton (G.induce G.support).ConnectedComponent :=
      SimpleGraph.Preconnected.subsingleton_connectedComponent hsupport
    haveI : Nonempty (G.induce G.support).ConnectedComponent :=
      ⟨(G.induce G.support).connectedComponentMk x⟩
    exact Nat.card_unique
  have hface_one : 1 <= (R.toHypermap).faceOrbitCount := by
    have h := Hypermap.componentCount_le_faceOrbitCount (G := R.toHypermap)
    simpa [hcomponent_count] using h
  have hedge_support :
      G.edgeFinset.card + 1 <= Fintype.card G.support :=
    edgeFinset_card_add_one_le_support_card_of_degree_le_two_of_exists_degree_le_one
      (G := G) hdegree ⟨x, hxdegree⟩
  have hleft_le :
      (R.toHypermap).eulerLeft <= (R.toHypermap).eulerRight := by
    have hdart :
        Fintype.card (R.toHypermap).Dart = 2 * G.edgeFinset.card :=
      orientedEdge_card_eq_twice_card_edges (G := G)
    rw [Hypermap.eulerLeft, Hypermap.eulerRight,
      hcomponent_count, R.edgeOrbitCount_eq_edgeFinset_card,
      R.nodeOrbitCount_eq_support_card, hdart]
    omega
  have hplanar : (R.toHypermap).EulerPlanar :=
    Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight
      (G := R.toHypermap) hleft_le
  exact ⟨R, (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mpr hplanar⟩

/-- A maximum-degree-two graph with no supported degree-at-most-one vertex is
a graph whose non-isolated components are cycles, in mathlib's `IsCycles`
sense. -/
theorem isCycles_of_degree_le_two_of_no_support_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hno : ¬ Exists fun x : G.support => G.degree (x : V) <= 1) :
    G.IsCycles := by
  classical
  intro v hv_nonempty
  have hv_support : v ∈ G.support := by
    rcases hv_nonempty with ⟨w, hvw⟩
    exact (SimpleGraph.mem_support (G := G)).mpr ⟨w, hvw⟩
  have hnot_le_one : ¬ G.degree v <= 1 := by
    intro hv
    exact hno ⟨⟨v, hv_support⟩, hv⟩
  have hdeg_eq : G.degree v = 2 := by
    have hle := hdegree v
    omega
  have hcard :
      (G.neighborSet v).ncard = G.degree v := by
    simpa [Set.ncard_eq_toFinset_card'] using
      (SimpleGraph.card_neighborSet_eq_degree (G := G) (v := v))
  omega

/-- In the nonempty support of a maximum-degree-two graph, absence of supported
endpoints produces an actual simple cycle witness. -/
theorem exists_cycle_of_degree_le_two_no_support_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    [Nonempty G.support]
    (hno : ¬ Exists fun x : G.support => G.degree (x : V) <= 1) :
    Exists fun u : V => Exists fun c : G.Walk u u => c.IsCycle := by
  classical
  let x : G.support := Classical.choice (inferInstance : Nonempty G.support)
  have hcycles : G.IsCycles :=
    isCycles_of_degree_le_two_of_no_support_degree_le_one
      (G := G) hdegree hno
  have hx_neighbor : (G.neighborSet (x : V)).Nonempty := by
    rcases (SimpleGraph.mem_support (G := G)).mp x.property with ⟨w, hxw⟩
    exact ⟨w, hxw⟩
  let C : G.ConnectedComponent := G.connectedComponentMk (x : V)
  have hxC : (x : V) ∈ C.supp := by
    simp [C]
  rcases SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (G := G) (v := (x : V)) (c := C) hcycles hxC hx_neighbor with
    ⟨p, hpcycle, _hpverts⟩
  exact ⟨x, p, hpcycle⟩

/-- Connected-support maximum-degree-two endpoint for the Kuratowski
rotation-system bridge.  The proof splits exactly as in the elementary graph
argument: either there is a supported endpoint, giving the pathlike Euler
count, or every supported vertex has degree two, giving a simple cycle and the
two-face cycle count. -/
theorem exists_eulerRotationSystem_of_degree_le_two_support_preconnected_nonempty
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hsupport : (G.induce G.support).Preconnected)
    [Nonempty G.support] :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  by_cases hexists : Exists fun x : G.support => G.degree (x : V) <= 1
  · exact
      exists_eulerRotationSystem_of_degree_le_two_support_preconnected_exists_degree_le_one
        (G := G) hdegree hsupport hexists
  · rcases
      exists_cycle_of_degree_le_two_no_support_degree_le_one
        (G := G) hdegree hexists with
      ⟨u, c, hc⟩
    exact exists_eulerRotationSystem_of_degree_le_two_support_preconnected_cycle
      (G := G) hdegree hsupport c hc

/-- Connected-support maximum-degree-two endpoint, including the edgeless
support-empty case. -/
theorem exists_eulerRotationSystem_of_degree_le_two_support_preconnected
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdegree : forall x : V, G.degree x <= 2)
    (hsupport : (G.induce G.support).Preconnected) :
    Exists fun R : RotationSystem G =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  by_cases hnonempty : Nonempty G.support
  · letI : Nonempty G.support := hnonempty
    exact exists_eulerRotationSystem_of_degree_le_two_support_preconnected_nonempty
      (G := G) hdegree hsupport
  · exact exists_eulerRotationSystem_of_edgeless (G := G) (by
      intro x y hxy
      exact hnonempty ⟨⟨x, hxy.left_mem_support⟩⟩)
end FourColor

end Schematic.Math.GraphTheory
