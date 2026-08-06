import Schematic.Math.GraphTheory.Embedding.KuratowskiRotation.Foundations

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace CompleteFourEndpoint

/-- A universe-lifted complete graph on four vertices.  The lift keeps this
endpoint in the same universe as an arbitrary four-vertex source graph, so the
existing same-universe hypermap isomorphism transport can be reused. -/
def K4LiftGraph : SimpleGraph (ULift.{u, 0} (Fin 4)) :=
  SimpleGraph.completeGraph (ULift.{u, 0} (Fin 4))

instance k4LiftGraphDecidableRel : DecidableRel K4LiftGraph.Adj := by
  dsimp [K4LiftGraph]
  infer_instance

def k4Next (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 1 then 2 else if b = 2 then 3 else 1
  else if a = 1 then if b = 0 then 3 else if b = 3 then 2 else 0
  else if a = 2 then if b = 0 then 1 else if b = 1 then 3 else 0
  else if b = 0 then 2 else if b = 2 then 1 else 0

def k4Prev (a b : Fin 4) : Fin 4 :=
  if a = 0 then if b = 1 then 3 else if b = 2 then 1 else 2
  else if a = 1 then if b = 0 then 2 else if b = 3 then 0 else 3
  else if a = 2 then if b = 0 then 3 else if b = 1 then 0 else 1
  else if b = 0 then 1 else if b = 2 then 0 else 2

def k4NextV (a b : ULift.{u, 0} (Fin 4)) :
    ULift.{u, 0} (Fin 4) :=
  ⟨k4Next a.down b.down⟩

def k4PrevV (a b : ULift.{u, 0} (Fin 4)) :
    ULift.{u, 0} (Fin 4) :=
  ⟨k4Prev a.down b.down⟩

theorem k4NextV_ne (a b : ULift.{u, 0} (Fin 4))
    (hab : K4LiftGraph.Adj a b) :
    k4NextV a b ≠ a := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  fin_cases a <;> fin_cases b <;>
    simp [K4LiftGraph, k4NextV, k4Next] at hab ⊢

theorem k4PrevV_ne (a b : ULift.{u, 0} (Fin 4))
    (hab : K4LiftGraph.Adj a b) :
    k4PrevV a b ≠ a := by
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  fin_cases a <;> fin_cases b <;>
    simp [K4LiftGraph, k4PrevV, k4Prev] at hab ⊢

def nodeFun (e : OrientedEdge K4LiftGraph) :
    OrientedEdge K4LiftGraph :=
  ⟨(e.tail, k4NextV e.tail e.head), by
    change e.tail ≠ k4NextV e.tail e.head
    exact (k4NextV_ne e.tail e.head e.adj).symm⟩

def nodeInvFun (e : OrientedEdge K4LiftGraph) :
    OrientedEdge K4LiftGraph :=
  ⟨(e.tail, k4PrevV e.tail e.head), by
    change e.tail ≠ k4PrevV e.tail e.head
    exact (k4PrevV_ne e.tail e.head e.adj).symm⟩

set_option maxHeartbeats 1000000 in
def node : Equiv.Perm (OrientedEdge K4LiftGraph) where
  toFun := nodeFun
  invFun := nodeInvFun
  left_inv := by
    intro e
    rcases e with ⟨⟨a, b⟩, hab⟩
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    fin_cases a <;> fin_cases b <;>
      simp [nodeFun, nodeInvFun, OrientedEdge.tail, OrientedEdge.head,
        k4NextV, k4PrevV, k4Next, k4Prev, K4LiftGraph] at hab ⊢
  right_inv := by
    intro e
    rcases e with ⟨⟨a, b⟩, hab⟩
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    fin_cases a <;> fin_cases b <;>
      simp [nodeFun, nodeInvFun, OrientedEdge.tail, OrientedEdge.head,
        k4NextV, k4PrevV, k4Next, k4Prev, K4LiftGraph] at hab ⊢

@[simp]
theorem node_apply (e : OrientedEdge K4LiftGraph) :
    node e = nodeFun e :=
  rfl

@[simp]
theorem node_symm_apply (e : OrientedEdge K4LiftGraph) :
    node.symm e = nodeInvFun e :=
  rfl

set_option maxHeartbeats 1000000 in
noncomputable def rotationSystem : RotationSystem K4LiftGraph where
  node := node
  node_tail := by intro e; rfl
  node_orbit_of_same_tail := by
    intro e f hef
    rcases e with ⟨⟨et, eh⟩, headj⟩
    rcases f with ⟨⟨ft, fh⟩, hfadj⟩
    rcases et with ⟨et⟩
    rcases eh with ⟨eh⟩
    rcases ft with ⟨ft⟩
    rcases fh with ⟨fh⟩
    fin_cases et <;> fin_cases eh <;> fin_cases ft <;> fin_cases fh <;>
      simp [OrientedEdge.tail, K4LiftGraph] at headj hfadj hef ⊢
    all_goals
      first | exact PermReachable.refl node _
            | exact PermReachable.forward node _
            | exact PermReachable.trans node
                (PermReachable.forward node _) (PermReachable.forward node _)

def faceCode (e : OrientedEdge K4LiftGraph) : Fin 4 :=
  if e.tail.down = 0 ∧ e.head.down = 1 then 0
  else if e.tail.down = 1 ∧ e.head.down = 2 then 0
  else if e.tail.down = 2 ∧ e.head.down = 0 then 0
  else if e.tail.down = 0 ∧ e.head.down = 2 then 1
  else if e.tail.down = 2 ∧ e.head.down = 3 then 1
  else if e.tail.down = 3 ∧ e.head.down = 0 then 1
  else if e.tail.down = 0 ∧ e.head.down = 3 then 2
  else if e.tail.down = 3 ∧ e.head.down = 1 then 2
  else if e.tail.down = 1 ∧ e.head.down = 0 then 2
  else 3

theorem face_eq (e : OrientedEdge K4LiftGraph) :
    (rotationSystem.toHypermap).face e = nodeInvFun e.symm := by
  rfl

set_option maxHeartbeats 1000000 in
theorem faceCode_face (e : OrientedEdge K4LiftGraph) :
    faceCode ((rotationSystem.toHypermap).face e) = faceCode e := by
  rw [face_eq]
  rcases e with ⟨⟨et, eh⟩, headj⟩
  rcases et with ⟨et⟩
  rcases eh with ⟨eh⟩
  fin_cases et <;> fin_cases eh <;> simp [K4LiftGraph] at headj ⊢
  all_goals
    simp [nodeInvFun, k4PrevV, k4Prev, faceCode, OrientedEdge.tail,
      OrientedEdge.head, OrientedEdge.symm]

theorem faceCode_face_symm (e : OrientedEdge K4LiftGraph) :
    faceCode ((rotationSystem.toHypermap).face.symm e) = faceCode e := by
  have h := faceCode_face ((rotationSystem.toHypermap).face.symm e)
  simpa using h.symm

theorem faceCode_of_link {e f : OrientedEdge K4LiftGraph}
    (hef : PermLink (rotationSystem.toHypermap).face e f) :
    faceCode e = faceCode f := by
  cases hef with
  | forward => exact (faceCode_face e).symm
  | backward => exact (faceCode_face_symm e).symm

theorem faceCode_of_reachable {e f : OrientedEdge K4LiftGraph}
    (hef : PermReachable (rotationSystem.toHypermap).face e f) :
    faceCode e = faceCode f :=
  hef.apply_eq faceCode (fun {_ _} h => faceCode_of_link h)

noncomputable def faceOrbitCode :
    (rotationSystem.toHypermap).FaceOrbit → Fin 4 :=
  Quotient.lift faceCode (by
    intro e f hef
    exact faceCode_of_reachable hef)

def faceRep : Fin 4 → OrientedEdge K4LiftGraph
  | 0 => ⟨(⟨0⟩, ⟨1⟩), by simp [K4LiftGraph]⟩
  | 1 => ⟨(⟨0⟩, ⟨2⟩), by simp [K4LiftGraph]⟩
  | 2 => ⟨(⟨0⟩, ⟨3⟩), by simp [K4LiftGraph]⟩
  | 3 => ⟨(⟨1⟩, ⟨3⟩), by simp [K4LiftGraph]⟩

set_option maxHeartbeats 1000000 in
theorem faceCode_faceRep (i : Fin 4) :
    faceCode (faceRep i) = i := by
  fin_cases i <;>
    simp [faceRep, faceCode, OrientedEdge.tail, OrientedEdge.head]

noncomputable def faceOrbitRep :
    Fin 4 → (rotationSystem.toHypermap).FaceOrbit :=
  fun i => PermOrbit.of (rotationSystem.toHypermap).face (faceRep i)

theorem faceOrbitRep_injective : Function.Injective faceOrbitRep := by
  intro i j hij
  have hcode := congrArg faceOrbitCode hij
  change faceCode (faceRep i) = faceCode (faceRep j) at hcode
  rw [faceCode_faceRep i, faceCode_faceRep j] at hcode
  exact hcode

theorem four_le_faceOrbitCount :
    4 ≤ (rotationSystem.toHypermap).faceOrbitCount := by
  classical
  have hcard :
      Fintype.card (Fin 4) ≤
        Fintype.card (rotationSystem.toHypermap).FaceOrbit :=
    Fintype.card_le_of_injective faceOrbitRep faceOrbitRep_injective
  rw [Hypermap.faceOrbitCount, Nat.card_eq_fintype_card]
  simpa using hcard

/-- The complete four-vertex graph has an explicit tetrahedral Euler-planar
rotation system. -/
theorem exists_eulerRotationSystem :
    Exists fun R : RotationSystem K4LiftGraph.{u} =>
      (R.toHypermap).dual.EulerPlanar := by
  classical
  refine ⟨rotationSystem.{u}, ?_⟩
  have hbase : ((rotationSystem.{u}).toHypermap).EulerPlanar := by
    apply Hypermap.eulerPlanar_of_eulerLeft_le_eulerRight
    have hedge_card : (K4LiftGraph.{u}).edgeFinset.card = 6 := by
      have hcardV : Fintype.card (ULift.{u, 0} (Fin 4)) = 4 := by
        simp
      have h :=
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two
          (V := ULift.{u, 0} (Fin 4))
      simpa [K4LiftGraph, hcardV] using h
    have hsupport_univ : (K4LiftGraph.{u}).support = Set.univ := by
      ext x
      rcases x with ⟨x⟩
      fin_cases x <;> simp [K4LiftGraph]
    have hsupport_card :
        Fintype.card (K4LiftGraph.{u}).support = 4 := by
      have hcardV : Fintype.card (ULift.{u, 0} (Fin 4)) = 4 := by
        simp
      rw [support_card_eq_of_support_eq_univ
        (G := K4LiftGraph.{u}) hsupport_univ]
      exact hcardV
    have hpre : (K4LiftGraph.{u}).Preconnected := by
      intro x y
      by_cases hxy : x = y
      · subst y
        exact SimpleGraph.Reachable.rfl
      · exact
          (show (K4LiftGraph.{u}).Adj x y by
            simpa [K4LiftGraph] using hxy).reachable
    haveI : Nonempty (K4LiftGraph.{u}).support := by
      refine ⟨⟨⟨0⟩, ?_⟩⟩
      rw [SimpleGraph.mem_support]
      exact ⟨⟨1⟩, by simp [K4LiftGraph]⟩
    have hcomponent :
        ((rotationSystem.{u}).toHypermap).componentCount = 1 := by
      rw [(rotationSystem.{u}).componentCount_eq_supportComponent_card]
      exact
        supportComponent_card_eq_one_of_preconnected_nonempty
          (G := K4LiftGraph.{u})
          (support_preconnected_of_preconnected
            (G := K4LiftGraph.{u}) hpre)
    have hdart :
        Fintype.card ((rotationSystem.{u}).toHypermap).Dart = 12 := by
      change Fintype.card (OrientedEdge K4LiftGraph.{u}) = 12
      rw [orientedEdge_card_eq_twice_card_edges
        (G := K4LiftGraph.{u}), hedge_card]
    have hedge :
        ((rotationSystem.{u}).toHypermap).edgeOrbitCount = 6 := by
      rw [(rotationSystem.{u}).edgeOrbitCount_eq_edgeFinset_card,
        hedge_card]
    have hnode :
        ((rotationSystem.{u}).toHypermap).nodeOrbitCount = 4 := by
      rw [(rotationSystem.{u}).nodeOrbitCount_eq_support_card,
        hsupport_card]
    have hface :
        4 ≤ ((rotationSystem.{u}).toHypermap).faceOrbitCount :=
      four_le_faceOrbitCount.{u}
    rw [Hypermap.eulerLeft, Hypermap.eulerRight, hcomponent, hdart,
      hedge, hnode]
    omega
  exact
    (Hypermap.dual_eulerPlanar_iff
      (G := (rotationSystem.{u}).toHypermap)).mpr hbase

end CompleteFourEndpoint

end FourColor

end Schematic.Math.GraphTheory
