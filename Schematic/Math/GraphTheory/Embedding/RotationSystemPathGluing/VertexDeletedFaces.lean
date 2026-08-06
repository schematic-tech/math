import Schematic.Math.GraphTheory.Embedding.RotationSystemPathGluing.EdgeDeletion
import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.FanGraph
import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.FaceBoundaries

/-! Reconstructing crossed face boundaries after deleting a vertex. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

open RotationSystemFan

/-- Deleting the common fresh vertex from the union of two fan graphs leaves
exactly the union of their old graphs.  This is the graph isomorphism used
after a facial-path cycle sum. -/
noncomputable def addNodeGraphSupOldIso
    {V : Type u} (G K : SimpleGraph V) (A B : Set V) :
    (RotationSystemFan.addNodeGraph G A ⊔
        RotationSystemFan.addNodeGraph K B).induce
      {z : Option V | z ≠ none} ≃g G ⊔ K where
  toFun z :=
    match hz : z.1 with
    | some v => v
    | none => False.elim (z.2 hz)
  invFun v := ⟨some v, Option.some_ne_none v⟩
  left_inv := by
    intro ⟨z, hz⟩
    cases z with
    | none => exact False.elim (hz rfl)
    | some v => rfl
  right_inv := by
    intro v
    rfl
  map_rel_iff' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    cases x with
    | none => exact False.elim (hx rfl)
    | some a =>
        cases y with
        | none => exact False.elim (hy rfl)
        | some b => rfl

/-- The oriented-dart list of a walk included into a supergraph is obtained by
including each oriented edge of the original list. -/
theorem walkMapLe_orientedDarts
    {V : Type u} {G H : SimpleGraph V} {s t : V}
    (h : G <= H) (p : G.Walk s t) :
    (p.mapLe h).darts.map (orientedEdgeDartEquiv (G := H)).symm =
      (p.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
        (liftOrientedEdge h) := by
  change
    (p.map (.ofLE h)).darts.map (orientedEdgeDartEquiv (G := H)).symm = _
  rw [SimpleGraph.Walk.darts_map, List.map_map, List.map_map]
  apply List.map_congr_left
  intro d _hd
  apply Subtype.ext
  rfl

/-- Graph-level form of the degree-two face splice.  The two crossed face
sectors are first merged in the predicate restriction of the old hypermap and
then transported to the explicit rotation system on the induced graph away
from `v`.  The returned equality records the old dart represented by every
dart of the new face boundary. -/
theorem exists_vertexDeletedFaceBoundary_of_two_crossed_faces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (x y : OrientedEdge G)
    (hx : x.tail = v) (hy : y.tail = v)
    (left right : List (OrientedEdge G))
    (hleft : left ≠ []) (hright : right ≠ [])
    (hleftSurvives :
      forall z : OrientedEdge G, z ∈ left ->
        z.tail ≠ v ∧ z.head ≠ v)
    (hrightSurvives :
      forall z : OrientedEdge G, z ∈ right ->
        z.tail ≠ v ∧ z.head ≠ v)
    (hnodup : (left ++ right).Nodup)
    (hleftPath : (R.toHypermap).FacePath x (left ++ [y.symm]))
    (hleftClose : (R.toHypermap).face y.symm = x)
    (hrightPath : (R.toHypermap).FacePath y (right ++ [x.symm]))
    (hrightClose : (R.toHypermap).face x.symm = y) :
    let D := RotationSystemVertexDeletion.vertexDeletedRotationSystem R v
    let phi :=
      RotationSystemVertexDeletion.vertexDeletedRotationSystem_toPredicateRestrictionIso
        R v
    Exists fun B : RotationSystemFan.FaceBoundary D.toHypermap =>
      ((B.first :: B.rest).map phi.toEquiv).map Subtype.val =
        left ++ right := by
  classical
  let H := (R.toHypermap).predicateRestriction
    (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
  let D := RotationSystemVertexDeletion.vertexDeletedRotationSystem R v
  let phi : Hypermap.Iso D.toHypermap H :=
    RotationSystemVertexDeletion.vertexDeletedRotationSystem_toPredicateRestrictionIso
      R v
  rcases
      RotationSystemVertexDeletion.predicateRestriction_exists_faceBoundary_of_two_crossed_faces
        R v x y hx hy left right hleft hright hleftSurvives
          hrightSurvives hnodup hleftPath hleftClose hrightPath hrightClose with
    ⟨C, hC⟩
  let C' : RotationSystemFan.FaceBoundary H := {
    first := C.first
    rest := C.rest
    path := C.path
    close := C.close
    nodup := C.nodup
  }
  let B : RotationSystemFan.FaceBoundary D.toHypermap :=
    C'.mapIso phi.symm
  refine ⟨B, ?_⟩
  change
    (((C'.first :: C'.rest).map phi.symm.toEquiv).map
      phi.toEquiv).map Subtype.val = left ++ right
  have hpoint (z : H.Dart) :
      phi.toEquiv (phi.symm.toEquiv z) = z :=
    phi.toEquiv.apply_symm_apply z
  have hroundtrip :
      ((C'.first :: C'.rest).map phi.symm.toEquiv).map phi.toEquiv =
        C'.first :: C'.rest := by
    rw [List.map_map]
    have hfun : phi.toEquiv ∘ phi.symm.toEquiv = id := by
      funext z
      exact hpoint z
    rw [hfun, List.map_id_fun]
    rfl
  rw [hroundtrip]
  simpa [C'] using hC

/-- Two facial cycles meeting at a vertex in crossed order merge to one
explicit face boundary when that vertex is deleted.  The hypotheses expose
the two cycle dart lists as the intervening surviving sectors bracketed by
the four crossed spokes; all face-path and closing equations are recovered
from faciality. -/
theorem exists_vertexDeletedFaceBoundary_of_crossed_facial_cycles
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (x y : OrientedEdge G)
    (hx : x.tail = v) (hy : y.tail = v)
    (left right : List (OrientedEdge G))
    (hleft : left ≠ []) (hright : right ≠ [])
    (hleftSurvives :
      forall z : OrientedEdge G, z ∈ left ->
        z.tail ≠ v ∧ z.head ≠ v)
    (hrightSurvives :
      forall z : OrientedEdge G, z ∈ right ->
        z.tail ≠ v ∧ z.head ≠ v)
    (hnodup : (left ++ right).Nodup)
    {r₁ r₂ : V}
    (c₁ : G.Walk r₁ r₁) (hc₁ : c₁.IsCycle)
    (c₂ : G.Walk r₂ r₂) (hc₂ : c₂.IsCycle)
    (hfac₁ : IsFacialCycle R c₁ hc₁)
    (hfac₂ : IsFacialCycle R c₂ hc₂)
    (hc₁Darts :
      c₁.darts.map (orientedEdgeDartEquiv (G := G)).symm =
        x :: left ++ [y.symm])
    (hc₂Darts :
      c₂.darts.map (orientedEdgeDartEquiv (G := G)).symm =
        y :: right ++ [x.symm]) :
    let D := RotationSystemVertexDeletion.vertexDeletedRotationSystem R v
    let phi :=
      RotationSystemVertexDeletion.vertexDeletedRotationSystem_toPredicateRestrictionIso
        R v
    Exists fun B : RotationSystemFan.FaceBoundary D.toHypermap =>
      ((B.first :: B.rest).map phi.toEquiv).map Subtype.val =
        left ++ right := by
  classical
  let B₁ : RotationSystemFan.FaceBoundary R.toHypermap :=
    RotationSystemFan.orderedFacialCycleBoundary R c₁ hc₁ hfac₁
  let B₂ : RotationSystemFan.FaceBoundary R.toHypermap :=
    RotationSystemFan.orderedFacialCycleBoundary R c₂ hc₂ hfac₂
  have hB₁List : B₁.first :: B₁.rest = x :: left ++ [y.symm] :=
    (RotationSystemFan.orderedFacialCycleBoundary_darts
      R c₁ hc₁ hfac₁).trans hc₁Darts
  have hB₂List : B₂.first :: B₂.rest = y :: right ++ [x.symm] :=
    (RotationSystemFan.orderedFacialCycleBoundary_darts
      R c₂ hc₂ hfac₂).trans hc₂Darts
  have hB₁First : B₁.first = x := (List.cons.inj hB₁List).1
  have hB₁Rest : B₁.rest = left ++ [y.symm] :=
    (List.cons.inj hB₁List).2
  have hB₂First : B₂.first = y := (List.cons.inj hB₂List).1
  have hB₂Rest : B₂.rest = right ++ [x.symm] :=
    (List.cons.inj hB₂List).2
  have hleftPath : (R.toHypermap).FacePath x (left ++ [y.symm]) := by
    simpa [hB₁First, hB₁Rest] using B₁.path
  have hrightPath : (R.toHypermap).FacePath y (right ++ [x.symm]) := by
    simpa [hB₂First, hB₂Rest] using B₂.path
  have hlastLeft :
      (x :: (left ++ [y.symm])).getLastD x = y.symm := by
    induction left generalizing x with
    | nil => rfl
    | cons z zs ih =>
        simp [List.getLastD]
  have hlastRight :
      (y :: (right ++ [x.symm])).getLastD y = x.symm := by
    induction right generalizing y with
    | nil => rfl
    | cons z zs ih =>
        simp [List.getLastD]
  have hleftClose : (R.toHypermap).face y.symm = x := by
    calc
      (R.toHypermap).face y.symm =
          (R.toHypermap).face ((B₁.first :: B₁.rest).getLastD B₁.first) := by
        rw [hB₁First, hB₁Rest]
        exact (congrArg (R.toHypermap).face hlastLeft).symm
      _ = B₁.first := B₁.close
      _ = x := hB₁First
  have hrightClose : (R.toHypermap).face x.symm = y := by
    calc
      (R.toHypermap).face x.symm =
          (R.toHypermap).face ((B₂.first :: B₂.rest).getLastD B₂.first) := by
        rw [hB₂First, hB₂Rest]
        exact (congrArg (R.toHypermap).face hlastRight).symm
      _ = B₂.first := B₂.close
      _ = y := hB₂First
  exact exists_vertexDeletedFaceBoundary_of_two_crossed_faces
    R v x y hx hy left right hleft hright hleftSurvives
      hrightSurvives hnodup hleftPath hleftClose hrightPath hrightClose

/-- Delete the common fresh vertex from two complementary fresh-node path
faces.  Their old-path sectors become one ordered face boundary in the
vertex-deleted cycle sum. -/
theorem exists_vertexDeletedFaceBoundary_of_fresh_path_faces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V}
    (A B : Set V) {s t : V}
    [DecidableRel
      (RotationSystemFan.addNodeGraph G A ⊔
        RotationSystemFan.addNodeGraph K B).Adj]
    (hsA : s ∈ A) (htA : t ∈ A)
    (hsB : s ∈ B) (htB : t ∈ B)
    (hst : s ≠ t)
    (a : G.Walk t s) (ha : a.IsPath)
    (b : K.Walk s t) (hb : b.IsPath)
    (U : RotationSystem
      (RotationSystemFan.addNodeGraph G A ⊔
        RotationSystemFan.addNodeGraph K B))
    (haFacial :
      IsFacialCycle U
        ((RotationSystemFan.addNodeGraphPathCycleAtNewIn
            G A htA hsA a).mapLe le_sup_left)
        ((RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
            A htA hsA hst.symm a ha).mapLe le_sup_left))
    (hbFacial :
      IsFacialCycle U
        ((RotationSystemFan.addNodeGraphPathCycleAtNewIn
            K B hsB htB b).mapLe le_sup_right)
        ((RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
            B hsB htB hst b hb).mapLe le_sup_right))
    (hnodup :
      let left :=
        ((a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
          (RotationSystemFan.addNodeGraphSomeOrientedEdge G A)).map
            (liftOrientedEdge (show
              RotationSystemFan.addNodeGraph G A <=
                RotationSystemFan.addNodeGraph G A ⊔
                  RotationSystemFan.addNodeGraph K B from le_sup_left))
      let right :=
        ((b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
          (RotationSystemFan.addNodeGraphSomeOrientedEdge K B)).map
            (liftOrientedEdge (show
              RotationSystemFan.addNodeGraph K B <=
                RotationSystemFan.addNodeGraph G A ⊔
                  RotationSystemFan.addNodeGraph K B from le_sup_right))
      (left ++ right).Nodup) :
    let H := RotationSystemFan.addNodeGraph G A ⊔
      RotationSystemFan.addNodeGraph K B
    let D := RotationSystemVertexDeletion.vertexDeletedRotationSystem U none
    let phi :=
      RotationSystemVertexDeletion.vertexDeletedRotationSystem_toPredicateRestrictionIso
        U none
    let left :=
      ((a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
        (RotationSystemFan.addNodeGraphSomeOrientedEdge G A)).map
          (liftOrientedEdge (show
            RotationSystemFan.addNodeGraph G A <= H from le_sup_left))
    let right :=
      ((b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
        (RotationSystemFan.addNodeGraphSomeOrientedEdge K B)).map
          (liftOrientedEdge (show
            RotationSystemFan.addNodeGraph K B <= H from le_sup_right))
    Exists fun C : RotationSystemFan.FaceBoundary D.toHypermap =>
      ((C.first :: C.rest).map phi.toEquiv).map Subtype.val =
        left ++ right := by
  classical
  let H₁ := RotationSystemFan.addNodeGraph G A
  let H₂ := RotationSystemFan.addNodeGraph K B
  let H := H₁ ⊔ H₂
  let left : List (OrientedEdge H) :=
    ((a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
      (RotationSystemFan.addNodeGraphSomeOrientedEdge G A)).map
        (liftOrientedEdge (show H₁ <= H from le_sup_left))
  let right : List (OrientedEdge H) :=
    ((b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
      (RotationSystemFan.addNodeGraphSomeOrientedEdge K B)).map
        (liftOrientedEdge (show H₂ <= H from le_sup_right))
  let x₁ : OrientedEdge H₁ :=
    ⟨(none, some t), by simp [H₁, RotationSystemFan.addNodeGraph, htA]⟩
  let y₂ : OrientedEdge H₂ :=
    ⟨(none, some s), by simp [H₂, RotationSystemFan.addNodeGraph, hsB]⟩
  let x : OrientedEdge H := liftOrientedEdge le_sup_left x₁
  let y : OrientedEdge H := liftOrientedEdge le_sup_right y₂
  have hx : x.tail = none := rfl
  have hy : y.tail = none := rfl
  have hleftNe : left ≠ [] := by
    have haNotNil : ¬ a.Nil := a.not_nil_of_ne hst.symm
    have haDarts : a.darts ≠ [] :=
      SimpleGraph.Walk.darts_eq_nil.not.mpr haNotNil
    simp [left, haDarts]
  have hrightNe : right ≠ [] := by
    have hbNotNil : ¬ b.Nil := b.not_nil_of_ne hst
    have hbDarts : b.darts ≠ [] :=
      SimpleGraph.Walk.darts_eq_nil.not.mpr hbNotNil
    simp [right, hbDarts]
  have hleftSurvives : forall z : OrientedEdge H, z ∈ left ->
      z.tail ≠ none ∧ z.head ≠ none := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨z₁, hz₁, rfl⟩
    rcases List.mem_map.mp hz₁ with ⟨e, _he, rfl⟩
    exact ⟨by simp, by simp⟩
  have hrightSurvives : forall z : OrientedEdge H, z ∈ right ->
      z.tail ≠ none ∧ z.head ≠ none := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨z₂, hz₂, rfl⟩
    rcases List.mem_map.mp hz₂ with ⟨e, _he, rfl⟩
    exact ⟨by simp, by simp⟩
  let c₁ :=
    (RotationSystemFan.addNodeGraphPathCycleAtNewIn G A htA hsA a).mapLe
      (show H₁ <= H from le_sup_left)
  let hc₁ :=
    (RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
      A htA hsA hst.symm a ha).mapLe
        (show H₁ <= H from le_sup_left)
  let c₂ :=
    (RotationSystemFan.addNodeGraphPathCycleAtNewIn K B hsB htB b).mapLe
      (show H₂ <= H from le_sup_right)
  let hc₂ :=
    (RotationSystemFan.addNodeGraphPathCycleAtNewIn_isCycle
      B hsB htB hst b hb).mapLe
        (show H₂ <= H from le_sup_right)
  have hc₁Darts :
      c₁.darts.map (orientedEdgeDartEquiv (G := H)).symm =
        x :: left ++ [y.symm] := by
    rw [show c₁ =
        (RotationSystemFan.addNodeGraphPathCycleAtNewIn G A htA hsA a).mapLe
          (show H₁ <= H from le_sup_left) by rfl,
      walkMapLe_orientedDarts,
      RotationSystemFan.addNodeGraphPathCycleAtNewIn_orientedDarts]
    simp only [List.map_cons, List.map_append]
    change x :: left ++ [_] = x :: left ++ [y.symm]
    congr 3
  have hc₂Darts :
      c₂.darts.map (orientedEdgeDartEquiv (G := H)).symm =
        y :: right ++ [x.symm] := by
    rw [show c₂ =
        (RotationSystemFan.addNodeGraphPathCycleAtNewIn K B hsB htB b).mapLe
          (show H₂ <= H from le_sup_right) by rfl,
      walkMapLe_orientedDarts,
      RotationSystemFan.addNodeGraphPathCycleAtNewIn_orientedDarts]
    simp only [List.map_cons, List.map_append]
    change y :: right ++ [_] = y :: right ++ [x.symm]
    congr 3
  exact exists_vertexDeletedFaceBoundary_of_crossed_facial_cycles
    U none x y hx hy left right hleftNe hrightNe hleftSurvives
      hrightSurvives hnodup c₁ hc₁ c₂ hc₂
        (by simpa [c₁, hc₁, H, H₁, H₂] using haFacial)
        (by simpa [c₂, hc₂, H, H₁, H₂] using hbFacial)
        hc₁Darts hc₂Darts


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
