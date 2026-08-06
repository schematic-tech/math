import Schematic.Math.GraphTheory.Embedding.RotationSystemPathGluing.VertexDeletedFaces

/-! Transporting a facial path append to the union of the old graphs. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemGluing

open RotationSystemFan

/-- Delete the auxiliary vertex used to close two oppositely oriented facial
paths, transport the resulting rotation to the union of the old graphs, and
retain the concatenated old paths as one facial cycle. -/
theorem exists_oldUnion_facialAppend_of_fresh_path_faces
    {V : Type u} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V}
    (A B : Set V) {s t : V}
    [DecidableRel
      (addNodeGraph G A ⊔ addNodeGraph K B).Adj]
    [DecidableRel (G ⊔ K).Adj]
    (hsA : s ∈ A) (htA : t ∈ A)
    (hsB : s ∈ B) (htB : t ∈ B)
    (hst : s ≠ t)
    (a : G.Walk t s) (ha : a.IsPath)
    (b : K.Walk s t) (hb : b.IsPath)
    (U : RotationSystem (addNodeGraph G A ⊔ addNodeGraph K B))
    (hU : U.toHypermap.dual.EulerPlanar)
    (haFacial :
      IsFacialCycle U
        ((addNodeGraphPathCycleAtNewIn G A htA hsA a).mapLe le_sup_left)
        ((addNodeGraphPathCycleAtNewIn_isCycle
            A htA hsA hst.symm a ha).mapLe le_sup_left))
    (hbFacial :
      IsFacialCycle U
        ((addNodeGraphPathCycleAtNewIn K B hsB htB b).mapLe le_sup_right)
        ((addNodeGraphPathCycleAtNewIn_isCycle
            B hsB htB hst b hb).mapLe le_sup_right))
    (hnodup :
      let H := addNodeGraph G A ⊔ addNodeGraph K B
      let left :=
        ((a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
          (addNodeGraphSomeOrientedEdge G A)).map
            (liftOrientedEdge (show addNodeGraph G A ≤ H from le_sup_left))
      let right :=
        ((b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
          (addNodeGraphSomeOrientedEdge K B)).map
            (liftOrientedEdge (show addNodeGraph K B ≤ H from le_sup_right))
      (left ++ right).Nodup)
    (hc :
      ((a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
        (b.mapLe (show K ≤ G ⊔ K from le_sup_right))).IsCycle) :
    Exists fun R : RotationSystem (G ⊔ K) =>
      R.toHypermap.dual.EulerPlanar ∧
        IsFacialCycle R
          ((a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
            (b.mapLe (show K ≤ G ⊔ K from le_sup_right))) hc := by
  classical
  let H := addNodeGraph G A ⊔ addNodeGraph K B
  let D := RotationSystemVertexDeletion.vertexDeletedRotationSystem U none
  let phi :=
    RotationSystemVertexDeletion.vertexDeletedRotationSystem_toPredicateRestrictionIso
      U none
  let e := addNodeGraphSupOldIso G K A B
  let R : RotationSystem (G ⊔ K) := RotationSystem.ofIso e.symm D
  let psi : Hypermap.Iso R.toHypermap D.toHypermap :=
    RotationSystem.ofIso_toHypermapIso e.symm D
  let c : (G ⊔ K).Walk t t :=
    (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
      (b.mapLe (show K ≤ G ⊔ K from le_sup_right))
  change c.IsCycle at hc
  have hD : D.toHypermap.dual.EulerPlanar :=
    RotationSystemVertexDeletion.vertexDeletedRotationSystem_dual_eulerPlanar
      U none hU
  have hR : R.toHypermap.dual.EulerPlanar := by
    have hDprimal : D.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := D.toHypermap)).mp hD
    have hRprimal : R.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hDprimal
    exact (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mpr hRprimal
  rcases exists_vertexDeletedFaceBoundary_of_fresh_path_faces
      A B hsA htA hsB htB hst a ha b hb U haFacial hbFacial hnodup with
    ⟨C, hC⟩
  let C' : FaceBoundary R.toHypermap := C.mapIso psi.symm
  let oldToDeleted : OrientedEdge (G ⊔ K) ≃
      OrientedEdge (H.induce {z : Option V | z ≠ none}) :=
    orientedEdgeEquivOfGraphIso e.symm
  let oldToFresh : OrientedEdge (G ⊔ K) → OrientedEdge H :=
    fun d => (phi.toEquiv (oldToDeleted d)).1
  have hOldToFreshInjective : Function.Injective oldToFresh := by
    intro d f hdf
    apply oldToDeleted.injective
    apply phi.toEquiv.injective
    apply Subtype.ext
    exact hdf
  have hC'map :
      (C'.first :: C'.rest).map oldToFresh =
        let left :=
          ((a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
            (addNodeGraphSomeOrientedEdge G A)).map
              (liftOrientedEdge
                (show addNodeGraph G A ≤ H from le_sup_left))
        let right :=
          ((b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
            (addNodeGraphSomeOrientedEdge K B)).map
              (liftOrientedEdge
                (show addNodeGraph K B ≤ H from le_sup_right))
        left ++ right := by
    calc
      ((C.first :: C.rest).map psi.symm.toEquiv).map oldToFresh =
          (C.first :: C.rest).map (fun d => (phi.toEquiv d).1) := by
        have hmap (l : List D.toHypermap.Dart) :
            (l.map psi.symm.toEquiv).map oldToFresh =
              l.map (fun d => (phi.toEquiv d).1) := by
          induction l with
          | nil => rfl
          | cons d l ih =>
              change
                oldToFresh (psi.symm.toEquiv d) ::
                    (l.map psi.symm.toEquiv).map oldToFresh =
                  (phi.toEquiv d).1 ::
                    l.map (fun z => (phi.toEquiv z).1)
              apply congrArg₂ (fun x xs => x :: xs)
              · change
                  (phi.toEquiv (oldToDeleted (psi.symm.toEquiv d))).1 =
                    (phi.toEquiv d).1
                rw [show oldToDeleted (psi.symm.toEquiv d) = d by
                  exact psi.toEquiv.apply_symm_apply d]
              · exact ih
        exact hmap (C.first :: C.rest)
      _ = _ := by
        have hmap (l : List D.toHypermap.Dart) :
            l.map (fun d => (phi.toEquiv d).1) =
              (l.map phi.toEquiv).map Subtype.val := by
          induction l with
          | nil => rfl
          | cons d l ih =>
              change
                (phi.toEquiv d).1 :: l.map (fun z => (phi.toEquiv z).1) =
                  (phi.toEquiv d).1 ::
                    (l.map phi.toEquiv).map Subtype.val
              exact congrArg (List.cons (phi.toEquiv d).1) ih
        rw [hmap]
        exact hC
  have hcMap :
      (c.darts.map (orientedEdgeDartEquiv (G := G ⊔ K)).symm).map
          oldToFresh =
        let left :=
          ((a.darts.map (orientedEdgeDartEquiv (G := G)).symm).map
            (addNodeGraphSomeOrientedEdge G A)).map
              (liftOrientedEdge
                (show addNodeGraph G A ≤ H from le_sup_left))
        let right :=
          ((b.darts.map (orientedEdgeDartEquiv (G := K)).symm).map
            (addNodeGraphSomeOrientedEdge K B)).map
              (liftOrientedEdge
                (show addNodeGraph K B ≤ H from le_sup_right))
        left ++ right := by
    rw [show c =
        (a.mapLe (show G ≤ G ⊔ K from le_sup_left)).append
          (b.mapLe (show K ≤ G ⊔ K from le_sup_right)) by rfl]
    rw [SimpleGraph.Walk.darts_append, List.map_append, List.map_append]
    rw [walkMapLe_orientedDarts, walkMapLe_orientedDarts]
    simp only [List.map_map]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro d hd
      apply Subtype.ext
      rfl
    · apply List.map_congr_left
      intro d hd
      apply Subtype.ext
      rfl
  have hlist :
      C'.first :: C'.rest =
        c.darts.map (orientedEdgeDartEquiv (G := G ⊔ K)).symm := by
    apply (List.map_inj_right (fun x y hxy =>
      hOldToFreshInjective hxy)).mp
    exact hC'map.trans hcMap.symm
  let E : OrientedEdge (G ⊔ K) ≃ (G ⊔ K).Dart :=
    orientedEdgeDartEquiv (G := G ⊔ K)
  let ds : List (OrientedEdge (G ⊔ K)) := c.darts.map E.symm
  have hcDartsNe : c.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hc.not_nil
  have hdsNe : ds ≠ [] := by simp [ds, hcDartsNe]
  have hdsFirst : ds.head hdsNe = cycleFirstDart c hc := by
    apply E.injective
    rw [List.head_map, E.apply_symm_apply]
    rw [← c.firstDart_eq_head_darts hc.not_nil]
    apply SimpleGraph.Dart.ext
    exact calc
      (c.firstDart hc.not_nil).toProd = (t, c.snd) :=
        c.firstDart_toProd hc.not_nil
      _ = (E (cycleFirstDart c hc)).toProd := by
        apply Prod.ext
        · exact (cycleFirstDart_tail c hc).symm
        · rfl
  have hdsEq : ds = cycleFirstDart c hc :: ds.tail := by
    calc
      ds = ds.head hdsNe :: ds.tail := (List.cons_head_tail hdsNe).symm
      _ = cycleFirstDart c hc :: ds.tail := by rw [hdsFirst]
  have hfirst : C'.first = cycleFirstDart c hc := by
    have hlist' : C'.first :: C'.rest = ds := by
      simpa [ds, E] using hlist
    rw [hdsEq] at hlist'
    exact (List.cons.inj hlist').1
  refine ⟨R, hR, ?_⟩
  simpa [c] using C'.isFacialCycle_of_eq_cycleDarts c hc hfirst hlist


end RotationSystemGluing
end FourColor
end Schematic.Math.GraphTheory
