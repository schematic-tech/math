import Schematic.Math.GraphTheory.Embedding.RotationSystemVertexDeletion.FacePaths

/-!
Merged face boundaries produced by deleting a vertex.
-/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemVertexDeletion

/-- Low-level ordered face boundary used below the fan module in the import
graph.  `RotationSystemFan.FaceBoundary` has the same fields and packages this
data at the higher API layer. -/
structure PredicateRestrictionFaceBoundary (H : Hypermap.{u}) where
  first : H.Dart
  rest : List H.Dart
  path : H.FacePath first rest
  close : H.face ((first :: rest).getLastD first) = first
  nodup : (first :: rest).Nodup

/-- Deleting a vertex merges two explicitly crossed incident faces.  The two
old face boundaries start with outgoing darts `x` and `y` at the deleted
vertex and end with `y.symm` and `x.symm`, respectively.  If their intervening
dart lists survive and are jointly nodup, their concatenation is an exact face
boundary of the restricted hypermap.

This is the degree-two local operation needed for disk gluing.  It deliberately
does not assume that the ambient graph is two-connected or that every node
orbit is nontrivial; isolated ambient vertices and unrelated leaf components
are irrelevant to the two displayed faces. -/
theorem predicateRestriction_exists_faceBoundary_of_two_crossed_faces
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
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    Exists fun B : PredicateRestrictionFaceBoundary H =>
      (B.first :: B.rest).map Subtype.val = left ++ right := by
  classical
  cases left with
  | nil => exact (hleft rfl).elim
  | cons a as =>
    cases right with
    | nil => exact (hright rfl).elim
    | cons b bs =>
      let old := R.toHypermap
      let H := old.predicateRestriction
        (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
      have ha : a.tail ≠ v ∧ a.head ≠ v :=
        hleftSurvives a (by simp)
      have hb : b.tail ≠ v ∧ b.head ≠ v :=
        hrightSurvives b (by simp)
      have has :
          forall z : OrientedEdge G, z ∈ as ->
            z.tail ≠ v ∧ z.head ≠ v := by
        intro z hz
        exact hleftSurvives z (by simp [hz])
      have hbs :
          forall z : OrientedEdge G, z ∈ bs ->
            z.tail ≠ v ∧ z.head ≠ v := by
        intro z hz
        exact hrightSurvives z (by simp [hz])
      let aD : H.Dart := ⟨a, ha⟩
      let bD : H.Dart := ⟨b, hb⟩
      let asD : List H.Dart := survivingDartList v as has
      let bsD : List H.Dart := survivingDartList v bs hbs
      have hleftTail : old.FacePath a (as ++ [y.symm]) :=
        ((Hypermap.FacePath.cons (G := old) x a (as ++ [y.symm])).mp
          (by simpa [old] using hleftPath)).2
      have hrightTail : old.FacePath b (bs ++ [x.symm]) :=
        ((Hypermap.FacePath.cons (G := old) y b (bs ++ [x.symm])).mp
          (by simpa [old] using hrightPath)).2
      rcases Hypermap.FacePath.split_append_cons
          (G := old) (p := as) (y := y.symm) (q := []) hleftTail with
        ⟨hpathA, hlastA, _⟩
      rcases Hypermap.FacePath.split_append_cons
          (G := old) (p := bs) (y := x.symm) (q := []) hrightTail with
        ⟨hpathB, hlastB, _⟩
      have hcloseX : old.face y.symm = x := by
        simpa [old] using hleftClose
      have hcloseY : old.face x.symm = y := by
        simpa [old] using hrightClose
      have hnodeX : R.node x = y := by
        have h := old.node_face_eq_edge_symm y.symm
        simpa [old, hcloseX] using h
      have hnodeY : R.node y = x := by
        have h := old.node_face_eq_edge_symm x.symm
        simpa [old, hcloseY] using h
      have hfaceX : old.face x = a :=
        ((Hypermap.FacePath.cons (G := old) x a (as ++ [y.symm])).mp
          (by simpa [old] using hleftPath)).1
      have hfaceY : old.face y = b :=
        ((Hypermap.FacePath.cons (G := old) y b (bs ++ [x.symm])).mp
          (by simpa [old] using hrightPath)).1
      have hpathAH : H.FacePath aD asD := by
        simpa [H, old, aD, asD, survivingDartList] using
          predicateRestriction_facePath_of_facePath_survives
            R v hpathA (fun z hz =>
              hleftSurvives z (by simp [hz]))
      have hpathBH : H.FacePath bD bsD := by
        simpa [H, old, bD, bsD, survivingDartList] using
          predicateRestriction_facePath_of_facePath_survives
            R v hpathB (fun z hz =>
              hrightSurvives z (by simp [hz]))
      let wA : OrientedEdge G := (a :: as).getLastD a
      let wB : OrientedEdge G := (b :: bs).getLastD b
      have hwA : wA.tail ≠ v ∧ wA.head ≠ v := by
        exact hleftSurvives wA (by
          change (a :: as).getLastD a ∈ a :: as
          rw [List.getLastD_cons]
          exact List.getLastD_mem_cons)
      have hwB : wB.tail ≠ v ∧ wB.head ≠ v := by
        exact hrightSurvives wB (by
          change (b :: bs).getLastD b ∈ b :: bs
          rw [List.getLastD_cons]
          exact List.getLastD_mem_cons)
      let wAD : H.Dart := ⟨wA, hwA⟩
      let wBD : H.Dart := ⟨wB, hwB⟩
      have hmapA : (aD :: asD).map Subtype.val = a :: as := by
        change a :: (survivingDartList v as has).map Subtype.val = a :: as
        rw [survivingDartList_map_val]
      have hmapB : (bD :: bsD).map Subtype.val = b :: bs := by
        change b :: (survivingDartList v bs hbs).map Subtype.val = b :: bs
        rw [survivingDartList_map_val]
      have hmapAs : asD.map Subtype.val = as := by
        change (survivingDartList v as has).map Subtype.val = as
        exact survivingDartList_map_val v as has
      have hmapBs : bsD.map Subtype.val = bs := by
        change (survivingDartList v bs hbs).map Subtype.val = bs
        exact survivingDartList_map_val v bs hbs
      have hlastAD : (aD :: asD).getLastD aD = wAD := by
        apply Subtype.ext
        change ((aD :: asD).getLastD aD).1 = wA
        have hlastMap :=
          List.getLastD_map
            (f := Subtype.val) (l := aD :: asD) (a := aD)
        calc
          ((aD :: asD).getLastD aD).1 =
              ((aD :: asD).map Subtype.val).getLastD aD.1 :=
            hlastMap.symm
          _ = (a :: as).getLastD a := by rw [hmapA]; rfl
          _ = wA := rfl
      have hlastBD : (bD :: bsD).getLastD bD = wBD := by
        apply Subtype.ext
        change ((bD :: bsD).getLastD bD).1 = wB
        have hlastMap :=
          List.getLastD_map
            (f := Subtype.val) (l := bD :: bsD) (a := bD)
        calc
          ((bD :: bsD).getLastD bD).1 =
              ((bD :: bsD).map Subtype.val).getLastD bD.1 :=
            hlastMap.symm
          _ = (b :: bs).getLastD b := by rw [hmapB]; rfl
          _ = wB := rfl
      have hfaceSymmX : old.face.symm x = y.symm := by
        rw [← hcloseX]
        simp
      have hfaceSymmY : old.face.symm y = x.symm := by
        rw [← hcloseY]
        simp
      have htargetX :
          let target := old.face (R.node x)
          target.tail ≠ v ∧ target.head ≠ v := by
        simpa [hnodeX, hfaceY] using hb
      have htargetY :
          let target := old.face (R.node y)
          target.tail ≠ v ∧ target.head ≠ v := by
        simpa [hnodeY, hfaceX] using ha
      have hjumpAB : H.face wAD = bD := by
        have h :=
          predicateRestriction_face_after_deleted_pair_of_target_survives
            R v x wA hx hwA
              (hlastA.trans hfaceSymmX.symm) htargetX
        apply Subtype.ext
        simpa [H, old, wAD, bD, hnodeX, hfaceY] using
          congrArg Subtype.val h
      have hjumpBA : H.face wBD = aD := by
        have h :=
          predicateRestriction_face_after_deleted_pair_of_target_survives
            R v y wB hy hwB
              (hlastB.trans hfaceSymmY.symm) htargetY
        apply Subtype.ext
        simpa [H, old, wBD, aD, hnodeY, hfaceX] using
          congrArg Subtype.val h
      have hmergedPath : H.FacePath aD (asD ++ bD :: bsD) :=
        Hypermap.FacePath.append_cons
          (G := H) hpathAH hlastAD hjumpAB hpathBH
      have hmergedClose :
          H.face ((aD :: (asD ++ bD :: bsD)).getLastD aD) = aD := by
        rw [Hypermap.list_getLastD_cons_append_of_getLast
          aD wAD asD (bD :: bsD) hlastAD]
        change H.face ((bD :: bsD).getLastD bD) = aD
        rw [hlastBD]
        exact hjumpBA
      have hfullMap :
          (aD :: (asD ++ bD :: bsD)).map Subtype.val =
            (a :: as) ++ (b :: bs) := by
        calc
          (aD :: (asD ++ bD :: bsD)).map Subtype.val =
              ((aD :: asD) ++ (bD :: bsD)).map Subtype.val := by
            simp
          _ = (aD :: asD).map Subtype.val ++
                (bD :: bsD).map Subtype.val := by
            exact List.map_append
          _ = (a :: as) ++ (b :: bs) := by
            rw [hmapA, hmapB]
            rfl
      have hmergedNodup :
          (aD :: (asD ++ bD :: bsD)).Nodup := by
        apply (List.nodup_map_iff Subtype.val_injective).mp
        rw [hfullMap]
        exact hnodup
      let B : PredicateRestrictionFaceBoundary H := {
        first := aD
        rest := asD ++ bD :: bsD
        path := hmergedPath
        close := hmergedClose
        nodup := hmergedNodup
      }
      exact ⟨B, by simpa [B] using hfullMap⟩

/-- The final jump in Coq `wheel_segment`: after an old face prefix reaches
the predecessor of `face⁻¹ x`, deleting the vertex of `x` skips
`face⁻¹ x, x` and enters the face sector following `node x`. -/
theorem predicateRestriction_face_after_deleted_pair
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (R : RotationSystem G) (v : V)
    (hnode : ∀ d : OrientedEdge G, R.node d ≠ d)
    (x w : OrientedEdge G)
    (hx : x.tail = v)
    (hw : w.tail ≠ v ∧ w.head ≠ v)
    (hfaceW :
      (R.toHypermap).face w = (R.toHypermap).face.symm x) :
    let H := (R.toHypermap).predicateRestriction
      (fun e : OrientedEdge G => e.tail ≠ v ∧ e.head ≠ v)
    let target := (R.toHypermap).face (R.node x)
    H.face (⟨w, hw⟩ : H.Dart) =
      (⟨target, facePort_survives R v hnode (R.node x)
        ((R.node_tail x).trans hx)⟩ : H.Dart) := by
  exact
    predicateRestriction_face_after_deleted_pair_of_target_survives
      R v x w hx hw hfaceW
        (facePort_survives R v hnode (R.node x)
          ((R.node_tail x).trans hx))


end RotationSystemVertexDeletion

end FourColor

end Schematic.Math.GraphTheory
