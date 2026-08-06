import Schematic.Math.GraphTheory.Embedding.RotationSystemFaceCrossing.Trimming

/-! The Jordan contradiction forced by crossing face contours. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v

/-- The two contours selected from same-oriented theta ports force a
Moebius path.  Unlike Coq's globally two-connected `two_connected_cyle`
statement, the connector is trimmed first; its contacts split the face
cycle, and the branch contour is then trimmed across those two new arcs.
This absorbs arbitrary extra ambient contacts with the branch vertex. -/
theorem FaceOrbitCrossingArcs.false_of_jordan
    {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    {R : RotationSystem H}
    {e : OrientedEdge H}
    {D : FaceOrbitCrossingData R e}
    (A : FaceOrbitCrossingArcs D)
    (hJ : (R.toHypermap).Jordan) :
    False := by
  classical
  rcases A.exists_trimmed with ⟨T⟩
  have hcL_ne_x : T.connectorLeft ≠ D.x := by
    intro h
    exact T.connector_tail_ne T.connectorLeft (by simp)
      (by simpa [h] using D.x_tail)
  have hcR_ne_y : T.connectorRight ≠ D.y := by
    intro h
    exact T.connector_tail_ne T.connectorRight (by simp)
      (by simpa [h] using D.y_tail)
  have hcL_left : T.connectorLeft ∈ A.left := by
    have hmem := T.connectorLeft_mem
    rw [List.mem_cons] at hmem
    exact hmem.resolve_left hcL_ne_x
  have hcR_right : T.connectorRight ∈ A.right := by
    have hmem := T.connectorRight_mem
    rw [List.mem_cons] at hmem
    exact hmem.resolve_left hcR_ne_y
  rcases (List.mem_iff_append).1 hcL_left with
    ⟨leftPre, leftPost, hleftSplit⟩
  rcases (List.mem_iff_append).1 hcR_right with
    ⟨rightPre, rightPost, hrightSplit⟩
  let arcATail : List (OrientedEdge H) :=
    leftPost ++ D.y :: rightPre
  let arcBTail : List (OrientedEdge H) :=
    rightPost ++ D.x :: leftPre
  have hcycleX :
      (R.toHypermap).FacePath D.x
        ((A.left ++ D.y :: A.right) ++ [D.x]) := by
    have hleftLast :
        (D.x :: (A.left ++ [D.y])).getLastD D.x = D.y := by
      simp [List.getLastD]
    have happend :
        (R.toHypermap).FacePath D.x
          ((A.left ++ [D.y]) ++ (A.right ++ [D.x])) :=
      Hypermap.FacePath.append
        (G := R.toHypermap) A.left_path hleftLast A.right_path
    simpa only [List.append_assoc, List.singleton_append] using happend
  have hsplitAtCL :
      A.left ++ D.y :: A.right =
        leftPre ++ T.connectorLeft ::
          (arcATail ++ T.connectorRight :: rightPost) := by
    simp [hleftSplit, hrightSplit, arcATail, List.append_assoc]
  have hcycleCL :
      (R.toHypermap).FacePath T.connectorLeft
        ((arcATail ++ T.connectorRight :: arcBTail) ++
          [T.connectorLeft]) := by
    have hrot :=
      Hypermap.FacePath.rotate_closed_of_eq
        (G := R.toHypermap) hcycleX hsplitAtCL
    have hcycleListEq :
        ((arcATail ++ T.connectorRight :: arcBTail) ++
            [T.connectorLeft]) =
          (arcATail ++ T.connectorRight :: rightPost) ++
            D.x :: leftPre ++ [T.connectorLeft] := by
      simp only [arcBTail, List.append_assoc, List.cons_append]
    rw [hcycleListEq]
    exact hrot
  have hPQ :
      ((D.x :: leftPre) ++
        (T.connectorLeft :: arcATail ++
          T.connectorRight :: rightPost)).Nodup := by
    simpa [hleftSplit, hrightSplit, arcATail, List.append_assoc] using
      A.orbit_nodup
  have hQP :
      ((T.connectorLeft :: arcATail ++
          T.connectorRight :: rightPost) ++
        (D.x :: leftPre)).Nodup := by
    rcases List.nodup_append.mp hPQ with ⟨hP, hQ, hPQdisj⟩
    exact List.nodup_append.mpr
      ⟨hQ, hP, by
        intro a ha b hb hab
        exact hPQdisj b hb a ha hab.symm⟩
  have hcycleCLNodup :
      (T.connectorLeft :: arcATail ++
        T.connectorRight :: arcBTail).Nodup := by
    simpa [arcBTail, List.append_assoc] using hQP
  let arcA : Set (OrientedEdge H) :=
    {z | z ∈ T.connectorLeft :: arcATail}
  let arcB : Set (OrientedEdge H) :=
    {z | z ∈ T.connectorRight :: arcBTail}
  have hArcDisjoint : Disjoint arcA arcB := by
    have hparts :
        ((T.connectorLeft :: arcATail) ++
          (T.connectorRight :: arcBTail)).Nodup := by
      simpa [List.cons_append, List.append_assoc] using hcycleCLNodup
    rw [Set.disjoint_left]
    intro z hzA hzB
    exact (List.nodup_append.mp hparts).2.2 z hzA z hzB rfl
  have hyArcA : D.y ∈ arcA := by
    simp [arcA, arcATail]
  have hxArcB : D.x ∈ arcB := by
    simp [arcB, arcBTail]
  rcases R.toHypermap_exists_short_cPath_of_same_tail_controlled
      (e := D.y) (f := D.x)
      (D.y_tail.trans D.x_tail.symm) with
    ⟨nodePath, hnodePath, hnodeLast, hnodeNodup, hnodeTail⟩
  rcases Hypermap.CPath.exists_trimmed_between_disjoint
      (G := R.toHypermap)
      (A := arcA) (B := arcB)
      hnodePath hnodeLast hnodeNodup
      hyArcA hxArcB hArcDisjoint with
    ⟨nodeA, nodeB, nodeMiddle,
      hnodeAArc, hnodeBArc, hnodeTrimmed, hnodeTrimmedNodup,
      hnodeMiddleAvoid, hnodeSub⟩
  change OrientedEdge H at nodeA nodeB
  change List (OrientedEdge H) at nodeMiddle
  have hnodeTailBranch :
      ∀ z : OrientedEdge H,
        z ∈ nodeA :: nodeMiddle ++ [nodeB] →
          z.tail = D.branch := by
    intro z hz
    exact (hnodeTail z (hnodeSub z hz)).trans D.y_tail
  have hnodeA_ne_cL : nodeA ≠ T.connectorLeft := by
    intro h
    exact T.connector_tail_ne T.connectorLeft
      (by simp)
      (by simpa [h] using
        hnodeTailBranch nodeA (List.mem_cons_self))
  have hnodeB_ne_cR : nodeB ≠ T.connectorRight := by
    intro h
    exact T.connector_tail_ne T.connectorRight
      (List.mem_cons_self)
      (by simpa [h] using
        hnodeTailBranch nodeB (by simp))
  have hnodeA_tail : nodeA ∈ arcATail := by
    change nodeA ∈ T.connectorLeft :: arcATail at hnodeAArc
    exact (List.mem_cons.mp hnodeAArc).resolve_left hnodeA_ne_cL
  have hnodeB_tail : nodeB ∈ arcBTail := by
    change nodeB ∈ T.connectorRight :: arcBTail at hnodeBArc
    exact (List.mem_cons.mp hnodeBArc).resolve_left hnodeB_ne_cR
  rcases (List.mem_iff_append).1 hnodeA_tail with
    ⟨aPre, aPost, hASplit⟩
  rcases (List.mem_iff_append).1 hnodeB_tail with
    ⟨bPre, bPost, hBSplit⟩
  have hsplitAtNodeB :
      arcATail ++ T.connectorRight :: arcBTail =
        (arcATail ++ T.connectorRight :: bPre) ++
          nodeB :: bPost := by
    simp [hBSplit, List.append_assoc]
  have hcycleNodeB :
      (R.toHypermap).FacePath nodeB
        (bPost ++ T.connectorLeft ::
          (arcATail ++ T.connectorRight :: bPre) ++ [nodeB]) := by
    exact Hypermap.FacePath.rotate_closed_of_eq
      (G := R.toHypermap) hcycleCL hsplitAtNodeB
  let faceSegment : List (OrientedEdge H) :=
    (bPost ++ T.connectorLeft ::
      aPre ++ nodeA :: aPost) ++ [T.connectorRight]
  have hcycleNodeBSplit :
      (R.toHypermap).FacePath nodeB
        ((bPost ++ T.connectorLeft ::
            aPre ++ nodeA :: aPost) ++
          T.connectorRight :: (bPre ++ [nodeB])) := by
    simpa [faceSegment, hASplit, List.append_assoc] using hcycleNodeB
  have hfaceSegment :
      (R.toHypermap).FacePath nodeB faceSegment := by
    rcases Hypermap.FacePath.prefix_append_singleton_of_split
        (G := R.toHypermap) hcycleNodeBSplit with
      ⟨hprefix, _hlast, _hsuffix⟩
    change
      (R.toHypermap).FacePath nodeB
        ((bPost ++ T.connectorLeft ::
          aPre ++ nodeA :: aPost) ++ [T.connectorRight])
    exact hprefix
  have hfaceSegmentLast :
      (nodeB :: faceSegment).getLastD nodeB =
        T.connectorRight := by
    simp [faceSegment, List.getLastD]
  have hcycleAsPQ :
      ((T.connectorLeft :: arcATail ++
          T.connectorRight :: bPre) ++
        (nodeB :: bPost)).Nodup := by
    simpa [hBSplit, List.append_assoc] using hcycleCLNodup
  have hcycleAtNodeBNodup :
      ((nodeB :: bPost) ++
        (T.connectorLeft :: arcATail ++
          T.connectorRight :: bPre)).Nodup := by
    rcases List.nodup_append.mp hcycleAsPQ with
      ⟨hP, hQ, hPQdisj⟩
    exact List.nodup_append.mpr
      ⟨hQ, hP, by
        intro a ha b hb hab
        exact hPQdisj b hb a ha hab.symm⟩
  have hfaceSegmentNodup :
      (nodeB :: faceSegment).Nodup := by
    have hprefix :
        (nodeB :: faceSegment) <+:
          ((nodeB :: bPost) ++
            (T.connectorLeft :: arcATail ++
              T.connectorRight :: bPre)) := by
      refine ⟨bPre, ?_⟩
      simp [faceSegment, hASplit, List.append_assoc]
    exact hprefix.nodup hcycleAtNodeBNodup
  have hcrossOrder :
      Hypermap.ListMemBeforeEq faceSegment T.connectorLeft nodeA := by
    have hmem :
        nodeA ∈
          T.connectorLeft ::
            aPre ++ nodeA :: aPost ++ [T.connectorRight] := by
      simp
    have hlocal :
        Hypermap.ListMemBeforeEq
          (T.connectorLeft ::
            aPre ++ nodeA :: aPost ++ [T.connectorRight])
          T.connectorLeft nodeA :=
      Hypermap.ListMemBeforeEq.cons_self _ _ _ hmem
    simpa [faceSegment, List.append_assoc] using
      Hypermap.ListMemBeforeEq.append_right bPost hlocal
  have hArcOrbit :
      ∀ {z : OrientedEdge H},
        PermReachable (R.toHypermap).face D.x z →
          z ∈ arcA ∨ z ∈ arcB := by
    intro z hz
    have hzFull := (A.orbit_membership z).2 hz
    rcases List.mem_append.mp hzFull with hzLeftArc | hzRightArc
    · rw [List.mem_cons] at hzLeftArc
      rcases hzLeftArc with rfl | hzLeft
      · right
        change D.x ∈ T.connectorRight :: arcBTail
        simp [arcBTail]
      · rw [hleftSplit] at hzLeft
        rcases List.mem_append.mp hzLeft with hzPre | hzCLPost
        · right
          change z ∈ T.connectorRight :: arcBTail
          simp [arcBTail, hzPre]
        · rw [List.mem_cons] at hzCLPost
          rcases hzCLPost with rfl | hzPost
          · left
            change T.connectorLeft ∈ T.connectorLeft :: arcATail
            simp
          · left
            change z ∈ T.connectorLeft :: arcATail
            simp [arcATail, hzPost]
    · rw [List.mem_cons] at hzRightArc
      rcases hzRightArc with rfl | hzRight
      · left
        change D.y ∈ T.connectorLeft :: arcATail
        simp [arcATail]
      · rw [hrightSplit] at hzRight
        rcases List.mem_append.mp hzRight with hzPre | hzCRPost
        · left
          change z ∈ T.connectorLeft :: arcATail
          simp [arcATail, hzPre]
        · rw [List.mem_cons] at hzCRPost
          rcases hzCRPost with rfl | hzPost
          · right
            change
              T.connectorRight ∈ T.connectorRight :: arcBTail
            simp
          · right
            change z ∈ T.connectorRight :: arcBTail
            simp [arcBTail, hzPost]
  have hOriginalOrbit :
      ∀ {z : OrientedEdge H},
        PermReachable (R.toHypermap).face D.x z →
          z ∈ D.x :: A.left ∨ z ∈ D.y :: A.right := by
    intro z hz
    have hzFull := (A.orbit_membership z).2 hz
    have :
        z ∈ (D.x :: A.left) ++ (D.y :: A.right) := by
      simpa [List.cons_append, List.append_assoc] using hzFull
    exact List.mem_append.mp this
  have hnodeBReach :
      PermReachable (R.toHypermap).face D.x nodeB := by
    apply (A.orbit_membership nodeB).1
    have hnodeBFull :
        nodeB ∈ (D.x :: A.left) ++ (D.y :: A.right) := by
      rw [hleftSplit, hrightSplit]
      have htail :
          nodeB ∈ rightPost ++ D.x :: leftPre := by
        simpa only [arcBTail] using hnodeB_tail
      rcases List.mem_append.mp htail with hRightPost | hXLeftPre
      · apply List.mem_append_right (D.x :: leftPre ++
          T.connectorLeft :: leftPost)
        apply List.mem_cons_of_mem D.y
        exact List.mem_append_right rightPre
          (List.mem_cons_of_mem T.connectorRight hRightPost)
      · rw [List.mem_cons] at hXLeftPre
        rcases hXLeftPre with rfl | hLeftPre
        · exact List.mem_append_left _ (List.mem_cons_self)
        · apply List.mem_append_left
            (D.y :: rightPre ++ T.connectorRight :: rightPost)
          apply List.mem_cons_of_mem D.x
          exact List.mem_append_left
            (T.connectorLeft :: leftPost) hLeftPre
    simpa only [List.cons_append, List.append_assoc] using hnodeBFull
  let successors : List (OrientedEdge H) :=
    nodeMiddle ++ [nodeB]
  have hsuccessorsNe : successors ≠ [] := by
    simp [successors]
  let first : OrientedEdge H := successors.head hsuccessorsNe
  let nodeRest : List (OrientedEdge H) := successors.tail
  have hsuccessorsEq : successors = first :: nodeRest := by
    exact (List.cons_head_tail hsuccessorsNe).symm
  have hnodeCons :
      (R.toHypermap).CPath nodeA (first :: nodeRest) := by
    have hpath :
        (R.toHypermap).CPath nodeA successors := by
      simpa only [successors] using hnodeTrimmed
    rw [hsuccessorsEq] at hpath
    exact hpath
  have hfirstTail : first.tail = D.branch := by
    apply hnodeTailBranch first
    have : first ∈ successors := by
      rw [hsuccessorsEq]
      simp
    simpa [successors] using
      (List.mem_cons_of_mem nodeA this)
  have hnodeFirst :
      (R.toHypermap).node first = nodeA := by
    exact R.toHypermap_node_apply_eq_of_cLink_same_tail
      ((hnodeTailBranch nodeA (by simp)).trans hfirstTail.symm)
      ((Hypermap.CPath.cons
        (G := R.toHypermap) nodeA first nodeRest).mp hnodeCons).1
  have hnodeSuffix :
      (R.toHypermap).CPath first nodeRest :=
    ((Hypermap.CPath.cons
      (G := R.toHypermap) nodeA first nodeRest).mp hnodeCons).2
  have hnodeSuffixLast :
      (first :: nodeRest).getLastD first = nodeB := by
    rw [← hsuccessorsEq]
    change (nodeMiddle ++ [nodeB]).getLastD first = nodeB
    induction nodeMiddle with
    | nil =>
        simp [List.getLastD]
    | cons z p ih =>
        simp [List.getLastD]
  have hconnectorSplit :=
    Hypermap.CPath.split_append_cons
      (G := R.toHypermap)
      (p := T.connectorMiddle) (q := [])
      (by simpa using T.connector_path)
  have hconnectorPrefix :
      (R.toHypermap).CPath T.connectorRight T.connectorMiddle :=
    hconnectorSplit.1
  have hfaceCR_ne_CL :
      (R.toHypermap).face T.connectorRight ≠ T.connectorLeft := by
    have hCRCL :
        (R.toHypermap).FacePath T.connectorRight
          (arcBTail ++ [T.connectorLeft]) := by
      have hsuffix :
          (R.toHypermap).FacePath T.connectorRight
            (arcBTail ++ [T.connectorLeft]) :=
        Hypermap.FacePath.suffix_of_append
          (G := R.toHypermap)
          (p := arcATail) (q := arcBTail ++ [T.connectorLeft])
          (by simpa [List.append_assoc] using hcycleCL)
      exact hsuffix
    have hswapped :
        ((T.connectorRight :: arcBTail) ++
          (T.connectorLeft :: arcATail)).Nodup := by
      have hparts :
          ((T.connectorLeft :: arcATail) ++
            (T.connectorRight :: arcBTail)).Nodup := by
        simpa [List.cons_append, List.append_assoc] using hcycleCLNodup
      rcases List.nodup_append.mp hparts with ⟨hP, hQ, hPQdisj⟩
      exact List.nodup_append.mpr
        ⟨hQ, hP, by
          intro a ha b hb hab
          exact hPQdisj b hb a ha hab.symm⟩
    have hCRCLNodup :
        (T.connectorRight :: arcBTail ++ [T.connectorLeft]).Nodup := by
      have hprefix :
          (T.connectorRight :: arcBTail ++ [T.connectorLeft]) <+:
            ((T.connectorRight :: arcBTail) ++
              (T.connectorLeft :: arcATail)) := by
        refine ⟨arcATail, ?_⟩
        simp [List.cons_append, List.append_assoc]
      exact hprefix.nodup hswapped
    exact Hypermap.FacePath.face_ne_endpoint_of_middle
      (G := R.toHypermap) hCRCL hCRCLNodup
      (by
        intro hnil
        rw [hnil] at hnodeB_tail
        exact List.not_mem_nil hnodeB_tail)
  have hconnectorLast :
      (R.toHypermap).node.symm
          ((T.connectorRight :: T.connectorMiddle).getLastD
            T.connectorRight) =
        T.connectorLeft := by
    rcases hconnectorSplit.2.1 with hnode | hface
    · exact hnode.symm
    · let pred : OrientedEdge H :=
        (T.connectorRight :: T.connectorMiddle).getLastD
          T.connectorRight
      have hpredMem :
          pred ∈ T.connectorRight :: T.connectorMiddle := by
        simpa only [pred, List.getLastD_cons] using
          (List.getLastD_mem_cons
            (a := T.connectorRight) (l := T.connectorMiddle))
      rw [List.mem_cons] at hpredMem
      rcases hpredMem with hpredR | hpredMiddle
      · exfalso
        apply hfaceCR_ne_CL
        have hraw :
            (T.connectorRight :: T.connectorMiddle).getLastD
                T.connectorRight =
              T.connectorRight := by
          simpa only [pred] using hpredR
        calc
          (R.toHypermap).face T.connectorRight =
              (R.toHypermap).face
                ((T.connectorRight :: T.connectorMiddle).getLastD
                  T.connectorRight) := by rw [hraw]
          _ = T.connectorLeft := hface.symm
      · have havoid :=
          T.connectorMiddle_avoids_arcs pred hpredMiddle
        have hCLReach :
            PermReachable (R.toHypermap).face D.x T.connectorLeft := by
          apply (A.orbit_membership T.connectorLeft).1
          have :
              T.connectorLeft ∈
                (D.x :: A.left) ++ (D.y :: A.right) := by
            exact List.mem_append_left _ T.connectorLeft_mem
          simpa [List.cons_append, List.append_assoc] using this
        have hpredEq :
            pred = (R.toHypermap).face.symm T.connectorLeft := by
          apply (R.toHypermap).face.injective
          simpa [pred] using hface.symm
        have hpredReach :
            PermReachable (R.toHypermap).face D.x pred := by
          rw [hpredEq]
          exact PermReachable.trans (R.toHypermap).face hCLReach
            (PermReachable.backward
              (R.toHypermap).face T.connectorLeft)
        rcases hOriginalOrbit hpredReach with hleft | hright
        · exfalso
          exact havoid.2 hleft
        · exfalso
          exact havoid.1 hright
  have hnodeChunkNodup :
      (first :: nodeRest).Nodup := by
    have htailNodup :=
      (List.nodup_cons.mp hnodeTrimmedNodup).2
    have hsuccessorsNodup : successors.Nodup := by
      simpa only [successors] using htailNodup
    rw [hsuccessorsEq] at hsuccessorsNodup
    exact hsuccessorsNodup
  have hconnectorMiddleNodup :
      T.connectorMiddle.Nodup := by
    have htailNodup :=
      (List.nodup_cons.mp T.connector_nodup).2
    exact (List.nodup_append.mp
      (by simpa [List.append_assoc] using htailNodup)).1
  have hnodeFaceDisjoint :
      ∀ a ∈ first :: nodeRest,
        ∀ b ∈ faceSegment, a ≠ b := by
    intro a ha b hb hab
    subst b
    have haSuccessors : a ∈ successors := by
      rw [hsuccessorsEq]
      exact ha
    have haCases :
        a ∈ nodeMiddle ∨ a = nodeB := by
      have haList : a ∈ nodeMiddle ++ [nodeB] := by
        simpa only [successors] using haSuccessors
      rcases List.mem_append.mp haList with
        haMiddle | haLast
      · exact Or.inl haMiddle
      · exact Or.inr (by simpa using haLast)
    rcases haCases with haMiddle | rfl
    · have havoid := hnodeMiddleAvoid a haMiddle
      have hreachA :
          PermReachable (R.toHypermap).face D.x a := by
        exact PermReachable.trans (R.toHypermap).face hnodeBReach
          (Hypermap.FacePath.mem_faceReachable
            (G := R.toHypermap) hfaceSegment
              (List.mem_cons_of_mem nodeB hb))
      rcases hArcOrbit hreachA with haArc | haArc
      · exact havoid.1 haArc
      · exact havoid.2 haArc
    · exact (List.nodup_cons.mp hfaceSegmentNodup).1 hb
  have hfaceConnectorDisjoint :
      ∀ a ∈ faceSegment,
        ∀ b ∈ T.connectorMiddle, a ≠ b := by
    intro a ha b hb hab
    subst b
    have hreach :
        PermReachable (R.toHypermap).face D.x a :=
      PermReachable.trans (R.toHypermap).face hnodeBReach
        (Hypermap.FacePath.mem_faceReachable
          (G := R.toHypermap) hfaceSegment
            (List.mem_cons_of_mem nodeB ha))
    have havoid := T.connectorMiddle_avoids_arcs a hb
    rcases hOriginalOrbit hreach with hleft | hright
    · exact havoid.2 hleft
    · exact havoid.1 hright
  have hnodeConnectorDisjoint :
      ∀ a ∈ first :: nodeRest,
        ∀ b ∈ T.connectorMiddle, a ≠ b := by
    intro a ha b hb hab
    have haTail : a.tail = D.branch := by
      apply hnodeTailBranch a
      have haSuccessors : a ∈ successors := by
        rw [hsuccessorsEq]
        exact ha
      have haTailList : a ∈ nodeMiddle ++ [nodeB] := by
        simpa only [successors] using haSuccessors
      exact List.mem_cons_of_mem nodeA haTailList
    have hbTail : b.tail ≠ D.branch :=
      T.connector_tail_ne b (by simp [hb])
    exact hbTail (by simpa [hab] using haTail)
  have hnodeFaceNodup :
      ((first :: nodeRest) ++ faceSegment).Nodup :=
    List.nodup_append.mpr
      ⟨hnodeChunkNodup,
        (List.nodup_cons.mp hfaceSegmentNodup).2,
        hnodeFaceDisjoint⟩
  have hfullNodup :
      (((first :: nodeRest) ++ faceSegment) ++
        T.connectorMiddle).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnodeFaceNodup, hconnectorMiddleNodup, ?_⟩
    intro a ha b hb
    rcases List.mem_append.mp ha with haNode | haFace
    · exact hnodeConnectorDisjoint a haNode b hb
    · exact hfaceConnectorDisjoint a haFace b hb
  apply Hypermap.Jordan.not_alternating_cPaths
    (G := R.toHypermap) hJ
    hnodeSuffix hnodeSuffixLast
    hfaceSegment hfaceSegmentLast
    hconnectorPrefix hnodeFirst hconnectorLast
  · change
      (first ::
        ((nodeRest ++ faceSegment) ++ T.connectorMiddle)).Nodup
    simpa only [List.cons_append] using hfullNodup
  · exact hcrossOrder


end FourColor
end Schematic.Math.GraphTheory
