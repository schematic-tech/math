import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.OrderedSelections

/-! Iterated spoke insertion with an ordered retained face. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u

namespace RotationSystemFan

/-- Exact finite version of Coq's `plane_add_fan`: add a finite ordered list
of spokes from the new vertex and retain precisely the face suffix beginning
with the last inserted spoke. -/
theorem exists_addNodeGraph_orderedRetained
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (A : Set V) [DecidableRel (addNodeGraph G A).Adj]
    (y : V) (ys : List V)
    (R : RotationSystem (addNodeGraph G A))
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge (addNodeGraph G A))
    (qs residual : List (OrientedEdge (addNodeGraph G A)))
    (hselect : OrderedSelections (q :: qs) B.rest residual)
    (htails : List.Forall₂ (fun q y => q.tail = some y)
      (q :: qs) (y :: ys))
    (hys : (y :: ys).Nodup)
    (hdisjoint : forall z, z ∈ y :: ys -> z ∉ A)
    (hfirst : B.first.tail = none) :
    letI : DecidableRel (addNodeGraph G (insertList (y :: ys) A)).Adj :=
      Classical.decRel _
    Exists fun S : RotationSystem (addNodeGraph G (insertList (y :: ys) A)) =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun C : FaceBoundary S.toHypermap =>
          C.first.tail = none ∧
            Exists fun lift : OrientedEdge (addNodeGraph G A) ->
                OrientedEdge (addNodeGraph G (insertList (y :: ys) A)) =>
              (forall d, (lift d).tail = d.tail) ∧
                C.rest = residual.map lift := by
  classical
  induction ys generalizing A y R B q qs residual with
  | nil =>
      cases htails with
      | cons hq htails =>
        cases htails
        have hy : y ∉ A := hdisjoint y (by simp)
        rcases hselect.singleton_split with ⟨pre, post, hrest, hresidual⟩
        letI : DecidableRel (addNodeGraph G (insert y A)).Adj :=
        Classical.decRel _
        rcases exists_addNodeGraph_insertRetained A y hy R hR B q pre post hrest
            hfirst hq with
          ⟨S, hS, C, hCfirst, lift, hliftTail, hCrest⟩
        refine ⟨S, hS, C, hCfirst, lift, hliftTail, ?_⟩
        rw [hresidual]
        simpa [insertList] using hCrest
  | cons z zs ih =>
      cases htails with
      | cons hq htails =>
        cases htails with
        | cons hr htails =>
          rename_i r rs
          have hy : y ∉ A := hdisjoint y (by simp)
          have hysParts : y ∉ z :: zs ∧ (z :: zs).Nodup :=
            List.nodup_cons.mp hys
          have hysTail : (z :: zs).Nodup := hysParts.2
          have hyNotMem : y ∉ z :: zs := hysParts.1
          have hdisjointTail : forall w, w ∈ z :: zs -> w ∉ insert y A := by
            intro w hw
            simp only [Set.mem_insert_iff, not_or]
            exact ⟨fun hwy => hyNotMem (hwy ▸ hw), hdisjoint w (by simp [hw])⟩
          rcases hselect.cons_split with ⟨pre, post, hrest, htail⟩
          letI : DecidableRel (addNodeGraph G (insert y A)).Adj :=
            Classical.decRel _
          rcases exists_addNodeGraph_insertRetained A y hy R hR B q pre post hrest
              hfirst hq with
            ⟨S1, hS1, C1, hC1first, lift1, hlift1Tail, hC1rest⟩
          have hselectMap0 :
              OrderedSelections ((r :: rs).map lift1) (post.map lift1)
                (residual.map lift1) := by
            exact htail.map lift1
          have hselectMap :
              OrderedSelections ((r :: rs).map lift1) C1.rest
                (residual.map lift1) := by
            rw [hC1rest]
            exact hselectMap0.prepend [lift1 q]
          have htailsMap :
              List.Forall₂ (fun d w => d.tail = some w)
                ((r :: rs).map lift1) (z :: zs) :=
            Internal.forall2_map_left_tail lift1
              (fun (d : OrientedEdge (addNodeGraph G A)) (w : V) hdw => by
                rw [hlift1Tail d, hdw]) (.cons hr htails)
          rcases ih (insert y A) z S1 hS1 C1 (lift1 r) (rs.map lift1)
              (residual.map lift1)
              hselectMap htailsMap hysTail hdisjointTail hC1first with
            ⟨S, hS, C, hCfirst, lift2, hlift2Tail, hCrest⟩
          let lift : OrientedEdge (addNodeGraph G A) ->
              OrientedEdge (addNodeGraph G (insertList (z :: zs) (insert y A))) :=
            fun d => lift2 (lift1 d)
          refine ⟨S, hS, C, hCfirst, lift, ?_, ?_⟩
          · intro d
            calc
              (lift d).tail = (lift1 d).tail := hlift2Tail _
              _ = d.tail := hlift1Tail _
          · rw [hCrest]
            rw [List.map_map]
            exact congrArg (fun f => residual.map f) (by
              funext d
              rfl)

/-- Deleting the new vertex recovers the old graph. -/
noncomputable def addNodeGraphOldIso
    {V : Type u} (G : SimpleGraph V) (A : Set V) :
    (addNodeGraph G A).induce {z : Option V | z ≠ none} ≃g G where
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

theorem addNodeGraph_singleton_new_degree_le_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : V) :
    letI : DecidableRel (addNodeGraph G ({x} : Set V)).Adj :=
      Classical.decRel _
    (addNodeGraph G ({x} : Set V)).degree none <= 1 := by
  classical
  let H := addNodeGraph G ({x} : Set V)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hsubset : H.neighborFinset none ⊆ {some x} := by
    intro z hz
    have hzAdj : H.Adj none z := by
      simpa [SimpleGraph.mem_neighborFinset] using hz
    cases z with
    | none => exact False.elim (H.loopless.irrefl none hzAdj)
    | some z =>
        have hzEq : z = x := by
          simpa [H, addNodeGraph] using hzAdj
        simp [hzEq]
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hsubset).trans (by simp)

/-- Exact graph-indexed `plane_add_node1`: attach `none` as a leaf at the
corner `B.first`, preserving the complete old face boundary and appending the
incoming leaf dart. -/
theorem exists_addNodeGraph_singletonBoundary
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : V)
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (hx : B.first.tail = x) :
    letI : DecidableRel (addNodeGraph G ({x} : Set V)).Adj :=
      Classical.decRel _
    Exists fun S : RotationSystem (addNodeGraph G ({x} : Set V)) =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun C : FaceBoundary S.toHypermap =>
          C.first.tail = none ∧
            Exists fun lift : OrientedEdge G ->
                OrientedEdge (addNodeGraph G ({x} : Set V)) =>
              (forall d, (lift d).tail = some d.tail) ∧
                (forall d, (lift d).head = some d.head) ∧
                  Exists fun incoming :
                  OrientedEdge (addNodeGraph G ({x} : Set V)) =>
                    incoming.tail = some x ∧
                      C.rest = (B.first :: B.rest).map lift ++ [incoming] := by
  classical
  let H := addNodeGraph G ({x} : Set V)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hnew : H.Adj none (some x) := by
    simp [H, addNodeGraph]
  have hdegree : H.degree none <= 1 := by
    exact addNodeGraph_singleton_new_degree_le_one (G := G) x
  let D := H.induce {z : Option V | z ≠ none}
  let phi : D ≃g G := addNodeGraphOldIso G ({x} : Set V)
  let RD : RotationSystem D := RotationSystem.ofIso phi R
  let psi : Hypermap.Iso RD.toHypermap R.toHypermap :=
    RotationSystem.ofIso_toHypermapIso phi R
  have hRD : (RD.toHypermap).dual.EulerPlanar := by
    have hprimal : R.toHypermap.EulerPlanar :=
      (Hypermap.dual_eulerPlanar_iff (G := R.toHypermap)).mp hR
    have hsource : RD.toHypermap.EulerPlanar :=
      (psi.eulerPlanar_iff).mpr hprimal
    exact (Hypermap.dual_eulerPlanar_iff (G := RD.toHypermap)).mpr hsource
  let BD : FaceBoundary RD.toHypermap := B.mapIso psi.symm
  let p : OrientedEdge D := BD.first
  have hp : ((p.tail : {z : Option V // z ≠ none}) : Option V) = some x := by
    change
      ((((orientedEdgeEquivOfGraphIso phi).symm B.first).tail :
        {z : Option V // z ≠ none}) : Option V) = some x
    calc
      (((orientedEdgeEquivOfGraphIso phi).symm B.first).tail :
          {z : Option V // z ≠ none}).val =
          (phi.symm B.first.tail).val := by rfl
      _ = some x := by rw [hx]; rfl
  let S : RotationSystem H :=
    leafReattachRotationSystemAt hnew hdegree RD p hp
  have hS : (S.toHypermap).dual.EulerPlanar := by
    exact leafReattachRotationSystemAt_dual_eulerPlanar
      hnew hdegree RD p hp hRD
  let leafIso : Hypermap.Iso S.toHypermap
      (LeafExtension.leafHypermap RD.toHypermap (some p)) :=
    leafReattachRotationSystemAt_toHypermapIso hnew hdegree RD p hp
  let pureBoundary :
      FaceBoundary (LeafExtension.leafHypermap RD.toHypermap (some p)) :=
    BD.addLeaf
  let C : FaceBoundary S.toHypermap := pureBoundary.mapIso leafIso.symm
  let lift : OrientedEdge G -> OrientedEdge H := fun d =>
    leafIso.toEquiv.symm
      (ExtDart.old (psi.toEquiv.symm d))
  let incoming : OrientedEdge H := leafIso.toEquiv.symm ExtDart.newEdge
  refine ⟨S, hS, C, ?_, lift, ?_, ?_, incoming, ?_, ?_⟩
  · change (leafIso.toEquiv.symm ExtDart.new).tail = none
    rfl
  · intro d
    change
      (leafIso.toEquiv.symm (ExtDart.old (psi.toEquiv.symm d))).tail =
        some d.tail
    rfl
  · intro d
    change
      (leafIso.toEquiv.symm (ExtDart.old (psi.toEquiv.symm d))).head =
        some d.head
    rfl
  · change (leafIso.toEquiv.symm ExtDart.newEdge).tail = some x
    rfl
  · change
      (((BD.first :: BD.rest).map ExtDart.old ++ [ExtDart.newEdge]).map
          leafIso.toEquiv.symm) =
        (B.first :: B.rest).map lift ++ [incoming]
    let oldDarts := (BD.first :: BD.rest).map ExtDart.old
    calc
      ((oldDarts ++ [ExtDart.newEdge]).map leafIso.toEquiv.symm) =
          oldDarts.map leafIso.toEquiv.symm ++
            [leafIso.toEquiv.symm ExtDart.newEdge] := by
        simpa only [List.map_singleton] using
          (List.map_append (f := leafIso.toEquiv.symm)
            (l₁ := oldDarts) (l₂ := [ExtDart.newEdge]))
      _ = (B.first :: B.rest).map lift ++ [incoming] := by
        congr 1
        change
          (((B.first :: B.rest).map psi.toEquiv.symm).map ExtDart.old).map
              leafIso.toEquiv.symm =
            (B.first :: B.rest).map lift
        induction (B.first :: B.rest) with
        | nil => rfl
        | cons d ds ih =>
            change lift d ::
                ((ds.map psi.toEquiv.symm).map ExtDart.old).map
                  leafIso.toEquiv.symm =
              lift d :: ds.map lift
            exact congrArg (List.cons (lift d)) ih

/-- Insert one fresh vertex adjacent to two distinct vertices of an ordered
face and expose the two resulting faces.  If the old boundary order is
`B.first :: pre ++ q :: post`, the retained face runs through the old suffix
and the complementary face through the old prefix. -/
theorem exists_addNodeGraph_pairSplitBoundaries
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {s t : V} (hst : s ≠ t)
    (R : RotationSystem G)
    (hR : (R.toHypermap).dual.EulerPlanar)
    (B : FaceBoundary R.toHypermap)
    (q : OrientedEdge G)
    (pre post : List (OrientedEdge G))
    (hrest : B.rest = pre ++ q :: post)
    (hfirst : B.first.tail = s)
    (hq : q.tail = t) :
    letI : DecidableRel
        (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
    Exists fun S : RotationSystem
        (addNodeGraph G (insert t ({s} : Set V))) =>
      (S.toHypermap).dual.EulerPlanar ∧
        Exists fun suffixFace : FaceBoundary S.toHypermap =>
          Exists fun prefixFace : FaceBoundary S.toHypermap =>
            suffixFace.first.tail = none ∧
              prefixFace.first.tail = some t ∧
                prefixFace.first.head = none ∧
                Exists fun lift : OrientedEdge G ->
                    OrientedEdge (addNodeGraph G (insert t ({s} : Set V))) =>
                  (forall d, lift d =
                    addNodeGraphSomeOrientedEdge G (insert t ({s} : Set V)) d) ∧
                  (forall d, (lift d).tail = some d.tail) ∧
                    (forall d, (lift d).head = some d.head) ∧
                      Exists fun toS : OrientedEdge
                          (addNodeGraph G (insert t ({s} : Set V))) =>
                        toS.tail = some s ∧
                          Exists fun fromS : OrientedEdge
                              (addNodeGraph G (insert t ({s} : Set V))) =>
                            fromS.tail = none ∧
                              fromS.head = some s ∧
                              suffixFace.rest =
                                lift q :: post.map lift ++ [toS] ∧
                              prefixFace.rest =
                                fromS :: lift B.first :: pre.map lift := by
  classical
  let H1 := addNodeGraph G ({s} : Set V)
  letI : DecidableRel H1.Adj := Classical.decRel _
  rcases exists_addNodeGraph_singletonBoundary s R hR B hfirst with
    ⟨R1, hR1, B1, hB1first, lift1, hlift1Tail, hlift1Head, incoming1,
      hincoming1Tail, hB1rest⟩
  have htNot : t ∉ ({s} : Set V) := by simp [hst.symm]
  let q1 : OrientedEdge H1 := lift1 q
  let pre1 : List (OrientedEdge H1) := lift1 B.first :: pre.map lift1
  let post1 : List (OrientedEdge H1) := post.map lift1 ++ [incoming1]
  have hB1split : B1.rest = pre1 ++ q1 :: post1 := by
    rw [hB1rest, hrest]
    dsimp only [pre1, q1, post1]
    change
      (lift1 B.first :: List.map lift1 (pre ++ q :: post)) ++ [incoming1] = _
    rw [List.map_append]
    change
      (lift1 B.first :: (List.map lift1 pre ++
        lift1 q :: List.map lift1 post)) ++ [incoming1] = _
    simp only [List.cons_append, List.append_assoc]
  have hq1 : q1.tail = some t := by
    rw [hlift1Tail, hq]
  letI : DecidableRel
      (addNodeGraph G (insert t ({s} : Set V))).Adj := Classical.decRel _
  rcases exists_addNodeGraph_insertSplitBoundaries
      ({s} : Set V) t htNot R1 hR1 B1 q1 pre1 post1
      hB1split hB1first hq1 with
    ⟨S, hS, suffixFace, prefixFace, hsuffixFirst, hprefixFirst,
      lift2, hlift2Tail, hlift2Head, hsuffixRest, hprefixRest⟩
  let lift : OrientedEdge G ->
      OrientedEdge (addNodeGraph G (insert t ({s} : Set V))) :=
    fun d => lift2 (lift1 d)
  let toS : OrientedEdge (addNodeGraph G (insert t ({s} : Set V))) :=
    lift2 incoming1
  let fromS : OrientedEdge (addNodeGraph G (insert t ({s} : Set V))) :=
    lift2 B1.first
  have hprefixRestFinal :
      prefixFace.rest = fromS :: lift B.first :: pre.map lift := by
    rw [hprefixRest]
    change lift2 B1.first ::
        (lift1 B.first :: pre.map lift1).map lift2 =
      fromS :: lift B.first :: pre.map lift
    simp [lift, fromS, List.map_map]
  have hprefixFirstHead : prefixFace.first.head = none := by
    have hpath :
        S.toHypermap.FacePath prefixFace.first
          (fromS :: lift B.first :: pre.map lift) := by
      simpa only [hprefixRestFinal] using prefixFace.path
    have hstep : S.toHypermap.face prefixFace.first = fromS :=
      (Hypermap.FacePath.cons S.toHypermap prefixFace.first fromS
        (lift B.first :: pre.map lift)).mp hpath |>.1
    calc
      prefixFace.first.head =
          (S.toHypermap.face prefixFace.first).tail :=
        (S.toHypermap_face_tail prefixFace.first).symm
      _ = fromS.tail := congrArg OrientedEdge.tail hstep
      _ = none := by
        change (lift2 B1.first).tail = none
        rw [hlift2Tail, hB1first]
  have hfromSHead : fromS.head = some s := by
    have hpath :
        S.toHypermap.FacePath prefixFace.first
          (fromS :: lift B.first :: pre.map lift) := by
      simpa only [hprefixRestFinal] using prefixFace.path
    have htailPath :
        S.toHypermap.FacePath fromS (lift B.first :: pre.map lift) :=
      (Hypermap.FacePath.cons S.toHypermap prefixFace.first fromS
        (lift B.first :: pre.map lift)).mp hpath |>.2
    have hstep : S.toHypermap.face fromS = lift B.first :=
      (Hypermap.FacePath.cons S.toHypermap fromS (lift B.first)
        (pre.map lift)).mp htailPath |>.1
    calc
      fromS.head = (S.toHypermap.face fromS).tail :=
        (S.toHypermap_face_tail fromS).symm
      _ = (lift B.first).tail := congrArg OrientedEdge.tail hstep
      _ = some B.first.tail := hlift2Tail _ |>.trans (hlift1Tail _)
      _ = some s := congrArg some hfirst
  have hliftCanonical : forall d,
      lift d = addNodeGraphSomeOrientedEdge G (insert t ({s} : Set V)) d := by
    intro d
    apply Subtype.ext
    exact Prod.ext
      (hlift2Tail _ |>.trans (hlift1Tail _))
      (hlift2Head _ |>.trans (hlift1Head _))
  refine ⟨S, hS, suffixFace, prefixFace, hsuffixFirst, hprefixFirst,
    hprefixFirstHead, lift, hliftCanonical, ?_, ?_, toS, ?_, fromS, ?_, hfromSHead,
    ?_, ?_⟩
  · intro d
    calc
      (lift d).tail = (lift1 d).tail := hlift2Tail _
      _ = some d.tail := hlift1Tail _
  · intro d
    calc
      (lift d).head = (lift1 d).head := hlift2Head _
      _ = some d.head := hlift1Head _
  · calc
      toS.tail = incoming1.tail := hlift2Tail _
      _ = some s := hincoming1Tail
  · calc
      fromS.tail = B1.first.tail := hlift2Tail _
      _ = none := hB1first
  · rw [hsuffixRest]
    change lift2 (lift1 q) ::
        (post.map lift1 ++ [incoming1]).map lift2 =
      lift q :: post.map lift ++ [toS]
    simp [lift, toS, List.map_map]
  · exact hprefixRestFinal


end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
