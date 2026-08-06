import Schematic.Math.GraphTheory.Embedding.Walkup.PermutationDeletion

/-! Construction and elementary invariants of the Walkup dart deletion. -/

namespace Schematic.Math.GraphTheory

namespace FourColor

universe u

namespace Hypermap

variable (G : Hypermap.{u})

/-- The dart domain with a single dart removed, used by the Walkup
transforms. -/
abbrev DeletedDart (z : G.Dart) :=
  DeletedPoint z

/-- The node permutation with dart `z` deleted and its cycle spliced. -/
def walkupSkipNode [DecidableEq G.Dart] (z : G.Dart) :
    Equiv.Perm (G.DeletedDart z) :=
  PermSkip.skip G.node z

/-- The face permutation with dart `z` deleted and its cycle spliced. -/
def walkupSkipFace [DecidableEq G.Dart] (z : G.Dart) :
    Equiv.Perm (G.DeletedDart z) :=
  PermSkip.skip G.face z

/-- Coq `skip_edge1`: the edge-side splicing function used by `WalkupE`. -/
def walkupSkipEdgeAux (z x : G.Dart) : G.Dart :=
  if G.edge z = z then G.edge x
  else if G.face (G.edge x) = z then G.edge z
  else if G.edge x = z then G.edge (G.node z)
  else G.edge x

theorem walkupSkipEdgeAux_ne_deleted
    {z : G.Dart} (x : G.DeletedDart z) :
    G.walkupSkipEdgeAux z x.1 ≠ z := by
  unfold walkupSkipEdgeAux
  split_ifs with hez hfe hex
  · intro hxz
    have hsame : G.edge x.1 = G.edge z := by
      rw [hxz, hez]
    exact x.2 (G.edge.injective hsame)
  · exact hez
  · intro hz
    have hfacez : G.face z = z := by
      calc
        G.face z = G.face (G.edge (G.node z)) := by rw [hz]
        _ = z := by simp
    apply hfe
    rw [hex, hfacez]
  · exact hex

/-- Coq `skip_edge`: `skip_edge1` restricted to the deleted dart domain. -/
def walkupSkipEdge (z : G.Dart) : G.DeletedDart z → G.DeletedDart z :=
  fun x => ⟨G.walkupSkipEdgeAux z x.1, G.walkupSkipEdgeAux_ne_deleted x⟩

@[simp]
theorem walkupSkipEdge_apply_val
    {z : G.Dart} (x : G.DeletedDart z) :
    ((G.walkupSkipEdge z x : G.DeletedDart z) : G.Dart) =
      G.walkupSkipEdgeAux z x.1 :=
  rfl

theorem walkupSkipEdgeAux_cancel
    {z x : G.Dart} (hx : x ≠ z) :
    PermSkip.skipAux G.node z
        (PermSkip.skipAux G.face z (G.walkupSkipEdgeAux z x)) = x := by
  by_cases hez : G.edge z = z
  · by_cases hfe : G.face (G.edge x) = z
    · have hnodz : G.node z = x := by
        rw [← hfe]
        simp
      have hnodfacez : G.node (G.face z) = z := by
        calc
          G.node (G.face z) =
              G.node (G.face (G.edge z)) := by rw [hez]
          _ = z := by simp
      simp [walkupSkipEdgeAux, PermSkip.skipAux, hez, hfe, hnodz,
        hnodfacez]
    · simp [walkupSkipEdgeAux, PermSkip.skipAux, hez, hfe, hx]
  · by_cases hfe : G.face (G.edge x) = z
    · have hnodz : G.node z = x := by
        rw [← hfe]
        simp
      have hfaceez : G.face (G.edge z) ≠ z := by
        intro hz
        have hsame : G.face (G.edge x) = G.face (G.edge z) := by
          rw [hfe, hz]
        have hedge : G.edge x = G.edge z := G.face.injective hsame
        exact hx (G.edge.injective hedge)
      simp [walkupSkipEdgeAux, PermSkip.skipAux, hez, hfe, hfaceez, hnodz]
    · by_cases hex : G.edge x = z
      · have hnodfacez : G.node (G.face z) = x := by
          apply G.edge.injective
          calc
            G.edge (G.node (G.face z)) = z := by simp
            _ = G.edge x := hex.symm
        have hnodfacez_ne : G.node (G.face z) ≠ z := by
          intro hz
          exact hx (by rw [← hnodfacez, hz])
        have hfez : G.face z ≠ z := by
          intro hz
          exact hfe (by rw [hex, hz])
        simp only [walkupSkipEdgeAux, hez, hfez, hex, ↓reduceIte]
        change
          PermSkip.skipAux G.node z
            (PermSkip.skipAux G.face z (G.edge (G.node z))) = x
        have hface : G.face (G.edge (G.node z)) = z := by simp
        simp [PermSkip.skipAux, hface, hnodfacez, hx]
      · simp [walkupSkipEdgeAux, PermSkip.skipAux, hez, hfe, hex, hx]

theorem walkupSkipEdge_cancel
    {z : G.Dart} (x : G.DeletedDart z) :
    G.walkupSkipNode z (G.walkupSkipFace z (G.walkupSkipEdge z x)) = x := by
  apply Subtype.ext
  exact G.walkupSkipEdgeAux_cancel x.2

/-- Coq `WalkupE`: delete `z`, splice the node and face cycles directly, and
use the inverse of their composite as the edge permutation. -/
def walkupE (z : G.Dart) : Hypermap.{u} where
  Dart := G.DeletedDart z
  edge := ((G.walkupSkipFace z).trans (G.walkupSkipNode z)).symm
  node := G.walkupSkipNode z
  face := G.walkupSkipFace z
  node_face_edge := by
    intro x
    simp

@[simp]
theorem walkupE_node (z : G.Dart) :
    (G.walkupE z).node = G.walkupSkipNode z :=
  rfl

@[simp]
theorem walkupE_face (z : G.Dart) :
    (G.walkupE z).face = G.walkupSkipFace z :=
  rfl

@[simp]
theorem walkupE_node_apply_coe
    {z : G.Dart} (x : G.DeletedDart z) :
    ((G.walkupE z).node x).1 = PermSkip.skipAux G.node z x.1 :=
  rfl

theorem walkupE_node_apply_coe_of_ne
    {z : G.Dart} (x : G.DeletedDart z) (hx : G.node x.1 ≠ z) :
    ((G.walkupE z).node x).1 = G.node x.1 := by
  exact PermSkip.skip_apply_of_apply_ne G.node x hx

theorem walkupE_node_apply_coe_of_eq
    {z : G.Dart} (x : G.DeletedDart z) (hx : G.node x.1 = z) :
    ((G.walkupE z).node x).1 = G.node z := by
  exact PermSkip.skip_apply_of_apply_eq G.node x hx

@[simp]
theorem walkupE_face_apply_coe
    {z : G.Dart} (x : G.DeletedDart z) :
    ((G.walkupE z).face x).1 = PermSkip.skipAux G.face z x.1 :=
  rfl

theorem walkupE_face_apply_coe_of_ne
    {z : G.Dart} (x : G.DeletedDart z) (hx : G.face x.1 ≠ z) :
    ((G.walkupE z).face x).1 = G.face x.1 := by
  exact PermSkip.skip_apply_of_apply_ne G.face x hx

theorem walkupE_face_apply_coe_of_eq
    {z : G.Dart} (x : G.DeletedDart z) (hx : G.face x.1 = z) :
    ((G.walkupE z).face x).1 = G.face z := by
  exact PermSkip.skip_apply_of_apply_eq G.face x hx

theorem walkupE_nodeOrbitCount_add_indicator (z : G.Dart) :
    (if G.node z = z then 1 else 0) + (G.walkupE z).nodeOrbitCount =
      G.nodeOrbitCount := by
  simpa [nodeOrbitCount, NodeOrbit, walkupE_node, walkupSkipNode] using
    PermSkip.orbitCount_skip_add_indicator G.node z

theorem walkupE_faceOrbitCount_add_indicator (z : G.Dart) :
    (if G.face z = z then 1 else 0) + (G.walkupE z).faceOrbitCount =
      G.faceOrbitCount := by
  simpa [faceOrbitCount, FaceOrbit, walkupE_face, walkupSkipFace] using
    PermSkip.orbitCount_skip_add_indicator G.face z

theorem walkupE_nodeOrbitCount_of_node_ne
    {z : G.Dart} (hz : G.node z ≠ z) :
    (G.walkupE z).nodeOrbitCount = G.nodeOrbitCount := by
  have h := G.walkupE_nodeOrbitCount_add_indicator z
  simpa [hz] using h

theorem walkupE_faceOrbitCount_of_face_ne
    {z : G.Dart} (hz : G.face z ≠ z) :
    (G.walkupE z).faceOrbitCount = G.faceOrbitCount := by
  have h := G.walkupE_faceOrbitCount_add_indicator z
  simpa [hz] using h

theorem walkupE_nodeOrbitCount_add_one_of_node_eq
    {z : G.Dart} (hz : G.node z = z) :
    (G.walkupE z).nodeOrbitCount + 1 = G.nodeOrbitCount := by
  have h := G.walkupE_nodeOrbitCount_add_indicator z
  simpa [hz, Nat.add_comm] using h

theorem walkupE_faceOrbitCount_add_one_of_face_eq
    {z : G.Dart} (hz : G.face z = z) :
    (G.walkupE z).faceOrbitCount + 1 = G.faceOrbitCount := by
  have h := G.walkupE_faceOrbitCount_add_indicator z
  simpa [hz, Nat.add_comm] using h

/-- Coq `WalkupI`: include a dart into `WalkupE`, using an existing dart of
`WalkupE` as the default when asked to include the deleted dart. -/
def walkupI {z : G.Dart} (u : (G.walkupE z).Dart) (x : G.Dart) :
    (G.walkupE z).Dart :=
  DeletedPoint.lift u x

@[simp]
theorem walkupI_coe
    {z : G.Dart} (u : (G.walkupE z).Dart) (x : G.Dart) :
    (G.walkupI u x).1 =
      if x = z then u.1 else x := by
  exact DeletedPoint.lift_coe u x

theorem walkupI_coe_of_ne
    {z x : G.Dart} (u : (G.walkupE z).Dart) (hx : x ≠ z) :
    (G.walkupI u x).1 = x := by
  exact DeletedPoint.lift_coe_of_ne u hx

/-- Coq `Walkup_seq`: a list avoiding the deleted dart lifts to `WalkupE`. -/
theorem walkupE_seq
    (z : G.Dart) (p : List G.Dart) (hp : z ∉ p) :
    ∃ q : List (G.walkupE z).Dart, q.map Subtype.val = p :=
  DeletedPoint.exists_list_coe_eq p hp

theorem walkupE_val_injective (z : G.Dart) :
    Function.Injective (fun x : (G.walkupE z).Dart => x.1) := by
  intro x y hxy
  exact Subtype.ext hxy

theorem walkupE_walkupE_val_injective
    {z : G.Dart} (u : (G.walkupE z).Dart) :
    Function.Injective
      (fun x : ((G.walkupE z).walkupE u).Dart => x.1.1) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

/-- The composed projection out of two successive `WalkupE` deletions has
image exactly the complement of the two deleted darts. -/
def walkupE_walkupE_complEquiv
    {z : G.Dart} (u : (G.walkupE z).Dart) :
    ((G.walkupE z).walkupE u).Dart ≃
      {x : G.Dart // x ≠ z ∧ x ≠ u.1} where
  toFun x := ⟨x.1.1, x.1.2, by
    intro hx
    exact x.2 (Subtype.ext hx)⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    intro hx
    exact x.2.2 (congrArg Subtype.val hx)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

@[simp]
theorem walkupE_walkupE_complEquiv_apply
    {z : G.Dart} (u : (G.walkupE z).Dart)
    (x : ((G.walkupE z).walkupE u).Dart) :
    (G.walkupE_walkupE_complEquiv u x).1 = x.1.1 :=
  rfl

theorem walkupE_walkupE_val_mem_range_iff
    {z : G.Dart} (u : (G.walkupE z).Dart) (x : G.Dart) :
    x ∈ Set.range (fun w : ((G.walkupE z).walkupE u).Dart => w.1.1) ↔
      x ≠ z ∧ x ≠ u.1 := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1.2, by
      intro hx
      exact w.2 (Subtype.ext hx)⟩
  · rintro ⟨hxz, hxu⟩
    exact ⟨⟨⟨x, hxz⟩, by
      intro hx
      exact hxu (congrArg Subtype.val hx)⟩, rfl⟩

theorem node_compl_of_node_node_eq
    {z x : G.Dart} (hzz : G.node (G.node z) = z)
    (hxz : x ≠ z) (hxnode : x ≠ G.node z) :
    G.node x ≠ z ∧ G.node x ≠ G.node z := by
  constructor
  · intro hbad
    have hsame : G.node x = G.node (G.node z) := by
      rw [hbad, hzz]
    exact hxnode (G.node.injective hsame)
  · intro hbad
    exact hxz (G.node.injective hbad)

/-- When `z` lies in a two-node orbit, `node` restricts to a permutation of
the complement of `z` and `node z`. -/
def nodeOnTwoNodeComplement
    {z : G.Dart} (hzz : G.node (G.node z) = z) :
    Equiv.Perm {x : G.Dart // x ≠ z ∧ x ≠ G.node z} where
  toFun x :=
    ⟨G.node x.1, G.node_compl_of_node_node_eq hzz x.2.1 x.2.2⟩
  invFun x := ⟨G.node.symm x.1, by
    constructor
    · intro hbad
      apply x.2.2
      calc
        x.1 = G.node (G.node.symm x.1) := by simp
        _ = G.node z := by rw [hbad]
    · intro hbad
      apply x.2.1
      calc
        x.1 = G.node (G.node.symm x.1) := by simp
        _ = G.node (G.node z) := by rw [hbad]
        _ = z := hzz⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[simp]
theorem walkupE_dart_card (z : G.Dart) :
    Fintype.card (G.walkupE z).Dart = Fintype.card G.Dart - 1 :=
  DeletedPoint.card z

theorem walkupE_dart_card_add_one (z : G.Dart) :
    Fintype.card (G.walkupE z).Dart + 1 = Fintype.card G.Dart :=
  DeletedPoint.card_add_one z

theorem walkupE_dart_card_lt (z : G.Dart) :
    Fintype.card (G.walkupE z).Dart < Fintype.card G.Dart :=
  DeletedPoint.card_lt z

theorem walkupE_edge_apply
    {z : G.Dart} (x : G.DeletedDart z) :
    (G.walkupE z).edge x = G.walkupSkipEdge z x := by
  let nf : Equiv.Perm (G.DeletedDart z) :=
    (G.walkupSkipFace z).trans (G.walkupSkipNode z)
  apply nf.injective
  change
    nf ((G.walkupE z).edge x) = nf (G.walkupSkipEdge z x)
  have hright : nf (G.walkupSkipEdge z x) = x := by
    exact G.walkupSkipEdge_cancel x
  calc
    nf ((G.walkupE z).edge x) = x := by
      change nf (nf.symm x) = x
      simp
    _ = nf (G.walkupSkipEdge z x) := hright.symm

@[simp]
theorem walkupE_edge_apply_coe
    {z : G.Dart} (x : G.DeletedDart z) :
    ((G.walkupE z).edge x).1 =
      G.walkupSkipEdgeAux z x.1 := by
  rw [G.walkupE_edge_apply]
  rfl

@[simp]
theorem walkupE_walkupE_edge_apply_coe
    {z : G.Dart} {u : (G.walkupE z).Dart}
    (x : ((G.walkupE z).walkupE u).Dart) :
    (((G.walkupE z).walkupE u).edge x).1.1 =
      ((G.walkupE z).walkupSkipEdgeAux u x.1).1 := by
  rw [(G.walkupE z).walkupE_edge_apply_coe]

theorem walkupE_edge_eq_skip_edge_of_edge_eq
    {z : G.Dart} (hz : G.edge z = z) :
    (G.walkupE z).edge = PermSkip.skip G.edge z := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  have hx : G.edge x.1 ≠ z := by
    intro hbad
    have hsame : G.edge x.1 = G.edge z := by rw [hbad, hz]
    exact x.2 (G.edge.injective hsame)
  rw [G.walkupE_edge_apply_coe]
  change G.walkupSkipEdgeAux z x.1 = PermSkip.skipAux G.edge z x.1
  simp [walkupSkipEdgeAux, PermSkip.skipAux, hz, hx]

theorem walkupE_edge_eq_skip_edge_of_node_eq
    {z : G.Dart} (hz : G.node z = z) :
    (G.walkupE z).edge = PermSkip.skip G.edge z := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [G.walkupE_edge_apply_coe]
  change G.walkupSkipEdgeAux z x.1 = PermSkip.skipAux G.edge z x.1
  unfold walkupSkipEdgeAux PermSkip.skipAux
  by_cases hez : G.edge z = z
  · simp [hez]
  · have hface_edge_ne : G.face (G.edge x.1) ≠ z := by
      intro hbad
      exact x.2
        (calc
          x.1 = G.node (G.face (G.edge x.1)) :=
            (G.node_face_edge x.1).symm
          _ = G.node z := by rw [hbad]
          _ = z := hz)
    by_cases hex : G.edge x.1 = z
    · simp [hez, hex, hz]
    · simp [hez, hface_edge_ne, hex]

theorem walkupE_edge_eq_skip_edge_of_face_eq
    {z : G.Dart} (hz : G.face z = z) :
    (G.walkupE z).edge = PermSkip.skip G.edge z := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rw [G.walkupE_edge_apply_coe]
  change G.walkupSkipEdgeAux z x.1 = PermSkip.skipAux G.edge z x.1
  unfold walkupSkipEdgeAux PermSkip.skipAux
  by_cases hez : G.edge z = z
  · simp [hez]
  · by_cases hface_edge : G.face (G.edge x.1) = z
    · have hex : G.edge x.1 = z := by
        apply G.face.injective
        calc
          G.face (G.edge x.1) = z := hface_edge
          _ = G.face z := hz.symm
      simp only [hez, hex, hz, ↓reduceIte]
    · have hex : G.edge x.1 ≠ z := by
        intro hex
        exact hface_edge (by rw [hex, hz])
      simp only [hez, hface_edge, hex, ↓reduceIte]

theorem walkupE_edge_eq_skip_edge_of_link_self
    {z : G.Dart} (hz : G.Link z z) :
    (G.walkupE z).edge = PermSkip.skip G.edge z := by
  rcases hz with hz | hz | hz
  · exact G.walkupE_edge_eq_skip_edge_of_edge_eq hz.symm
  · exact G.walkupE_edge_eq_skip_edge_of_node_eq hz.symm
  · exact G.walkupE_edge_eq_skip_edge_of_face_eq hz.symm

theorem walkupE_edgeOrbitCount_add_one_of_edge_eq
    {z : G.Dart} (hz : G.edge z = z) :
    (G.walkupE z).edgeOrbitCount + 1 = G.edgeOrbitCount := by
  change Nat.card (PermOrbit (G.walkupE z).edge) + 1 =
    Nat.card (PermOrbit G.edge)
  rw [G.walkupE_edge_eq_skip_edge_of_edge_eq hz]
  exact PermSkip.orbitCount_skip_add_one_of_fixed G.edge hz

theorem walkupE_edgeOrbitCount_add_indicator_of_link_self
    {z : G.Dart} (hz : G.Link z z) :
    (if G.edge z = z then 1 else 0) + (G.walkupE z).edgeOrbitCount =
      G.edgeOrbitCount := by
  change
    (if G.edge z = z then 1 else 0) +
        Nat.card (PermOrbit (G.walkupE z).edge) =
      Nat.card (PermOrbit G.edge)
  rw [G.walkupE_edge_eq_skip_edge_of_link_self hz]
  exact PermSkip.orbitCount_skip_add_indicator G.edge z

theorem walkupE_edgeOrbit_step_of_link_self_of_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    1 + (G.walkupE z).edgeOrbitCount = G.edgeOrbitCount + 1 := by
  have h := G.walkupE_edgeOrbitCount_add_indicator_of_link_self hz
  simp [he] at h
  omega

theorem edge_eq_self_of_node_eq_self_of_face_eq_self
    {z : G.Dart} (hn : G.node z = z) (hf : G.face z = z) :
    G.edge z = z := by
  apply G.face.injective
  calc
    G.face (G.edge z) = z := by
      simpa [hn] using G.face_edge_node z
    _ = G.face z := hf.symm

theorem node_face_indicator_add_eq_one_of_link_self_of_edge_ne
    {z : G.Dart} (hz : G.Link z z) (he : G.edge z ≠ z) :
    (if G.node z = z then 1 else 0) +
        (if G.face z = z then 1 else 0) = 1 := by
  rcases hz with hz_edge | hz_node | hz_face
  · exact False.elim (he hz_edge.symm)
  · have hn : G.node z = z := hz_node.symm
    have hf_ne : G.face z ≠ z := by
      intro hf
      exact he (G.edge_eq_self_of_node_eq_self_of_face_eq_self hn hf)
    simp [hn, hf_ne]
  · have hf : G.face z = z := hz_face.symm
    have hn_ne : G.node z ≠ z := by
      intro hn
      exact he (G.edge_eq_self_of_node_eq_self_of_face_eq_self hn hf)
    simp [hn_ne, hf]

theorem face_ne_of_node_eq_self_of_edge_ne
    {z : G.Dart} (hn : G.node z = z) (he : G.edge z ≠ z) :
    G.face z ≠ z := by
  intro hf
  exact he (G.edge_eq_self_of_node_eq_self_of_face_eq_self hn hf)

theorem node_ne_of_face_eq_self_of_edge_ne
    {z : G.Dart} (hf : G.face z = z) (he : G.edge z ≠ z) :
    G.node z ≠ z := by
  intro hn
  exact he (G.edge_eq_self_of_node_eq_self_of_face_eq_self hn hf)

theorem walkupE_reachable_edge_to_face_of_node_eq_self_of_edge_ne
    {z : G.Dart} (hn : G.node z = z) (he : G.edge z ≠ z) :
    (G.walkupE z).Reachable
      (⟨G.edge z, he⟩ : G.DeletedDart z)
      (⟨G.face z, G.face_ne_of_node_eq_self_of_edge_ne hn he⟩ :
        G.DeletedDart z) := by
  let u : G.DeletedDart z := ⟨G.edge z, he⟩
  let v : G.DeletedDart z :=
    ⟨G.face z, G.face_ne_of_node_eq_self_of_edge_ne hn he⟩
  have hface_edge : G.face (G.edge z) = z := by
    simpa [hn] using G.face_edge_node z
  have hface : (G.walkupE z).face u = v := by
    apply Subtype.ext
    change ((G.walkupSkipFace z u : G.DeletedDart z) : G.Dart) = v.1
    calc
      ((G.walkupSkipFace z u : G.DeletedDart z) : G.Dart) =
          G.face z := PermSkip.skip_apply_of_apply_eq G.face u hface_edge
      _ = v.1 := rfl
  have hreach : (G.walkupE z).Reachable u v := by
    rw [← hface]
    exact (G.walkupE z).reachable_face u
  simpa [u, v] using hreach

theorem walkupE_reachable_edge_to_node_of_face_eq_self_of_edge_ne
    {z : G.Dart} (hf : G.face z = z) (he : G.edge z ≠ z) :
    (G.walkupE z).Reachable
      (⟨G.edge z, he⟩ : G.DeletedDart z)
      (⟨G.node z, G.node_ne_of_face_eq_self_of_edge_ne hf he⟩ :
        G.DeletedDart z) := by
  let u : G.DeletedDart z :=
    ⟨G.node z, G.node_ne_of_face_eq_self_of_edge_ne hf he⟩
  let v : G.DeletedDart z := ⟨G.edge z, he⟩
  have hedge_node : G.edge (G.node z) = z := by
    calc
      G.edge (G.node z) = G.face.symm z := G.edge_node_eq_face_symm z
      _ = z := by
        calc
          G.face.symm z = G.face.symm (G.face z) := by rw [hf]
          _ = z := by simp
  have hedge : (G.walkupE z).edge u = v := by
    apply Subtype.ext
    have hperm :
        (G.walkupE z).edge u = (PermSkip.skip G.edge z) u := by
      exact congrArg (fun f : Equiv.Perm (G.DeletedDart z) => f u)
        (G.walkupE_edge_eq_skip_edge_of_face_eq hf)
    have hval :
        ((G.walkupE z).edge u).1 =
          ((PermSkip.skip G.edge z u : G.DeletedDart z) : G.Dart) :=
      congrArg Subtype.val hperm
    calc
      ((G.walkupE z).edge u).1 =
          ((PermSkip.skip G.edge z u : G.DeletedDart z) : G.Dart) := hval
      _ = G.edge z := PermSkip.skip_apply_of_apply_eq G.edge u hedge_node
      _ = v.1 := rfl
  have hreach : (G.walkupE z).Reachable v u := by
    rw [← hedge]
    exact (G.walkupE z).reachable_edge_symm u
  simpa [u, v] using hreach

theorem node_eq_self_iff_face_eq_self_of_edge_eq_self
    {z : G.Dart} (he : G.edge z = z) :
    G.node z = z ↔ G.face z = z := by
  have hnode_face : G.node (G.face z) = z := by
    simpa [he] using G.node_face_edge z
  constructor
  · intro hn
    apply G.node.injective
    calc
      G.node (G.face z) = z := hnode_face
      _ = G.node z := hn.symm
  · intro hf
    simpa [hf] using hnode_face

theorem walkupE_eulerRight_add_indicators_of_edge_eq
    {z : G.Dart} (he : G.edge z = z) :
    (1 + (if G.node z = z then 1 else 0) +
        (if G.face z = z then 1 else 0)) +
      (G.walkupE z).eulerRight = G.eulerRight := by
  have hedge := G.walkupE_edgeOrbitCount_add_one_of_edge_eq he
  have hnode := G.walkupE_nodeOrbitCount_add_indicator z
  have hface := G.walkupE_faceOrbitCount_add_indicator z
  unfold eulerRight at *
  omega

theorem walkupE_eulerRight_step_of_edge_eq
    {z : G.Dart} (he : G.edge z = z) :
    2 * (if G.node z = z then 2 else 1) +
      (G.walkupE z).eulerRight = G.eulerRight + 1 := by
  have hright := G.walkupE_eulerRight_add_indicators_of_edge_eq he
  by_cases hn : G.node z = z
  · have hf : G.face z = z :=
      (G.node_eq_self_iff_face_eq_self_of_edge_eq_self he).mp hn
    simp [hn, hf] at hright ⊢
    omega
  · have hf : G.face z ≠ z := by
      intro hf
      exact hn ((G.node_eq_self_iff_face_eq_self_of_edge_eq_self he).mpr hf)
    simp [hn, hf] at hright ⊢
    omega

theorem walkupE_exists_eulerRight_step_of_edge_eq
    {z : G.Dart} (he : G.edge z = z) :
    ∃ b : Nat,
      2 * b + (G.walkupE z).eulerRight = G.eulerRight + 1 :=
  ⟨if G.node z = z then 2 else 1,
    G.walkupE_eulerRight_step_of_edge_eq he⟩

theorem walkupE_edge_apply_coe_of_edge_fixed
    {z : G.Dart} (he : G.edge z = z) (x : G.DeletedDart z) :
    ((G.walkupE z).edge x).1 = G.edge x.1 := by
  have hperm :
      (G.walkupE z).edge x = (PermSkip.skip G.edge z) x := by
    exact congrArg (fun f : Equiv.Perm (G.DeletedDart z) => f x)
      (G.walkupE_edge_eq_skip_edge_of_edge_eq he)
  calc
    ((G.walkupE z).edge x).1 =
        ((PermSkip.skip G.edge z x : G.DeletedDart z) : G.Dart) :=
      congrArg Subtype.val hperm
    _ = G.edge x.1 := PermSkip.skip_apply_of_fixed G.edge he x

theorem walkupE_node_apply_coe_of_fixed
    {z : G.Dart} (hn : G.node z = z) (x : G.DeletedDart z) :
    ((G.walkupE z).node x).1 = G.node x.1 :=
  PermSkip.skip_apply_of_fixed G.node hn x

theorem walkupE_face_apply_coe_of_fixed
    {z : G.Dart} (hf : G.face z = z) (x : G.DeletedDart z) :
    ((G.walkupE z).face x).1 = G.face x.1 :=
  PermSkip.skip_apply_of_fixed G.face hf x

theorem walkupE_eulerRight_add_three_of_all_fixed
    {z : G.Dart} (he : G.edge z = z) (hn : G.node z = z)
    (hf : G.face z = z) :
    (G.walkupE z).eulerRight + 3 = G.eulerRight := by
  have h := G.walkupE_eulerRight_add_indicators_of_edge_eq he
  simpa [hn, hf, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h


end Hypermap

end FourColor

end Schematic.Math.GraphTheory
