import Schematic.Math.GraphTheory.Embedding.Geometry.Disk

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- A predicate is closed under face orbits. -/
def FaceClosed (A : G.Dart → Prop) : Prop :=
  ∀ ⦃x y : G.Dart⦄, A x → PermReachable G.face x y → A y

/-- Face closure of a predicate. -/
def FaceClosure (A : G.Dart → Prop) (x : G.Dart) : Prop :=
  ∃ y : G.Dart, PermReachable G.face x y ∧ A y

/-- Coq `kernel r`: the complement of the perimeter face band. -/
def Kernel (r : List G.Dart) (x : G.Dart) : Prop :=
  ¬ G.FaceBand r x

theorem kernel_faceClosed (r : List G.Dart) :
    G.FaceClosed (G.Kernel r) := by
  intro x y hx hxy hyBand
  exact hx (FaceBand.of_faceReachable (G := G) hyBand
    (PermReachable.symm G.face hxy))

theorem kernel_off_ring
    {r : List G.Dart} {x : G.Dart}
    (hx : G.Kernel r x) :
    x ∉ r := by
  intro hxr
  exact hx (FaceBand.of_mem (G := G) hxr
    (PermReachable.refl G.face x))

theorem faceClosure_of_mem
    {A : G.Dart → Prop} {x : G.Dart}
    (hx : A x) :
    G.FaceClosure A x :=
  ⟨x, PermReachable.refl G.face x, hx⟩

theorem faceClosure_of_faceReachable
    {A : G.Dart → Prop} {x y : G.Dart}
    (hx : G.FaceClosure A x)
    (hxy : PermReachable G.face x y) :
    G.FaceClosure A y := by
  rcases hx with ⟨z, hxz, hz⟩
  exact ⟨z, PermReachable.trans G.face
    (PermReachable.symm G.face hxy) hxz, hz⟩

theorem faceClosure_eq_self_of_faceClosed
    {A : G.Dart → Prop}
    (hclosed : G.FaceClosed A)
    (x : G.Dart) :
    G.FaceClosure A x ↔ A x := by
  constructor
  · rintro ⟨y, hxy, hy⟩
    exact hclosed hy (PermReachable.symm G.face hxy)
  · exact faceClosure_of_mem (G := G)

theorem FaceClosed.of_faceBand_sources
    {A : G.Dart → Prop}
    (hclosed : G.FaceClosed A)
    {s : List G.Dart}
    (hs : ∀ x : G.Dart, x ∈ s → A x) :
    ∀ ⦃y : G.Dart⦄, G.FaceBand s y → A y := by
  intro y hy
  rcases hy with ⟨x, hx, hxy⟩
  exact hclosed (hs x hx) hxy

theorem FaceClosed.of_faceBand_append_sources
    {A : G.Dart → Prop}
    (hclosed : G.FaceClosed A)
    {s t : List G.Dart}
    (hs : ∀ x : G.Dart, x ∈ s → A x)
    (ht : ∀ x : G.Dart, x ∈ t → A x) :
    ∀ ⦃y : G.Dart⦄, G.FaceBand (s ++ t) y → A y :=
  FaceClosed.of_faceBand_sources (G := G) hclosed (s := s ++ t) (by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs x hx
    · exact ht x hx)

theorem FaceBand.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {u : G.Dart} :
    G.FaceBand r u ↔ G.FaceBand s u := by
  constructor
  · exact FaceBand.subset (G := G) (fun x hx => (hmem x).1 hx)
  · exact FaceBand.subset (G := G) (fun x hx => (hmem x).2 hx)

theorem FaceBand.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {u : G.Dart} :
    G.FaceBand r u ↔ G.FaceBand s u :=
  FaceBand.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem FaceBand.rotate
    (n : Nat) {r : List G.Dart} {u : G.Dart} :
    G.FaceBand (r.rotate n) u ↔ G.FaceBand r u :=
  FaceBand.congr_mem (G := G)
    (fun x => by simp [List.mem_rotate])

theorem DLink.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {x y : G.Dart} :
    G.DLink r x y ↔ G.DLink s x y := by
  simp [DLink, hmem]

theorem DLink.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {x y : G.Dart} :
    G.DLink r x y ↔ G.DLink s x y :=
  DLink.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem DLink.rotate
    (n : Nat) {r : List G.Dart} {x y : G.Dart} :
    G.DLink (r.rotate n) x y ↔ G.DLink r x y :=
  DLink.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem DConnect.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {x y : G.Dart} :
    G.DConnect r x y ↔ G.DConnect s x y := by
  constructor
  · intro hxy
    exact hxy.lift id fun _ _ h => (DLink.congr_mem (G := G) hmem).1 h
  · intro hxy
    exact hxy.lift id fun _ _ h => (DLink.congr_mem (G := G) hmem).2 h

theorem DConnect.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {x y : G.Dart} :
    G.DConnect r x y ↔ G.DConnect s x y :=
  DConnect.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem DConnect.rotate
    (n : Nat) {r : List G.Dart} {x y : G.Dart} :
    G.DConnect (r.rotate n) x y ↔ G.DConnect r x y :=
  DConnect.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem DiskN.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {x : G.Dart} :
    G.DiskN r x ↔ G.DiskN s x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, (hmem y).1 hy,
      (DConnect.congr_mem (G := G) hmem).1 hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, (hmem y).2 hy,
      (DConnect.congr_mem (G := G) hmem).2 hxy⟩

theorem DiskN.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {x : G.Dart} :
    G.DiskN r x ↔ G.DiskN s x :=
  DiskN.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem DiskN.rotate
    (n : Nat) {r : List G.Dart} {x : G.Dart} :
    G.DiskN (r.rotate n) x ↔ G.DiskN r x :=
  DiskN.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem DiskE.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {x : G.Dart} :
    G.DiskE r x ↔ G.DiskE s x := by
  simp [DiskE, DiskN.congr_mem (G := G) hmem, hmem]

theorem DiskE.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {x : G.Dart} :
    G.DiskE r x ↔ G.DiskE s x :=
  DiskE.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem DiskE.rotate
    (n : Nat) {r : List G.Dart} {x : G.Dart} :
    G.DiskE (r.rotate n) x ↔ G.DiskE r x :=
  DiskE.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem DiskF.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {x : G.Dart} :
    G.DiskF r x ↔ G.DiskF s x := by
  simp [DiskF, DiskN.congr_mem (G := G) hmem,
    FaceBand.congr_mem (G := G) hmem]

theorem DiskF.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {x : G.Dart} :
    G.DiskF r x ↔ G.DiskF s x :=
  DiskF.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem DiskF.rotate
    (n : Nat) {r : List G.Dart} {x : G.Dart} :
    G.DiskF (r.rotate n) x ↔ G.DiskF r x :=
  DiskF.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem DiskFC.congr_mem
    {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s)
    {x : G.Dart} :
    G.DiskFC r x ↔ G.DiskFC s x := by
  simp [DiskFC, DiskN.congr_mem (G := G) hmem,
    FaceBand.congr_mem (G := G) hmem]

theorem DiskFC.perm
    {r s : List G.Dart}
    (hp : r.Perm s)
    {x : G.Dart} :
    G.DiskFC r x ↔ G.DiskFC s x :=
  DiskFC.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem DiskFC.rotate
    (n : Nat) {r : List G.Dart} {x : G.Dart} :
    G.DiskFC (r.rotate n) x ↔ G.DiskFC r x :=
  DiskFC.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem NontrivialRing.congr_mem
    {m : Nat} {r s : List G.Dart}
    (hmem : ∀ x : G.Dart, x ∈ r ↔ x ∈ s) :
    G.NontrivialRing m r ↔ G.NontrivialRing m s := by
  have hF :
      G.FaceOrbitCountOf (G.DiskF r) =
        G.FaceOrbitCountOf (G.DiskF s) :=
    G.faceOrbitCountOf_congr
      (fun x => DiskF.congr_mem (G := G) hmem)
  have hFC :
      G.FaceOrbitCountOf (G.DiskFC r) =
        G.FaceOrbitCountOf (G.DiskFC s) :=
    G.faceOrbitCountOf_congr
      (fun x => DiskFC.congr_mem (G := G) hmem)
  simp [NontrivialRing, hF, hFC]

theorem NontrivialRing.perm
    {m : Nat} {r s : List G.Dart}
    (hp : r.Perm s) :
    G.NontrivialRing m r ↔ G.NontrivialRing m s :=
  NontrivialRing.congr_mem (G := G) (fun _ => hp.mem_iff)

theorem NontrivialRing.rotate
    (n : Nat) {m : Nat} {r : List G.Dart} :
    G.NontrivialRing m (r.rotate n) ↔ G.NontrivialRing m r :=
  NontrivialRing.congr_mem (G := G)
    (fun z => by simp [List.mem_rotate])

theorem FaceBand.nil
    {u : G.Dart} :
    ¬ G.FaceBand [] u := by
  rintro ⟨x, hx, _⟩
  cases hx

theorem FaceBand.singleton
    {x u : G.Dart} :
    G.FaceBand [x] u ↔ PermReachable G.face x u := by
  rw [FaceBand.cons]
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim (FaceBand.nil (G := G) h)
  · exact Or.inl

theorem FaceBand.concat
    {r : List G.Dart} {x u : G.Dart} :
    G.FaceBand (r ++ [x]) u ↔
      G.FaceBand r u ∨ PermReachable G.face x u := by
  rw [FaceBand.append, FaceBand.singleton]

theorem FaceBand.append_comm
    {r s : List G.Dart} {u : G.Dart} :
    G.FaceBand (r ++ s) u ↔ G.FaceBand (s ++ r) u := by
  rw [FaceBand.append, FaceBand.append]
  exact or_comm

theorem FaceBand.optional_prefix
    {r : List G.Dart} {x u : G.Dart} (b : Bool) :
    G.FaceBand ((if b then [x] else []) ++ r) u ↔
      (b = true ∧ PermReachable G.face x u) ∨ G.FaceBand r u := by
  cases b <;> simp [FaceBand.cons]

theorem FaceBand.two_optional_prefixes
    {r : List G.Dart} {x y u : G.Dart} (b0 b1 : Bool) :
    G.FaceBand
        ((if b0 then [x] else []) ++ (if b1 then [y] else []) ++ r) u ↔
      (b0 = true ∧ PermReachable G.face x u) ∨
        (b1 = true ∧ PermReachable G.face y u) ∨
          G.FaceBand r u := by
  cases b0 <;> cases b1 <;> simp [FaceBand.cons]

theorem FaceBand.optional_middle
    {r s : List G.Dart} {x u : G.Dart} (b : Bool) :
    G.FaceBand (r ++ (if b then [x] else []) ++ s) u ↔
      G.FaceBand r u ∨
        (b = true ∧ PermReachable G.face x u) ∨
          G.FaceBand s u := by
  rw [FaceBand.append]
  cases b
  · simp
  · simp
    rw [FaceBand.concat]
    tauto

theorem FaceBand.rotate_cons
    {r : List G.Dart} {x u : G.Dart} :
    G.FaceBand (x :: r) u ↔ G.FaceBand (r ++ [x]) u := by
  rw [FaceBand.cons, FaceBand.concat]
  exact or_comm

/-- The finite set of darts in the face orbit of `x`. -/
noncomputable def faceOrbitFinset
    [Fintype G.Dart] [DecidableEq G.Dart]
    (x : G.Dart) : Finset G.Dart := by
  classical
  exact Finset.univ.filter (fun y : G.Dart => PermReachable G.face x y)

@[simp]
theorem mem_faceOrbitFinset
    [Fintype G.Dart] [DecidableEq G.Dart]
    {x y : G.Dart} :
    y ∈ G.faceOrbitFinset x ↔ PermReachable G.face x y := by
  classical
  simp [faceOrbitFinset]

/-- A concrete list enumerating the face orbit of `x`.  This is useful at the
graph-embedding boundary, where the face containing a contracted vertex must
be turned into finite boundary data. -/
noncomputable def faceOrbitList
    [Fintype G.Dart] [DecidableEq G.Dart]
    (x : G.Dart) : List G.Dart :=
  (G.faceOrbitFinset x).toList

@[simp]
theorem mem_faceOrbitList
    [Fintype G.Dart] [DecidableEq G.Dart]
    {x y : G.Dart} :
    y ∈ G.faceOrbitList x ↔ PermReachable G.face x y := by
  classical
  simp [faceOrbitList]

theorem faceOrbitList_self_mem
    [Fintype G.Dart] [DecidableEq G.Dart]
    (x : G.Dart) :
    x ∈ G.faceOrbitList x := by
  rw [mem_faceOrbitList]
  exact PermReachable.refl G.face x

theorem FaceBand.faceOrbitList_iff
    [Fintype G.Dart] [DecidableEq G.Dart]
    {x u : G.Dart} :
    G.FaceBand (G.faceOrbitList x) u ↔
      PermReachable G.face x u := by
  constructor
  · rintro ⟨y, hy, hyu⟩
    exact PermReachable.trans G.face ((mem_faceOrbitList (G := G)).mp hy) hyu
  · intro hxu
    exact ⟨x, G.faceOrbitList_self_mem x, hxu⟩

theorem faceOrbitList_face_mem
    [Fintype G.Dart] [DecidableEq G.Dart]
    {x y : G.Dart}
    (hy : y ∈ G.faceOrbitList x) :
    G.face y ∈ G.faceOrbitList x := by
  rw [mem_faceOrbitList] at hy ⊢
  exact PermReachable.trans G.face hy (PermReachable.forward G.face y)

theorem faceOrbitList_face_symm_mem
    [Fintype G.Dart] [DecidableEq G.Dart]
    {x y : G.Dart}
    (hy : y ∈ G.faceOrbitList x) :
    G.face.symm y ∈ G.faceOrbitList x := by
  rw [mem_faceOrbitList] at hy ⊢
  exact PermReachable.trans G.face hy (PermReachable.backward G.face y)

/-- A list is face-simple when no two entries lie in the same face orbit.
This is the Prop-valued analogue of Coq `simple` for `permF G`. -/
def FaceSimple (s : List G.Dart) : Prop :=
  s.Pairwise (fun x y => ¬ PermReachable G.face x y)

theorem faceBand_iff_mem_faceOrbit_map
    {s : List G.Dart} {u : G.Dart} :
    G.FaceBand s u ↔
      PermOrbit.of G.face u ∈ s.map (PermOrbit.of G.face) := by
  constructor
  · rintro ⟨x, hx, hxu⟩
    exact List.mem_map.mpr
      ⟨x, hx, PermOrbit.of_eq_of G.face hxu⟩
  · intro hu
    rcases List.mem_map.mp hu with ⟨x, hx, hxu⟩
    exact ⟨x, hx, Quotient.exact hxu⟩

theorem faceSimple_iff_nodup_faceOrbit_map
    {s : List G.Dart} :
    G.FaceSimple s ↔
      (s.map (PermOrbit.of G.face)).Nodup := by
  induction s with
  | nil =>
      simp [FaceSimple]
  | cons x s ih =>
      rw [FaceSimple, List.pairwise_cons, List.map_cons,
        List.nodup_cons, ← ih]
      constructor
      · rintro ⟨hhead, htail⟩
        refine ⟨?_, htail⟩
        intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hyx⟩
        exact hhead y hy
          (PermReachable.symm G.face (Quotient.exact hyx))
      · rintro ⟨hhead, htail⟩
        refine ⟨?_, htail⟩
        intro y hy hxy
        apply hhead
        exact List.mem_map.mpr
          ⟨y, hy, (PermOrbit.of_eq_of G.face hxy).symm⟩

/-- A face-simple list meets exactly one face orbit per listed dart.  This is
the `fcard face (fband r) = size r` count used by Coq's snip arithmetic. -/
theorem faceOrbitCountOf_faceBand_eq_length
    {s : List G.Dart} (hs : G.FaceSimple s) :
    G.FaceOrbitCountOf (G.FaceBand s) = s.length := by
  classical
  let orbitList : List G.FaceOrbit :=
    s.map (PermOrbit.of G.face)
  let e : G.FaceOrbitMeeting (G.FaceBand s) ≃
      {o : G.FaceOrbit // o ∈ orbitList} :=
    Equiv.subtypeEquivRight (fun o => by
      refine Quotient.inductionOn o ?_
      intro u
      constructor
      · rintro ⟨x, hxu, hx⟩
        have hxmem : PermOrbit.of G.face x ∈ orbitList :=
          (faceBand_iff_mem_faceOrbit_map (G := G)).mp hx
        simpa only [hxu] using hxmem
      · intro hu
        exact ⟨u, rfl,
          (faceBand_iff_mem_faceOrbit_map (G := G)).mpr hu⟩)
  have hnodup : orbitList.Nodup := by
    exact (faceSimple_iff_nodup_faceOrbit_map G).mp hs
  rw [FaceOrbitCountOf]
  calc
    Nat.card (G.FaceOrbitMeeting (G.FaceBand s)) =
        Nat.card {o : G.FaceOrbit // o ∈ orbitList} :=
      Nat.card_congr e
    _ = Fintype.card {o : G.FaceOrbit // o ∈ orbitList} :=
      Nat.card_eq_fintype_card
    _ = orbitList.toFinset.card := by
      simpa using Fintype.card_coe orbitList.toFinset
    _ = orbitList.length := List.toFinset_card_of_nodup hnodup
    _ = s.length := by simp [orbitList]

/-- Coq `eq_simple`: lists of the same length meeting exactly the same face
orbits are face-simple simultaneously. -/
theorem FaceSimple.congr_of_faceBand_iff_of_length_eq
    {s t : List G.Dart}
    (hband : ∀ u : G.Dart, G.FaceBand s u ↔ G.FaceBand t u)
    (hlen : s.length = t.length) :
    G.FaceSimple s ↔ G.FaceSimple t := by
  classical
  let f : G.Dart → PermOrbit G.face := PermOrbit.of G.face
  have hmem : ∀ o : PermOrbit G.face, o ∈ s.map f ↔ o ∈ t.map f := by
    intro o
    refine Quotient.inductionOn o ?_
    intro u
    simpa [f, faceBand_iff_mem_faceOrbit_map (G := G)] using hband u
  have hfinset : (s.map f).toFinset = (t.map f).toFinset := by
    ext o
    simpa using hmem o
  have nodup_iff_card (l : List (PermOrbit G.face)) :
      l.Nodup ↔ l.toFinset.card = l.length := by
    constructor
    · exact List.toFinset_card_of_nodup
    · intro hcard
      have hcard' :
          (↑l : Multiset (PermOrbit G.face)).toFinset.card =
            (↑l : Multiset (PermOrbit G.face)).card := by
        simpa using hcard
      simpa using
        (Multiset.toFinset_card_eq_card_iff_nodup.mp hcard')
  rw [faceSimple_iff_nodup_faceOrbit_map,
    faceSimple_iff_nodup_faceOrbit_map]
  constructor
  · intro hs
    apply (nodup_iff_card _).2
    calc
      (t.map f).toFinset.card = (s.map f).toFinset.card := by rw [hfinset]
      _ = (s.map f).length := List.toFinset_card_of_nodup hs
      _ = s.length := by simp
      _ = t.length := hlen
      _ = (t.map f).length := by simp
  · intro ht
    apply (nodup_iff_card _).2
    calc
      (s.map f).toFinset.card = (t.map f).toFinset.card := by rw [hfinset]
      _ = (t.map f).length := List.toFinset_card_of_nodup ht
      _ = t.length := by simp
      _ = s.length := hlen.symm
      _ = (s.map f).length := by simp

theorem FaceSimple.tail
    {s : List G.Dart} {x : G.Dart}
    (hs : G.FaceSimple (x :: s)) :
    G.FaceSimple s :=
  (List.pairwise_cons.mp hs).2

theorem FaceSimple.not_faceReachable_head
    {s : List G.Dart} {x y : G.Dart}
    (hs : G.FaceSimple (x :: s))
    (hy : y ∈ s) :
    ¬ PermReachable G.face x y :=
  (List.pairwise_cons.mp hs).1 y hy

theorem FaceSimple.map_iff
    {H : Hypermap} {f : G.Dart → H.Dart}
    (hf :
      ∀ x y : G.Dart,
        PermReachable H.face (f x) (f y) ↔
          PermReachable G.face x y)
    {s : List G.Dart} :
    H.FaceSimple (s.map f) ↔ G.FaceSimple s := by
  simp [FaceSimple, List.pairwise_map, hf]

theorem FaceSimple.perm
    {s t : List G.Dart}
    (hp : s.Perm t)
    (hs : G.FaceSimple s) :
    G.FaceSimple t := by
  refine (hp.pairwise_iff ?_).1 hs
  intro x y hxy hyx
  exact hxy (PermReachable.symm G.face hyx)

theorem FaceSimple.rotate
    (n : Nat) {s : List G.Dart}
    (hs : G.FaceSimple s) :
    G.FaceSimple (s.rotate n) :=
  FaceSimple.perm (G := G) (List.rotate_perm s n).symm hs

theorem FaceSimple.eq_of_faceReachable_of_mem
    {s : List G.Dart}
    (hs : G.FaceSimple s)
    {x y : G.Dart}
    (hx : x ∈ s)
    (hy : y ∈ s)
    (hxy : PermReachable G.face x y) :
    x = y := by
  by_contra hne
  have hsym :
      Symmetric (fun x y : G.Dart => ¬ PermReachable G.face x y) := by
    intro x y hxy hyx
    exact hxy (PermReachable.symm G.face hyx)
  exact (List.Pairwise.forall hsym hs hx hy hne) hxy

theorem FaceSimple.nodup
    {s : List G.Dart}
    (hs : G.FaceSimple s) :
    s.Nodup := by
  rw [FaceSimple] at hs
  exact hs.imp (by
    intro x y hxy hEq
    subst y
    exact hxy (PermReachable.refl G.face x))

/-- A face-simple pair of source lists that covers every face partitions the
map into the two corresponding face bands. -/
theorem FaceSimple.faceBand_left_iff_not_right_of_append_cover
    {s r : List G.Dart}
    (hsimple : G.FaceSimple (s ++ r))
    (hcover : ∀ x : G.Dart, G.FaceBand (s ++ r) x)
    (x : G.Dart) :
    G.FaceBand s x ↔ ¬ G.FaceBand r x := by
  constructor
  · rintro ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : PermReachable G.face a b :=
      PermReachable.trans G.face hax (PermReachable.symm G.face hbx)
    have habEq : a = b :=
      Hypermap.FaceSimple.eq_of_faceReachable_of_mem
        (G := G) hsimple
        (List.mem_append.mpr (Or.inl ha))
        (List.mem_append.mpr (Or.inr hb)) hab
    have hnodup : (s ++ r).Nodup := hsimple.nodup
    have hdisjoint : s.Disjoint r :=
      List.disjoint_of_nodup_append hnodup
    exact hdisjoint ha (habEq ▸ hb)
  · intro hnotRight
    rcases hcover x with ⟨a, ha, hax⟩
    rcases List.mem_append.mp ha with haLeft | haRight
    · exact ⟨a, haLeft, hax⟩
    · exact False.elim (hnotRight ⟨a, haRight, hax⟩)

/-- Chord-prefix form of face-simplicity.  If a ring has been rotated into
`y₂ :: p₁ ++ y₁ :: p₂` and a new chord dart `x` lies in the face orbit of
`y₁`, then replacing the terminal projection `y₁` by `x` keeps the displayed
prefix face-simple.  This is the face-simplicity part of Coq
`scycle_chord_ring`. -/
theorem FaceSimple.chord_prefix
    {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hs : G.FaceSimple (y₂ :: p₁ ++ y₁ :: p₂))
    (hy₁x : PermReachable G.face y₁ x) :
    G.FaceSimple (x :: y₂ :: p₁) := by
  have htail : G.FaceSimple (y₂ :: p₁) := by
    rw [FaceSimple] at hs ⊢
    have hsub :
        (y₂ :: p₁).Sublist (y₂ :: p₁ ++ y₁ :: p₂) := by
      simp [List.cons_append]
    exact List.Pairwise.sublist hsub hs
  rw [FaceSimple, List.pairwise_cons]
  constructor
  · intro z hz hxz
    have hsym :
        Symmetric (fun a b : G.Dart => ¬ PermReachable G.face a b) := by
      intro a b hab hba
      exact hab (PermReachable.symm G.face hba)
    have hnodup :
        ((y₂ :: p₁) ++ y₁ :: p₂).Nodup := by
      simpa [List.cons_append] using FaceSimple.nodup (G := G) hs
    have hy₁_not_prefix : y₁ ∉ y₂ :: p₁ := by
      intro hy₁
      have hdisj := (List.nodup_append.mp hnodup).2.2
      exact hdisj y₁ hy₁ y₁ (by simp) rfl
    have hzOrig : z ∈ y₂ :: p₁ ++ y₁ :: p₂ := by
      rw [List.mem_cons] at hz
      rcases hz with hzy₂ | hzp₁
      · simp [hzy₂]
      · simp [hzp₁]
    have hy₁Orig : y₁ ∈ y₂ :: p₁ ++ y₁ :: p₂ := by
      simp
    have hzy₁_ne : z ≠ y₁ := by
      intro hzy₁
      subst z
      exact hy₁_not_prefix hz
    have hzy₁ :
        ¬ PermReachable G.face z y₁ :=
      List.Pairwise.forall hsym hs hzOrig hy₁Orig hzy₁_ne
    exact hzy₁
      (PermReachable.trans G.face
        (PermReachable.symm G.face hxz)
        (PermReachable.symm G.face hy₁x))
  · simpa [FaceSimple] using htail

theorem FaceSimple.edge_chord_suffix_of_plain
    {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hs : G.FaceSimple (y₂ :: p₁ ++ y₁ :: p₂))
    (hy₂ex : PermReachable G.face y₂ (G.edge x)) :
    G.FaceSimple (G.edge x :: y₁ :: p₂) := by
  have hperm :
      (y₂ :: p₁ ++ y₁ :: p₂).Perm
        (y₁ :: p₂ ++ y₂ :: p₁) := by
    simpa [List.cons_append, List.append_assoc] using
      (List.perm_append_comm :
        ((y₂ :: p₁) ++ (y₁ :: p₂)).Perm ((y₁ :: p₂) ++ (y₂ :: p₁)))
  have hsRot : G.FaceSimple (y₁ :: p₂ ++ y₂ :: p₁) :=
    FaceSimple.perm (G := G) hperm hs
  exact FaceSimple.chord_prefix
    (G := G) (x := G.edge x) (y₁ := y₂) (y₂ := y₁)
    (p₁ := p₂) (p₂ := p₁) hsRot hy₂ex

private theorem forall₂_exists_left_of_mem_right
    {α β : Type _} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys)
    {y : β}
    (hy : y ∈ ys) :
    ∃ x : α, x ∈ xs ∧ R x y := by
  induction h with
  | nil =>
      cases hy
  | cons hxy hrest ih =>
      simp at hy
      rcases hy with hy | hy
      · subst y
        exact ⟨_, by simp, hxy⟩
      · rcases ih hy with ⟨x, hx, hxy'⟩
        exact ⟨x, by simp [hx], hxy'⟩

theorem FaceSimple.of_forall₂_faceReachable
    {s t : List G.Dart}
    (hst :
      List.Forall₂ (fun x y : G.Dart => PermReachable G.face x y) s t)
    (hs : G.FaceSimple s) :
    G.FaceSimple t := by
  induction hst with
  | nil =>
      simp [FaceSimple]
  | cons hxy hrest ih =>
      rw [FaceSimple] at hs ⊢
      rw [List.pairwise_cons] at hs ⊢
      constructor
      · intro y hy htarget
        rcases forall₂_exists_left_of_mem_right hrest hy with
          ⟨x, hx, hxyTail⟩
        exact hs.1 x hx
          (PermReachable.trans G.face hxy
            (PermReachable.trans G.face htarget
              (PermReachable.symm G.face hxyTail)))
      · exact ih hs.2

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
