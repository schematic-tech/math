import Schematic.Math.GraphTheory.Embedding.Geometry.RLinkPaths

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Coq `scycle rlink r`: an `rlink` cycle whose listed darts are face-simple. -/
def SimpleRLinkCycle (r : List G.Dart) : Prop :=
  G.RLinkCycle r ∧ G.FaceSimple r

theorem SimpleRLinkCycle.cycle
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r) :
    G.RLinkCycle r :=
  hr.1

theorem SimpleRLinkCycle.faceSimple
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r) :
    G.FaceSimple r :=
  hr.2

/-- Chord-ring constructor in rotated-prefix form.  This packages the core
list decomposition used in Coq `scycle_chord_ring`: after rotating a simple
`rlink` cycle to `y₂ :: p₁ ++ y₁ :: p₂`, a chord dart `x` whose reverse
projects to `y₂` and whose own face projects to `y₁` forms the simple
`rlink` cycle `x :: y₂ :: p₁`. -/
theorem SimpleRLinkCycle.chord_prefix_of_decomposition
    {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hxy₂ : G.RLink x y₂)
    (hy₁x : PermReachable G.face y₁ x) :
    G.SimpleRLinkCycle (x :: y₂ :: p₁) := by
  have hpathOrig :
      G.RLinkPath y₂ (p₁ ++ y₁ :: p₂) := hr.1.1
  have hpathPrefix :
      G.RLinkPath y₂ p₁ :=
    RLinkPath.prefix_of_append (G := G) hpathOrig
  have hlast_y₁ :
      G.RLink ((y₂ :: p₁).getLastD y₂) y₁ :=
    RLinkPath.last_link_of_append_cons (G := G) hpathOrig
  have hclose :
      G.RLink ((x :: y₂ :: p₁).getLastD x) x := by
    have hlast_eq :
        (x :: y₂ :: p₁).getLastD x =
          (y₂ :: p₁).getLastD y₂ := by
      simp [List.getLastD]
    rw [hlast_eq]
    exact RLink.of_faceReachable_right (G := G) hlast_y₁ hy₁x
  exact
    ⟨⟨⟨hxy₂, hpathPrefix⟩, hclose⟩,
      FaceSimple.chord_prefix (G := G) hr.2 hy₁x⟩

theorem SimpleRLinkCycle.edge_chord_suffix_of_decomposition
    (hPlain : G.Plain)
    {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    (hr : G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂))
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x)) :
    G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂) := by
  have hpathOrig :
      G.RLinkPath y₂ (p₁ ++ y₁ :: p₂) := hr.1.1
  have hpathSuffix :
      G.RLinkPath y₁ p₂ :=
    RLinkPath.suffix_of_append_cons (G := G) hpathOrig
  have hlast_y₂ :
      G.RLink ((y₁ :: p₂).getLastD y₁) y₂ := by
    have hlast_eq :
        (y₂ :: p₁ ++ y₁ :: p₂).getLastD y₂ =
          (y₁ :: p₂).getLastD y₁ := by
      simpa [List.cons_append, List.append_assoc] using
        (List.getLastD_cons_append_cons y₂ y₁ p₁ p₂)
    rw [← hlast_eq]
    exact hr.1.2
  have hhead :
      G.RLink (G.edge x) y₁ := by
    unfold RLink
    simpa [Plain.edge_edge (G := G) hPlain x] using
      PermReachable.symm G.face hy₁x
  have hclose :
      G.RLink ((G.edge x :: y₁ :: p₂).getLastD (G.edge x)) (G.edge x) := by
    have hlast_eq :
        (G.edge x :: y₁ :: p₂).getLastD (G.edge x) =
          (y₁ :: p₂).getLastD y₁ := by
      simp [List.getLastD]
    rw [hlast_eq]
    exact RLink.of_faceReachable_right (G := G) hlast_y₂ hy₂ex
  exact
    ⟨⟨⟨hhead, hpathSuffix⟩, hclose⟩,
      FaceSimple.edge_chord_suffix_of_plain
        (G := G) hr.2 hy₂ex⟩

/-- Local-projection form of Coq `scycle_chord_ring`: if `y₁` and `y₂` are
the two distinct ring projections of `x` and `edge x`, then rotating the ring
at `y₂` and taking the prefix up to `y₁` gives the chord ring.  This is the
assumption-minimal core; global bridgelessness is only one way to prove the
projection inequality. -/
theorem SimpleRLinkCycle.exists_chord_prefix_of_witnesses
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x y₁ y₂ : G.Dart}
    (hy₁r : y₁ ∈ r)
    (hy₂r : y₂ ∈ r)
    (hy₂y₁ : y₂ ≠ y₁)
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x)) :
    ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
      r.rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
        G.SimpleRLinkCycle (x :: y₂ :: p₁) := by
  rcases (List.mem_iff_append).1 hy₂r with ⟨pre, post, hsplit⟩
  have hrot :
      r.rotate pre.length = y₂ :: (post ++ pre) := by
    rw [hsplit]
    rw [List.rotate_append_length_eq]
    simp
  have hy₁Rot : y₁ ∈ y₂ :: (post ++ pre) := by
    rw [← hrot]
    simpa [List.mem_rotate] using hy₁r
  have hy₁Tail : y₁ ∈ post ++ pre := by
    rw [List.mem_cons] at hy₁Rot
    rcases hy₁Rot with hy₁Head | hy₁Tail
    · exact False.elim (hy₂y₁ hy₁Head.symm)
    · exact hy₁Tail
  rcases (List.mem_iff_append).1 hy₁Tail with ⟨p₁, p₂, htail⟩
  have hdecomp :
      r.rotate pre.length = y₂ :: p₁ ++ y₁ :: p₂ := by
    rw [hrot, htail]
    simp
  have hrRot : G.SimpleRLinkCycle (r.rotate pre.length) :=
    ⟨RLinkCycle.rotate (G := G) pre.length hr.1,
      FaceSimple.rotate (G := G) pre.length hr.2⟩
  have hrDecomp :
      G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂) := by
    simpa [hdecomp] using hrRot
  have hxy₂ : G.RLink x y₂ :=
    PermReachable.symm G.face hy₂ex
  exact
    ⟨p₁, p₂, pre.length, hdecomp,
      SimpleRLinkCycle.chord_prefix_of_decomposition
        (G := G) hrDecomp hxy₂ hy₁x⟩

/-- Symmetric chord-ring constructor for `edge x`, corresponding to Coq's
`cr2 := chord_ring (edge x)`. -/
theorem SimpleRLinkCycle.exists_edge_chord_prefix_of_witnesses
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x y₁ y₂ : G.Dart}
    (hy₁r : y₁ ∈ r)
    (hy₂r : y₂ ∈ r)
    (hy₂y₁ : y₂ ≠ y₁)
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x)) :
    ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
      r.rotate i = y₁ :: p₁ ++ y₂ :: p₂ ∧
        G.SimpleRLinkCycle (G.edge x :: y₁ :: p₁) := by
  have hy₁eex : PermReachable G.face y₁ (G.edge (G.edge x)) := by
    simpa [Plain.edge_edge (G := G) hPlain x] using hy₁x
  exact
    SimpleRLinkCycle.exists_chord_prefix_of_witnesses
      (G := G) hr (x := G.edge x) (y₁ := y₂) (y₂ := y₁)
      hy₂r hy₁r (by intro h; exact hy₂y₁ h.symm)
      hy₂ex hy₁eex

/-- Existential chord-ring constructor from Coq `scycle_chord_ring`.  If both
`x` and `edge x` lie in the face band of a simple `rlink` ring, bridgelessness
separates their projections; after rotating the ring at the `edge x`
projection, the prefix up to the `x` projection gives a new simple
`rlink` cycle. -/
theorem SimpleRLinkCycle.exists_chord_prefix_of_faceBand
    (hBridgeless : G.Bridgeless)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart}
    (hx : G.FaceBand r x)
    (hex : G.FaceBand r (G.edge x)) :
    ∃ y₁ : G.Dart, ∃ y₂ : G.Dart,
      ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
        y₁ ∈ r ∧ y₂ ∈ r ∧
          r.rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
            G.SimpleRLinkCycle (x :: y₂ :: p₁) := by
  rcases hx with ⟨y₁, hy₁r, hy₁x⟩
  rcases hex with ⟨y₂, hy₂r, hy₂ex⟩
  have hy₂y₁ : y₂ ≠ y₁ := by
    intro h
    subst y₂
    exact hBridgeless x
      (PermReachable.trans G.face
        (PermReachable.symm G.face hy₁x) hy₂ex)
  rcases SimpleRLinkCycle.exists_chord_prefix_of_witnesses
      (G := G) hr hy₁r hy₂r hy₂y₁ hy₁x hy₂ex with
    ⟨p₁, p₂, i, hdecomp, hcycle⟩
  exact
    ⟨y₁, y₂, p₁, p₂, i, hy₁r, hy₂r, hdecomp, hcycle⟩

/-- Same-decomposition paired chord-ring constructor.  This is the local Lean
form of Coq's adjacent definitions `cr1 := chord_ring x` and
`cr2 := chord_ring (edge x)`: after one rotation
`r.rotate i = y₂ :: p₁ ++ y₁ :: p₂`, the first chord ring is the prefix
`x :: y₂ :: p₁` and the second is the complementary suffix
`edge x :: y₁ :: p₂`. -/
theorem SimpleRLinkCycle.exists_chord_pair_same_decomposition_of_witnesses
    (hPlain : G.Plain)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x y₁ y₂ : G.Dart}
    (hy₁r : y₁ ∈ r)
    (hy₂r : y₂ ∈ r)
    (hy₂y₁ : y₂ ≠ y₁)
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x)) :
    ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
      r.rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
        G.SimpleRLinkCycle (x :: y₂ :: p₁) ∧
          G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂) := by
  rcases SimpleRLinkCycle.exists_chord_prefix_of_witnesses
      (G := G) hr hy₁r hy₂r hy₂y₁ hy₁x hy₂ex with
    ⟨p₁, p₂, i, hdecomp, hcycle₁⟩
  have hrRot : G.SimpleRLinkCycle (r.rotate i) :=
    ⟨RLinkCycle.rotate (G := G) i hr.1,
      FaceSimple.rotate (G := G) i hr.2⟩
  have hrDecomp :
      G.SimpleRLinkCycle (y₂ :: p₁ ++ y₁ :: p₂) := by
    simpa [hdecomp] using hrRot
  have hcycle₂ :
      G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂) :=
    SimpleRLinkCycle.edge_chord_suffix_of_decomposition
      (G := G) hPlain hrDecomp hy₁x hy₂ex
  exact ⟨p₁, p₂, i, hdecomp, hcycle₁, hcycle₂⟩

/-- Face-band version of the same-decomposition chord-ring constructor. -/
theorem SimpleRLinkCycle.exists_chord_pair_same_decomposition_of_faceBand
    (hPlain : G.Plain)
    (hBridgeless : G.Bridgeless)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart}
    (hx : G.FaceBand r x)
    (hex : G.FaceBand r (G.edge x)) :
    ∃ y₁ : G.Dart, ∃ y₂ : G.Dart,
      ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
        y₁ ∈ r ∧ y₂ ∈ r ∧
          r.rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
            G.SimpleRLinkCycle (x :: y₂ :: p₁) ∧
              G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂) := by
  rcases hx with ⟨y₁, hy₁r, hy₁x⟩
  rcases hex with ⟨y₂, hy₂r, hy₂ex⟩
  have hy₂y₁ : y₂ ≠ y₁ := by
    intro h
    subst y₂
    exact hBridgeless x
      (PermReachable.trans G.face
        (PermReachable.symm G.face hy₁x) hy₂ex)
  rcases SimpleRLinkCycle.exists_chord_pair_same_decomposition_of_witnesses
      (G := G) hPlain hr hy₁r hy₂r hy₂y₁ hy₁x hy₂ex with
    ⟨p₁, p₂, i, hdecomp, hcycle₁, hcycle₂⟩
  exact
    ⟨y₁, y₂, p₁, p₂, i, hy₁r, hy₂r,
      hdecomp, hcycle₁, hcycle₂⟩

/-- Paired chord-ring constructor for the two rings `chord_ring x` and
`chord_ring (edge x)`.  This packages the setup immediately following Coq
`scycle_chord_ring`; the two returned decompositions may use different
rotations of the same source ring. -/
theorem SimpleRLinkCycle.exists_chord_pair_of_faceBand
    (hPlain : G.Plain)
    (hBridgeless : G.Bridgeless)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart}
    (hx : G.FaceBand r x)
    (hex : G.FaceBand r (G.edge x)) :
    ∃ y₁ : G.Dart, ∃ y₂ : G.Dart,
      ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
        ∃ q₁ : List G.Dart, ∃ q₂ : List G.Dart, ∃ j : Nat,
          y₁ ∈ r ∧ y₂ ∈ r ∧
            r.rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
              r.rotate j = y₁ :: q₁ ++ y₂ :: q₂ ∧
                G.SimpleRLinkCycle (x :: y₂ :: p₁) ∧
                  G.SimpleRLinkCycle (G.edge x :: y₁ :: q₁) := by
  rcases hx with ⟨y₁, hy₁r, hy₁x⟩
  rcases hex with ⟨y₂, hy₂r, hy₂ex⟩
  have hy₂y₁ : y₂ ≠ y₁ := by
    intro h
    subst y₂
    exact hBridgeless x
      (PermReachable.trans G.face
        (PermReachable.symm G.face hy₁x) hy₂ex)
  rcases SimpleRLinkCycle.exists_chord_prefix_of_witnesses
      (G := G) hr hy₁r hy₂r hy₂y₁ hy₁x hy₂ex with
    ⟨p₁, p₂, i, hdecomp₁, hcycle₁⟩
  rcases SimpleRLinkCycle.exists_edge_chord_prefix_of_witnesses
      (G := G) hPlain hr hy₁r hy₂r hy₂y₁ hy₁x hy₂ex with
    ⟨q₁, q₂, j, hdecomp₂, hcycle₂⟩
  exact
    ⟨y₁, y₂, p₁, p₂, i, q₁, q₂, j, hy₁r, hy₂r,
      hdecomp₁, hdecomp₂, hcycle₁, hcycle₂⟩

theorem properRing_chord_prefix_of_diskE_edge
    {r : List G.Dart} {x y₂ : G.Dart} {p₁ : List G.Dart}
    (hEdgeDisk : G.DiskE r (G.edge x))
    (hy₂r : y₂ ∈ r) :
    G.ProperRing (x :: y₂ :: p₁) := by
  cases p₁ with
  | nil =>
      left
      intro hpath
      have hxy₂ : G.edge x = y₂ := hpath.1
      exact hEdgeDisk.2 (by simpa [← hxy₂] using hy₂r)
  | cons z p₁ =>
      right
      simp

theorem length_chord_prefix_lt_of_decomposition
    {r : List G.Dart} {x y₁ y₂ : G.Dart} {p₁ p₂ : List G.Dart}
    {i : Nat}
    (hdecomp : r.rotate i = y₂ :: p₁ ++ y₁ :: p₂)
    (hp₂ : p₂ ≠ []) :
    (x :: y₂ :: p₁).length < r.length := by
  cases p₂ with
  | nil =>
      exact False.elim (hp₂ rfl)
  | cons z p₂ =>
      have hlen := congrArg List.length hdecomp
      simp [List.length_rotate] at hlen
      simp
      omega

theorem FaceBand.chord_prefix_union
    {x y₁ y₂ u : G.Dart} {p₁ p₂ : List G.Dart}
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x)) :
    (G.FaceBand (x :: y₂ :: p₁) u ∨
        G.FaceBand (G.edge x :: y₁ :: p₂) u) ↔
      G.FaceBand (y₂ :: p₁ ++ y₁ :: p₂) u := by
  have hx_iff :
      PermReachable G.face x u ↔ PermReachable G.face y₁ u := by
    constructor
    · intro hxu
      exact PermReachable.trans G.face hy₁x hxu
    · intro hy₁u
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hy₁x) hy₁u
  have hex_iff :
      PermReachable G.face (G.edge x) u ↔
        PermReachable G.face y₂ u := by
    constructor
    · intro hexu
      exact PermReachable.trans G.face hy₂ex hexu
    · intro hy₂u
      exact PermReachable.trans G.face
        (PermReachable.symm G.face hy₂ex) hy₂u
  rw [FaceBand.cons, FaceBand.cons, FaceBand.cons, FaceBand.append,
    hx_iff, hex_iff]
  rw [FaceBand.cons]
  rw [FaceBand.cons]
  tauto

/-- Same-decomposition chord rings also cover exactly the original face band.
This packages Coq's `fband_chord_ring` in the form needed by the
`diskF_chord_ring` transfer lemma. -/
theorem SimpleRLinkCycle.exists_chord_pair_same_decomposition_faceBand_union
    (hPlain : G.Plain)
    (hBridgeless : G.Bridgeless)
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {x : G.Dart}
    (hx : G.FaceBand r x)
    (hex : G.FaceBand r (G.edge x)) :
    ∃ y₁ : G.Dart, ∃ y₂ : G.Dart,
      ∃ p₁ : List G.Dart, ∃ p₂ : List G.Dart, ∃ i : Nat,
        y₁ ∈ r ∧ y₂ ∈ r ∧
          r.rotate i = y₂ :: p₁ ++ y₁ :: p₂ ∧
            G.SimpleRLinkCycle (x :: y₂ :: p₁) ∧
              G.SimpleRLinkCycle (G.edge x :: y₁ :: p₂) ∧
                (∀ u : G.Dart,
                  (G.FaceBand (x :: y₂ :: p₁) u ∨
                      G.FaceBand (G.edge x :: y₁ :: p₂) u) ↔
                    G.FaceBand r u) := by
  rcases hx with ⟨y₁, hy₁r, hy₁x⟩
  rcases hex with ⟨y₂, hy₂r, hy₂ex⟩
  have hy₂y₁ : y₂ ≠ y₁ := by
    intro h
    subst y₂
    exact hBridgeless x
      (PermReachable.trans G.face
        (PermReachable.symm G.face hy₁x) hy₂ex)
  rcases SimpleRLinkCycle.exists_chord_pair_same_decomposition_of_witnesses
      (G := G) hPlain hr hy₁r hy₂r hy₂y₁ hy₁x hy₂ex with
    ⟨p₁, p₂, i, hdecomp, hcycle₁, hcycle₂⟩
  refine
    ⟨y₁, y₂, p₁, p₂, i, hy₁r, hy₂r,
      hdecomp, hcycle₁, hcycle₂, ?_⟩
  intro u
  calc
    (G.FaceBand (x :: y₂ :: p₁) u ∨
        G.FaceBand (G.edge x :: y₁ :: p₂) u)
        ↔ G.FaceBand (y₂ :: p₁ ++ y₁ :: p₂) u :=
          FaceBand.chord_prefix_union (G := G) hy₁x hy₂ex
    _ ↔ G.FaceBand (r.rotate i) u := by
          rw [hdecomp]
    _ ↔ G.FaceBand r u :=
          FaceBand.rotate (G := G) i

/-- Generic `diskF_chord_ring` reducer.  Coq proves `diskF_chord_ring` from
`diskN_chord_ring` and `fband_chord_ring`; this lemma isolates exactly that
logical step for the Lean port. -/
theorem diskF_of_diskN_split_faceBand_union
    [Fintype G.Dart]
    {r cr₁ cr₂ : List G.Dart}
    (hDiskN :
      ∀ u : G.Dart,
        G.DiskN cr₁ u ↔ G.DiskN r u ∧ ¬ G.DiskN cr₂ u)
    (hFaceBand :
      ∀ u : G.Dart,
        (G.FaceBand cr₁ u ∨ G.FaceBand cr₂ u) ↔ G.FaceBand r u)
    (u : G.Dart) :
    G.DiskF cr₁ u ↔ G.DiskF r u ∧ ¬ G.DiskF cr₂ u := by
  constructor
  · intro hu
    have hsplit := (hDiskN u).1 hu.1
    refine ⟨⟨hsplit.1, ?_⟩, ?_⟩
    · intro hru
      rcases (hFaceBand u).2 hru with hu₁ | hu₂
      · exact hu.2 hu₁
      · rcases hu₂ with ⟨z, hz, hzu⟩
        have hzF₁ : G.DiskF cr₁ z :=
          G.diskF_of_faceReachable
            (PermReachable.symm G.face hzu) hu
        have hzNot₂ : ¬ G.DiskN cr₂ z :=
          ((hDiskN z).1 hzF₁.1).2
        exact hzNot₂ (G.diskN_of_mem hz)
    · intro hu₂
      exact hsplit.2 hu₂.1
  · rintro ⟨hu, hnot₂⟩
    refine ⟨(hDiskN u).2 ⟨hu.1, ?_⟩, ?_⟩
    · intro huN₂
      have huNoBand₂ : ¬ G.FaceBand cr₂ u := by
        intro huBand₂
        exact hu.2 ((hFaceBand u).1 (Or.inr huBand₂))
      exact hnot₂ ⟨huN₂, huNoBand₂⟩
    · intro huBand₁
      exact hu.2 ((hFaceBand u).1 (Or.inl huBand₁))

/-- Chord-decomposition form of Coq `diskF_chord_ring`.  Once the hard
`diskN_chord_ring` partition has been proved for the same decomposition
`y₂ :: p₁ ++ y₁ :: p₂`, the face-interior partition follows by the checked
face-band union. -/
theorem diskF_chord_prefix_of_diskN_split
    [Fintype G.Dart]
    {x y₁ y₂ u : G.Dart} {p₁ p₂ : List G.Dart}
    (hy₁x : PermReachable G.face y₁ x)
    (hy₂ex : PermReachable G.face y₂ (G.edge x))
    (hDiskN :
      ∀ u : G.Dart,
        G.DiskN (x :: y₂ :: p₁) u ↔
          G.DiskN (y₂ :: p₁ ++ y₁ :: p₂) u ∧
            ¬ G.DiskN (G.edge x :: y₁ :: p₂) u) :
    G.DiskF (x :: y₂ :: p₁) u ↔
      G.DiskF (y₂ :: p₁ ++ y₁ :: p₂) u ∧
        ¬ G.DiskF (G.edge x :: y₁ :: p₂) u :=
  G.diskF_of_diskN_split_faceBand_union
    hDiskN
    (fun u => FaceBand.chord_prefix_union (G := G) (u := u) hy₁x hy₂ex)
    u

theorem SimpleRLinkCycle.rotate
    (n : Nat) {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r) :
    G.SimpleRLinkCycle (r.rotate n) :=
  ⟨RLinkCycle.rotate (G := G) n hr.1,
    FaceSimple.rotate (G := G) n hr.2⟩

theorem SimpleRLinkCycle.exists_rotated_cons
    {r : List G.Dart}
    (hr : G.SimpleRLinkCycle r)
    {y : G.Dart}
    (hy : y ∈ r) :
    ∃ r1 : List G.Dart,
      G.SimpleRLinkCycle (y :: r1) ∧
        (y :: r1).Perm r ∧
          y ∉ r1 := by
  rcases (List.mem_iff_append).1 hy with ⟨pre, post, hsplit⟩
  have hrot :
      r.rotate pre.length = y :: (post ++ pre) := by
    rw [hsplit]
    rw [List.rotate_append_length_eq]
    simp
  refine ⟨post ++ pre, ?_, ?_, ?_⟩
  · have hcycle := SimpleRLinkCycle.rotate (G := G) pre.length hr
    simpa [hrot] using hcycle
  · rw [← hrot]
    exact List.rotate_perm r pre.length
  · have hcycle : G.SimpleRLinkCycle (y :: (post ++ pre)) := by
      have hcycleRot := SimpleRLinkCycle.rotate (G := G) pre.length hr
      simpa [hrot] using hcycleRot
    exact (List.nodup_cons.mp (FaceSimple.nodup (G := G) hcycle.2)).1

theorem SimpleRLinkCycle.exists_RCLPath_to_last
    [Fintype G.Dart]
    {y : G.Dart} {r1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1)) :
    ∃ c : List G.Dart,
      G.RCLPath (y :: r1) y c ∧
        (y :: c).getLastD y = (y :: r1).getLastD y :=
  RLinkPath.exists_RCLPath_from_ring_path
    (G := G) hr.2 (by simp) hr.1.1
    (by intro z hz; simp [hz])

theorem SimpleRLinkCycle.exists_RCLPath_to_last_subset
    [Fintype G.Dart]
    {y : G.Dart} {r1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1)) :
    ∃ c : List G.Dart,
      G.RCLPath (y :: r1) y c ∧
        (y :: c).getLastD y = (y :: r1).getLastD y ∧
          ∀ z : G.Dart, z ∈ y :: r1 → z ∈ y :: c :=
  RLinkPath.exists_RCLPath_from_ring_path_subset
    (G := G) hr.2 (by simp) hr.1.1
    (by intro z hz; simp [hz])

theorem SimpleRLinkCycle.exists_RCLPath_to_last_subset_faceBand
    [Fintype G.Dart]
    {y : G.Dart} {r1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1)) :
    ∃ c : List G.Dart,
      G.RCLPath (y :: r1) y c ∧
        (y :: c).getLastD y = (y :: r1).getLastD y ∧
          (∀ z : G.Dart, z ∈ y :: r1 → z ∈ y :: c) ∧
            ∀ t : G.Dart, G.FaceBand c t → G.FaceBand r1 t :=
  RLinkPath.exists_RCLPath_from_ring_path_subset_faceBand
    (G := G) hr.2 (by simp) hr.1.1
    (by intro z hz; simp [hz])

theorem SimpleRLinkCycle.exists_RCLPath_to_last_subset_faceBand_nodup
    [Fintype G.Dart]
    {y : G.Dart} {r1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1)) :
    ∃ c : List G.Dart,
      G.RCLPath (y :: r1) y c ∧
        (y :: c).getLastD y = (y :: r1).getLastD y ∧
          (∀ z : G.Dart, z ∈ y :: r1 → z ∈ y :: c) ∧
            c.Nodup ∧
              ∀ t : G.Dart, G.FaceBand c t → G.FaceBand r1 t :=
  RLinkPath.exists_RCLPath_from_ring_path_subset_faceBand_nodup
    (G := G) hr.2 (by simp) hr.1.1
    (by intro z hz; simp [hz]) hr.2

theorem SimpleRLinkCycle.not_faceReachable_head_of_faceBand_tail
    {y : G.Dart} {r1 c : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hband : ∀ t : G.Dart, G.FaceBand c t → G.FaceBand r1 t) :
    ∀ t : G.Dart, t ∈ c → ¬ PermReachable G.face y t := by
  intro t htc hyt
  have htBand : G.FaceBand c t :=
    FaceBand.of_mem (G := G) htc (PermReachable.refl G.face t)
  rcases hband t htBand with ⟨u, hu, hut⟩
  have hyu : PermReachable G.face y u :=
    PermReachable.trans G.face hyt (PermReachable.symm G.face hut)
  have hyuEq : y = u :=
    FaceSimple.eq_of_faceReachable_of_mem (G := G) hr.2
      (by simp) (by simp [hu]) hyu
  have hyNotTail :
      y ∉ r1 :=
    (List.nodup_cons.mp (FaceSimple.nodup (G := G) hr.2)).1
  exact hyNotTail (by simpa [hyuEq] using hu)

theorem SimpleRLinkCycle.disjoint_facePath_of_faceBand_tail
    {y x z : G.Dart} {r1 c p : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hband : ∀ t : G.Dart, G.FaceBand c t → G.FaceBand r1 t)
    (hp : G.FacePath x p)
    (hlast : (x :: p).getLastD x = z)
    (hyz : PermReachable G.face y z) :
    ∀ t : G.Dart, t ∈ c → t ∈ x :: p → False := by
  intro t htc htp
  exact SimpleRLinkCycle.not_faceReachable_head_of_faceBand_tail
      (G := G) hr hband t htc
    (FacePath.faceReachable_of_faceReachable_last_eq
      (G := G) hp hlast hyz t htp)

theorem SimpleRLinkCycle.disjoint_facePath_of_faceBand_tail_face_last
    {y x z : G.Dart} {r1 c p : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hband : ∀ t : G.Dart, G.FaceBand c t → G.FaceBand r1 t)
    (hp : G.FacePath x p)
    (hfaceLast : G.face ((x :: p).getLastD x) = z)
    (hyz : PermReachable G.face y z) :
    ∀ t : G.Dart, t ∈ c → t ∈ x :: p → False := by
  intro t htc htp
  exact SimpleRLinkCycle.not_faceReachable_head_of_faceBand_tail
      (G := G) hr hband t htc
    (FacePath.faceReachable_of_faceReachable_face_last_eq
      (G := G) hp hfaceLast hyz t htp)

theorem SimpleRLinkCycle.exists_temp_RCLCycle_from_facePath_prefix
    [Fintype G.Dart]
    {y z' x' : G.Dart} {r1 p q1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hp : G.FacePath z' p)
    (hpNodup : (z' :: p).Nodup)
    (hlastp : (z' :: p).getLastD z' = y)
    (hz' : z' = G.face (G.edge ((y :: r1).getLastD y)))
    (hq1 : G.FacePath x' q1)
    (hfaceq1 : G.face ((x' :: q1).getLastD x') = z')
    (hyz' : PermReachable G.face y z')
    (hprefixDisj : ∀ t : G.Dart, t ∈ z' :: p → t ∉ x' :: q1) :
    ∃ c : List G.Dart,
      G.RCLCycle (y :: r1) (z' :: c) ∧
        (z' :: c).Nodup ∧
          (z' :: c).getLastD z' = (y :: r1).getLastD y ∧
            (∀ t : G.Dart, t ∈ y :: r1 → t ∈ z' :: c) ∧
              ∀ t : G.Dart, t ∈ z' :: c → t ∉ x' :: q1 := by
  rcases SimpleRLinkCycle.exists_RCLPath_to_last_subset_faceBand_nodup
      (G := G) hr with
    ⟨c2, hc2, hlast2, hsubC2, hc2Nodup, hband2⟩
  let z := (y :: r1).getLastD y
  have hz : z ∈ y :: r1 := by
    exact List.getLastD_cons_mem y r1
  have hcycle : G.RCLCycle (y :: r1) (z' :: (p ++ c2)) := by
    exact RCLCycle.of_facePath_prefix_RCLPath_tail
      (G := G) hr.2 hp hpNodup hlastp (by simp) hc2 hlast2 hz hz'
  have hlastFull :
      (z' :: (p ++ c2)).getLastD z' = z := by
    calc
      (z' :: (p ++ c2)).getLastD z' =
          (y :: c2).getLastD y :=
            list_getLastD_cons_append_of_getLast z' y p c2 hlastp
      _ = z := hlast2
  have hdisjC2Prefix :
      ∀ t : G.Dart, t ∈ c2 → t ∈ z' :: p → False :=
    SimpleRLinkCycle.disjoint_facePath_of_faceBand_tail
      (G := G) hr hband2 hp hlastp (PermReachable.refl G.face y)
  have hnodupFull : (z' :: (p ++ c2)).Nodup := by
    rw [← List.cons_append, List.nodup_append]
    refine ⟨hpNodup, hc2Nodup, ?_⟩
    intro a ha b hb hab
    subst b
    exact hdisjC2Prefix a hb ha
  have hprefix_mem :
      ∀ t : G.Dart, t ∈ z' :: p → t ∈ z' :: (p ++ c2) := by
    intro t ht
    rw [List.mem_cons] at ht ⊢
    rcases ht with htz | htp
    · exact Or.inl htz
    · exact Or.inr (List.mem_append_left c2 htp)
  have hyPrefix : y ∈ z' :: p := by
    rw [← hlastp]
    exact List.getLastD_cons_mem z' p
  have hringSub :
      ∀ t : G.Dart, t ∈ y :: r1 → t ∈ z' :: (p ++ c2) := by
    intro t ht
    rw [List.mem_cons] at ht
    rcases ht with hty | htr1
    · subst t
      exact hprefix_mem y hyPrefix
    · have htYC2 : t ∈ y :: c2 :=
        hsubC2 t (by simp [htr1])
      rw [List.mem_cons] at htYC2
      rcases htYC2 with hty | htc2
      · subst t
        exact hprefix_mem y hyPrefix
      · exact List.mem_cons_of_mem z'
          (List.mem_append_right p htc2)
  have hnoContact :
      ∀ t : G.Dart, t ∈ z' :: (p ++ c2) → t ∉ x' :: q1 := by
    intro t ht htq1
    have htCases : t ∈ z' :: p ∨ t ∈ c2 := by
      rw [List.mem_cons] at ht
      rcases ht with htz | htpc2
      · exact Or.inl (by simp [htz])
      · rw [List.mem_append] at htpc2
        rcases htpc2 with htp | htc2
        · exact Or.inl (by simp [htp])
        · exact Or.inr htc2
    rcases htCases with htprefix | htc2
    · exact hprefixDisj t htprefix htq1
    · have hnot :
          ¬ PermReachable G.face y t :=
        SimpleRLinkCycle.not_faceReachable_head_of_faceBand_tail
          (G := G) hr hband2 t htc2
      exact hnot
        (FacePath.faceReachable_of_faceReachable_face_last_eq
          (G := G) hq1 hfaceq1 hyz' t htq1)
  exact ⟨p ++ c2, hcycle, hnodupFull, hlastFull, hringSub, hnoContact⟩

theorem SimpleRLinkCycle.exists_contact_path_for_temp_RCLCycle
    [Fintype G.Dart]
    {y z' x' x : G.Dart} {r1 p q1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hp : G.FacePath z' p)
    (hpNodup : (z' :: p).Nodup)
    (hlastp : (z' :: p).getLastD z' = y)
    (hz' : z' = G.face (G.edge ((y :: r1).getLastD y)))
    (hq1 : G.FacePath x' q1)
    (hfaceq1 : G.face ((x' :: q1).getLastD x') = z')
    (hyz' : PermReachable G.face y z')
    (hprefixDisj : ∀ t : G.Dart, t ∈ z' :: p → t ∉ x' :: q1)
    (hdx : G.DiskN (y :: r1) x)
    (hx' : x' = G.face (G.edge x)) :
    ∃ c : List G.Dart,
      G.RCLCycle (y :: r1) (z' :: c) ∧
        (z' :: c).Nodup ∧
          (z' :: c).getLastD z' = (y :: r1).getLastD y ∧
            (∀ t : G.Dart, t ∈ y :: r1 → t ∈ z' :: c) ∧
              (∀ t : G.Dart, t ∈ z' :: c → t ∉ x' :: q1) ∧
                ∃ x1 : G.Dart, ∃ q : List G.Dart,
                  G.node x1 ∈ z' :: c ∧
                    G.CPath x1 q ∧
                      (x1 :: q).getLastD x1 = x' ∧
                        ∀ t : G.Dart, t ∈ x1 :: q → t ∉ z' :: c := by
  rcases SimpleRLinkCycle.exists_temp_RCLCycle_from_facePath_prefix
      (G := G) hr hp hpNodup hlastp hz' hq1 hfaceq1 hyz'
      hprefixDisj with
    ⟨c, hc, hcNodup, hlastc, hringSub, hnoContact⟩
  have hx'not : G.face (G.edge x) ∉ z' :: c := by
    intro hxmem
    exact hnoContact (G.face (G.edge x)) hxmem (by
      rw [← hx']
      simp)
  rcases DiskN.exists_node_contact_cPath_to_face_edge_of_ring_subset
      (G := G) hc hringSub hdx hx'not with
    ⟨x1, q, hnode, hpath, hlast, havoid⟩
  refine ⟨c, hc, hcNodup, hlastc, hringSub, hnoContact, x1, q,
    hnode, hpath, ?_, havoid⟩
  simpa [← hx'] using hlast

theorem SimpleRLinkCycle.not_contact_path_for_temp_RCLCycle
    [Fintype G.Dart]
    (hJ : G.Jordan)
    {y z' x' x : G.Dart} {r1 p q1 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hp : G.FacePath z' p)
    (hpNodup : (z' :: p).Nodup)
    (hlastp : (z' :: p).getLastD z' = y)
    (hz' : z' = G.face (G.edge ((y :: r1).getLastD y)))
    (hq1 : G.FacePath x' q1)
    (hfaceq1 : G.face ((x' :: q1).getLastD x') = z')
    (hyz' : PermReachable G.face y z')
    (hprefixDisj : ∀ t : G.Dart, t ∈ z' :: p → t ∉ x' :: q1)
    (hdx : G.DiskN (y :: r1) x)
    (hx' : x' = G.face (G.edge x)) :
    False := by
  rcases SimpleRLinkCycle.exists_contact_path_for_temp_RCLCycle
      (G := G) hr hp hpNodup hlastp hz' hq1 hfaceq1 hyz'
      hprefixDisj hdx hx' with
    ⟨c, hc, hcNodup, hlastc, _hringSub, hnoContact,
      x1, q, hnode, hpath, hlastq, havoid⟩
  have hq1C : G.CPath x' q1 :=
    FacePath.to_CPath (G := G) hq1
  have hpath0 : G.CPath x1 (q ++ q1) :=
    CPath.append (G := G) hpath hlastq hq1C
  have hlast0 :
      (x1 :: (q ++ q1)).getLastD x1 =
        (x' :: q1).getLastD x' :=
    list_getLastD_cons_append_of_getLast x1 x' q q1 hlastq
  have hlink0 :
      G.CLink ((x1 :: (q ++ q1)).getLastD x1) z' := by
    have hlinkTail : G.CLink ((x' :: q1).getLastD x') z' :=
      Or.inr hfaceq1.symm
    have hlast0' :
        (x1 :: (q ++ q1)).getLast?.getD x1 =
          (x' :: q1).getLast?.getD x' := by
      simpa [List.getLastD] using hlast0
    simpa [hlast0'] using hlinkTail
  have havoid0 :
      ∀ t : G.Dart, t ∈ x1 :: (q ++ q1) → t ∉ z' :: c := by
    intro t ht htc
    have htCases : t ∈ x1 :: q ∨ t ∈ q1 := by
      rw [List.mem_cons] at ht
      rcases ht with htx1 | htqq1
      · exact Or.inl (by simp [htx1])
      · rw [List.mem_append] at htqq1
        rcases htqq1 with htq | htq1
        · exact Or.inl (by simp [htq])
        · exact Or.inr htq1
    rcases htCases with htq | htq1
    · exact havoid t htq htc
    · exact hnoContact t htc (by simp [htq1])
  rcases CPath.shorten (G := G) hpath0 with
    ⟨q0, hq0, hlastq0, hq0Nodup, hsubq0⟩
  have hlinkq0 :
      G.CLink ((x1 :: q0).getLastD x1) z' := by
    rw [hlastq0]
    exact hlink0
  have havoidq0 :
      ∀ t : G.Dart, t ∈ x1 :: q0 → t ∉ z' :: c := by
    intro t ht
    exact havoid0 t (hsubq0 t ht)
  have hzlast :
      G.node.symm ((z' :: c).getLastD z') = z' := by
    rw [hlastc, hz', face_edge_eq_node_symm]
  exact Jordan.not_cPath_to_RCLCycle_with_node_contact
    (G := G) hJ hq0 hlinkq0 hc hq0Nodup hcNodup
    (fun t htpath htcycle => havoidq0 t htpath htcycle)
    hnode hzlast

theorem SimpleRLinkCycle.not_tail_hit_for_diskE_edge_split
    [Fintype G.Dart]
    (hJ : G.Jordan)
    {y x x' z' : G.Dart} {r1 q1 q2 : List G.Dart}
    (hr : G.SimpleRLinkCycle (y :: r1))
    (hx' : x' = G.face (G.edge x))
    (hz' : z' = G.face (G.edge ((y :: r1).getLastD y)))
    (hq1 : G.FacePath x' q1)
    (hfaceq1 : G.face ((x' :: q1).getLastD x') = z')
    (hq2 : G.FacePath z' q2)
    (hyTail : y ∈ z' :: q2)
    (hnodup : (x' :: (q1 ++ z' :: q2)).Nodup)
    (hyz' : PermReachable G.face y z')
    (hdx : G.DiskN (y :: r1) x) :
    False := by
  have hfull :
      ((x' :: q1) ++ (z' :: q2)).Nodup := by
    simpa [List.cons_append, List.append_assoc] using hnodup
  have htailNodup : (z' :: q2).Nodup :=
    (List.nodup_append.mp hfull).2.1
  have hdisj := (List.nodup_append.mp hfull).2.2
  rw [List.mem_cons] at hyTail
  rcases hyTail with hyz | hyq2
  · subst y
    have hpNodup : (z' :: ([] : List G.Dart)).Nodup := by simp
    have hlastp : (z' :: ([] : List G.Dart)).getLastD z' = z' := by
      simp [List.getLastD]
    have hprefixDisj :
        ∀ t : G.Dart, t ∈ z' :: ([] : List G.Dart) → t ∉ x' :: q1 := by
      intro t ht htq1
      simp at ht
      subst t
      exact hdisj z' htq1 z' (by simp) rfl
    exact SimpleRLinkCycle.not_contact_path_for_temp_RCLCycle
      (G := G) hJ hr (by simp [FacePath]) hpNodup hlastp hz'
      hq1 hfaceq1 hyz' hprefixDisj hdx hx'
  · rcases FacePath.exists_prefix_append_singleton_at_tail_mem
        (G := G) hq2 hyq2 with
      ⟨pre, post, hsplit, hp, hlastp, _hpost⟩
    have hprefixSub :
        (z' :: (pre ++ [y])).Sublist (z' :: q2) := by
      rw [hsplit]
      simp
    have hpNodup : (z' :: (pre ++ [y])).Nodup :=
      List.Nodup.sublist hprefixSub htailNodup
    have hright_of_prefix :
        ∀ t : G.Dart, t ∈ z' :: (pre ++ [y]) → t ∈ z' :: q2 := by
      intro t ht
      exact hprefixSub.subset ht
    have hprefixDisj :
        ∀ t : G.Dart, t ∈ z' :: (pre ++ [y]) → t ∉ x' :: q1 := by
      intro t ht htq1
      exact hdisj t htq1 t (hright_of_prefix t ht) rfl
    exact SimpleRLinkCycle.not_contact_path_for_temp_RCLCycle
      (G := G) hJ hr hp hpNodup hlastp hz' hq1 hfaceq1
      hyz' hprefixDisj hdx hx'

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
