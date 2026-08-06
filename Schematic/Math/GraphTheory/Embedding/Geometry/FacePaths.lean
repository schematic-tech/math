import Schematic.Math.GraphTheory.Embedding.Geometry.FaceBand

namespace Schematic.Math.GraphTheory

namespace FourColor

namespace Hypermap

variable (G : Hypermap)

/-- Coq `path edge x p`: the listed darts follow successive `edge` links
starting from `x`. -/
def EdgePath (x : G.Dart) : List G.Dart → Prop
  := List.RelPath (fun a b => G.edge a = b) x

@[simp]
theorem EdgePath.nil (x : G.Dart) :
    G.EdgePath x [] := by
  simp [EdgePath]

@[simp]
theorem EdgePath.cons (x y : G.Dart) (p : List G.Dart) :
    G.EdgePath x (y :: p) ↔ G.edge x = y ∧ G.EdgePath y p := by
  rfl

/-- Coq `fpath (finv node) x p`: the listed darts follow successive
reverse-node links starting from `x`.  Unlike a general `CPath`, this records
that no face step occurs, which is the invariant used by `hcycle.v` when a
contour must avoid one graph vertex. -/
def NodeSymmPath (x : G.Dart) : List G.Dart → Prop
  := List.RelPath (fun a b => G.node.symm a = b) x

@[simp]
theorem NodeSymmPath.nil (x : G.Dart) :
    G.NodeSymmPath x [] := by
  simp [NodeSymmPath]

@[simp]
theorem NodeSymmPath.cons (x y : G.Dart) (p : List G.Dart) :
    G.NodeSymmPath x (y :: p) ↔
      G.node.symm x = y ∧ G.NodeSymmPath y p := by
  rfl

theorem NodeSymmPath.to_CPath
    {x : G.Dart} {p : List G.Dart}
    (hp : G.NodeSymmPath x p) :
    G.CPath x p := by
  refine List.RelPath.imp (S := G.CLink) ?_ hp
  intro a b hab
  exact Or.inl hab.symm

theorem exists_nodeSymmPath_to_nodeSymm_iterate
    (n : Nat) (x : G.Dart) :
    ∃ p : List G.Dart,
      G.NodeSymmPath x p ∧
        (x :: p).getLastD x =
          ((G.node.symm : G.Dart → G.Dart)^[n]) x :=
  List.RelPath.exists_to_iterate G.node.symm n x

theorem exists_nodeSymmPath_of_nodeSymmReachable
    [Fintype G.Dart]
    {x y : G.Dart}
    (hxy : PermReachable G.node.symm x y) :
    ∃ p : List G.Dart,
      G.NodeSymmPath x p ∧ (x :: p).getLastD x = y := by
  rcases permReachable_exists_iterate G.node.symm hxy with ⟨n, hn⟩
  rcases G.exists_nodeSymmPath_to_nodeSymm_iterate n x with
    ⟨p, hp, hlast⟩
  exact ⟨p, hp, by simpa [hn] using hlast⟩

/-- Coq `fpath face x p`: the listed darts follow successive `face` links
starting from `x`.  This is the local path object used in the `snip.v`
`diskE_edge` proof after the face orbit has been shortened. -/
def FacePath (x : G.Dart) : List G.Dart → Prop
  := List.RelPath (fun a b => G.face a = b) x

@[simp]
theorem FacePath.nil (x : G.Dart) :
    G.FacePath x [] := by
  simp [FacePath]

@[simp]
theorem FacePath.cons (x y : G.Dart) (p : List G.Dart) :
    G.FacePath x (y :: p) ↔ G.face x = y ∧ G.FacePath y p := by
  rfl

theorem FacePath.iff_isChain
    {x : G.Dart} {p : List G.Dart} :
    G.FacePath x p ↔
      List.IsChain (fun a b : G.Dart => G.face a = b) (x :: p) :=
  List.RelPath.iff_isChain

/-- A face orbit in cyclic order, starting at a prescribed dart.  Unlike
`faceOrbitList`, which is an unordered finite-set enumeration, this witness
retains the order needed to split the orbit into two face paths. -/
theorem exists_ordered_faceOrbitCycle
    [Fintype G.Dart]
    (x : G.Dart) :
    ∃ p : List G.Dart,
      G.FacePath x p ∧
        G.face ((x :: p).getLastD x) = x ∧
          (x :: p).Nodup ∧
            ∀ y : G.Dart,
              y ∈ x :: p ↔ PermReachable G.face x y := by
  classical
  let period : Nat :=
    Function.minimalPeriod (G.face : G.Dart → G.Dart) x
  let c : List G.Dart :=
    (List.range period).map
      (fun n : Nat => ((G.face : G.Dart → G.Dart)^[n]) x)
  have hxPeriodic :
      x ∈ Function.periodicPts (G.face : G.Dart → G.Dart) :=
    G.face.injective.mem_periodicPts x
  have hperiodPos : 0 < period := by
    exact Function.minimalPeriod_pos_of_mem_periodicPts hxPeriodic
  have hrange : List.range period ≠ [] := by
    simpa [List.range_eq_nil] using hperiodPos.ne'
  have hc : c ≠ [] := by
    simpa [c] using hrange
  have hcHead : c.head hc = x := by
    simp [c, List.head_map, List.head_range]
  have hcEq : c = x :: c.tail := by
    calc
      c = c.head hc :: c.tail := (List.cons_head_tail hc).symm
      _ = x :: c.tail := by rw [hcHead]
  have hcChain :
      List.IsChain (fun a b : G.Dart => G.face a = b) c := by
    simp only [c, List.isChain_map, List.isChain_range]
    intro n hn
    rw [Function.iterate_succ_apply']
  have hcNodup : c.Nodup := by
    unfold c
    apply List.Nodup.map_on
    · intro i hi j hj hij
      have hi' : i <
          Function.minimalPeriod (G.face : G.Dart → G.Dart) x := by
        simpa [period] using List.mem_range.mp hi
      have hj' : j <
          Function.minimalPeriod (G.face : G.Dart → G.Dart) x := by
        simpa [period] using List.mem_range.mp hj
      exact
        (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
          (f := (G.face : G.Dart → G.Dart)) (x := x) hi' hj').mp hij
    · exact List.nodup_range
  have hcClose : G.face (c.getLastD x) = x := by
    change
      G.face
        ((List.map
          (fun k : Nat => ((G.face : G.Dart → G.Dart)^[k]) x)
          (List.range period)).getLastD
            (((G.face : G.Dart → G.Dart)^[0]) x)) = x
    rw [List.getLastD_map]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hperiodPos.ne'
    rw [hn, List.range_succ, List.getLastD_concat]
    calc
      G.face (((G.face : G.Dart → G.Dart)^[n]) x) =
          ((G.face : G.Dart → G.Dart)^[n + 1]) x := by
        rw [Function.iterate_succ_apply']
      _ = ((G.face : G.Dart → G.Dart)^[period]) x := by
        rw [hn]
      _ = x := Function.iterate_minimalPeriod
  refine ⟨c.tail, ?_, ?_, ?_, ?_⟩
  · rw [FacePath.iff_isChain, ← hcEq]
    exact hcChain
  · simpa [← hcEq] using hcClose
  · simpa [← hcEq] using hcNodup
  · intro y
    rw [← hcEq]
    constructor
    · intro hy
      simp only [c, List.mem_map] at hy
      rcases hy with ⟨n, hn, rfl⟩
      exact permReachable_of_iterate_eq G.face rfl
    · intro hxy
      rcases permReachable_exists_iterate G.face hxy with ⟨k, hk⟩
      let n : Nat := k % period
      have hn : n < period := Nat.mod_lt k hperiodPos
      have hiter :
          ((G.face : G.Dart → G.Dart)^[n]) x = y := by
        rw [show n = k % period from rfl]
        change
          ((G.face : G.Dart → G.Dart)^[
            k % Function.minimalPeriod (G.face : G.Dart → G.Dart) x]) x = y
        rw [Function.iterate_mod_minimalPeriod_eq]
        exact hk
      simp only [c, List.mem_map]
      exact ⟨n, List.mem_range.mpr hn, hiter⟩

theorem FacePath.to_CPath
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p) :
    G.CPath x p := by
  refine List.RelPath.imp (S := G.CLink) ?_ hp
  intro a b hab
  exact Or.inr hab.symm

theorem FacePath.snoc
    {x y z : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : G.face y = z) :
    G.FacePath x (p ++ [z]) :=
  List.RelPath.snoc hp hlast hyz

theorem FacePath.append
    {x y : G.Dart} {p q : List G.Dart}
    (hp : G.FacePath x p)
    (hlast : (x :: p).getLastD x = y)
    (hq : G.FacePath y q) :
    G.FacePath x (p ++ q) :=
  List.RelPath.append hp hlast hq

theorem FacePath.append_cons
    {x y z : G.Dart} {p q : List G.Dart}
    (hp : G.FacePath x p)
    (hlast : (x :: p).getLastD x = y)
    (hyz : G.face y = z)
    (hq : G.FacePath z q) :
    G.FacePath x (p ++ z :: q) :=
  List.RelPath.append_cons hp hlast hyz hq

theorem FacePath.split_append_cons
    {x y : G.Dart} {p q : List G.Dart}
    (hp : G.FacePath x (p ++ y :: q)) :
    G.FacePath x p ∧
      G.face ((x :: p).getLastD x) = y ∧
        G.FacePath y q :=
  List.RelPath.split_append_cons hp

theorem FacePath.prefix_append_singleton_of_split
    {x y : G.Dart} {p q : List G.Dart}
    (hp : G.FacePath x (p ++ y :: q)) :
    G.FacePath x (p ++ [y]) ∧
      (x :: (p ++ [y])).getLastD x = y ∧
        G.FacePath y q := by
  rcases FacePath.split_append_cons (G := G) hp with
    ⟨hpPrefix, hlink, hsuffix⟩
  refine ⟨FacePath.snoc (G := G) hpPrefix rfl hlink,
    List.getLastD_cons_append_singleton x y p, hsuffix⟩

/-- Rotate a closed face path at a supplied list decomposition. -/
theorem FacePath.rotate_closed_of_eq
    {x y : G.Dart} {p pre post : List G.Dart}
    (hp : G.FacePath x (p ++ [x]))
    (hsplit : p = pre ++ y :: post) :
    G.FacePath y (post ++ x :: pre ++ [y]) := by
  have hpSplit :
      G.FacePath x (pre ++ y :: (post ++ [x])) := by
    simpa [hsplit, List.append_assoc] using hp
  rcases FacePath.split_append_cons (G := G) hpSplit with
    ⟨hpre, hpreLast, hpost⟩
  have hpreToY : G.FacePath x (pre ++ [y]) :=
    FacePath.snoc (G := G) hpre rfl hpreLast
  have hpostLast :
      (y :: (post ++ [x])).getLastD y = x :=
    List.getLastD_cons_append_singleton y x post
  simpa [List.append_assoc] using
    FacePath.append (G := G) hpost hpostLast hpreToY

/-- Rotate a closed face path so that a selected noninitial dart becomes its
new initial dart. -/
theorem FacePath.rotate_closed_at
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x (p ++ [x]))
    (hy : y ∈ p) :
    ∃ pre post : List G.Dart,
      p = pre ++ y :: post ∧
        G.FacePath y (post ++ x :: pre ++ [y]) := by
  rcases (List.mem_iff_append).1 hy with ⟨pre, post, hsplit⟩
  exact ⟨pre, post, hsplit,
    FacePath.rotate_closed_of_eq (G := G) hp hsplit⟩

theorem FacePath.suffix_of_append
    {s x : G.Dart} {p q : List G.Dart}
    (hp : G.FacePath s (p ++ x :: q)) :
    G.FacePath x q :=
  List.RelPath.suffix_of_append hp

theorem FacePath.suffix_of_append_self
    {x : G.Dart} {p q : List G.Dart}
    (hp : G.FacePath x (p ++ x :: q)) :
    G.FacePath x q :=
  FacePath.suffix_of_append (G := G) hp

/-- Split one ordered face orbit at two distinct darts.  The two returned
face paths are complementary, and their half-open dart lists are disjoint by
the nodupness of the orbit cycle. -/
theorem exists_complementary_facePaths
    [Fintype G.Dart]
    {x y : G.Dart}
    (hxy : PermReachable G.face x y)
    (hne : x ≠ y) :
    ∃ left right : List G.Dart,
      G.FacePath x (left ++ [y]) ∧
        G.FacePath y (right ++ [x]) ∧
          (x :: left ++ y :: right).Nodup ∧
            ∀ z : G.Dart,
              z ∈ x :: left ++ y :: right ↔
                PermReachable G.face x z := by
  classical
  rcases G.exists_ordered_faceOrbitCycle x with
    ⟨p, hp, hclose, hnodup, horbit⟩
  have hyFull : y ∈ x :: p := (horbit y).2 hxy
  have hyTail : y ∈ p := by
    rw [List.mem_cons] at hyFull
    exact hyFull.resolve_left (Ne.symm hne)
  rcases (List.mem_iff_append).1 hyTail with ⟨left, right, hpEq⟩
  have hpSplit : G.FacePath x (left ++ y :: right) := by
    simpa [hpEq] using hp
  rcases FacePath.prefix_append_singleton_of_split (G := G) hpSplit with
    ⟨hleft, _hlast, hright⟩
  have hcloseRight :
      G.face ((y :: right).getLastD y) = x := by
    rw [← List.getLastD_cons_append_cons x y left right]
    simpa [hpEq] using hclose
  have hrightClose : G.FacePath y (right ++ [x]) :=
    FacePath.snoc (G := G) hright rfl hcloseRight
  refine ⟨left, right, hleft, hrightClose, ?_, ?_⟩
  · simpa [hpEq, List.append_assoc] using hnodup
  · intro z
    simpa [hpEq, List.append_assoc] using horbit z

/-- The first face successor on a nontrivial face path to `y` belongs to the
half-open source arc. -/
theorem FacePath.face_mem_sourceArc
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x (p ++ [y]))
    (hxy : G.face x ≠ y) :
    G.face x ∈ x :: p := by
  cases p with
  | nil =>
      have hstep : G.face x = y := by
        simpa [FacePath] using hp
      exact False.elim (hxy hstep)
  | cons z p =>
      have hstep : G.face x = z := by
        exact (FacePath.cons (G := G) x z (p ++ [y])).mp hp |>.1
      simp [hstep]

/-- The predecessor of the endpoint of a nontrivial face path belongs to the
half-open source arc. -/
theorem FacePath.face_symm_mem_sourceArc
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x (p ++ [y])) :
    G.face.symm y ∈ x :: p := by
  have hpNe : x :: p ≠ [] := by simp
  have hlink :
      G.face ((x :: p).getLastD x) = y :=
    (FacePath.split_append_cons
      (G := G) (p := p) (q := []) (by simpa using hp)).2.1
  have hpred :
      (x :: p).getLastD x = G.face.symm y := by
    apply G.face.injective
    simpa using hlink
  rw [← hpred]
  exact List.getLastD_cons_mem x p

/-- If a face path has a genuine internal dart before its endpoint, then its
first face step cannot jump directly to that endpoint. -/
theorem FacePath.face_ne_endpoint_of_middle
    {x y : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x (p ++ [y]))
    (hnodup : (x :: p ++ [y]).Nodup)
    (hpne : p ≠ []) :
    G.face x ≠ y := by
  cases p with
  | nil =>
      exact (hpne rfl).elim
  | cons z p =>
      have hface : G.face x = z :=
        (FacePath.cons (G := G) x z (p ++ [y])).mp hp |>.1
      intro hxy
      have hzy : z = y := hface.symm.trans hxy
      have hzNotMem :
          z ∉ p ++ [y] :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
      exact hzNotMem (by simp [hzy])

/-- Two internally disjoint contours whose endpoints alternate on one face
cycle form a Moebius path.  The caller supplies the already-spliced nodup
list; this lemma packages the final `hcycle.v::two_connected_cyle` Jordan
argument independently of how the four boundary contacts were selected. -/
theorem Jordan.not_alternating_cPaths
    (hJ : G.Jordan)
    {first nodeStart nodeEnd connectorStart connectorEnd : G.Dart}
    {nodeRest faceSegment connectorMiddle : List G.Dart}
    (hnode : G.CPath first nodeRest)
    (hnodeLast :
      (first :: nodeRest).getLastD first = nodeEnd)
    (hface : G.FacePath nodeEnd faceSegment)
    (hfaceLast :
      (nodeEnd :: faceSegment).getLastD nodeEnd = connectorStart)
    (hconnector : G.CPath connectorStart connectorMiddle)
    (hnodeFirst : G.node first = nodeStart)
    (hconnectorLast :
      G.node.symm
        ((connectorStart :: connectorMiddle).getLastD connectorStart) =
          connectorEnd)
    (hnodup :
      (first :: (nodeRest ++ faceSegment ++ connectorMiddle)).Nodup)
    (hcross :
      ListMemBeforeEq faceSegment connectorEnd nodeStart) :
    False := by
  have hnodeFace :
      G.CPath first (nodeRest ++ faceSegment) :=
    CPath.append (G := G) hnode hnodeLast
      (FacePath.to_CPath (G := G) hface)
  have hnodeFaceLast :
      (first :: (nodeRest ++ faceSegment)).getLastD first =
        connectorStart := by
    calc
      (first :: (nodeRest ++ faceSegment)).getLastD first =
          (nodeEnd :: faceSegment).getLastD nodeEnd :=
        list_getLastD_cons_append_of_getLast
          first nodeEnd nodeRest faceSegment hnodeLast
      _ = connectorStart := hfaceLast
  have hpath :
      G.CPath first (nodeRest ++ faceSegment ++ connectorMiddle) := by
    simpa [List.append_assoc] using
      CPath.append (G := G) hnodeFace hnodeFaceLast hconnector
  have hlast :
      G.node.symm
          ((first :: (nodeRest ++ faceSegment ++ connectorMiddle)).getLastD
            first) =
        connectorEnd := by
    have hfullLast :
        (first :: ((nodeRest ++ faceSegment) ++ connectorMiddle)).getLastD
            first =
          (connectorStart :: connectorMiddle).getLastD connectorStart :=
      list_getLastD_cons_append_of_getLast
        first connectorStart (nodeRest ++ faceSegment) connectorMiddle
        hnodeFaceLast
    rw [hfullLast]
    exact hconnectorLast
  have hmem :
      ListMemBeforeEq
        (nodeRest ++ faceSegment ++ connectorMiddle)
        connectorEnd nodeStart :=
    by
      have hcross' :
          ListMemBeforeEq (faceSegment ++ connectorMiddle)
            connectorEnd nodeStart :=
        ListMemBeforeEq.append_left hcross
      simpa [List.append_assoc] using
        ListMemBeforeEq.append_right nodeRest hcross'
  apply hJ (first :: (nodeRest ++ faceSegment ++ connectorMiddle))
  apply MoebiusPath.of_cons (G := G) hnodup hpath
  rw [hlast, hnodeFirst]
  exact hmem

theorem FacePath.shorten
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p) :
    ∃ q : List G.Dart,
      G.FacePath x q ∧
        (x :: q).getLastD x = (x :: p).getLastD x ∧
          (x :: q).Nodup ∧
            ∀ y : G.Dart, y ∈ x :: q → y ∈ x :: p := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ {x : G.Dart} {p : List G.Dart},
      p.length = n →
        G.FacePath x p →
          ∃ q : List G.Dart,
            G.FacePath x q ∧
              (x :: q).getLastD x = (x :: p).getLastD x ∧
                (x :: q).Nodup ∧
                  ∀ y : G.Dart, y ∈ x :: q → y ∈ x :: p
  have hP : ∀ n : Nat, (∀ m : Nat, m < n → P m) → P n := by
    intro n ih x p hlen hp
    cases p with
    | nil =>
        refine ⟨[], by simp [FacePath], by simp [List.getLastD], by simp, ?_⟩
        intro y hy
        exact hy
    | cons y p =>
        by_cases hxTail : x ∈ y :: p
        · rcases (List.mem_iff_append).1 hxTail with ⟨pre, post, hsplit⟩
          have hpLoop : G.FacePath x (pre ++ x :: post) := by
            simpa [hsplit] using hp
          have hpostPath : G.FacePath x post :=
            FacePath.suffix_of_append_self (G := G) hpLoop
          have hpostLen : post.length < n := by
            have hlen' :
                (pre ++ x :: post).length = n := by
              simpa [hsplit] using hlen
            simp at hlen'
            omega
          rcases ih post.length hpostLen rfl hpostPath with
            ⟨q, hq, hlast, hnodup, hsub⟩
          refine ⟨q, hq, ?_, hnodup, ?_⟩
          · calc
              (x :: q).getLastD x = (x :: post).getLastD x := hlast
              _ = (x :: (pre ++ x :: post)).getLastD x :=
                    (List.getLastD_cons_append_self x pre post).symm
              _ = (x :: y :: p).getLastD x := by simp [hsplit]
          · intro z hz
            have hzPost : z ∈ x :: post := hsub z hz
            rw [List.mem_cons] at hzPost ⊢
            rcases hzPost with hzPost | hzPost
            · exact Or.inl hzPost
            · exact Or.inr (by
                rw [hsplit]
                exact List.mem_append_right pre
                  (List.mem_cons_of_mem x hzPost))
        · have hp' : G.face x = y ∧ G.FacePath y p := by
            simpa [FacePath] using hp
          have hlt : p.length < n := by
            simp at hlen
            omega
          rcases ih p.length hlt rfl hp'.2 with
            ⟨q, hq, hlast, hnodup, hsub⟩
          refine ⟨y :: q, ⟨hp'.1, hq⟩, ?_, ?_, ?_⟩
          · simpa [List.getLastD] using hlast
          · refine List.nodup_cons.mpr ⟨?_, hnodup⟩
            intro hxq
            exact hxTail (hsub x hxq)
          · intro z hz
            rw [List.mem_cons] at hz ⊢
            rcases hz with hz | hz
            · exact Or.inl hz
            · exact Or.inr (hsub z hz)
  exact (Nat.strong_induction_on (p := P) p.length hP) rfl hp

theorem FacePath.to_RCLPath_of_avoids_ring
    {r : List G.Dart} {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (havoid : ∀ y : G.Dart, y ∈ x :: p → y ∉ r) :
    G.RCLPath r x p := by
  induction p generalizing x with
  | nil =>
      simp [RCLPath]
  | cons y p ih =>
      have hp' : G.face x = y ∧ G.FacePath y p := by
        simpa [FacePath] using hp
      have hxNot : x ∉ r := havoid x (by simp)
      refine ⟨?_, ?_⟩
      · simp [RCLStep, hxNot, hp'.1]
      · apply ih hp'.2
        intro z hz
        exact havoid z (by simp [hz])

theorem exists_facePath_to_face_iterate
    (n : Nat) (x : G.Dart) :
    ∃ p : List G.Dart,
      G.FacePath x p ∧
        (x :: p).getLastD x = ((G.face : G.Dart → G.Dart)^[n]) x :=
  List.RelPath.exists_to_iterate G.face n x

theorem exists_facePath_of_faceReachable
    [Fintype G.Dart]
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    ∃ p : List G.Dart,
      G.FacePath x p ∧ (x :: p).getLastD x = y := by
  rcases permReachable_exists_iterate G.face hxy with ⟨n, hn⟩
  rcases G.exists_facePath_to_face_iterate n x with ⟨p, hp, hlast⟩
  exact ⟨p, hp, by simpa [hn] using hlast⟩

theorem exists_short_facePath_of_faceReachable
    [Fintype G.Dart]
    {x y : G.Dart}
    (hxy : PermReachable G.face x y) :
    ∃ p : List G.Dart,
      G.FacePath x p ∧
        (x :: p).getLastD x = y ∧
          (x :: p).Nodup := by
  rcases G.exists_facePath_of_faceReachable hxy with ⟨p, hp, hlast⟩
  rcases FacePath.shorten (G := G) hp with
    ⟨q, hq, hqLast, hqNodup, _⟩
  exact ⟨q, hq, by rw [hqLast, hlast], hqNodup⟩

theorem FacePath.step_mem_tail_or_last
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    {y : G.Dart}
    (hy : y ∈ x :: p) :
    G.face y ∈ p ∨ y = (x :: p).getLastD x := by
  induction p generalizing x with
  | nil =>
      simp at hy
      subst y
      right
      simp [List.getLastD]
  | cons z p ih =>
      have hp' : G.face x = z ∧ G.FacePath z p := by
        simpa [FacePath] using hp
      rw [List.mem_cons] at hy
      rcases hy with hy | hy
      · subst y
        left
        simp [hp'.1]
      · rcases ih hp'.2 hy with hmem | hlast
        · left
          simp [hmem]
        · right
          simpa [List.getLastD] using hlast

theorem FacePath.face_mem_of_mem_closed
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hclose : G.face ((x :: p).getLastD x) = x)
    {y : G.Dart}
    (hy : y ∈ x :: p) :
    G.face y ∈ x :: p := by
  rcases FacePath.step_mem_tail_or_last (G := G) hp hy with hmem | hlast
  · exact List.mem_cons_of_mem x hmem
  · subst y
    rw [hclose]
    simp

theorem FacePath.iterate_mem_of_closed
    {x : G.Dart} {p : List G.Dart}
    (hp : G.FacePath x p)
    (hclose : G.face ((x :: p).getLastD x) = x)
    (n : Nat) :
    ((G.face : G.Dart → G.Dart)^[n]) x ∈ x :: p := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using
        FacePath.face_mem_of_mem_closed (G := G) hp hclose ih

/-- Coq `proper_ring`: a ring is nonempty and is not just a two-dart edge
orbit.  The boolean Coq definition is
`if r is x :: p then ~~ path edge x p || (2 < size r) else false`. -/
def ProperRing : List G.Dart → Prop
  | [] => False
  | x :: p => ¬ G.EdgePath x p ∨ 2 < (x :: p).length

@[simp]
theorem not_properRing_nil :
    ¬ G.ProperRing [] := by
  simp [ProperRing]

@[simp]
theorem properRing_cons (x : G.Dart) (p : List G.Dart) :
    G.ProperRing (x :: p) ↔ ¬ G.EdgePath x p ∨ 2 < (x :: p).length := by
  rfl

theorem properRing_of_length_gt_two
    {r : List G.Dart}
    (hr : 2 < r.length) :
    G.ProperRing r := by
  cases r with
  | nil =>
      simp at hr
  | cons x p =>
      exact Or.inr hr

theorem ProperRing.exists_mem
    {r : List G.Dart}
    (hr : G.ProperRing r) :
    ∃ x : G.Dart, x ∈ r := by
  cases r with
  | nil =>
      contradiction
  | cons x p =>
      exact ⟨x, by simp⟩

/-- Coq `rev_ring`: reverse the ring and cross each dart by `edge`. -/
def RevRing (r : List G.Dart) : List G.Dart :=
  (r.map G.edge).reverse

@[simp]
theorem length_revRing (r : List G.Dart) :
    (G.RevRing r).length = r.length := by
  simp [RevRing]

theorem mem_revRing_of_plain
    (hG : G.Plain)
    {r : List G.Dart} {x : G.Dart} :
    x ∈ G.RevRing r ↔ G.edge x ∈ r := by
  constructor
  · intro hx
    rw [RevRing, List.mem_reverse, List.mem_map] at hx
    rcases hx with ⟨y, hy, hyx⟩
    have hxy : G.edge x = y := by
      rw [← hyx, (hG y).1]
    simpa [hxy] using hy
  · intro hx
    rw [RevRing, List.mem_reverse, List.mem_map]
    exact ⟨G.edge x, hx, (hG x).1⟩

theorem revRing_revRing_of_plain
    (hG : G.Plain)
    (r : List G.Dart) :
    G.RevRing (G.RevRing r) = r := by
  simp [RevRing, List.map_reverse, List.map_map, Function.comp_def,
    fun x : G.Dart => (hG x).1]

theorem properRing_revRing_iff_of_plain
    (hG : G.Plain)
    (r : List G.Dart) :
    G.ProperRing (G.RevRing r) ↔ G.ProperRing r := by
  cases r with
  | nil =>
      simp [RevRing]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [RevRing, ProperRing, EdgePath]
      | cons y ys =>
          cases ys with
          | nil =>
              simp [RevRing, ProperRing, EdgePath, (hG y).1, eq_comm]
          | cons z zs =>
              have hlen : 2 < (x :: y :: z :: zs).length := by simp
              have hlenRev :
                  2 < (G.RevRing (x :: y :: z :: zs)).length := by
                simp [length_revRing]
              exact ⟨fun _ => properRing_of_length_gt_two (G := G) hlen,
                fun _ => properRing_of_length_gt_two (G := G) hlenRev⟩

theorem properRing_rotate_iff_of_plain
    (hG : G.Plain)
    (n : Nat) (r : List G.Dart) :
    G.ProperRing (r.rotate n) ↔ G.ProperRing r := by
  by_cases hlen : 2 < r.length
  · have hlenRot : 2 < (r.rotate n).length := by
      simpa [List.length_rotate] using hlen
    exact ⟨fun _ => properRing_of_length_gt_two (G := G) hlen,
      fun _ => properRing_of_length_gt_two (G := G) hlenRot⟩
  · cases r with
    | nil =>
        simp [ProperRing]
    | cons x xs =>
        cases xs with
        | nil =>
            have hrot : (([x] : List G.Dart).rotate n) = [x] := by
              have hmod : n % 1 = 0 := Nat.mod_one n
              simp [List.rotate, hmod]
            simp [hrot, ProperRing]
        | cons y ys =>
            cases ys with
            | nil =>
                rcases Nat.mod_two_eq_zero_or_one n with hn | hn
                · have hrot :
                      (([x, y] : List G.Dart).rotate n) = [x, y] := by
                    simp [List.rotate, hn]
                  simp [hrot]
                · have hrot :
                      (([x, y] : List G.Dart).rotate n) = [y, x] := by
                    simp [List.rotate, hn]
                  simp [hrot, ProperRing, EdgePath]
                  constructor
                  · intro hn' hy
                    exact hn' (by rw [← hy, (hG x).1])
                  · intro hn' hx
                    exact hn' (by rw [← hx, (hG y).1])
            | cons z zs =>
                have : 2 < (x :: y :: z :: zs : List G.Dart).length := by
                  simp
                contradiction

theorem FaceBand.pair
    {x y u : G.Dart} :
    G.FaceBand [x, y] u ↔
      PermReachable G.face x u ∨ PermReachable G.face y u := by
  rw [FaceBand.cons, FaceBand.singleton]

theorem not_FaceBand_pair
    {x y u : G.Dart} :
    ¬ G.FaceBand [x, y] u ↔
      ¬ PermReachable G.face x u ∧ ¬ PermReachable G.face y u := by
  rw [FaceBand.pair]
  constructor
  · intro h
    exact ⟨fun hx => h (Or.inl hx), fun hy => h (Or.inr hy)⟩
  · rintro ⟨hx, hy⟩ (h | h)
    · exact hx h
    · exact hy h

theorem FaceBand.triple
    {x y z u : G.Dart} :
    G.FaceBand [x, y, z] u ↔
      PermReachable G.face x u ∨
        PermReachable G.face y u ∨
          PermReachable G.face z u := by
  rw [FaceBand.cons, FaceBand.pair]

theorem not_FaceBand_triple
    {x y z u : G.Dart} :
    ¬ G.FaceBand [x, y, z] u ↔
      ¬ PermReachable G.face x u ∧
        ¬ PermReachable G.face y u ∧
          ¬ PermReachable G.face z u := by
  rw [FaceBand.triple]
  constructor
  · intro h
    exact ⟨fun hx => h (Or.inl hx),
      ⟨fun hy => h (Or.inr (Or.inl hy)),
        fun hz => h (Or.inr (Or.inr hz))⟩⟩
  · rintro ⟨hx, hy, hz⟩ (h | h | h)
    · exact hx h
    · exact hy h
    · exact hz h

theorem RingAdj.of_faceReachable_left
    {x x' y : G.Dart}
    (hxx' : PermReachable G.face x x')
    (hxy : G.RingAdj x' y) :
    G.RingAdj x y := by
  rcases hxy with ⟨z, hx'z, hzy⟩
  exact ⟨z, PermReachable.trans G.face hxx' hx'z, hzy⟩

theorem RingAdj.congr_faceReachable_left
    {x x' y : G.Dart}
    (hxx' : PermReachable G.face x x') :
    G.RingAdj x y ↔ G.RingAdj x' y := by
  constructor
  · intro hxy
    exact RingAdj.of_faceReachable_left (G := G)
      (PermReachable.symm G.face hxx') hxy
  · intro hx'y
    exact RingAdj.of_faceReachable_left (G := G) hxx' hx'y

theorem RingAdj.exists_mem_congr_faceReachable_left
    {r : List G.Dart} {x x' : G.Dart}
    (hxx' : PermReachable G.face x x') :
    (∃ y : G.Dart, y ∈ r ∧ G.RingAdj x y) ↔
      ∃ y : G.Dart, y ∈ r ∧ G.RingAdj x' y := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy,
      (RingAdj.congr_faceReachable_left (G := G) hxx').1 hxy⟩
  · rintro ⟨y, hy, hx'y⟩
    exact ⟨y, hy,
      (RingAdj.congr_faceReachable_left (G := G) hxx').2 hx'y⟩

theorem RingAdj.of_faceReachable_right
    {x y y' : G.Dart}
    (hxy : G.RingAdj x y)
    (hyy' : PermReachable G.face y y') :
    G.RingAdj x y' := by
  rcases hxy with ⟨z, hxz, hzy⟩
  exact ⟨z, hxz, PermReachable.trans G.face hzy hyy'⟩

/-- Coq `geometry.v::no_adj_adj`: a face in the same orbit as an adjacent
face is adjacent as well. -/
theorem RingAdj.not_faceReachable_of_not_ringAdj_of_ringAdj
    {x y₁ y₂ : G.Dart}
    (hxy₁ : ¬ G.RingAdj x y₁)
    (hxy₂ : G.RingAdj x y₂) :
    ¬ PermReachable G.face y₁ y₂ := by
  intro hy₁y₂
  apply hxy₁
  exact RingAdj.of_faceReachable_right (G := G) hxy₂
    (PermReachable.symm G.face hy₁y₂)

/-- Coq `geometry.v::adj_no_cface`: adjacent faces of a bridgeless hypermap
are distinct. -/
theorem Bridgeless.not_faceReachable_of_ringAdj
    (hG : G.Bridgeless) {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    ¬ PermReachable G.face x y := by
  rintro hface
  rcases hxy with ⟨z, hxz, hedgeZY⟩
  exact hG z
    (PermReachable.trans G.face
      (PermReachable.symm G.face hxz)
      (PermReachable.trans G.face hface
        (PermReachable.symm G.face hedgeZY)))

theorem RingAdj.exists_mem_optional_prefix
    {r : List G.Dart} {x y : G.Dart} (b : Bool) :
    (∃ z : G.Dart,
      z ∈ (if b then [y] else []) ++ r ∧ G.RingAdj x z) ↔
      (b = true ∧ G.RingAdj x y) ∨
        ∃ z : G.Dart, z ∈ r ∧ G.RingAdj x z := by
  cases b <;> simp

theorem RingAdj.exists_mem_two_optional_prefixes
    {r : List G.Dart} {x y z : G.Dart} (b0 b1 : Bool) :
    (∃ w : G.Dart,
      w ∈ (if b0 then [y] else []) ++ (if b1 then [z] else []) ++ r ∧
        G.RingAdj x w) ↔
      (b0 = true ∧ G.RingAdj x y) ∨
        (b1 = true ∧ G.RingAdj x z) ∨
          ∃ w : G.Dart, w ∈ r ∧ G.RingAdj x w := by
  cases b0 <;> cases b1 <;> simp

theorem RingAdj.exists_mem_optional_middle
    {r s : List G.Dart} {x y : G.Dart} (b : Bool) :
    (∃ z : G.Dart,
      z ∈ r ++ (if b then [y] else []) ++ s ∧ G.RingAdj x z) ↔
      (∃ z : G.Dart, z ∈ r ∧ G.RingAdj x z) ∨
        (b = true ∧ G.RingAdj x y) ∨
          ∃ z : G.Dart, z ∈ s ∧ G.RingAdj x z := by
  have hmem : ∀ z : G.Dart,
      z ∈ r ++ (if b then [y] else []) ++ s ↔
        z ∈ r ∨ (b = true ∧ z = y) ∨ z ∈ s := by
    intro z
    cases b <;> simp
  constructor
  · rintro ⟨z, hz, hxz⟩
    rcases (hmem z).1 hz with hz | hmid | hz
    · exact Or.inl ⟨z, hz, hxz⟩
    · exact Or.inr (Or.inl ⟨hmid.1, by simpa [hmid.2] using hxz⟩)
    · exact Or.inr (Or.inr ⟨z, hz, hxz⟩)
  · rintro (⟨z, hz, hxz⟩ | hmid | ⟨z, hz, hxz⟩)
    · exact ⟨z, (hmem z).2 (Or.inl hz), hxz⟩
    · exact ⟨y, (hmem y).2 (Or.inr (Or.inl ⟨hmid.1, rfl⟩)), hmid.2⟩
    · exact ⟨z, (hmem z).2 (Or.inr (Or.inr hz)), hxz⟩

theorem RingAdj.symm_of_plain
    (hG : G.Plain)
    {x y : G.Dart}
    (hxy : G.RingAdj x y) :
    G.RingAdj y x := by
  rcases hxy with ⟨z, hxz, hzy⟩
  refine ⟨G.edge z, PermReachable.symm G.face hzy, ?_⟩
  simpa [hG z |>.1] using PermReachable.symm G.face hxz

theorem Cubic.precubic
    (hG : G.Cubic) :
    G.Precubic := by
  intro x
  exact Or.inr (Or.inr (hG x).1)

theorem Precubic.cubic_of_no_short_node_orbits
    (hG : G.Precubic)
    (hfixed : ∀ x : G.Dart, G.node x ≠ x)
    (hperiodTwo : ∀ x : G.Dart, G.node (G.node x) ≠ x) :
    G.Cubic := by
  intro x
  constructor
  · rcases hG x with h1 | h2 | h3
    · exact False.elim (hfixed x h1)
    · exact False.elim (hperiodTwo x h2)
    · exact h3
  · exact hfixed x

theorem Precubic.node_symm_period
    (hG : G.Precubic)
    (x : G.Dart) :
    G.node.symm x = x ∨
      G.node.symm (G.node.symm x) = x ∨
        G.node.symm (G.node.symm (G.node.symm x)) = x := by
  rcases hG x with h1 | h2 | h3
  · left
    calc
      G.node.symm x = G.node.symm (G.node x) := by rw [h1]
      _ = x := by simp
  · right
    left
    have hsym : G.node x = G.node.symm x := by
      calc
        G.node x = G.node.symm (G.node (G.node x)) := by
          exact (G.node.symm_apply_apply (G.node x)).symm
        _ = G.node.symm x := by rw [h2]
    calc
      G.node.symm (G.node.symm x) = G.node.symm (G.node x) := by rw [← hsym]
      _ = x := by simp
  · right
    right
    have hA : G.node (G.node x) = G.node.symm x := by
      calc
        G.node (G.node x) =
            G.node.symm (G.node (G.node (G.node x))) := by
              exact (G.node.symm_apply_apply (G.node (G.node x))).symm
        _ = G.node.symm x := by rw [h3]
    have hB : G.node x = G.node.symm (G.node.symm x) := by
      calc
        G.node x = G.node.symm (G.node (G.node x)) := by
          exact (G.node.symm_apply_apply (G.node x)).symm
        _ = G.node.symm (G.node.symm x) := by rw [hA]
    have hC : x = G.node.symm (G.node.symm (G.node.symm x)) := by
      calc
        x = G.node.symm (G.node x) := by
          exact (G.node.symm_apply_apply x).symm
        _ = G.node.symm (G.node.symm (G.node.symm x)) := by rw [hB]
    exact hC.symm

theorem Precubic.mirror
    (hG : G.Precubic) :
    G.mirror.Precubic := by
  intro x
  change
    G.node.symm x = x ∨
      G.node.symm (G.node.symm x) = x ∨
        G.node.symm (G.node.symm (G.node.symm x)) = x
  exact Precubic.node_symm_period (G := G) hG x

theorem Cubic.node_symm_period_three
    (hG : G.Cubic)
    (x : G.Dart) :
    G.node.symm (G.node.symm (G.node.symm x)) = x := by
  have h3 : G.node (G.node (G.node x)) = x := (hG x).1
  have hA : G.node (G.node x) = G.node.symm x := by
    calc
      G.node (G.node x) =
          G.node.symm (G.node (G.node (G.node x))) := by
            exact (G.node.symm_apply_apply (G.node (G.node x))).symm
      _ = G.node.symm x := by rw [h3]
  have hB : G.node x = G.node.symm (G.node.symm x) := by
    calc
      G.node x = G.node.symm (G.node (G.node x)) := by
        exact (G.node.symm_apply_apply (G.node x)).symm
      _ = G.node.symm (G.node.symm x) := by rw [hA]
  have hC : x = G.node.symm (G.node.symm (G.node.symm x)) := by
    calc
      x = G.node.symm (G.node x) := by
        exact (G.node.symm_apply_apply x).symm
      _ = G.node.symm (G.node.symm (G.node.symm x)) := by rw [hB]
  exact hC.symm

theorem Cubic.mirror
    (hG : G.Cubic) :
    G.mirror.Cubic := by
  intro x
  constructor
  · change G.node.symm (G.node.symm (G.node.symm x)) = x
    exact Cubic.node_symm_period_three (G := G) hG x
  · intro hfixed
    have hbad : G.node x = x := by
      change G.node.symm x = x at hfixed
      calc
        G.node x = G.node (G.node.symm x) := by rw [hfixed]
        _ = x := by simp
    exact (hG x).2 hbad

theorem Plain.edge_edge
    (hG : G.Plain)
    (x : G.Dart) :
    G.edge (G.edge x) = x :=
  (hG x).1

theorem Plain.edge_ne
    (hG : G.Plain)
    (x : G.Dart) :
    G.edge x ≠ x :=
  (hG x).2

theorem Plain.eq_edge_of_edge_eq
    (hG : G.Plain)
    {x y : G.Dart}
    (hxy : G.edge x = y) :
    x = G.edge y := by
  calc
    x = G.edge (G.edge x) :=
      (Plain.edge_edge (G := G) hG x).symm
    _ = G.edge y := by rw [hxy]

theorem Plain.edge_symm_eq
    (hG : G.Plain)
    (x : G.Dart) :
    G.edge.symm x = G.edge x := by
  apply G.edge.injective
  calc
    G.edge (G.edge.symm x) = x := by simp
    _ = G.edge (G.edge x) :=
      (Plain.edge_edge (G := G) hG x).symm

end Hypermap

end FourColor

end Schematic.Math.GraphTheory
