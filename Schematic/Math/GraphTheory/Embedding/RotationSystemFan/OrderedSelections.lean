import Schematic.Math.GraphTheory.Embedding.RotationSystemFan.FanGraph

/-! Finite ordered selections from facial boundaries. -/

namespace Schematic.Math.GraphTheory

open SimpleGraph

namespace FourColor

universe u v w

namespace RotationSystemFan

/-- Insert the vertices of `ys` into a set, from left to right.  This is the
set carried by the graph-indexed fan induction. -/
def insertList {V : Type u} : List V -> Set V -> Set V
  | [], A => A
  | y :: ys, A => insertList ys (insert y A)

/-- `OrderedSelections qs source residual` records that `qs` occurs in
`source` in order and that `residual` is the suffix beginning with the last
selected entry.  For no selections the whole source is retained. -/
inductive OrderedSelections {alpha : Type u} :
    List alpha -> List alpha -> List alpha -> Prop
  | nil (source : List alpha) : OrderedSelections [] source source
  | one (pre : List alpha) (q : alpha) (post : List alpha) :
      OrderedSelections [q] (pre ++ q :: post) (q :: post)
  | cons (pre : List alpha) (q r : alpha) (qs post residual : List alpha)
      (tail : OrderedSelections (r :: qs) post residual) :
      OrderedSelections (q :: r :: qs) (pre ++ q :: post) residual

namespace OrderedSelections

theorem map
    {alpha : Type u} {beta : Type v} (f : alpha -> beta)
    {qs source residual : List alpha}
    (h : OrderedSelections qs source residual) :
    OrderedSelections (qs.map f) (source.map f) (residual.map f) := by
  induction h with
  | nil source => exact .nil (source.map f)
  | one pre q post =>
      simpa using OrderedSelections.one (pre.map f) (f q) (post.map f)
  | cons pre q r qs post residual tail ih =>
      simpa using OrderedSelections.cons (pre.map f) (f q) (f r)
        (qs.map f) (post.map f) (residual.map f) ih

theorem prepend
    {alpha : Type u} {q : alpha} {qs source residual : List alpha}
    (pref : List alpha)
    (h : OrderedSelections (q :: qs) source residual) :
    OrderedSelections (q :: qs) (pref ++ source) residual := by
  cases h with
  | one pre q post =>
      simpa [List.append_assoc] using
        OrderedSelections.one (pref ++ pre) q post
  | cons pre q r qs post residual tail =>
      simpa [List.append_assoc] using
        OrderedSelections.cons (pref ++ pre) q r qs post residual tail

theorem appendSuffix
    {alpha : Type u} {q : alpha} {qs source residual : List alpha}
    (suffix : List alpha)
    (h : OrderedSelections (q :: qs) source residual) :
    OrderedSelections (q :: qs) (source ++ suffix) (residual ++ suffix) := by
  cases h with
  | one pre q post =>
      simpa [List.append_assoc] using
        OrderedSelections.one pre q (post ++ suffix)
  | cons pre q r qs post residual tail =>
      simpa [List.append_assoc] using
        OrderedSelections.cons pre q r qs (post ++ suffix)
          (residual ++ suffix) (tail.appendSuffix suffix)

end OrderedSelections

theorem OrderedSelections.singleton_split
    {alpha : Type u} {q : alpha} {source residual : List alpha}
    (h : OrderedSelections [q] source residual) :
    Exists fun pre : List alpha => Exists fun post : List alpha =>
      source = pre ++ q :: post ∧ residual = q :: post := by
  cases h with
  | one pre q post => exact ⟨pre, post, rfl, rfl⟩

theorem OrderedSelections.cons_split
    {alpha : Type u} {q r : alpha} {qs source residual : List alpha}
    (h : OrderedSelections (q :: r :: qs) source residual) :
    Exists fun pre : List alpha => Exists fun post : List alpha =>
      source = pre ++ q :: post ∧
        OrderedSelections (r :: qs) post residual := by
  cases h with
  | cons pre q r qs post residual tail => exact ⟨pre, post, rfl, tail⟩

namespace Internal

theorem exists_orderedSelections_filter
    {alpha : Type u} (p : alpha -> Bool) (source : List alpha)
    (hne : source.filter p ≠ []) :
    Exists fun q : alpha => Exists fun qs : List alpha =>
      Exists fun residual : List alpha =>
        source.filter p = q :: qs ∧
          OrderedSelections (q :: qs) source residual := by
  induction source with
  | nil => simp at hne
  | cons a source ih =>
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha]
        cases htail : source.filter p with
        | nil =>
            exact ⟨a, [], a :: source, by simp, by
              exact OrderedSelections.one [] a source⟩
        | cons q qs =>
            have htailNe : source.filter p ≠ [] := by simp [htail]
            rcases ih htailNe with ⟨q', qs', residual, hfilter, hselect⟩
            have hq : q' = q := by
              simpa [htail] using (congrArg List.head? hfilter).symm
            subst q'
            have hqs : qs' = qs := by
              simpa [htail] using (congrArg List.tail hfilter).symm
            subst qs'
            exact ⟨a, q :: qs, residual, by simp, by
              exact OrderedSelections.cons [] a q qs source residual hselect⟩
      · rw [List.filter_cons_of_neg ha]
        have hneTail : source.filter p ≠ [] := by
          intro hnil
          apply hne
          rw [List.filter_cons_of_neg ha, hnil]
        rcases ih hneTail with ⟨q, qs, residual, hfilter, hselect⟩
        exact ⟨q, qs, residual, hfilter, by
          simpa using hselect.prepend [a]⟩

end Internal

/-- If `q` is the final selected entry of a list, filtering produces a
nonempty ordered selection whose retained suffix is exactly `q :: suffix`. -/
theorem exists_orderedSelections_filter_with_final
    {alpha : Type u} (p : alpha -> Bool)
    (pre : List alpha) (q : alpha) (suffix : List alpha)
    (hq : p q = true)
    (hsuffix : forall a, a ∈ suffix -> p a = false) :
    Exists fun first : alpha =>
      Exists fun rest : List alpha =>
        (pre ++ q :: suffix).filter p = first :: rest ∧
          OrderedSelections (first :: rest)
            (pre ++ q :: suffix) (q :: suffix) := by
  induction pre with
  | nil =>
      have hfilterSuffix : suffix.filter p = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha
        simp [hsuffix a ha]
      exact ⟨q, [], by simp [hq, hfilterSuffix], by
        exact OrderedSelections.one [] q suffix⟩
  | cons a pre ih =>
      rcases ih with ⟨first, rest, hfilter, hselect⟩
      by_cases ha : p a = true
      · refine ⟨a, first :: rest, ?_, ?_⟩
        · simp [ha, hfilter]
        · simpa using OrderedSelections.cons [] a first rest
            (pre ++ q :: suffix) (q :: suffix) hselect
      · refine ⟨first, rest, ?_, ?_⟩
        · simp [ha, hfilter]
        · simpa using hselect.prepend [a]

/-- Every dart after the first dart of a simple path starts at an internal
vertex. -/
theorem Walk.IsPath.dart_fst_mem_internalVertices_of_mem_tail_darts
    {V : Type u} {G : SimpleGraph V} {x y : V}
    {p : G.Walk x y} (hp : p.IsPath) {d : G.Dart}
    (hd : d ∈ p.darts.tail) :
    d.fst ∈ Walk.InternalVertices p := by
  cases p with
  | nil => simp at hd
  | cons h p =>
      have hd' : d ∈ p.darts := by simpa using hd
      have hmem : d.fst ∈ p.support :=
        p.dart_fst_mem_support_of_mem_darts hd'
      have hnotStart : d.fst ≠ x := by
        have hnodup := hp.support_nodup
        rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
        intro hdx
        exact hnodup.1 (hdx ▸ hmem)
      exact ⟨by simp [hmem], hnotStart,
        Walk.IsPath.dart_fst_ne_end_of_mem_darts hp (by
          rw [SimpleGraph.Walk.darts_cons]
          exact List.mem_cons_of_mem _ hd')⟩

/-- Every internal vertex of a simple path starts a dart after its first
dart. -/
theorem Walk.IsPath.exists_mem_tail_darts_fst_eq_of_mem_internalVertices
    {V : Type u} {G : SimpleGraph V} {x y z : V}
    {p : G.Walk x y} (hp : p.IsPath)
    (hz : z ∈ Walk.InternalVertices p) :
    Exists fun d : G.Dart => d ∈ p.darts.tail ∧ d.fst = z := by
  have hzDrop : z ∈ p.support.dropLast := by
    apply List.mem_dropLast_of_mem_of_ne_getLast hz.1
    simpa using hz.2.2
  have hzMap : z ∈ p.darts.map (fun d : G.Dart => d.fst) := by
    rwa [SimpleGraph.Walk.map_fst_darts]
  rcases List.mem_map.mp hzMap with ⟨d, hd, hdz⟩
  refine ⟨d, ?_, hdz⟩
  cases p with
  | nil => exact (hz.2.1 (by simpa using hz.1)).elim
  | cons h p =>
      rw [SimpleGraph.Walk.darts_cons, List.mem_cons] at hd
      rcases hd with hdFirst | hdTail
      · have : z = x := by simpa [hdFirst] using hdz.symm
        exact (hz.2.1 this).elim
      · simpa using hdTail

@[simp]
theorem mem_insertList_iff
    {V : Type u} [DecidableEq V]
    (z : V) (ys : List V) (A : Set V) :
    z ∈ insertList ys A ↔ z ∈ A ∨ z ∈ ys := by
  induction ys generalizing A with
  | nil => simp [insertList]
  | cons y ys ih =>
      rw [insertList, ih]
      simp only [Set.mem_insert_iff, List.mem_cons]
      tauto

namespace Internal

theorem forall2_tail_map
    {V : Type u} {G : SimpleGraph V}
    (ds : List (OrientedEdge G)) :
    List.Forall₂ (fun d z => d.tail = z) ds (ds.map OrientedEdge.tail) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons rfl ih

theorem forall2_map_left_tail
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    {R : alpha -> beta -> Prop} {S : gamma -> beta -> Prop}
    (f : alpha -> gamma)
    (hf : forall a b, R a b -> S (f a) b)
    {xs : List alpha} {ys : List beta}
    (h : List.Forall₂ R xs ys) :
    List.Forall₂ S (xs.map f) ys := by
  induction h with
  | nil => exact .nil
  | cons hab hrest ih => exact .cons (hf _ _ hab) ih

end Internal

end RotationSystemFan

end FourColor

end Schematic.Math.GraphTheory
