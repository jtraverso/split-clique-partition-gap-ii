module

public import PaperVI.Counting
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset PaperVI

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every discarded clique in an edge-disjoint family consumes a different
missing edge. The retained cliques are actual cliques of the subgraph. -/
theorem retained_card_loss_le (J G : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel G.Adj]
    (S : Finset (Finset V))
    (hclique : ∀ Q ∈ S, J.IsClique (Q : Set V))
    (hdisj : ∀ Q ∈ S, ∀ R ∈ S, Q ≠ R → (Q ∩ R).card ≤ 1) :
    ∃ kept ⊆ S, (∀ Q ∈ kept, G.IsClique (Q : Set V)) ∧
      S.card ≤ kept.card + (J.edgeFinset \ G.edgeFinset).card := by
  classical
  let kept : Finset (Finset V) := S.filter fun (Q : Finset V) => G.IsClique (Q : Set V)
  let bad := S \ kept
  have hex (Q : bad) :
      ∃ e ∈ J.edgeFinset \ G.edgeFinset, e.toFinset ⊆ Q.1 := by
    have hQ := mem_sdiff.mp Q.2
    have hn : ¬ G.IsClique (Q.1 : Set V) := fun h =>
      hQ.2 (mem_filter.mpr ⟨hQ.1, h⟩)
    have hx : ∃ a ∈ Q.1, ∃ b ∈ Q.1, a ≠ b ∧ ¬ G.Adj a b := by
      by_contra! hh
      exact hn (fun a ha b hb hne => hh a ha b hb hne)
    obtain ⟨a, ha, b, hb, hne, hab⟩ := hx
    refine ⟨s(a, b), mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr
      (hclique _ hQ.1 ha hb hne), fun hm => hab (SimpleGraph.mem_edgeFinset.mp hm)⟩, ?_⟩
    intro v hv
    rcases (Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv)) with rfl | rfl <;> assumption
  choose edge hmissing hins using hex
  have hinj : Function.Injective edge := by
    intro Q R h
    apply Subtype.ext
    by_contra hne
    have hf : (edge Q).toFinset ⊆ Q.1 ∩ R.1 :=
      fun v hv => mem_inter.mpr ⟨hins Q hv, hins R (h ▸ hv)⟩
    have hsize := card_le_card hf
    rw [Sym2.card_toFinset_of_not_isDiag _
      (J.not_isDiag_of_mem_edgeFinset (mem_sdiff.mp (hmissing Q)).1)] at hsize
    have h₁ := (mem_sdiff.mp Q.2).1
    have h₂ := (mem_sdiff.mp R.2).1
    exact (by omega : ¬ (Q.1 ∩ R.1).card ≤ 1) (hdisj _ h₁ _ h₂ hne)
  have hbad : bad.card ≤ (J.edgeFinset \ G.edgeFinset).card := by
    rw [← show bad.attach.card = bad.card by simp, ← card_image_of_injective _ hinj]
    exact card_le_card (fun e he => by
      obtain ⟨Q, _, rfl⟩ := mem_image.mp he
      exact hmissing Q)
  have hsub : kept ⊆ S := filter_subset _ _
  have hsplit : bad.card + kept.card = S.card := card_sdiff_add_card_eq_card hsub
  exact ⟨kept, hsub, fun _ hQ => (mem_filter.mp hQ).2, by omega⟩

private theorem mem_inner {G : SimpleGraph V} [DecidableRel G.Adj]
    {Q : Finset V} {e : Sym2 V} :
    e ∈ innerEdges G Q ↔ e ∈ G.edgeFinset ∧ ∀ x ∈ e.toFinset, x ∈ Q := by
  simp only [innerEdges, mem_filter]

private theorem inner_support_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q R : Finset V} (h : (Q ∩ R).card ≤ 1) :
    Disjoint (innerEdges G Q) (innerEdges G R) := by
  rw [Finset.disjoint_left]
  intro e he hf
  have hsub : e.toFinset ⊆ Q ∩ R :=
    fun x hx => mem_inter.mpr ⟨(mem_inner.mp he).2 x hx, (mem_inner.mp hf).2 x hx⟩
  have hsize := card_le_card hsub
  rw [Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeFinset (mem_inner.mp he).1)]
    at hsize
  omega

/-- Finish a physical triangle packing in the Palomar clique-partition model.
Every unused edge becomes exactly one piece. -/
theorem cpLe_three_add_triangle_gain_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (hsize : ∀ Q ∈ S, Q.card = 3)
    (hclique : ∀ Q ∈ S, G.IsClique (Q : Set V))
    (hdisj : ∀ Q ∈ S, ∀ R ∈ S, Q ≠ R → (Q ∩ R).card ≤ 1) :
    cpLe 3 G + 2 * S.card ≤ G.edgeFinset.card := by
  classical
  let covered := S.biUnion (innerEdges G)
  let R := G.edgeFinset \ covered
  let P := S ∪ R.image Sym2.toFinset
  have hrest (e : Sym2 V) (he : e ∈ R) : e.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeFinset (mem_sdiff.mp he).1)
  have hcovered : covered ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨Q, _, heQ⟩ := mem_biUnion.mp he
    exact (mem_inner.mp heQ).1
  have hcovercard : covered.card = 3 * S.card := by
    rw [show covered = S.biUnion (innerEdges G) from rfl,
      card_biUnion (fun Q hQ T hT hn => inner_support_disjoint G (hdisj Q hQ T hT hn))]
    have hs (Q : Finset V) (hQ : Q ∈ S) : (innerEdges G Q).card = 3 := by
      rw [card_innerEdges_of_isClique G Q (hclique Q hQ), hsize Q hQ]
      decide
    rw [sum_congr rfl hs]
    simp [nsmul_eq_mul, Nat.mul_comm]
  have hpart : IsCliquePartition G P := by
    constructor
    · intro B hB
      rcases mem_union.mp hB with hB | hB
      · rw [hsize B hB]
        decide
      · obtain ⟨e, he, rfl⟩ := mem_image.mp hB
        exact (hrest e he).ge
    · intro B hB
      rcases mem_union.mp hB with hB | hB
      · exact hclique B hB
      · obtain ⟨e, he, rfl⟩ := mem_image.mp hB
        exact (isCliquePartition_edges G).isClique _ (mem_image.mpr ⟨e, (mem_sdiff.mp he).1, rfl⟩)
    · intro a b hab
      let e := s(a, b)
      have he : e ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hab
      have hin (Q : Finset V) (ha : a ∈ Q) (hb : b ∈ Q) : e ∈ innerEdges G Q := by
        refine mem_inner.mpr ⟨he, ?_⟩
        intro v hv
        rcases Sym2.mem_iff.mp (Sym2.mem_toFinset.mp hv) with rfl | rfl <;> assumption
      have heq (f : Sym2 V) (ha : a ∈ f.toFinset) (hb : b ∈ f.toFinset) : f = e :=
        (Sym2.mem_and_mem_iff hab.ne).mp ⟨Sym2.mem_toFinset.mp ha, Sym2.mem_toFinset.mp hb⟩
      by_cases hc : e ∈ covered
      · obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp hc
        have hsub := (mem_inner.mp heQ).2
        refine ⟨Q, ⟨mem_union_left _ hQ, hsub a (by simp [e]), hsub b (by simp [e])⟩, ?_⟩
        intro B hB
        obtain ⟨hB, haB, hbB⟩ := hB
        rcases mem_union.mp hB with hB | hB
        · by_contra hne
          exact Finset.disjoint_left.mp (inner_support_disjoint G (hdisj B hB Q hQ hne))
            (hin B haB hbB) heQ
        · obtain ⟨f, hf, rfl⟩ := mem_image.mp hB
          exact False.elim ((mem_sdiff.mp hf).2 (heq f haB hbB ▸ hc))
      · refine ⟨e.toFinset, ⟨mem_union_right _ (mem_image.mpr ⟨e, mem_sdiff.mpr ⟨he, hc⟩, rfl⟩),
          by simp [e], by simp [e]⟩, ?_⟩
        intro B hB
        obtain ⟨hB, haB, hbB⟩ := hB
        rcases mem_union.mp hB with hB | hB
        · exact False.elim (hc (mem_biUnion.mpr ⟨B, hB, hin B haB hbB⟩))
        · obtain ⟨f, _, rfl⟩ := mem_image.mp hB
          rw [heq f haB hbB]
  have hcp := cpLe_le hpart (r := 3) (by
    intro Q hQ
    rcases mem_union.mp hQ with hQ | hQ
    · exact (hsize Q hQ).le
    · obtain ⟨e, he, rfl⟩ := mem_image.mp hQ
      rw [hrest e he]
      decide)
  have hP : P.card ≤ S.card + R.card :=
    (card_union_le _ _).trans (Nat.add_le_add_left card_image_le _)
  have hh : R.card + covered.card = G.edgeFinset.card := card_sdiff_add_card_eq_card hcovered
  omega

end QuadraticExteriorPalomar
