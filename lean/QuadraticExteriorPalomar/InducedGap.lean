module

public import GapExtremal.Defs
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H D : SimpleGraph V}

/-- Restrict the blocks to the retained vertices. Isolated labels can be kept
in the vertex type, so all gap comparisons refer to the same type. -/
private theorem restrict_cp (W : Finset V)
    (h : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W) :
    H.cliquePartitionNumber ≤ G.cliquePartitionNumber := by
  classical
  obtain ⟨P, hp, hc⟩ := SimpleGraph.exists_isCliquePartition_card_eq G
  rw [← hc]
  let f (Q : Finset V) := Q ∩ W
  let R := (P.image f).filter (fun Q => 2 ≤ Q.card)
  have hr : H.IsCliquePartition R := by
    refine ⟨fun Q hQ => (mem_filter.mp hQ).2, ?_, ?_⟩
    · intro Q hQ
      obtain ⟨U, hU, rfl⟩ := mem_image.mp (mem_filter.mp hQ).1
      intro a ha b hb hab
      exact (h a b).2 ⟨hp.isClique U hU (mem_inter.mp ha).1 (mem_inter.mp hb).1 hab,
        (mem_inter.mp ha).2, (mem_inter.mp hb).2⟩
    · intro a b hab
      obtain ⟨hg, ha, hb⟩ := (h a b).1 hab
      obtain ⟨U, ⟨hU, hau, hbu⟩, hu⟩ := hp.existsUnique a b hg
      have ha' : a ∈ f U := mem_inter.mpr ⟨hau, ha⟩
      have hb' : b ∈ f U := mem_inter.mpr ⟨hbu, hb⟩
      refine ⟨f U, ⟨mem_filter.mpr ⟨mem_image_of_mem f hU,
        Finset.one_lt_card.mpr ⟨a, ha', b, hb', hab.ne⟩⟩, ha', hb'⟩, ?_⟩
      rintro Q ⟨hQ, hqa, hqb⟩
      obtain ⟨U', hU', rfl⟩ := mem_image.mp (mem_filter.mp hQ).1
      exact congrArg f (hu _ ⟨hU', (mem_inter.mp hqa).1, (mem_inter.mp hqb).1⟩)
  exact (SimpleGraph.cliquePartitionNumber_le hr).trans
    ((card_le_card (filter_subset _ _)).trans card_image_le)

private theorem restrict_frac (W : Finset V)
    (h : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W) :
    H.fracCliquePartitionNumber ≤ G.fracCliquePartitionNumber := by
  classical
  apply SimpleGraph.le_fracCliquePartitionNumber
  intro w hw
  let trace (U : Finset V) := U ∩ W
  let z (Q : Finset V) := ∑ U : Finset V, if trace U = Q ∧ 2 ≤ Q.card then w U else 0
  have sum_fiber (A : Finset (Finset V)) (U : Finset V) :
      (∑ Q ∈ A, if trace U = Q ∧ 2 ≤ Q.card then w U else 0) =
        if trace U ∈ A ∧ 2 ≤ (trace U).card then w U else 0 := by
    by_cases hm : trace U ∈ A
    · rw [sum_eq_single_of_mem (trace U) hm]
      · simp [hm]
      · intro Q _ hn
        simp [Ne.symm hn]
    · rw [sum_eq_zero, ite_eq_right (by simp [hm])]
      intro Q hQ
      have hn : trace U ≠ Q := fun heq => hm (heq ▸ hQ)
      simp [hn]
  have hz : H.IsFracCliquePartition z := by
    refine ⟨fun Q => sum_nonneg fun U _ => by split_ifs <;> simp [hw.nonneg], ?_, ?_⟩
    · intro Q hQ
      obtain ⟨U, _, hn⟩ := exists_ne_zero_of_sum_ne_zero hQ
      split at hn
      next hc =>
        obtain ⟨rfl, hs⟩ := hc
        refine ⟨hs, ?_⟩
        intro a ha b hb hab
        exact (h a b).2 ⟨(hw.support U hn).2 (mem_inter.mp ha).1 (mem_inter.mp hb).1 hab,
          (mem_inter.mp ha).2, (mem_inter.mp hb).2⟩
      next => exact (hn rfl).elim
    · intro a b hab
      obtain ⟨hg, ha, hb⟩ := (h a b).1 hab
      unfold z
      rw [sum_comm]
      simp_rw [sum_fiber]
      rw [← hw.edge a b hg, sum_filter]
      apply sum_congr rfl
      intro U _
      apply if_congr _ rfl rfl
      simp only [mem_filter, mem_univ, true_and, trace, mem_inter, ha, hb, and_true]
      exact ⟨And.left, fun ⟨hau, hbu⟩ => ⟨⟨hau, hbu⟩, one_lt_card.mpr
        ⟨a, mem_inter.mpr ⟨hau, ha⟩, b, mem_inter.mpr ⟨hbu, hb⟩, hab.ne⟩⟩⟩
  refine (SimpleGraph.fracCliquePartitionNumber_le hz).trans ?_
  unfold z
  rw [sum_comm]
  simp_rw [sum_fiber]
  exact sum_le_sum fun U _ => by split_ifs <;> simp [hw.nonneg]

/-- A partition of the extra graph gives an upper bound on the cost of
extending either an integral or a fractional partition of the old graph. -/
private theorem extend_costs (R : Finset (Finset V)) (hr : D.IsCliquePartition R)
    (hg : ∀ u v, G.Adj u v ↔ H.Adj u v ∨ D.Adj u v)
    (hd : ∀ u v, H.Adj u v → ¬ D.Adj u v) :
    G.cliquePartitionNumber ≤ H.cliquePartitionNumber + R.card ∧
      G.fracCliquePartitionNumber ≤ H.fracCliquePartitionNumber + R.card := by
  classical
  have other {A B : SimpleGraph V} {P : Finset (Finset V)} (hp : A.IsCliquePartition P)
      (hdis : ∀ u v, A.Adj u v → ¬ B.Adj u v) {a b : V} (hab : B.Adj a b) :
      ∀ Q ∈ P, a ∈ Q → b ∈ Q → False := by
    intro Q hQ ha hb
    exact hdis a b (hp.isClique Q hQ ha hb hab.ne) hab
  constructor
  · obtain ⟨P, hp, hc⟩ := SimpleGraph.exists_isCliquePartition_card_eq H
    rw [← hc]
    have hu : G.IsCliquePartition (P ∪ R) := by
      refine ⟨fun Q hQ => (mem_union.mp hQ).elim (hp.two_le Q) (hr.two_le Q), ?_, ?_⟩
      · intro Q hQ a ha b hb hab
        exact (hg a b).2 ((mem_union.mp hQ).imp
          (fun hP => hp.isClique Q hP ha hb hab) (fun hR => hr.isClique Q hR ha hb hab))
      · intro a b hab
        rcases (hg a b).1 hab with hh | hD
        · obtain ⟨U, ⟨hu, ha, hb⟩, unique⟩ := hp.existsUnique a b hh
          refine ⟨U, ⟨mem_union_left R hu, ha, hb⟩, ?_⟩
          rintro Q ⟨hq, hqa, hqb⟩
          exact (mem_union.mp hq).elim (fun hP => unique Q ⟨hP, hqa, hqb⟩)
            (fun hR => (other hr (fun u v hD hH => hd u v hH hD) hh Q hR hqa hqb).elim)
        · obtain ⟨U, ⟨hu, ha, hb⟩, unique⟩ := hr.existsUnique a b hD
          refine ⟨U, ⟨mem_union_right P hu, ha, hb⟩, ?_⟩
          rintro Q ⟨hq, hqa, hqb⟩
          exact (mem_union.mp hq).elim
            (fun hP => (other hp hd hD Q hP hqa hqb).elim) (fun hR => unique Q ⟨hR, hqa, hqb⟩)
    exact (SimpleGraph.cliquePartitionNumber_le hu).trans (card_union_le _ _)
  · apply sub_le_iff_le_add.mp
    apply SimpleGraph.le_fracCliquePartitionNumber
    intro w hw
    let i (Q : Finset V) : ℝ := if Q ∈ R then 1 else 0
    have hi : D.IsFracCliquePartition i := hr.isFracCliquePartition
    have hz {A : SimpleGraph V} {z : Finset V → ℝ} (hz : A.IsFracCliquePartition z)
        {a b : V} (hne : a ≠ b) (hna : ¬ A.Adj a b) :
        ∑ Q ∈ univ.filter (fun Q : Finset V => a ∈ Q ∧ b ∈ Q), z Q = 0 := by
      apply sum_eq_zero
      intro Q hQ
      by_contra hn
      exact hna ((hz.support Q hn).2 (mem_filter.mp hQ).2.1 (mem_filter.mp hQ).2.2 hne)
    have hsum : G.IsFracCliquePartition (fun Q => w Q + i Q) := by
      refine ⟨fun Q => add_nonneg (hw.nonneg Q) (hi.nonneg Q), ?_, ?_⟩
      · intro Q hn
        by_cases h : w Q = 0
        · have hh := hi.support Q (by simpa [h] using hn)
          exact ⟨hh.1, fun a ha b hb hab => (hg a b).2 (.inr (hh.2 ha hb hab))⟩
        · have hh := hw.support Q h
          exact ⟨hh.1, fun a ha b hb hab => (hg a b).2 (.inl (hh.2 ha hb hab))⟩
      · intro a b hab
        rw [sum_add_distrib]
        rcases (hg a b).1 hab with hh | hD
        · rw [hw.edge a b hh, hz hi hab.ne (hd a b hh), add_zero]
        · rw [hi.edge a b hD, hz hw hab.ne (fun hh => hd a b hh hD), zero_add]
    have hcost := SimpleGraph.fracCliquePartitionNumber_le hsum
    have hiSum : ∑ Q, i Q = (R.card : ℝ) := by simp [i]
    rw [sum_add_distrib, hiSum] at hcost
    linarith

/-- Isolating a set of vertices changes the actual gap by at most the cost
of any supplied clique partition of the removed edges. -/
theorem gap_change_of_induced_restriction (W : Finset V) (R : Finset (Finset V))
    (h : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W)
    (hr : D.IsCliquePartition R)
    (hg : ∀ u v, G.Adj u v ↔ H.Adj u v ∨ D.Adj u v)
    (hd : ∀ u v, H.Adj u v → ¬ D.Adj u v) :
    |GapExtremal.gap G - GapExtremal.gap H| ≤ (R.card : ℝ) := by
  have loI : (H.cliquePartitionNumber : ℝ) ≤ G.cliquePartitionNumber := by
    exact_mod_cast restrict_cp W h
  have loF := restrict_frac W h
  obtain ⟨hi, hf⟩ := extend_costs R hr hg hd
  have hi' : (G.cliquePartitionNumber : ℝ) ≤ (H.cliquePartitionNumber : ℝ) + R.card := by
    exact_mod_cast hi
  unfold GapExtremal.gap
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A partially hosted graph can be compared with its completed witness by
isolating the added hosts. Only their incident edges enter this estimate. -/
theorem gap_change_le_removed_edges [DecidableRel G.Adj] [DecidableRel H.Adj]
    (W : Finset V) (h : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ u ∈ W ∧ v ∈ W) :
    |GapExtremal.gap G - GapExtremal.gap H| ≤
      ((G.edgeFinset \ H.edgeFinset).card : ℝ) := by
  obtain ⟨R, hr, hc⟩ := SimpleGraph.exists_isCliquePartition_card_eq_edgeFinset (G \ H)
  have hg (u v : V) : G.Adj u v ↔ H.Adj u v ∨ (G \ H).Adj u v := by
    change G.Adj u v ↔ H.Adj u v ∨ G.Adj u v ∧ ¬ H.Adj u v
    by_cases hh : H.Adj u v
    · simp [hh, ((h u v).1 hh).1]
    · simp [hh]
  have hb := gap_change_of_induced_restriction W R h hr hg (fun _ _ hh hd => hd.2 hh)
  have hcount : R.card = (G.edgeFinset \ H.edgeFinset).card := by
    rw [hc]
    apply congrArg Finset.card
    ext e
    induction e using Sym2.ind with
    | h u v => simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  simpa only [hcount] using hb

end QuadraticExteriorPalomar
