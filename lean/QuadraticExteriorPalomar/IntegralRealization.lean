/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import GapExtremal.Bridge

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
variable {B : SimpleGraph V} [DecidableRel B.Adj] {N : H → Finset V}

/-- Witness-explicit form of Paper I's `host_fractional_partition`. Its
construction and accounting are from GapExtremal.Bridge. Keeping the actual
completion lets us prove integrality for characteristic residual weights. -/
private theorem canonical_partition {φ : V → V → H} (hH : HostHyp B N φ) {y : Finset V → ℝ}
    (hy : ResPack y) :
    let x := completion (hostGraph N) (weightOf B y) (cliqueOf B φ)
    (hostGraph N).IsFracCliquePartition x ∧
      ∑ Q ∈ (hostGraph N).cliqueSets, x Q =
        (E2 (hostGraph N) : ℝ) - (∑ S, y S * w B S + 2 * (jPairs B univ).card) := by
  classical
  have hres : ∀ p ∈ jPairs B univ, resLoad y p ≤ 1 := by
    intro p hp
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (two_of_mem_jPairs hp)
    rw [resLoad_pair]; exact hy.load a b hab
  have hcl : ∀ k, IsClq (hostGraph N) (cliqueOf B φ k) := by
    rintro (⟨S, hS⟩ | k)
    · refine ⟨by simpa [cliqueOf, Finset.card_disjSum] using hS, ?_⟩
      intro u hu v hv huv
      simp only [cliqueOf, Finset.mem_disjSum, Finset.notMem_empty] at hu hv
      rcases u with x | h <;> rcases v with x' | h' <;> simp_all
    · obtain ⟨hne, hk⟩ := ends_spec k
      have h1 : (ends B k).1 ∈ k.1 := by rw [hk]; simp
      have h2 : (ends B k).2 ∈ k.1 := by rw [hk]; simp
      have hnadj := nonadj_of_mem_jPairs k.2 _ h1 _ h2
      have hcov := hH.cover _ _ hne hnadj
      refine ⟨?_, ?_⟩
      · simp [cliqueOf, Finset.card_disjSum, two_of_mem_jPairs k.2]
      · intro u hu v hv huv
        simp only [cliqueOf] at hu hv
        rcases u with x | h <;> rcases v with x' | h'
        · simpa using huv
        · rw [Finset.inl_mem_disjSum, hk] at hu
          rw [Finset.inr_mem_disjSum, Finset.mem_singleton] at hv
          rw [hostGraph_inl_inr, hv]
          simp only [mem_insert, mem_singleton] at hu
          rcases hu with rfl | rfl
          exacts [hcov.1, hcov.2]
        · rw [Finset.inl_mem_disjSum, hk] at hv
          rw [Finset.inr_mem_disjSum, Finset.mem_singleton] at hu
          rw [hostGraph_inr_inl, hu]
          simp only [mem_insert, mem_singleton] at hv
          rcases hv with rfl | rfl
          exacts [hcov.1, hcov.2]
        · rw [Finset.inr_mem_disjSum, Finset.mem_singleton] at hu hv
          exact absurd (by rw [hu, hv]) huv
  have hz : ∀ k, 0 ≤ weightOf B y k := by
    rintro (S | k)
    · exact hy.nonneg _
    · simp only [weightOf]; linarith [hres k.1 k.2]
  -- loads
  have hload : ∀ u v, (hostGraph N).Adj u v → loadQ (weightOf B y) (cliqueOf B φ) {u, v} ≤ 1 := by
    rintro (a | h) (b | h') huv
    · exact load_core hy a b (by simpa using huv)
    · exact load_host hH hy a h'
    · rw [Finset.pair_comm]; exact load_host hH hy b h
    · exact absurd huv (hostGraph_inr_inr N h h')
  have hval : ∑ k, weightOf B y k * ((((cliqueOf B φ k).card.choose 2 : ℕ) : ℝ) - 1) =
      ∑ S, y S * w B S + 2 * (jPairs B univ).card := by
    rw [Fintype.sum_sum_type]
    have hA : ∑ S : {S : Finset V // 2 ≤ S.card}, weightOf B y (Sum.inl S) *
        ((((cliqueOf B φ (Sum.inl S)).card.choose 2 : ℕ) : ℝ) - 1) =
        ∑ S, y S * ((((S.card.choose 2 : ℕ) : ℝ)) - 1) := by
      simp only [weightOf, cliqueOf, Finset.card_disjSum, Finset.card_empty, add_zero]
      rw [← Finset.sum_subtype (univ.filter fun S : Finset V => 2 ≤ S.card)
        (p := fun S : Finset V => 2 ≤ S.card) (fun S => by simp)
        (fun S => y S * ((((S.card.choose 2 : ℕ) : ℝ)) - 1)), Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs with h
      · rfl
      · have : y S = 0 := by
          by_contra h'
          exact h (hy.two S h')
        simp [this]
    have hB : ∑ k : {p : Finset V // p ∈ jPairs B univ}, weightOf B y (Sum.inr k) *
        ((((cliqueOf B φ (Sum.inr k)).card.choose 2 : ℕ) : ℝ) - 1) =
        ∑ p ∈ jPairs B univ, 2 * (1 - resLoad y p) := by
      rw [← Finset.sum_coe_sort (jPairs B univ)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [weightOf, cliqueOf, Finset.card_disjSum, Finset.card_singleton,
        two_of_mem_jPairs k.2]
      norm_num
      ring
    have hw : ∀ S, y S * ((((S.card.choose 2 : ℕ) : ℝ)) - 1) =
        y S * w B S + 2 * (y S * (jPairs B S).card) := by
      intro S
      have h1 := w_add_two_j B S
      have h' : ((((S.card.choose 2 : ℕ) : ℝ)) - 1) = (w B S : ℝ) + 2 * (jPairs B S).card := by
        exact_mod_cast h1.symm
      rw [h']
      ring
    have hdouble : ∑ S, y S * ((jPairs B S).card : ℝ) = ∑ p ∈ jPairs B univ, resLoad y p := by
      unfold resLoad
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [jPairs_eq_filter B S, Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> simp
    rw [hA, hB, Finset.sum_congr rfl fun S _ => hw S, Finset.sum_add_distrib, ← Finset.mul_sum,
      hdouble]
    have h2 : ∑ p ∈ jPairs B univ, 2 * (1 - resLoad y p) =
        2 * (jPairs B univ).card - 2 * ∑ p ∈ jPairs B univ, resLoad y p := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      ring
    rw [h2]
    ring
  exact ⟨completion_isFrac hz hcl hload, by rw [completion_sum hcl, hval]⟩

/-- Integer-valued fractional partitions give genuine partitions of the same cost. -/
theorem partition_of_integral_weights {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph U} {x : Finset U → ℝ} (hx : G.IsFracCliquePartition x)
    (hint : ∀ Q, ∃ z : ℤ, (z : ℝ) = x Q) :
    (G.cliquePartitionNumber : ℝ) ≤ ∑ Q, x Q := by
  classical
  let P := univ.filter fun Q => x Q ≠ 0
  have one (Q) (hq : x Q ≠ 0) : x Q = 1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (hx.support Q hq).1
    have he := hx.edge a b ((hx.support Q hq).2 ha hb hab)
    have hu := single_le_sum (f := x) (fun R _ => hx.nonneg R)
      (mem_filter.mpr ⟨mem_univ Q,ha,hb⟩ : Q ∈ univ.filter (fun R : Finset U => a ∈ R ∧ b ∈ R))
    rw [he] at hu
    obtain ⟨z,hz⟩ := hint Q
    have hl := hx.nonneg Q
    rw [← hz] at hu hl hq ⊢
    norm_cast at hu hl hq ⊢
    omega
  have repr (Q) : x Q = if Q ∈ P then 1 else 0 := by
    by_cases hq : x Q = 0
    · simp [P,hq]
    · simpa [P,hq] using one Q hq
  have hP : G.IsCliquePartition P := by
    refine ⟨fun Q h => (hx.support Q (mem_filter.mp h).2).1,
      fun Q h => (hx.support Q (mem_filter.mp h).2).2, ?_⟩
    intro a b hab
    let A := univ.filter (fun Q : Finset U => a ∈ Q ∧ b ∈ Q)
    have hn : (A.filter (· ∈ P)).card = 1 := by
      have he := hx.edge a b hab
      change (∑ Q ∈ A, x Q) = 1 at he
      simp_rw [repr] at he
      rw [← sum_filter] at he
      simpa using he
    obtain ⟨Q,hQ⟩ := card_eq_one.mp hn
    have iff_mem (S : Finset U) : S ∈ P ∧ a ∈ S ∧ b ∈ S ↔ S = Q := by
      have h := Finset.ext_iff.mp hQ S
      simpa [A, and_comm, and_left_comm, and_assoc] using h
    exact ⟨Q,(iff_mem Q).2 rfl,fun S hs => (iff_mem S).1 hs⟩
  have hc : (∑ Q, x Q) = P.card := by
    simp_rw [repr]
    simp
  rw [hc]
  exact_mod_cast SimpleGraph.cliquePartitionNumber_le hP

private theorem indicator_pack (P : Finset (Finset V)) (hp : IsPack P)
    (hsize : ∀ Q ∈ P, 2 ≤ Q.card) :
    ResPack (fun Q => if Q ∈ P then (1 : ℝ) else 0) := by
  classical
  refine ⟨fun Q => by split_ifs <;> norm_num, fun Q hn => ?_, ?_⟩
  · by_cases h : Q ∈ P
    · exact hsize Q h
    · simp [h] at hn
  · intro a b hab
    let A := P.filter fun Q => a ∈ Q ∧ b ∈ Q
    have ha : A.card ≤ 1 := by
      apply card_le_one.mpr
      intro Q hQ R hR
      by_contra hn
      obtain ⟨hq,haQ,hbQ⟩ := mem_filter.mp hQ
      obtain ⟨hr,haR,hbR⟩ := mem_filter.mp hR
      exact hab (card_le_one.mp (hp Q hq R hr hn) _ (mem_inter.mpr ⟨haQ,haR⟩)
        _ (mem_inter.mpr ⟨hbQ,hbR⟩))
    calc
      _ = ∑ Q : Finset V, if Q ∈ A then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro Q _
        by_cases h : a ∈ Q ∧ b ∈ Q <;> simp [A,h]
      _ ≤ 1 := by simpa using (show (A.card : ℝ) ≤ 1 by exact_mod_cast ha)

/-- Lift a residual integral packing to a physical integral bound. -/
theorem cp_le_of_residual_pack {φ : V → V → H} (hh : HostHyp B N φ)
    (P : Finset (Finset V)) (hp : IsPack P) (hsize : ∀ Q ∈ P, 2 ≤ Q.card) :
    ((hostGraph N).cliquePartitionNumber : ℝ) ≤
      (E2 (hostGraph N) : ℝ) - ((∑ Q ∈ P, w B Q : ℤ) + 2 * (jPairs B univ).card) := by
  classical
  let y (S : Finset V) : ℝ := if S ∈ P then 1 else 0
  let Z := (Int.castRingHom ℝ).range
  have hy : ResPack y := indicator_pack P hp hsize
  have hyZ (S) : y S ∈ Z := by dsimp [y]; split_ifs <;> simp
  have hweight (k : KIdx B) : weightOf B y k ∈ Z := by
    cases k with
    | inl S => exact hyZ S
    | inr p =>
      apply Z.sub_mem Z.one_mem
      apply Z.sum_mem
      intro S _
      split_ifs
      · exact hyZ S
      · exact Z.zero_mem
  let x := completion (hostGraph N) (weightOf B y) (cliqueOf B φ)
  have hxZ (Q) : x Q ∈ Z := by
    unfold x completion
    apply Z.add_mem
    · apply Z.sum_mem
      intro k _
      split_ifs
      · exact hweight k
      · exact Z.zero_mem
    · split_ifs
      · apply Z.sub_mem Z.one_mem
        apply Z.sum_mem
        intro k _
        split_ifs
        · exact hweight k
        · exact Z.zero_mem
      · exact Z.zero_mem
  obtain ⟨hx, hcost⟩ := canonical_partition hh hy
  have h := partition_of_integral_weights hx (fun Q => hxZ Q)
  rw [← hx.sum_cliqueSets, hcost] at h
  simpa [y, ite_mul, ← Finset.sum_filter] using h

end QuadraticExteriorPalomar
