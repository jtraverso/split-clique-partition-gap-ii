module

public import QuadraticExteriorPalomar.Recovery

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Independent finite convex combinations of legal host matchings bound the
actual gap by the sum of the exact miss probabilities. -/
theorem gap_of_matching_mixtures (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (K : H → Type*) [∀ h, Fintype (K h)]
    (A : ∀ h, K h → Finset (Finset V)) (μ : ∀ h, K h → ℝ)
    (pos : ∀ h i, 0 ≤ μ h i) (norm : ∀ h, ∑ i, μ h i = 1)
    (req : ∀ h i, A h i ⊆ jPairs B univ)
    (mem : ∀ h i e, e ∈ A h i → e ⊆ N h)
    (matchAt : ∀ h i e, e ∈ A h i → ∀ f ∈ A h i, ∀ v ∈ e, v ∈ f → e = f) :
    |gap (hostGraph N) - (residualSup B - residualInt B)| ≤
      2 * ∑ e ∈ jPairs B univ, ∏ h, ∑ i, (if e ∈ A h i then 0 else μ h i) := by
  classical
  let J := jPairs B univ
  let prob (d : ∀ h, K h) := ∏ h, μ h (d h)
  let seen (d : ∀ h, K h) := univ.biUnion (fun h => A h (d h))
  have hn : ∑ d, prob d = 1 := by
    simp only [prob,← Fintype.prod_sum,norm,prod_const_one]
  have valid (d : ∀ h, K h) :
      |gap (hostGraph N) - (residualSup B - residualInt B)| ≤ 2 * ((J \ seen d).card : ℝ) := by
    have sub : seen d ⊆ J := by
      intro e he
      obtain ⟨h,_,hm⟩ := mem_biUnion.mp he
      exact req h _ hm
    have pick (e : seen d) : ∃ h, e.val ∈ A h (d h) := by
      obtain ⟨h,_,hm⟩ := mem_biUnion.mp e.2
      exact ⟨h,hm⟩
    choose f hf using pick
    rw [card_sdiff_of_subset sub]
    apply gap_stability_of_partial_assignment B N hi _ sub f (fun e => mem _ _ _ (hf e))
    intro e g he v hv hw
    exact Subtype.ext (matchAt _ _ _ (hf e) _ (he.symm ▸ hf g) _ hv hw)
  have miss (e : Finset V) :
      (∑ d : ∀ h, K h, if e ∈ seen d then 0 else prob d) =
      ∏ h, ∑ i, if e ∈ A h i then 0 else μ h i := by
    rw [Fintype.prod_sum]
    apply sum_congr rfl
    intro d _
    by_cases he : e ∈ seen d
    · obtain ⟨h,_,ha⟩ := mem_biUnion.mp he
      rw [if_pos he]
      symm
      apply Finset.prod_eq_zero (mem_univ h)
      exact if_pos ha
    · rw [if_neg he]
      exact prod_congr rfl fun h _ => (if_neg (fun ha => he (mem_biUnion.mpr ⟨h,mem_univ _,ha⟩))).symm
  have count (d : ∀ h, K h) :
      prob d * ((J \ seen d).card : ℝ) = ∑ e ∈ J, if e ∈ seen d then 0 else prob d := by
    have hf : J \ seen d = J.filter (fun e => e ∉ seen d) := by ext e; simp
    calc
      _ = ∑ _e ∈ J.filter (fun e => e ∉ seen d), prob d := by simp [hf,mul_comm]
      _ = _ := by rw [sum_filter]; simp only [ite_not]
  calc
    _ = ∑ d, prob d * |gap (hostGraph N) - (residualSup B - residualInt B)| := by
      rw [← sum_mul, hn,one_mul]
    _ ≤ ∑ d, prob d * (2 * ((J \ seen d).card : ℝ)) :=
      sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (valid d) (prod_nonneg fun _ _ => pos _ _)
    _ = 2 * ∑ e ∈ J, ∏ h, ∑ i, (if e ∈ A h i then 0 else μ h i) := by
      simp_rw [mul_left_comm (prob _) 2, count]
      rw [← mul_sum,sum_comm]
      simp_rw [miss]

/-- Edmonds' mixture supplies the marginals. The product is bounded separately
on each edge, before summing across the required pairs. -/
theorem miss_product_le_exp {T : Type*} [Fintype T] (x : T → ℝ)
    (upper : ∀ h, x h ≤ 1) :
    (∏ h, (1 - x h)) ≤ Real.exp (- ∑ h, x h) := by
  rw [← sum_neg_distrib,Real.exp_sum]
  exact prod_le_prod₀ (fun h _ => sub_nonneg.mpr (upper h))
    (fun h _ => by linarith [Real.add_one_le_exp (-x h)])

end QuadraticExteriorPalomar
