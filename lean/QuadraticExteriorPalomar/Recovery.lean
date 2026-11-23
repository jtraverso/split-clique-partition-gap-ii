module

public import QuadraticExteriorPalomar.ExactTransfer

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sum_core_gain (B : SimpleGraph V) [DecidableRel B.Adj] (y : Finset V → ℝ) :
    ∑ Q, y Q * ((Q.card.choose 2 : ℝ) - 1) =
      ∑ Q, y Q * w B Q + 2 * ∑ p ∈ jPairs B univ, resLoad y p := by
  classical
  have dbl : ∑ Q, y Q * ((jPairs B Q).card : ℝ) = ∑ p ∈ jPairs B univ, resLoad y p := by
    unfold resLoad
    rw [sum_comm]
    refine sum_congr rfl fun Q _ => ?_
    rw [jPairs_eq_filter B Q, card_filter]
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    split_ifs <;> simp
  rw [← dbl, Finset.mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro Q _
  have hw : (w B Q : ℝ) + 2 * ((jPairs B Q).card : ℝ) = (Q.card.choose 2 : ℝ) - 1 := by
    exact_mod_cast w_add_two_j B Q
  rw [← hw]
  ring

/-- The savings from the core and the assigned triangles, with each missing
pair charged only for the mass that the core leaves uncovered. -/
theorem partial_savings_identity (B : SimpleGraph V) [DecidableRel B.Adj]
    (y : Finset V → ℝ) (J₀ : Finset (Finset V)) (hs : J₀ ⊆ jPairs B univ) :
    (∑ Q, y Q * ((Q.card.choose 2 : ℝ) - 1)) + 2 * ∑ p ∈ J₀, (1 - resLoad y p) =
    (∑ Q, y Q * w B Q) + 2 * ((jPairs B univ).card : ℝ) -
      2 * ∑ p ∈ jPairs B univ \ J₀, (1 - resLoad y p) := by
  classical
  have h := sum_sdiff hs (f := fun p => 1 - resLoad y p)
  have total : (∑ p ∈ jPairs B univ, (1 - resLoad y p)) = ((jPairs B univ).card : ℝ) - ∑ p ∈ jPairs B univ, resLoad y p := by simp [sum_sub_distrib]
  rw [total] at h
  rw [sum_core_gain B y]
  linarith

private theorem score_edit_le (B C : SimpleGraph V) [DecidableRel B.Adj] [DecidableRel C.Adj]
    {y : Finset V → ℝ} (hy : ResPack y) :
    ∑ Q, y Q * w C Q ≤ ∑ Q, y Q * w B Q + 2 * ((jPairs B univ \ jPairs C univ).card : ℝ) := by
  classical
  let J := jPairs B univ
  let K := jPairs C univ
  have hcap : ∑ p ∈ J \ K, resLoad y p ≤ ((J \ K).card : ℝ) := by
    calc
      _ ≤ ∑ _p ∈ J \ K, (1 : ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp (two_of_mem_jPairs (mem_sdiff.mp hp).1)
        rw [resLoad_pair]
        exact hy.load a b hab
      _ = _ := by simp
  have hd : ∑ p ∈ J, resLoad y p ≤ ∑ p ∈ K, resLoad y p + ((J \ K).card : ℝ) := by
    have hcover : J ⊆ K ∪ (J \ K) := by intro p hp; by_cases hk : p ∈ K <;> simp [hp,hk]
    calc
      _ ≤ ∑ p ∈ K ∪ (J \ K), resLoad y p :=
        sum_le_sum_of_subset_of_nonneg hcover fun p _ _ => resLoad_nonneg hy p
      _ = _ + ∑ p ∈ J \ K, resLoad y p :=
        sum_union (disjoint_sdiff_self_right)
      _ ≤ _ := by linarith
  dsimp [J,K] at hd
  linarith [sum_core_gain B y, sum_core_gain C y]

theorem score_bdd (B : SimpleGraph V) [DecidableRel B.Adj] :
    BddAbove {s : ℝ | ∃ y : Finset V → ℝ, ResPack y ∧ ∑ Q, y Q * w B Q = s} := by
  classical
  refine ⟨∑ Q : Finset V, |(w B Q : ℝ)|, ?_⟩
  rintro _ ⟨y,hy,rfl⟩
  apply sum_le_sum
  intro Q _
  by_cases hz : y Q = 0
  · simp [hz]
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (hy.two Q hz)
  have h1 : y Q ≤ 1 := calc
    _ = (if a ∈ Q ∧ b ∈ Q then y Q else 0) := by simp [ha,hb]
    _ ≤ ∑ S, (if a ∈ S ∧ b ∈ S then y S else 0) :=
      single_le_sum (f := fun S => if a ∈ S ∧ b ∈ S then y S else 0)
        (fun S _ => by split_ifs <;> simp [hy.nonneg]) (mem_univ Q)
    _ ≤ _ := hy.load a b hab
  calc
    _ ≤ y Q * |(w B Q : ℝ)| := mul_le_mul_of_nonneg_left (le_abs_self _) (hy.nonneg _)
    _ ≤ 1 * |(w B Q : ℝ)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = _ := one_mul _

private theorem frac_edit_le (B C : SimpleGraph V) [DecidableRel B.Adj] [DecidableRel C.Adj] :
    residualSup C ≤ residualSup B + 2 * ((jPairs B univ \ jPairs C univ).card : ℝ) := by
  classical
  apply csSup_le
  · exact ⟨_,fun _ => 0,by constructor <;> simp,rfl⟩
  · rintro _ ⟨y,hy,rfl⟩
    exact (score_edit_le B C hy).trans (add_le_add_left
      (show ∑ Q, y Q * w B Q ≤ residualSup B from le_csSup (score_bdd B) ⟨y,hy,rfl⟩) _)

-- Characteristic weights, as in IntegralRealization.
theorem indicator_resPack (P : Finset (Finset V)) (hp : IsPack P)
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


private theorem int_edit_le (B C : SimpleGraph V) [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (residualInt C : ℝ) ≤ residualInt B + 2 * ((jPairs B univ \ jPairs C univ).card : ℝ) := by
  classical
  let P := (exists_best_pack C).choose
  obtain ⟨hp,hs,_⟩ := (exists_best_pack C).choose_spec
  have h := score_edit_le B C (indicator_resPack P hp hs)
  simp only [ite_mul, one_mul, zero_mul, ← sum_filter, filter_mem_eq_inter, univ_inter] at h
  have hB : (∑ Q ∈ P, w B Q) ≤ residualInt B := (exists_best_pack B).choose_spec.2.2 P hp
  have hC : residualInt C = ∑ Q ∈ P, w C Q := rfl
  rw [hC]
  push_cast
  have upper : ∑ Q ∈ P, (w B Q : ℝ) ≤ (residualInt B : ℝ) := by exact_mod_cast hB
  linarith

/-- The symmetric difference of the required pair sets counts exactly the
edited core pairs. The two optima may move in the same direction. -/
theorem residual_gap_edit_bound (B C : SimpleGraph V) [DecidableRel B.Adj] [DecidableRel C.Adj] :
    |(residualSup C - residualInt C) - (residualSup B - residualInt B)| ≤
      2 * (((jPairs B univ \ jPairs C univ).card : ℝ) +
           ((jPairs C univ \ jPairs B univ).card : ℝ)) := by
  apply abs_le.mpr
  constructor <;> linarith [frac_edit_le B C, frac_edit_le C B, int_edit_le B C, int_edit_le C B]

end QuadraticExteriorPalomar
