module

public import QuadraticExteriorPalomar.Retention
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset PaperVI
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cost in the same split graph in which the triangles are realized. -/
theorem split_cost_of_triangle_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V))
    (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (S : Finset (Finset V)) (hsize : ∀ Q ∈ S, Q.card = 3)
    (hclique : ∀ Q ∈ S, G.IsClique (Q : Set V))
    (hdisj : ∀ Q ∈ S, ∀ R ∈ S, Q ≠ R → (Q ∩ R).card ≤ 1)
    (loss : ℕ) (hcover : C.card.choose 2 ≤ S.card + loss) :
    cpLe 3 G + C.card.choose 2 ≤ sCount G C + 2 * loss := by
  have hcore : uCount G C = C.card.choose 2 := card_innerEdges_of_isClique G C hC
  have hext : extEdges G C = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e
    induction e using Sym2.ind with
    | h a b =>
      simp only [extEdges, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        Sym2.mem_toFinset, Sym2.mem_iff]
      rintro ⟨hab, h⟩
      exact hI a (h a (Or.inl rfl)) b (h b (Or.inr rfl)) hab
  have hcounts : uCount G C + mCount G C + sCount G C = G.edgeFinset.card :=
    card_kinds C G.edgeFinset
  rw [hcore, show mCount G C = 0 from by simp [mCount, hext], add_zero] at hcounts
  have htri := cpLe_three_add_triangle_gain_le G S hsize hclique hdisj
  omega

/-- The signed split lower bound holds for any exact nonnegative fractional
edge partition into cliques of arbitrary order. -/
theorem split_fractional_price (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (w : Finset V → ℝ) (hnonneg : ∀ Q, 0 ≤ w Q)
    (hsupport : ∀ Q, w Q ≠ 0 → G.IsClique (Q : Set V))
    (hcover : ∀ e ∈ G.edgeFinset,
      ∑ Q : Finset V, (if e.toFinset ⊆ Q then w Q else 0) = 1) :
    (sCount G C : ℝ) - uCount G C ≤ ∑ Q, w Q := by
  classical
  have hsum (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
      ∑ Q : Finset V, w Q * ((insideFilter F Q).card : ℝ) = F.card := by
    calc
      _ = ∑ Q : Finset V, ∑ e ∈ F, (if e.toFinset ⊆ Q then w Q else 0) := by
        apply sum_congr rfl
        intro Q _
        unfold insideFilter
        rw [card_filter, Nat.cast_sum, mul_sum]
        apply sum_congr rfl
        intro e _
        by_cases he : e.toFinset ⊆ Q
        · have hmem : ∀ v ∈ e.toFinset, v ∈ Q := fun _ hv => he hv
          simp only [if_pos he, if_pos hmem, Nat.cast_one, mul_one]
        · have hmem : ¬ (∀ v ∈ e.toFinset, v ∈ Q) := fun h => he (fun _ hv => h _ hv)
          simp only [if_neg he, if_neg hmem, Nat.cast_zero, mul_zero]
      _ = ∑ e ∈ F, ∑ Q : Finset V, (if e.toFinset ⊆ Q then w Q else 0) := sum_comm
      _ = ∑ _e ∈ F, (1 : ℝ) := sum_congr rfl (fun e he => hcover e (hF he))
      _ = F.card := by simp
  have hc := hsum (coreEdges G C) (coreEdges_subset G C)
  have hx := hsum (crossEdges G C) (crossEdges_subset G C)
  have hle : ∑ Q : Finset V,
      w Q * ((insideFilter (crossEdges G C) Q).card : ℝ) ≤
        ∑ Q : Finset V, (w Q + w Q * ((insideFilter (coreEdges G C) Q).card : ℝ)) := by
    apply sum_le_sum
    intro Q _
    by_cases hw : w Q = 0
    · simp [hw]
    have hcl := hsupport Q hw
    have hsmall : extSize C Q ≤ 1 := by
      unfold extSize
      rw [card_le_one]
      intro a ha b hb
      by_contra hne
      exact hI a (mem_sdiff.mp ha).2 b (mem_sdiff.mp hb).2
        (hcl (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 hne)
    rw [card_insideFilter_core G C Q hcl, card_insideFilter_cross G C Q hcl]
    have hprice : ((coreSize C Q * extSize C Q : ℕ) : ℝ) ≤
        1 + ((coreSize C Q).choose 2 : ℝ) := by
      have hc₁ := PaperVI.two_mul_choose_two (coreSize C Q)
      have hbin : (coreSize C Q : ℤ) ≤ 1 + ((coreSize C Q).choose 2 : ℤ) := by
        have hprod := PaperVI.int_mul_pred_nonneg ((coreSize C Q : ℤ) - 1)
        nlinarith
      have hm : coreSize C Q * extSize C Q ≤ coreSize C Q :=
        by simpa using Nat.mul_le_mul_left (coreSize C Q) hsmall
      exact_mod_cast (show (coreSize C Q * extSize C Q : ℕ) ≤
        1 + (coreSize C Q).choose 2 by exact hm.trans (by exact_mod_cast hbin))
    calc
      w Q * ((coreSize C Q * extSize C Q : ℕ) : ℝ) ≤
          w Q * (1 + ((coreSize C Q).choose 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hprice (hnonneg Q)
      _ = _ := by ring
  rw [sum_add_distrib, hx, hc] at hle
  exact sub_le_iff_le_add.mpr hle

end QuadraticExteriorPalomar
