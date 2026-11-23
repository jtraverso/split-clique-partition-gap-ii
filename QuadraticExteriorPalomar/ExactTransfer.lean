module

public import QuadraticExteriorPalomar.IsolatedLabels
public import QuadraticExteriorPalomar.ResidualProjection
public import QuadraticExteriorPalomar.MarkedLists
public import QuadraticExteriorPalomar.CrossDeletions

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

theorem exists_best_pack (B : SimpleGraph V) [DecidableRel B.Adj] :
    ∃ P : Finset (Finset V), IsPack P ∧ (∀ Q ∈ P, 2 ≤ Q.card) ∧
      ∀ T : Finset (Finset V), IsPack T → ∑ Q ∈ T, w B Q ≤ ∑ Q ∈ P, w B Q := by
  classical
  let A := univ.filter fun P : Finset (Finset V) => IsPack P ∧ ∀ Q ∈ P, 2 ≤ Q.card
  have he : ∅ ∈ A := mem_filter.mpr ⟨mem_univ _, by simp [IsPack]⟩
  obtain ⟨P,hp,hm⟩ := exists_max_image A (fun P => ∑ Q ∈ P, w B Q) ⟨_,he⟩
  refine ⟨P,(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2,?_⟩
  intro T ht
  let S := T.filter fun Q => 2 ≤ Q.card
  have hs : S ∈ A := mem_filter.mpr ⟨mem_univ _, fun Q h R h' =>
    ht Q (mem_filter.mp h).1 R (mem_filter.mp h').1, fun _ h => (mem_filter.mp h).2⟩
  apply le_trans _ (hm S hs)
  rw [show S = T.filter (fun Q => 2 ≤ Q.card) from rfl, sum_filter]
  apply sum_le_sum
  intro Q _
  split_ifs with h
  · exact le_rfl
  · have hw := w_add_two_j B Q
    rw [Nat.choose_eq_zero_of_lt (by omega : Q.card < 2)] at hw
    omega

/-- The maximum integral residual score. The empty packing is feasible. -/
noncomputable def residualInt (B : SimpleGraph V) [DecidableRel B.Adj] : ℤ :=
  ∑ Q ∈ (exists_best_pack B).choose, w B Q

/-- Exact transfer in the unrestricted GraphBase model of Paper I. -/
theorem gap_eq_residual_difference {B : SimpleGraph V} [DecidableRel B.Adj]
    {N : H → Finset V} {φ : V → V → H} (hh : HostHyp B N φ) :
    gap (hostGraph N) = residualSup B - residualInt B := by
  obtain ⟨hp,hs,hm⟩ := (exists_best_pack B).choose_spec
  have hu := cp_le_of_residual_pack hh _ hp hs
  change _ ≤ (E2 (hostGraph N) : ℝ) - ((residualInt B : ℝ) + _) at hu
  have hl := cp_ge hh (residualInt B) hm
  have hl' : (E2 (hostGraph N) : ℝ) - residualInt B - 2 * (jPairs B univ).card ≤
      (hostGraph N).cliquePartitionNumber := by exact_mod_cast hl
  unfold gap
  rw [frac_eq_residualSup hh]
  linarith

/-- Two-sided stability on the original split graph. -/
theorem gap_stability_of_partial_assignment
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (J₀ : Finset (Finset V)) (hsub : J₀ ⊆ jPairs B univ) (host : J₀ → H)
    (hmem : ∀ p : J₀, p.val ⊆ N (host p))
    (hmatch : ∀ p q : J₀, host p = host q → ∀ a ∈ p.val, a ∈ q.val → p = q) :
    |gap (hostGraph N) -
      (residualSup B - residualInt B)| ≤ 2 * (((jPairs B univ).card - J₀.card : ℕ) : ℝ) := by
  obtain ⟨_,_,hh,h⟩ := complete_partial_assignment B N hi J₀ hsub host hmem hmatch
  rw [gap_eq_residual_difference hh, gap_empty_host_labels, abs_sub_comm] at h
  exact h

/-- The two-sided error depends only on matching bounds on marked pairs. -/
theorem gap_stability_of_marked_lists
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (cap : ℕ → ℕ) (hcap : ∀ t < Fintype.card V, ∀ F : Finset (⊤ : SimpleGraph V).edgeSet,
      F ⊆ markedEdges B → (∀ e ∈ F, t < Fintype.card V - (markedHostList N e).card) →
      BasesMatching F → F.card ≤ cap t) :
    |gap (hostGraph N) -
      (residualSup B - residualInt B)| ≤ 2 * ((∑ t ∈ range (Fintype.card V), cap t : ℕ) : ℝ) := by
  obtain ⟨J,hj,host,hm,hp,hl⟩ := marked_assignment_of_deficit_bounds B N cap hcap
  exact (gap_stability_of_partial_assignment B N hi J hj host hm hp).trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) (by norm_num))

/-- Both physical gaps are measured on the same original vertex type. -/
theorem gap_stability_after_cross_deletions
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (host : Finset V → H) (hmem : ∀ p ∈ jPairs B univ, p ⊆ N (host p))
    (hmatch : ∀ p ∈ jPairs B univ, ∀ q ∈ jPairs B univ,
      host p = host q → ∀ a ∈ p, a ∈ q → p = q) (del : Finset (H × V)) :
    |gap (hostGraph (fun h => (N h).filter fun a => (h,a) ∉ del)) - gap (hostGraph N)| ≤
      2 * (del.card : ℝ) := by
  have hfull := gap_stability_of_partial_assignment B N hi (jPairs B univ) (Subset.rfl)
    (fun p => host p.val) (fun p => hmem _ p.property)
    (fun p q he a hp hq => Subtype.ext (hmatch _ p.property _ q.property he a hp hq))
  simp only [Nat.sub_self, Nat.cast_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hfull
  rw [hfull]
  obtain ⟨R,hsub,f,hf,hm,hl⟩ := retained_after_cross_deletions B N host hmem hmatch del
  exact (gap_stability_of_partial_assignment B (fun h => (N h).filter fun a => (h,a) ∉ del)
    (fun h a ha b hb => hi h a (mem_filter.mp ha).1 b (mem_filter.mp hb).1)
    R hsub f hf hm).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) (by norm_num))

end QuadraticExteriorPalomar
