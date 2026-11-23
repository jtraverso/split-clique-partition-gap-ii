module

public import QuadraticExteriorPalomar.Recovery

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Literal completion, including integrality when the input has integer weights. -/
theorem weighted_partial_completion (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (R : Finset (Finset V)) (hs : R ⊆ jPairs B univ)
    (host : R → H) (hm : ∀ e : R, e.val ⊆ N (host e))
    (hp : ∀ a b : R, host a = host b → ∀ v ∈ a.val, v ∈ b.val → a = b)
    (y : Finset V → ℝ) (hy : ResPack y) :
    ∃ x, (hostGraph N).IsFracCliquePartition x ∧
      ((∀ Q, ∃ z : ℤ, (z : ℝ) = y Q) → ∀ Q, ∃ z : ℤ, (z : ℝ) = x Q) ∧
      ∑ Q ∈ (hostGraph N).cliqueSets, x Q =
        E2 (hostGraph N) - ((∑ Q, y Q * w B Q) + 2 * ((jPairs B univ).card : ℝ)) +
          2 * ∑ e ∈ jPairs B univ \ R, (1 - resLoad y e) := by
  classical
  let S := {Q : Finset V // 2 ≤ Q.card}
  let block : S ⊕ R → Finset (V ⊕ H) := Sum.elim
    (fun Q => Q.val.disjSum ∅) (fun e => e.val.disjSum {host e})
  let wt : S ⊕ R → ℝ := Sum.elim (fun Q => y Q.val) (fun e => 1 - resLoad y e.val)
  have two (e : R) : e.val.card = 2 := two_of_mem_jPairs (hs e.2)
  have valid : ∀ k, IsClq (hostGraph N) (block k) := by
    rintro (Q | e)
    · refine ⟨by simpa [block,card_disjSum] using Q.2, ?_⟩
      intro a ha b hb hn
      cases a <;> cases b <;> simp_all [block]
    · refine ⟨by simp [block,card_disjSum,two], ?_⟩
      intro a ha b hb hn
      cases a <;> cases b <;> simp_all [block] <;> first | exact hm _ e.2 ha | exact hm _ e.2 hb
  have res_le (p : Finset V) (hc : p.card = 2) : resLoad y p ≤ 1 := by
    obtain ⟨a,b,hn,rfl⟩ := card_eq_two.mp hc
    rw [resLoad_pair]; exact hy.load a b hn
  have pos : ∀ k, 0 ≤ wt k := by
    rintro (Q | e)
    · exact hy.nonneg _
    · exact sub_nonneg.mpr (res_le _ (two e))
  have cross (a : V) (h : H) :
      loadQ wt block {Sum.inl a, Sum.inr h} ≤ 1 := by
    unfold loadQ
    rw [Fintype.sum_sum_type]
    simp only [block, wt, Sum.elim_inl, Sum.elim_inr, insert_subset_iff, singleton_subset_iff,
      inl_mem_disjSum, inr_mem_disjSum, notMem_empty, and_false, if_false, sum_const_zero,
      zero_add, mem_singleton]
    by_cases hex : ∃ e : R, a ∈ e.val ∧ h = host e
    · obtain ⟨e,ha,he⟩ := hex
      rw [sum_eq_single e, if_pos ⟨ha,he⟩]
      · linarith [resLoad_nonneg hy e.val]
      · intro f _ hn
        exact if_neg fun hf => hn (hp f e (hf.2.symm.trans he) a hf.1 ha)
      · simp
    · exact le_trans (le_of_eq (sum_eq_zero fun e _ => if_neg (fun he => hex ⟨e,he⟩))) zero_le_one
  have load : ∀ a b, (hostGraph N).Adj a b → loadQ wt block {a,b} ≤ 1 := by
    rintro (a | h) (b | h') hab
    · have hn : a ≠ b := hab
      unfold loadQ
      rw [Fintype.sum_sum_type]
      have h1 : (∑ Q : S, if ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)) ⊆ block (.inl Q)
          then wt (.inl Q) else 0) ≤ resLoad y {a,b} := by
        rw [resLoad_pair]
        calc
          _ = ∑ Q ∈ univ.filter (fun Q : Finset V => 2 ≤ Q.card),
              (if a ∈ Q ∧ b ∈ Q then y Q else 0) := by
            rw [sum_subtype _ (p := fun Q : Finset V => 2 ≤ Q.card) (F := inferInstanceAs (Fintype S))
              (fun Q => by simp) (fun Q => if a ∈ Q ∧ b ∈ Q then y Q else 0)]
            refine sum_congr rfl fun Q _ => ?_
            simp [block,wt,insert_subset_iff]
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun Q _ _ => by split_ifs <;> simp [hy.nonneg]
      have h2 : (∑ e : R, if ({Sum.inl a, Sum.inl b} : Finset (V ⊕ H)) ⊆ block (.inr e)
          then wt (.inr e) else 0) =
          if ({a,b} : Finset V) ∈ R then 1 - resLoad y {a,b} else 0 := by
        rw [← (sum_coe_sort R (fun p => if p = {a,b} then 1 - resLoad y p else 0)).trans
          (sum_ite_eq' _ _ _)]
        apply sum_congr rfl
        intro e _
        apply if_congr _ rfl rfl
        simp only [block,Sum.elim_inr,insert_subset_iff,singleton_subset_iff,inl_mem_disjSum]
        constructor
        · intro ⟨ha,hb⟩
          exact (eq_of_subset_of_card_le (by simpa [insert_subset_iff] using And.intro ha hb)
            (by rw [two e,card_pair hn])).symm
        · intro he
          simp [he]
      rw [h2]
      have := res_le {a,b} (card_pair hn)
      split_ifs <;> linarith
    · exact cross a h'
    · rw [pair_comm]; exact cross b h
    · exact False.elim (hostGraph_inr_inr N h h' hab)
  let x := completion (hostGraph N) wt block
  refine ⟨x,completion_isFrac pos valid load,?_,?_⟩
  · intro hint Q
    let Z := (Int.castRingHom ℝ).range
    have hw (k) : wt k ∈ Z := by
      cases k with
      | inl q => exact hint q.val
      | inr e =>
        apply Z.sub_mem Z.one_mem
        apply Z.sum_mem
        intro q _
        split_ifs
        · exact hint q
        · exact Z.zero_mem
    change x Q ∈ Z
    unfold x completion
    apply Z.add_mem
    · apply Z.sum_mem
      intro k _
      split_ifs <;> first | exact hw k | exact Z.zero_mem
    · split_ifs
      · apply Z.sub_mem Z.one_mem
        apply Z.sum_mem
        intro k _
        split_ifs <;> first | exact hw k | exact Z.zero_mem
      · exact Z.zero_mem
  · unfold x
    rw [completion_sum valid, Fintype.sum_sum_type]
    have ha : (∑ Q : S, wt (.inl Q) * ((((block (.inl Q)).card.choose 2 : ℕ) : ℝ) - 1)) =
        ∑ Q, y Q * ((Q.card.choose 2 : ℝ) - 1) := by
      simp only [wt,block,Sum.elim_inl,card_disjSum,card_empty,add_zero]
      rw [← sum_subtype (univ.filter fun Q : Finset V => 2 ≤ Q.card)
        (p := fun Q : Finset V => 2 ≤ Q.card) (fun Q => by simp)
        (fun Q => y Q * ((Q.card.choose 2 : ℝ) - 1)), sum_filter]
      apply sum_congr rfl
      intro Q _
      split_ifs with h
      · rfl
      · have hz : y Q = 0 := by by_contra hn; exact h (hy.two Q hn)
        simp [hz]
    have hb : (∑ e : R, wt (.inr e) * ((((block (.inr e)).card.choose 2 : ℕ) : ℝ) - 1)) =
        2 * ∑ p ∈ R, (1 - resLoad y p) := by
      rw [← sum_coe_sort R (fun p => 1 - resLoad y p),mul_sum]
      apply sum_congr rfl
      intro e _
      simp only [wt,block,Sum.elim_inr,card_disjSum,card_singleton,two e]
      norm_num
      ring
    rw [ha,hb,partial_savings_identity B y R hs]
    ring


/-- The asymmetric loss bounds on the actual physical gap. Each side uses
the optimizer for the corresponding partition cost. -/
theorem gap_stability_of_residual_loads (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (R : Finset (Finset V)) (hs : R ⊆ jPairs B univ) (host : R → H)
    (hm : ∀ e : R, e.val ⊆ N (host e))
    (hp : ∀ a b : R, host a = host b → ∀ v ∈ a.val, v ∈ b.val → a = b)
    (P : Finset (Finset V)) (hP : IsPack P) (hsize : ∀ Q ∈ P, 2 ≤ Q.card)
    (hbest : ∑ Q ∈ P, w B Q = residualInt B)
    (y : Finset V → ℝ) (hy : ResPack y) (hopt : ∑ Q, y Q * w B Q = residualSup B) :
    let miss := jPairs B univ \ R
    residualSup B - residualInt B - 2 * ∑ e ∈ miss, (1 - resLoad y e) ≤ gap (hostGraph N) ∧
    gap (hostGraph N) ≤ residualSup B - residualInt B +
      2 * ∑ e ∈ miss, (1 - resLoad (fun Q => if Q ∈ P then (1 : ℝ) else 0) e) := by
  classical
  let ind (Q : Finset V) : ℝ := if Q ∈ P then 1 else 0
  have hscore : ∑ Q, ind Q * w B Q = (residualInt B : ℝ) := by
    simp only [ind,ite_mul,one_mul,zero_mul,← sum_filter,filter_mem_eq_inter,univ_inter]
    exact_mod_cast hbest
  obtain ⟨xf,hf,_,cf⟩ := weighted_partial_completion B N R hs host hm hp y hy
  obtain ⟨xi,hi',hint,ci⟩ := weighted_partial_completion B N R hs host hm hp ind
    (indicator_resPack P hP hsize)
  have upperF := SimpleGraph.fracCliquePartitionNumber_le_sum_cliqueSets hf
  have integralQ (Q) : ∃ z : ℤ, (z : ℝ) = ind Q := by
    dsimp [ind]; split_ifs
    · exact ⟨1,by norm_num⟩
    · exact ⟨0,by norm_num⟩
  have upperI := partition_of_integral_weights hi' (hint integralQ)
  rw [← hi'.sum_cliqueSets,ci,hscore] at upperI
  rw [cf,hopt] at upperF
  have il := cp_ge_of_indep hi (residualInt B) (exists_best_pack B).choose_spec.2.2
  have lowerI : (E2 (hostGraph N) : ℝ) - residualInt B - 2 * ((jPairs B univ).card : ℝ) ≤
      (hostGraph N).cliquePartitionNumber := by exact_mod_cast il
  have lowerF := frac_ge_of_residual_upper B N hi (residualSup B)
    (fun y' hy' => le_csSup (score_bdd B) ⟨y',hy',rfl⟩)
  dsimp only
  change _ ≤ (hostGraph N).cliquePartitionNumber - (hostGraph N).fracCliquePartitionNumber ∧
    (hostGraph N).cliquePartitionNumber - (hostGraph N).fracCliquePartitionNumber ≤
      residualSup B - residualInt B + 2 * ∑ e ∈ jPairs B univ \ R, (1 - resLoad ind e)
  constructor <;> linarith

end QuadraticExteriorPalomar
