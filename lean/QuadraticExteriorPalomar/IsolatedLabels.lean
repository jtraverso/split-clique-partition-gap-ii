module

public import QuadraticExteriorPalomar.IntegralRealization

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {U W : Type*} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

/-- Transport both costs by summing coefficients on equal images. -/
private theorem transport_costs (G : SimpleGraph U) (K : SimpleGraph W)
    (f : Finset U → Finset W) (cl : ∀ Q, IsClq G Q → IsClq K (f Q))
    (ed : ∀ a b, K.Adj a b → ∃ u v, G.Adj u v ∧ ∀ Q, IsClq G Q →
      (a ∈ f Q ∧ b ∈ f Q ↔ u ∈ Q ∧ v ∈ Q)) :
    K.cliquePartitionNumber ≤ G.cliquePartitionNumber ∧
      K.fracCliquePartitionNumber ≤ G.fracCliquePartitionNumber := by
  classical
  let push (x : Finset U → ℝ) (R : Finset W) := ∑ Q, if f Q = R then x Q else 0
  have sum_push (x) (A : Finset (Finset W)) :
      ∑ R ∈ A, push x R = ∑ Q, if f Q ∈ A then x Q else 0 := by
    unfold push
    rw [sum_comm]
    simp
  have cost (x) : ∑ R, push x R = ∑ Q, x Q := by simpa using sum_push x univ
  have feasible {x} (hx : G.IsFracCliquePartition x) : K.IsFracCliquePartition (push x) := by
    constructor
    · intro R
      apply sum_nonneg
      intro Q _
      split_ifs <;> first | exact hx.nonneg _ | exact le_rfl
    · intro R hn
      by_contra h
      apply hn
      apply sum_eq_zero
      intro Q _
      by_cases hf : f Q = R
      · rw [ite_eq_left hf]
        by_contra hq
        exact h (hf ▸ isClq_iff.mp (cl Q (isClq_iff.mpr (hx.support Q hq))))
      · exact ite_eq_right hf
    · intro a b hab
      obtain ⟨u,v,huv,he⟩ := ed a b hab
      rw [sum_push, ← hx.edge u v huv, sum_filter]
      apply sum_congr rfl
      intro Q _
      by_cases hn : x Q = 0
      · simp [hn]
      · simp only [mem_filter, mem_univ, true_and, he Q (isClq_iff.mpr (hx.support Q hn))]
  constructor
  · obtain ⟨P,hP,hcard⟩ := SimpleGraph.exists_isCliquePartition_card_eq G
    let x (Q : Finset U) : ℝ := if Q ∈ P then 1 else 0
    have hx : G.IsFracCliquePartition x := hP.isFracCliquePartition
    have hz (R) : ∃ z : ℤ, (z : ℝ) = push x R := by
      refine ⟨∑ Q : Finset U, if f Q = R ∧ Q ∈ P then (1 : ℤ) else 0, ?_⟩
      push_cast
      apply sum_congr rfl
      intro Q _
      by_cases h : f Q = R <;> simp [h,x]
    have h := partition_of_integral_weights (feasible hx) hz
    rw [cost] at h
    simpa [x, ← hcard] using h
  · apply SimpleGraph.le_fracCliquePartitionNumber
    intro x hx
    exact (SimpleGraph.fracCliquePartitionNumber_le (feasible hx)).trans_eq (cost x)

/-- Adding any number of isolated vertices preserves the gap, also when
the original vertex type is empty. -/
theorem gap_eq_of_embedding_with_isolates (G : SimpleGraph U) (K : SimpleGraph W)
    (i : U ↪ W) (he : ∀ u v, K.Adj (i u) (i v) ↔ G.Adj u v)
    (hr : ∀ a b, K.Adj a b → a ∈ Set.range i) : gap K = gap G := by
  classical
  let lift (S : Finset U) := S.map i
  let pull (Q : Finset W) := Q.preimage i i.injective.injOn
  have live (Q : Finset W) (hq : IsClq K Q) : lift (pull Q) = Q := by
    ext a
    constructor
    · intro hm
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hm
      exact mem_preimage.mp hu
    · intro ha
      have hn : ∃ b ∈ Q, b ≠ a := by
        obtain ⟨b,hb,d,hd,hbd⟩ := one_lt_card.mp hq.1
        by_cases h : b = a
        · exact ⟨d,hd,h ▸ hbd.symm⟩
        · exact ⟨b,hb,h⟩
      obtain ⟨b,hb,hba⟩ := hn
      obtain ⟨u,rfl⟩ := hr a b (hq.2 a ha b hb hba.symm)
      exact mem_map.mpr ⟨u,mem_preimage.mpr ha,rfl⟩
  have h1 := transport_costs G K lift (by
    intro Q hq
    refine ⟨by simpa [lift] using hq.1, ?_⟩
    intro a ha b hb hab
    obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
    exact (he u v).2 (hq.2 u hu v hv (fun h => hab (congrArg i h)))) (by
    intro a b hab
    obtain ⟨u,rfl⟩ := hr a b hab
    obtain ⟨v,rfl⟩ := hr b _ hab.symm
    exact ⟨u,v,(he u v).1 hab,fun Q _ => by simp [lift]⟩)
  have h2 := transport_costs K G pull (by
    intro Q hq
    have hcard := congrArg Finset.card (live Q hq)
    simp only [lift, card_map] at hcard
    refine ⟨hcard ▸ hq.1, ?_⟩
    intro u hu v hv huv
    exact (he u v).1 (hq.2 _ (mem_preimage.mp hu) _ (mem_preimage.mp hv)
      (fun h => huv (i.injective h)))) (by
    intro u v huv
    exact ⟨i u,i v,(he u v).2 huv,fun Q _ => by simp [pull]⟩)
  unfold gap
  rw [le_antisymm h1.1 h2.1, le_antisymm h1.2 h2.2]

/-- The padded presentation used for completing a partial assignment has the
same gap as the physical split graph on the original vertex type. -/
theorem gap_empty_host_labels {V H A : Type*} [Fintype V] [DecidableEq V]
    [Fintype H] [DecidableEq H] [Fintype A] [DecidableEq A] (N : H → Finset V) :
    gap (hostGraph (Sum.elim N (fun _ : A => ∅))) = gap (hostGraph N) := by
  classical
  let i : V ⊕ H ↪ V ⊕ (H ⊕ A) :=
    Function.Embedding.sumMap (Function.Embedding.refl V) Function.Embedding.inl
  apply gap_eq_of_embedding_with_isolates _ _ i
  · rintro (u|u) (v|v) <;> rfl
  · rintro (u | (h | a)) b hab
    · exact ⟨Sum.inl u,rfl⟩
    · exact ⟨Sum.inr h,rfl⟩
    · cases b <;> simp [hostGraph] at hab

end QuadraticExteriorPalomar
