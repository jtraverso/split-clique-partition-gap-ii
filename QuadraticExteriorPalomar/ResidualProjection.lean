module

public import GapExtremal.Bridge

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

private theorem pair_mass {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph U} {x : Finset U → ℝ} (hx : G.IsFracCliquePartition x)
    {p : Finset U} (hp : IsClq G p) (ht : p.card = 2) :
    (∑ Q, if p ⊆ Q then x Q else 0) = 1 := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp ht
  simpa only [insert_subset_iff, singleton_subset_iff, sum_filter] using hx.edge a b (hp.2 a (by simp) b (by simp) hab)

private theorem mass_count {U K : Type*} [Fintype U] [DecidableEq U] [DecidableEq K]
    (P : Finset K) (x : Finset U → ℝ) (hit : K → Finset U → Prop)
    [DecidableRel hit] (h : ∀ p ∈ P, (∑ Q, if hit p Q then x Q else 0) = 1) :
    (∑ Q, x Q * ((P.filter fun p => hit p Q).card : ℝ)) = P.card := by
  classical
  calc
    _ = ∑ Q, ∑ p ∈ P, if hit p Q then x Q else 0 := by
      apply sum_congr rfl
      intro Q _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    _ = _ := by rw [sum_comm, sum_congr rfl h]; simp

private theorem fractional_edge_count {U : Type*} [Fintype U] [DecidableEq U]
    {G : SimpleGraph U} [DecidableRel G.Adj] {x : Finset U → ℝ}
    (hx : G.IsFracCliquePartition x) :
    (∑ Q, x Q * (Q.card.choose 2 : ℕ)) = E2 G := by
  classical
  let P := G.cliqueSets.filter fun p => p.card = 2
  have hm := mass_count P x (fun p Q => p ⊆ Q) (fun p hp =>
    pair_mass hx ((mem_cliques G).mp (mem_filter.mp hp).1) (mem_filter.mp hp).2)
  change _ = (P.card : ℝ)
  rw [← hm]
  apply sum_congr rfl
  intro Q _
  by_cases h : x Q = 0
  · simp [h]
  have eq : P.filter (· ⊆ Q) = Q.powersetCard 2 := by
    ext p
    simp only [P, mem_filter, mem_powersetCard, mem_cliques]
    exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h' =>
      ⟨⟨isClq_of_sub G (isClq_iff.mpr (hx.support Q h)) h'.1 h'.2,h'.2⟩,h'.1⟩⟩
  rw [eq, card_powersetCard]

private theorem sum_core (f : Finset (V ⊕ H) → ℝ) :
    ∑ S : Finset V, f (S.disjSum ∅) = ∑ Q, if Q.toRight = ∅ then f Q else 0 := by
  classical
  rw [← sum_filter]
  have eq : univ.filter (fun Q : Finset (V ⊕ H) => Q.toRight = ∅) =
      univ.image (fun S : Finset V => S.disjSum (∅ : Finset H)) := by
    ext Q
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      exact ⟨Q.toLeft, h ▸ Q.toLeft_disjSum_toRight⟩
    · rintro ⟨S,rfl⟩
      simp only [toRight_disjSum]
  rw [eq, sum_image]
  intro S _ T _ he
  simpa only [toLeft_disjSum] using congrArg Finset.toLeft he

/-- Restrict a physical fractional partition to its pure core pieces. -/
theorem pure_core_resPack {N : H → Finset V} {x : Finset (V ⊕ H) → ℝ}
    (hx : (hostGraph N).IsFracCliquePartition x) :
    ResPack (fun S : Finset V => x (S.disjSum ∅)) := by
  classical
  refine ⟨fun _ => hx.nonneg _, fun S hs => ?_, ?_⟩
  · simpa using (hx.support _ hs).1
  · intro a b hab
    let f (Q : Finset (V ⊕ H)) := if Sum.inl a ∈ Q ∧ Sum.inl b ∈ Q then x Q else 0
    have he := hx.edge (.inl a) (.inl b) ((hostGraph_inl_inl N a b).2 hab)
    rw [sum_filter] at he
    calc
      _ = ∑ S : Finset V, f (S.disjSum ∅) := by simp [f]
      _ ≤ ∑ Q, f Q := by
        rw [sum_core]
        apply sum_le_sum
        intro Q _
        split_ifs
        · exact le_rfl
        · dsimp [f]
          split_ifs <;> first | exact hx.nonneg _ | exact le_rfl
      _ = _ := he

private theorem block_gain {B : SimpleGraph V} [DecidableRel B.Adj]
    {N : H → Finset V} (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    {Q : Finset (V ⊕ H)} (hQ : IsClq (hostGraph N) Q) :
    ((Q.card.choose 2 : ℕ) : ℤ) - 1 ≤
      (if Q.toRight = ∅ then w B Q.toLeft else 0) + 2 * (jPairs B Q.toLeft).card := by
  have hs := Q.card_toLeft_add_card_toRight
  by_cases h : Q.toRight = ∅
  · rw [h, card_empty, add_zero] at hs
    rw [ite_eq_left h, w_add_two_j, hs]
  · rw [ite_eq_right h, zero_add]
    obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.mpr h
    have hu1 := le_antisymm (card_toRight_le hQ) (card_pos.mpr ⟨u,hu⟩)
    have pal (v) (hv : v ∈ Q.toLeft) : v ∈ N u :=
      hQ.2 _ (mem_toLeft.mp hv) _ (mem_toRight.mp hu) (by simp)
    have hz : (adjPairs B Q.toLeft).card = 0 := by
      rw [card_eq_zero, adjPairs, filter_eq_empty_iff]
      rintro p hp ⟨a, ha, b, hb, hab⟩
      have sub := (mem_powersetCard.mp hp).1
      exact hi u a (pal a (sub ha)) b (pal b (sub hb)) hab
    have hj := card_adj_add_j B Q.toLeft
    rw [hz, zero_add] at hj
    rw [hu1] at hs
    rw [← hs, hj]
    have h1 := two_mul_choose_two_int (Q.toLeft.card + 1)
    have h2 := two_mul_choose_two_int Q.toLeft.card
    push_cast at h1 ⊢
    nlinarith [sq_nonneg ((Q.toLeft.card : ℤ) - 1), sq_nonneg ((Q.toLeft.card : ℤ) - 2)]

/-- The reverse inequality for the fractional optimum in Paper I's transfer.
Only palette independence is needed in this direction. -/
theorem frac_ge_of_residual_upper (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (F : ℝ) (hF : ∀ y : Finset V → ℝ, ResPack y → ∑ S, y S * w B S ≤ F) :
    (E2 (hostGraph N) : ℝ) - (F + 2 * (jPairs B univ).card) ≤
      (hostGraph N).fracCliquePartitionNumber := by
  classical
  apply SimpleGraph.le_fracCliquePartitionNumber
  intro x hx
  have hm := mass_count (jPairs B univ) x (fun p Q => p ⊆ Q.toLeft) (by
    intro p hp
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp (two_of_mem_jPairs hp)
    simpa only [insert_subset_iff, singleton_subset_iff, mem_toLeft, sum_filter] using
      hx.edge (.inl a) (.inl b) ((hostGraph_inl_inl N a b).2 hab))
  simp_rw [← jPairs_eq_filter] at hm
  let g (Q : Finset (V ⊕ H)) := x Q * (w B Q.toLeft : ℝ)
  have hc := hF _ (pure_core_resPack hx)
  have hpure := sum_core g
  simp only [g, toLeft_disjSum] at hpure
  rw [hpure] at hc
  have point (Q : Finset (V ⊕ H)) :
      x Q * ((Q.card.choose 2 : ℕ) : ℝ) - x Q ≤
      (if Q.toRight = ∅ then x Q * (w B Q.toLeft : ℝ) else 0) +
        2 * (x Q * ((jPairs B Q.toLeft).card : ℝ)) := by
    by_cases hn : x Q = 0
    · simp [hn]
    have hh := block_gain hi (isClq_iff.mpr (hx.support Q hn))
    by_cases hr : Q.toRight = ∅
    · rw [ite_eq_left hr] at hh ⊢
      have hh' : ((Q.card.choose 2 : ℕ) : ℝ) - 1 ≤
          (w B Q.toLeft : ℝ) + 2 * (jPairs B Q.toLeft).card := by exact_mod_cast hh
      linarith only [mul_le_mul_of_nonneg_left hh' (hx.nonneg Q)]
    · rw [ite_eq_right hr, zero_add] at hh ⊢
      have hh' : ((Q.card.choose 2 : ℕ) : ℝ) - 1 ≤
          2 * (jPairs B Q.toLeft).card := by exact_mod_cast hh
      linarith only [mul_le_mul_of_nonneg_left hh' (hx.nonneg Q)]
  have h := sum_le_sum (fun Q (_ : Q ∈ univ) => point Q)
  rw [sum_sub_distrib, fractional_edge_count hx, sum_add_distrib, ← mul_sum, hm] at h
  linarith

/-- The value of the fractional residual problem with unit pair capacities. -/
noncomputable def residualSup (B : SimpleGraph V) [DecidableRel B.Adj] : ℝ :=
  sSup {s : ℝ | ∃ y : Finset V → ℝ, ResPack y ∧ ∑ Q, y Q * w B Q = s}

/-- Exact fractional optimum, without assuming an optimizer as input. -/
theorem frac_eq_residualSup {B : SimpleGraph V} [DecidableRel B.Adj]
    {N : H → Finset V} {φ : V → V → H} (hh : HostHyp B N φ) :
    (hostGraph N).fracCliquePartitionNumber =
      (E2 (hostGraph N) : ℝ) - (residualSup B + 2 * (jPairs B univ).card) := by
  classical
  let A := {s : ℝ | ∃ y : Finset V → ℝ, ResPack y ∧ ∑ Q, y Q * w B Q = s}
  have hz : ResPack (fun _ : Finset V => (0 : ℝ)) := by constructor <;> simp
  have ha : A.Nonempty := ⟨_, _, hz, rfl⟩
  let K : ℝ := E2 (hostGraph N) - 2 * (jPairs B univ).card -
    (hostGraph N).fracCliquePartitionNumber
  have ub : ∀ s ∈ A, s ≤ K := by
    rintro _ ⟨y,hy,rfl⟩
    dsimp [K]
    linarith [cpStar_le hh hy]
  have hsup : residualSup B ≤ K := csSup_le ha ub
  apply le_antisymm
  · dsimp [K] at hsup
    linarith
  · apply frac_ge_of_residual_upper B N hh.indep
    intro y hy
    exact le_csSup (show BddAbove A from ⟨K,ub⟩) ⟨y,hy,rfl⟩

end QuadraticExteriorPalomar
