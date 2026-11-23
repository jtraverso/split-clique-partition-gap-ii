module

public import QuadraticExteriorPalomar.HostTransfer

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Complete a partial matching assignment with one two-port host per missing
pair. The common ambient type has isolated labels for unused auxiliary hosts. -/
theorem complete_partial_assignment
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (J₀ : Finset (Finset V)) (hsub : J₀ ⊆ jPairs B univ) (host : J₀ → H)
    (hmem : ∀ p : J₀, p.val ⊆ N (host p))
    (hmatch : ∀ p q : J₀, host p = host q → ∀ a ∈ p.val, a ∈ q.val → p = q) :
    ∃ (N' : H ⊕ Finset V → Finset V) (φ : V → V → H ⊕ Finset V),
      HostHyp B N' φ ∧
      |gap (hostGraph N') - gap (hostGraph (Sum.elim N (fun _ : Finset V => ∅)))| ≤
        2 * ((((jPairs B univ).card - J₀.card : ℕ)) : ℝ) := by
  classical
  let M := jPairs B univ \ J₀
  let N' : H ⊕ Finset V → Finset V := Sum.elim N (fun p => if p ∈ M then p else ∅)
  let color (p : Finset V) : H ⊕ Finset V :=
    if hp : p ∈ J₀ then Sum.inl (host ⟨p, hp⟩) else Sum.inr p
  let φ (a b : V) := color {a,b}
  have marked {a b : V} (hab : a ≠ b) (hn : ¬ B.Adj a b) : {a,b} ∈ jPairs B univ := by
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨subset_univ _, card_pair hab⟩, ?_⟩
    rintro ⟨x, hx, y, hy, hxy⟩
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy.ne rfl
    · exact hn hxy
    · exact hn hxy.symm
    · exact hxy.ne rfl
  have hH : HostHyp B N' φ := by
    constructor
    · intro h
      cases h with
      | inl x => exact hi x
      | inr p =>
        by_cases hp : p ∈ M
        · simpa [N', hp] using nonadj_of_mem_jPairs (mem_sdiff.mp hp).1
        · simp [N', hp]
    · intro a b hab hn
      by_cases hp : {a,b} ∈ J₀
      · simpa [φ, color, hp, N'] using
          And.intro (hmem ⟨{a,b},hp⟩ (by simp : a ∈ ({a,b} : Finset V)))
            (hmem ⟨{a,b},hp⟩ (by simp : b ∈ ({a,b} : Finset V)))
      · have hm : {a,b} ∈ M := mem_sdiff.mpr ⟨marked hab hn, hp⟩
        simp [φ, color, hp, N', hm]
    · intro a b
      exact congrArg color (pair_comm a b)
    · intro a b d hab _ had _ heq
      have pairEq : ({a,b} : Finset V) = {a,d} := by
        by_cases hp : {a,b} ∈ J₀ <;> by_cases hq : {a,d} ∈ J₀ <;>
          simp [φ, color, hp, hq] at heq
        · exact congrArg Subtype.val (hmatch ⟨_,hp⟩ ⟨_,hq⟩ heq a (by simp) (by simp))
        · exact heq
      have hb : b ∈ ({a,d} : Finset V) := pairEq ▸ (by simp : b ∈ ({a,b} : Finset V))
      exact (mem_insert.mp hb).resolve_left hab.symm |> mem_singleton.mp
  let K : Finset (H ⊕ Finset V) := M.image Sum.inr
  have heq : dropPalettes N' K = Sum.elim N (fun _ : Finset V => ∅) := by
    funext h
    cases h with
    | inl x => simp [dropPalettes, N', K]
    | inr p => by_cases hp : p ∈ M <;> simp [dropPalettes, N', K, hp]
  have hs : ∑ h ∈ K, (N' h).card = 2 * M.card := by
    rw [show K = M.image Sum.inr from rfl, sum_image (fun _ _ _ _ heq => Sum.inr.inj heq)]
    calc
      _ = ∑ _p ∈ M, 2 := sum_congr rfl fun p hp => by
        simpa [N', hp] using two_of_mem_jPairs (mem_sdiff.mp hp).1
      _ = _ := by simp [Nat.mul_comm]
  refine ⟨N', φ, hH, ?_⟩
  simpa only [heq, hs, M, card_sdiff_of_subset hsub, Nat.cast_mul, Nat.cast_ofNat]
    using gap_change_of_dropped_hosts N' K

/-- Paper I's lower-bound route with a partial assignment on J₀. The extra
labels on the target have empty neighbourhoods. -/
theorem gap_ge_of_partial_assignment
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (J₀ : Finset (Finset V)) (hsub : J₀ ⊆ jPairs B univ) (host : J₀ → H)
    (hmem : ∀ p : J₀, p.val ⊆ N (host p))
    (hmatch : ∀ p q : J₀, host p = host q → ∀ a ∈ p.val, a ∈ q.val → p = q)
    (I : ℤ) (hI : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) :
    (∑ Q, y Q * w B Q) - I - 2 * ((((jPairs B univ).card - J₀.card : ℕ)) : ℝ) ≤
      gap (hostGraph (Sum.elim N (fun _ : Finset V => ∅))) := by
  obtain ⟨_, _, hh, hb⟩ := complete_partial_assignment B N hi J₀ hsub host hmem hmatch
  linarith [(abs_le.mp hb).2, gap_ge hh I hI hy]

end QuadraticExteriorPalomar
