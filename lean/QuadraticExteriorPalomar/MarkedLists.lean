module

public import QuadraticExteriorPalomar.SplitRealizer
public import QuadraticExteriorPalomar.PartialAssignment

@[expose] public section

namespace QuadraticExteriorPalomar

open Finset GapExtremal
open scoped BigOperators

variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The requested edges in the coordinate system of the list selector. -/
def markedEdges (B : SimpleGraph V) [DecidableRel B.Adj] :
    Finset (⊤ : SimpleGraph V).edgeSet :=
  univ.filter fun e => e.val.toFinset ∈ jPairs B univ

/-- A host is eligible precisely when its actual palette contains both ports. -/
def markedHostList (N : H → Finset V) (e : (⊤ : SimpleGraph V).edgeSet) : Finset H :=
  univ.filter fun h => e.val.toFinset ⊆ N h

private theorem pair_injective :
    Function.Injective (fun e : (⊤ : SimpleGraph V).edgeSet => e.val.toFinset) := by
  intro e f he
  change e.val.toFinset = f.val.toFinset at he
  apply Subtype.ext
  apply Sym2.ext
  intro x
  simpa only [Sym2.mem_toFinset] using (show x ∈ e.val.toFinset ↔ x ∈ f.val.toFinset by rw [he])

private theorem image_marked (B : SimpleGraph V) [DecidableRel B.Adj] :
    (markedEdges B).image (fun e => e.val.toFinset) = jPairs B univ := by
  ext p
  constructor
  · rintro hp
    obtain ⟨e, he, rfl⟩ := mem_image.mp hp
    exact (mem_filter.mp he).2
  · intro hp
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (two_of_mem_jPairs hp)
    let e : (⊤ : SimpleGraph V).edgeSet := ⟨s(a,b), by simpa using hab⟩
    have he : e.val.toFinset = {a,b} := Sym2.toFinset_mk_eq
    exact mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, he ▸ hp⟩, he⟩

/-- The selector on unordered edges supplies exactly the partial assignment
required by the score transfer on two-element sets, with the same loss. -/
theorem marked_assignment_of_deficit_bounds
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V) (cap : ℕ → ℕ)
    (hcap : ∀ t < Fintype.card V, ∀ F : Finset (⊤ : SimpleGraph V).edgeSet,
      F ⊆ markedEdges B → (∀ e ∈ F, t < Fintype.card V - (markedHostList N e).card) →
      BasesMatching F → F.card ≤ cap t) :
    ∃ J₀ ⊆ jPairs B univ, ∃ host : J₀ → H,
      (∀ p : J₀, p.val ⊆ N (host p)) ∧
      (∀ p q : J₀, host p = host q → ∀ a ∈ p.val, a ∈ q.val → p = q) ∧
      (jPairs B univ).card - J₀.card ≤ ∑ t ∈ range (Fintype.card V), cap t := by
  classical
  obtain ⟨S, hS, color, proper, _, hsize⟩ :=
    residual_host_realizer_of_deficit_bounds (markedEdges B) (markedHostList N) cap hcap
  let J₀ := S.image fun e => e.val.toFinset
  have repr (p : J₀) : ∃ e : S, e.val.val.toFinset = p.val := by
    obtain ⟨e, he, hp⟩ := mem_image.mp p.property
    exact ⟨⟨e,he⟩, hp⟩
  choose edge hedge using repr
  refine ⟨J₀, ?_, fun p => color (edge p), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨e, he, rfl⟩ := mem_image.mp hp
    exact (mem_filter.mp (hS he)).2
  · intro p
    rw [← hedge p]
    exact (mem_filter.mp (proper.1 (edge p) (mem_univ _))).2
  · intro p q heq a hp hq
    by_contra hn
    have hne : edge p ≠ edge q := fun h => hn (Subtype.ext (by rw [← hedge p, h, hedge q]))
    apply proper.2 (edge p) (mem_univ _) (edge q) (mem_univ _) hne _ heq
    exact not_disjoint_iff.mpr ⟨a, (hedge p).symm ▸ hp, (hedge q).symm ▸ hq⟩
  · rw [← image_marked B, card_image_of_injective _ pair_injective]
    change _ - (S.image _).card ≤ _
    rw [card_image_of_injective _ pair_injective]
    omega

/-- A lower bound for the physical gap from residual scores and the sizes
of matchings in deficient lists. Isolated auxiliary labels carry no edges. -/
theorem gap_ge_of_marked_list_bounds
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (cap : ℕ → ℕ) (hcap : ∀ t < Fintype.card V, ∀ F : Finset (⊤ : SimpleGraph V).edgeSet,
      F ⊆ markedEdges B → (∀ e ∈ F, t < Fintype.card V - (markedHostList N e).card) →
      BasesMatching F → F.card ≤ cap t)
    (I : ℤ) (hI : ∀ P : Finset (Finset V), IsPack P → ∑ Q ∈ P, w B Q ≤ I)
    {y : Finset V → ℝ} (hy : ResPack y) :
    (∑ Q, y Q * w B Q) - I - 2 * ((∑ t ∈ range (Fintype.card V), cap t : ℕ) : ℝ) ≤
      gap (hostGraph (Sum.elim N (fun _ : Finset V => ∅))) := by
  obtain ⟨J₀, hsub, host, hm, hp, hl⟩ := marked_assignment_of_deficit_bounds B N cap hcap
  exact le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hl) (by norm_num)) _)
    (gap_ge_of_partial_assignment B N hi J₀ hsub host hm hp I hI hy)

end QuadraticExteriorPalomar
