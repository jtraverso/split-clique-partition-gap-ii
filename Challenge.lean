module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Nat.Choose.Basic

/-! # Stability of the clique partition gap in split graphs

The partition costs below count cliques of arbitrary order, with unit load on every edge.
A required pair is a nonedge of the residual graph on the clique core.
The compared statements concern partial host assignments, crossing deletions from a full
assignment, and the endpoint omission bound for a general split presentation. -/

@[expose] public section
open Finset
open scoped BigOperators

namespace SimpleGraph
variable {V : Type*}
/-- A clique partition of `G`: cliques of order at least two such that every edge of `G` lies in exactly one of
them. -/
structure IsCliquePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop where
  two_le : ∀ B ∈ P, 2 ≤ B.card
  isClique : ∀ B ∈ P, G.IsClique (B : Set V)
  existsUnique : ∀ u v, G.Adj u v → ∃! B, B ∈ P ∧ u ∈ B ∧ v ∈ B

/-- The clique partition number `cp(G)`: the least size of a clique partition. -/
noncomputable def cliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ P, G.IsCliquePartition P ∧ P.card = k}

variable [Fintype V]


/-- A fractional clique partition: nonnegative weights on vertex sets, supported on cliques of order at least
two, with total weight exactly one on every edge. -/
structure IsFracCliquePartition [DecidableEq V] (G : SimpleGraph V) (x : Finset V → ℝ) : Prop where
  nonneg : ∀ Q, 0 ≤ x Q
  support : ∀ Q, x Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V)
  edge : ∀ u v, G.Adj u v → ∑ Q ∈ univ.filter (fun Q : Finset V => u ∈ Q ∧ v ∈ Q), x Q = 1

/-- The fractional clique partition number `cp*(G)`. -/
noncomputable def fracCliquePartitionNumber [DecidableEq V] (G : SimpleGraph V) : ℝ :=
  sInf {r | ∃ x, G.IsFracCliquePartition x ∧ ∑ Q, x Q = r}
end SimpleGraph

namespace GapExtremal
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The integrality gap `D G = cp G − cp* G`. -/
noncomputable def gap (G : SimpleGraph V) : ℝ :=
  (G.cliquePartitionNumber : ℝ) - G.fracCliquePartitionNumber

/-- Subgrafo de `B` inducido en `S`, visto como grafo sobre el mismo tipo de vértices. -/
def inducedOn (B : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := B.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance inducedOn.instDecidableRel (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) :
    DecidableRel (inducedOn B S).Adj := fun u v =>
  inferInstanceAs (Decidable (B.Adj u v ∧ u ∈ S ∧ v ∈ S))


/-- Número de aristas de `B` con ambos extremos en `S`. -/
def e (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) : ℕ :=
  (inducedOn B S).edgeFinset.card

/-- Peso de una columna: `w B S = 2 * e B S - C(|S|,2) - 1`. -/
def w (B : SimpleGraph V) [DecidableRel B.Adj] (S : Finset V) : ℤ :=
  2 * (e B S : ℤ) - ((S.card).choose 2 : ℤ) - 1

/-- A packing of columns: two distinct members share at most one vertex. -/
def IsPack (T : Finset (Finset V)) : Prop := ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → (Q ∩ Q').card ≤ 1
variable (B : SimpleGraph V) [DecidableRel B.Adj]

/-- Non-adjacent two-element subsets of `S` (the marked pairs `J` inside `S`). -/
def jPairs (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter fun p => ¬ ∃ x ∈ p, ∃ y ∈ p, B.Adj x y


/-- The split graph: core `V` (clique), hosts `H` (independent), host `h` adjacent to `N h`. -/
def hostGraph (N : H → Finset V) : SimpleGraph (V ⊕ H) where
  Adj a b :=
    match a, b with
    | .inl x, .inl y => x ≠ y
    | .inl x, .inr h => x ∈ N h
    | .inr h, .inl x => x ∈ N h
    | .inr _, .inr _ => False
  symm := ⟨by
    intro a b hab
    cases a <;> cases b
    · exact Ne.symm hab
    · exact hab
    · exact hab
    · exact hab⟩
  loopless := ⟨by
    intro a ha
    cases a with
    | inl _ => exact ha rfl
    | inr _ => exact ha⟩

/-- A fractional residual packing on the core (capacity 1 on every pair). -/
structure ResPack (y : Finset V → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ y S
  two : ∀ S, y S ≠ 0 → 2 ≤ S.card
  load : ∀ a b, a ≠ b → ∑ S, (if a ∈ S ∧ b ∈ S then y S else 0) ≤ 1
end GapExtremal

namespace QuadraticExteriorPalomar
open GapExtremal
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The value of the fractional residual problem with unit pair capacities. -/
noncomputable def residualSup (B : SimpleGraph V) [DecidableRel B.Adj] : ℝ :=
  sSup {s : ℝ | ∃ y : Finset V → ℝ, ResPack y ∧ ∑ Q, y Q * w B Q = s}
end QuadraticExteriorPalomar

namespace SplitGapIIRegistry
open GapExtremal QuadraticExteriorPalomar Finset
open scoped BigOperators
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Best total score of an integral family with disjoint pairs. -/
noncomputable def integralScore (B : SimpleGraph V) [DecidableRel B.Adj] : ℤ :=
  sSup {s : ℤ | ∃ P : Finset (Finset V), IsPack P ∧ (∀ Q ∈ P, 2 ≤ Q.card) ∧ ∑ Q ∈ P, w B Q = s}

/-- The two gaps differ by at most twice the number of unassigned required pairs. -/
theorem gap_stability_of_partial_assignment
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (J₀ : Finset (Finset V)) (hsub : J₀ ⊆ jPairs B univ) (host : J₀ → H)
    (hmem : ∀ p : J₀, p.val ⊆ N (host p))
    (hmatch : ∀ p q : J₀, host p = host q → ∀ a ∈ p.val, a ∈ q.val → p = q) :
    |gap (hostGraph N) -
      (residualSup B - integralScore B)| ≤ 2 * (((jPairs B univ).card - J₀.card : ℕ) : ℝ) := by
  sorry

/-- Deleting crossing incidences from a complete assignment changes the gap by at most twice their number. -/
theorem gap_stability_after_cross_deletions
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (host : Finset V → H) (hmem : ∀ p ∈ jPairs B univ, p ⊆ N (host p))
    (hmatch : ∀ p ∈ jPairs B univ, ∀ q ∈ jPairs B univ,
      host p = host q → ∀ a ∈ p, a ∈ q → p = q) (del : Finset (H × V)) :
    |gap (hostGraph (fun h => (N h).filter fun a => (h,a) ∉ del)) - gap (hostGraph N)| ≤
      2 * (del.card : ℝ) := by
  sorry

/-- With at least twice as many hosts as core vertices, only omissions beyond half the core size at each endpoint contribute to this upper bound. -/
theorem series_gap_le_of_vertex_excess (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (hC : G.IsClique (C : Set V)) (hI : ∀ x ∉ C, ∀ y ∉ C, ¬ G.Adj x y)
    (s : C → ℕ) (hsize : 2 * C.card ≤ Cᶜ.card)
    (hmiss : ∀ a : C, (Cᶜ.filter (fun x => ¬ G.Adj x a.val)).card ≤ C.card / 2 + s a) :
    GapExtremal.gap G ≤ 2 * (↑(∑ a, s a) : ℝ) := by
  sorry

end SplitGapIIRegistry
