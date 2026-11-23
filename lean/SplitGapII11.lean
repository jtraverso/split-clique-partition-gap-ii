import Mathlib.Tactic.NormNum

namespace QuadraticExteriorPalomar

/-- The two list sizes used in the mixed-pair and internal-pair stages. -/
theorem local_deletion_list_sizes (w v r : ℕ) :
    w ≤ w + v + r - 2 * ((v + r) / 2) ∧
      3 * w + 2 * r ≤ 3 * (w + v + r) - 2 * ((v + r) / 2) - 2 * v := by
  constructor <;> omega

/-- Gap arithmetic once the two partition optima have been certified. -/
theorem single_deletion_gap_jump :
    ((18 : ℚ) - 46 / 3) - (17 - 49 / 3) = 2 := by norm_num

end QuadraticExteriorPalomar

#print axioms QuadraticExteriorPalomar.local_deletion_list_sizes
#print axioms QuadraticExteriorPalomar.single_deletion_gap_jump
