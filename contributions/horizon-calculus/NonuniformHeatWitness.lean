import UniformHeatGuard
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace NonuniformHeatWitness
open UniformHeatGuard
open scoped BigOperators

/-- Literal finite entropy identity; full support is required for q, not p. -/
theorem entropy_plus_KL {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hq : ∀ i, q i ≠ 0) :
    Shannon Finset.univ p + KL Finset.univ p q = -∑ i, p i * Real.log (q i) := by
  have ht (i : ι) : p i * Real.log (p i / q i) =
      p i * Real.log (p i) - p i * Real.log (q i) := by
    by_cases hp : p i = 0
    · simp [hp]
    · rw [Real.log_div hp (hq i)]; ring
  simp only [Shannon, KL, ht, Finset.sum_sub_distrib]
  ring

noncomputable def p (t : ℝ) : Fin 2 → ℝ := ![1/3 + Real.sin t / 6, 2/3 - Real.sin t / 6]
noncomputable def q : Fin 2 → ℝ := ![1/3, 2/3]

theorem p_positive (t : ℝ) (i : Fin 2) : 0 < p t i := by
  fin_cases i <;> simp [p] <;> linarith [Real.neg_one_le_sin t, Real.sin_le_one t]

theorem p_normalized (t : ℝ) : ∑ i, p t i = 1 := by
  rw [Fin.sum_univ_two]; simp [p]; ring

theorem p_zero : p 0 = q := by ext i; fin_cases i <;> simp [p, q]

theorem q_positive (i : Fin 2) : 0 < q i := by fin_cases i <;> norm_num [q]

noncomputable def heat (t : ℝ) : ℝ := Shannon Finset.univ (p t) + KL Finset.univ (p t) q

theorem heat_explicit (t : ℝ) : heat t =
    -((1/3 + Real.sin t / 6) * Real.log (1/3) +
      (2/3 - Real.sin t / 6) * Real.log (2/3)) := by
  rw [heat, entropy_plus_KL _ _ (fun i => ne_of_gt (q_positive i)), Fin.sum_univ_two]
  rfl

theorem log_ratio : Real.log (2/3) - Real.log (1/3) = Real.log 2 := by
  rw [← Real.log_div (by norm_num : (2/3 : ℝ) ≠ 0) (by norm_num : (1/3 : ℝ) ≠ 0)]
  norm_num

/-- A smooth, globally normalized and positive law has nonzero heat derivative.
No entropy derivative or heat-flux identity is assumed. -/
theorem heat_hasDerivAt : HasDerivAt heat (Real.log 2 / 6) 0 := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin t / 6) (1/6) 0 := by
    simpa using (Real.hasDerivAt_sin 0).div_const 6
  have h := (((hs.const_add (1/3)).mul_const (Real.log (1/3))).add
    ((hs.const_sub (2/3)).mul_const (Real.log (2/3)))).neg
  have he : -(1 / 6 * Real.log (1 / 3) + -(1 / 6) * Real.log (2 / 3)) = Real.log 2 / 6 := by
    nlinarith [log_ratio]
  convert h using 1
  · ext t; exact heat_explicit t
  · exact he.symm

theorem heat_derivative_positive : 0 < Real.log 2 / 6 := by
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- The uniform-reference zero-derivative guard cannot be applied to this witness. -/
theorem reference_not_uniform : q ≠ (fun _ : Fin 2 => (Fintype.card (Fin 2) : ℝ)⁻¹) := by
  intro h
  have hh := congrFun h 0
  norm_num [q] at hh

theorem shannon_hasDerivAt :
    HasDerivAt (fun t => Shannon Finset.univ (p t)) (Real.log 2 / 6) 0 := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin t / 6) (1/6) 0 := by
    simpa using (Real.hasDerivAt_sin 0).div_const 6
  have hf := hs.const_add (1/3)
  have hg := hs.const_sub (2/3)
  have h := ((hf.mul (hf.log (by norm_num))).add (hg.mul (hg.log (by norm_num)))).neg
  convert h using 1
  · ext t
    simp only [Shannon, Fin.sum_univ_two, p, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rfl
  · simp only [Real.sin_zero, zero_div, add_zero, sub_zero]
    nlinarith [log_ratio]

/-- KL is stationary at p=q, although the cross-entropy/heat is not. -/
theorem KL_hasDerivAt : HasDerivAt (fun t => KL Finset.univ (p t) q) 0 0 := by
  have h := heat_hasDerivAt.sub shannon_hasDerivAt
  change HasDerivAt (fun t => heat t - Shannon Finset.univ (p t)) _ _ at h
  simpa only [heat, add_sub_cancel_left, sub_self] using h

#print axioms shannon_hasDerivAt
#print axioms KL_hasDerivAt
#print axioms heat_hasDerivAt
#print axioms heat_derivative_positive
end NonuniformHeatWitness
