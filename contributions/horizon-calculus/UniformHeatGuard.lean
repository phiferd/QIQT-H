import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/- Independent semantic guard for QIQT-H commit
0313e288c7ab3d3868c73ccdc6a68242efc0214a.
Shannon and KL below are literal copies of the two source definitions,
renamespaced to avoid importing the whole project's gravity stack.
This is not a build of that stack. -/
namespace UniformHeatGuard
open scoped BigOperators
noncomputable def Shannon {ι : Type*} (s : Finset ι) (p : ι → ℝ) : ℝ :=
  -∑ i ∈ s, p i * Real.log (p i)
noncomputable def KL {ι : Type*} (s : Finset ι) (p q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * Real.log (p i / q i)

theorem entropy_plus_uniform_KL {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hpsum : ∑ i, p i = 1) :
    Shannon Finset.univ p + KL Finset.univ p (fun _ => (Fintype.card ι : ℝ)⁻¹) =
      Real.log (Fintype.card ι) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht (i : ι) : p i * Real.log (p i / (Fintype.card ι : ℝ)⁻¹) =
      p i * Real.log (p i) + p i * Real.log (Fintype.card ι) := by
    by_cases hp : p i = 0
    · simp [hp]
    · rw [Real.log_div hp (inv_ne_zero hn), Real.log_inv]
      ring
  simp only [Shannon, KL, ht, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hpsum]
  ring

theorem hK_forces_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℝ → ι → ℝ) (hnorm : ∀ t, ∑ i, p t i = 1)
    (hzero : p 0 = fun _ => (Fintype.card ι : ℝ)⁻¹)
    (hbar Tkk : ℝ) (hbar0 : hbar ≠ 0)
    (hK : HasDerivAt (fun t => Shannon Finset.univ (p t) + KL Finset.univ (p t) (p 0))
      (2 * Real.pi / hbar * Tkk) 0) : Tkk = 0 := by
  have hf : (fun t => Shannon Finset.univ (p t) + KL Finset.univ (p t) (p 0)) =
      (fun _ : ℝ => Real.log (Fintype.card ι)) := by
    funext t
    rw [hzero]
    exact entropy_plus_uniform_KL (p t) (hnorm t)
  rw [hf] at hK
  have hz := hK.unique (hasDerivAt_const (0 : ℝ) (Real.log (Fintype.card ι)))
  exact (mul_eq_zero.mp hz).resolve_left (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hbar0)

-- Positive control: the same hK shape is satisfiable for a normalized uniform law and zero flux.
example (hbar : ℝ) :
    HasDerivAt (fun _ : ℝ => Shannon (Finset.univ : Finset (Fin 2)) (fun _ => 1/2) +
      KL Finset.univ (fun _ : Fin 2 => 1/2) (fun _ => 1/2))
      (2 * Real.pi / hbar * 0) 0 := by
  simpa using hasDerivAt_const (0 : ℝ) (Shannon (Finset.univ : Finset (Fin 2))
    (fun _ => 1/2) + KL Finset.univ (fun _ : Fin 2 => 1/2) (fun _ => 1/2))

-- Negative control: nonzero flux makes the hK hypothesis impossible.
theorem nonzero_flux_rejected {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ℝ → ι → ℝ) (hnorm : ∀ t, ∑ i, p t i = 1)
    (hzero : p 0 = fun _ => (Fintype.card ι : ℝ)⁻¹)
    (hbar Tkk : ℝ) (hbar0 : hbar ≠ 0) (hT : Tkk ≠ 0) :
    ¬ HasDerivAt (fun t => Shannon Finset.univ (p t) + KL Finset.univ (p t) (p 0))
      (2 * Real.pi / hbar * Tkk) 0 := by
  intro hK
  exact hT (hK_forces_zero p hnorm hzero hbar Tkk hbar0 hK)

#print axioms entropy_plus_uniform_KL
#print axioms hK_forces_zero
end UniformHeatGuard
