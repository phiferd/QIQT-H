import HalfLineCalculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory Set
noncomputable section
namespace CompactWitness

/-- A concrete mathlib smooth bump with plateau radius 1/4 and support radius 1/2. -/
def cutoff : ContDiffBump (-2 : ℝ) where
  rIn := 1/4
  rOut := 1/2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def profile (u : ℝ) : ℝ := u * cutoff u

theorem profile_smooth : ContDiff ℝ 3 profile :=
  contDiff_id.mul cutoff.contDiff

theorem profile_deriv_smooth : ContDiff ℝ 2 (deriv profile) :=
  profile_smooth.deriv'

theorem profile_second_smooth : ContDiff ℝ 1 (deriv (deriv profile)) :=
  profile_deriv_smooth.deriv'

theorem profile_compact : HasCompactSupport profile := cutoff.hasCompactSupport.mul_left

theorem profile_deriv_at_center : HasDerivAt profile 1 (-2 : ℝ) := by
  apply (hasDerivAt_id (-2 : ℝ)).congr_of_eventuallyEq
  filter_upwards [cutoff.eventuallyEq_one] with u hu
  simp [profile, hu]

theorem profile_deriv_center : deriv profile (-2) = 1 := profile_deriv_at_center.deriv

theorem support_negative (u : ℝ) (hu : u ∈ tsupport profile) : u ≤ -3/2 := by
  have h : u ∈ tsupport (cutoff : ℝ → ℝ) := tsupport_mul_subset_right hu
  rw [cutoff.tsupport_eq] at h
  have hd : |u - (-2)| ≤ (1/2 : ℝ) := by simpa [Metric.mem_closedBall, Real.dist_eq, cutoff] using h
  have := (abs_le.mp hd).2
  linarith

def positiveEnergy (u : ℝ) : ℝ := -(u*(deriv profile u)^2)

theorem positiveEnergy_continuous : Continuous positiveEnergy := by
  unfold positiveEnergy
  have := profile_deriv_smooth.continuous
  fun_prop

theorem positiveEnergy_compact : HasCompactSupport positiveEnergy := by
  apply profile_compact.mono'
  intro u hu
  by_contra hn
  exact hu (by simp [positiveEnergy, deriv_of_notMem_tsupport hn])

theorem positiveEnergy_nonneg : 0 ≤ positiveEnergy := by
  intro u
  by_cases hu : u ∈ tsupport profile
  · have := support_negative u hu
    dsimp [positiveEnergy]
    have : u ≤ 0 := by linarith
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _))
  · simp [positiveEnergy, deriv_of_notMem_tsupport hu]

theorem positiveEnergy_center : positiveEnergy (-2) = 2 := by
  norm_num [positiveEnergy, profile_deriv_center]

theorem positiveEnergy_integral_pos : 0 < ∫ u, positiveEnergy u :=
  positiveEnergy_continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    positiveEnergy_compact positiveEnergy_nonneg (by rw [positiveEnergy_center]; norm_num)

theorem energy_strictly_negative : (∫ u in Iic (0 : ℝ), u*(deriv profile u)^2) < 0 := by
  have heq : (∫ u in Iic (0 : ℝ), positiveEnergy u) = ∫ u, positiveEnergy u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hn : u ∉ tsupport profile := by
      intro hs
      have := support_negative u hs
      simp only [mem_Iic, not_le] at hu
      linarith
    simp [positiveEnergy, deriv_of_notMem_tsupport hn]
  have hp := positiveEnergy_integral_pos
  rw [← heq] at hp
  simp only [positiveEnergy, integral_neg] at hp
  linarith

def pairing (c t : ℝ) : ℝ := ∫ u in Iic (0 : ℝ),
  profile (Real.exp (c*t)*u)*deriv profile u -
    profile u*(Real.exp (c*t)*deriv profile (Real.exp (c*t)*u))

theorem pairing_derivative (c : ℝ) :
    HasDerivAt (pairing c) (2*c * ∫ u in Iic (0 : ℝ), u*(deriv profile u)^2) 0 := by
  apply HorizonCalculus.halfLine_dilation_symplectic_derivative c profile (deriv profile)
    (deriv (deriv profile))
  · intro u
    exact (profile_smooth.differentiable (by norm_num) u).hasDerivAt
  · intro u
    exact (profile_deriv_smooth.differentiable (by norm_num) u).hasDerivAt
  · exact profile_smooth.continuous
  · exact profile_deriv_smooth.continuous
  · exact profile_second_smooth.continuous
  · exact profile_compact

/-- The concrete nonzero energy integral exists in the usual Bochner sense. -/
theorem profile_energy_integrable :
    IntegrableOn (fun u => u*(deriv profile u)^2) (Iic (0 : ℝ)) :=
  HorizonCalculus.halfLine_energy_integrable profile (deriv profile)
    (fun u => (profile_smooth.differentiable (by norm_num) u).hasDerivAt)
    profile_deriv_smooth.continuous profile_compact

/-- Fixed KPV convention: sigma_minus(f,g)=integral(f' g - f g'),
with the SAME positive dilation exp(2*pi*t), not a reversed dilation. -/
def kpvPairing (t : ℝ) : ℝ := ∫ u in Iic (0 : ℝ),
  (Real.exp ((2*Real.pi)*t)*deriv profile (Real.exp ((2*Real.pi)*t)*u))*profile u -
    profile (Real.exp ((2*Real.pi)*t)*u)*deriv profile u

theorem kpvPairing_eq_neg : kpvPairing = fun t => -(pairing (2*Real.pi) t) := by
  funext t
  unfold kpvPairing pairing
  rw [← integral_neg]
  congr 1
  funext u
  ring

theorem kpvPairing_derivative :
    HasDerivAt kpvPairing (-(4*Real.pi * ∫ u in Iic (0 : ℝ), u*(deriv profile u)^2)) 0 := by
  rw [kpvPairing_eq_neg]
  convert (pairing_derivative (2*Real.pi)).neg using 1
  ring

theorem kpv_coefficient_positive :
    0 < -(4*Real.pi * ∫ u in Iic (0 : ℝ), u*(deriv profile u)^2) := by
  have hp : 0 < 4*Real.pi := mul_pos (by norm_num) Real.pi_pos
  exact neg_pos.mpr (mul_neg_of_pos_of_neg hp energy_strictly_negative)

/-- The same profile under sigma_plus has a strictly negative derivative. -/
theorem positive_dilation_coefficient_negative :
    4*Real.pi * (∫ u in Iic (0 : ℝ), u*(deriv profile u)^2) < 0 := by
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) energy_strictly_negative

/-- Non-vacuous sign rejection: no nonzero assumption remains to be supplied. -/
theorem concrete_wrong_sign_rejected :
    ¬ HasDerivAt (pairing (2*Real.pi))
      (-(4*Real.pi * ∫ u in Iic (0 : ℝ), u*(deriv profile u)^2)) 0 := by
  intro h
  have he := h.unique (pairing_derivative (2*Real.pi))
  have hn := positive_dilation_coefficient_negative
  nlinarith

/-- Changing convention flips the sign, while retaining the exact same dilation. -/
theorem kpv_wrong_sign_rejected :
    ¬ HasDerivAt kpvPairing
      (4*Real.pi * ∫ u in Iic (0 : ℝ), u*(deriv profile u)^2) 0 := by
  intro h
  have he := h.unique kpvPairing_derivative
  have hn := positive_dilation_coefficient_negative
  linarith

#print axioms profile_energy_integrable
#print axioms kpvPairing_derivative
#print axioms kpv_coefficient_positive
#print axioms concrete_wrong_sign_rejected
#print axioms kpv_wrong_sign_rejected
#print axioms pairing_derivative
#print axioms energy_strictly_negative
#print axioms profile_deriv_center
end CompactWitness
