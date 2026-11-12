import HorizonCalculus
import Mathlib.Analysis.Calculus.Deriv.Support

open MeasureTheory Set
namespace HorizonCalculus

/-- Finite-interval variant requiring only vanishing boundary products. -/
theorem integral_linearizedDensity_boundary (a b c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (ha : (a * f' a) * f a = 0) (hb : (b * f' b) * f b = 0) :
    (∫ u in a..b, linearizedDensity c f f' f'' u) =
      2 * c * ∫ u in a..b, u * (f' u)^2 := by
  have hu : Continuous (fun u => u * f' u) := continuous_id.mul hf'c
  have hud : ∀ u, HasDerivAt (fun u => u * f' u) (f' u + u * f'' u) u := by
    intro u
    simpa using (hasDerivAt_id u).mul (hf' u)
  have hv : Continuous (fun u => f' u + u * f'' u) := hf'c.add (continuous_id.mul hf''c)
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (a := a) (b := b) hu.continuousOn hfc.continuousOn
    (fun u _ => hud u) (fun u _ => hf u)
    (hv.intervalIntegrable a b) (hf'c.intervalIntegrable a b)
  simp only [ha, hb, sub_zero] at hibp
  have hI1 : IntervalIntegrable (fun u => (f' u + u * f'' u) * f u) volume a b :=
    (hv.mul hfc).intervalIntegrable a b
  have hI2 : IntervalIntegrable (fun u => (u * f' u) * f' u) volume a b :=
    (hu.mul hf'c).intervalIntegrable a b
  rw [intervalIntegral.integral_add hI1 hI2] at hibp
  have heq : (fun u => linearizedDensity c f f' f'' u) =
      (fun u => c * ((u * f' u) * f' u - (f' u + u * f'' u) * f u)) := by
    funext u; unfold linearizedDensity; ring
  rw [heq, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hI2 hI1]
  have hs : (∫ u in a..b, (u * f' u) * f' u) = ∫ u in a..b, u * (f' u)^2 := by
    congr 1; funext u; ring
  rw [hs] at hibp
  rw [hs]
  have hr : (∫ x in a..b, (f' x + x * f'' x) * f x) = -(∫ u in a..b, u * (f' u)^2) := by linarith
  rw [hr]
  ring

theorem dilation_symplectic_derivative_boundary (a b c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (ha : (a * f' a) * f a = 0) (hb : (b * f' b) * f b = 0) :
    HasDerivAt (fun t : ℝ => ∫ u in a..b,
      f (Real.exp (c*t)*u) * f' u - f u * (Real.exp (c*t) * f' (Real.exp (c*t)*u)))
      (2 * c * ∫ u in a..b, u * (f' u)^2) 0 := by
  let F : ℝ → ℝ → ℝ := fun t u =>
    f (Real.exp (c*t)*u) * f' u - f u * (Real.exp (c*t) * f' (Real.exp (c*t)*u))
  let D : ℝ → ℝ → ℝ := fun t u =>
    f' (Real.exp (c*t)*u) * (Real.exp (c*t)*c*u) * f' u -
    f u * (Real.exp (c*t)*c * f' (Real.exp (c*t)*u) +
      Real.exp (c*t) * (f'' (Real.exp (c*t)*u) * (Real.exp (c*t)*c*u)))
  have hF : Continuous (fun z : ℝ × ℝ => F z.1 z.2) := by dsimp [F]; fun_prop
  have hD : Continuous (fun z : ℝ × ℝ => D z.1 z.2) := by dsimp [D]; fun_prop
  have hd (t u : ℝ) : HasDerivAt (fun t => F t u) (D t u) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (c*s)) (Real.exp (c*t)*c) t :=
      by simpa using ((hasDerivAt_id t).const_mul c).exp
    have h1 := (hf (Real.exp (c*t)*u)).comp t (he.mul_const u)
    have h2 := (hf' (Real.exp (c*t)*u)).comp t (he.mul_const u)
    exact (h1.mul_const (f' u)).sub ((he.mul h2).const_mul (f u))
  have h := interval_parameter_derivative a b F D hF hD hd
  have heq : D 0 = linearizedDensity c f f' f'' := by
    funext u
    dsimp [D, linearizedDensity]
    simp only [mul_zero, Real.exp_zero, one_mul]
    ring
  rw [heq, integral_linearizedDensity_boundary a b c f f' f'' hf hf' hfc hf'c hf''c ha hb] at h
  exact h


/-- Outside the original compact support both stationary factors vanish.
This holds for every dilation parameter, without a moving-support assumption. -/
theorem dilation_density_zero_off_support (c t u : ℝ) (f f' : ℝ → ℝ)
    (hf : HasDerivAt f (f' u) u) (hu : u ∉ tsupport f) :
    f (Real.exp (c*t)*u) * f' u -
      f u * (Real.exp (c*t) * f' (Real.exp (c*t)*u)) = 0 := by
  have h0 := image_eq_zero_of_notMem_tsupport hu
  have h1 : f' u = 0 := by rw [← hf.deriv]; exact deriv_of_notMem_tsupport hu
  simp [h0, h1]

/-- A fixed compact truncation of the entire negative half-line is exact whenever
the integrand vanishes below the cutoff. No integrability assumption is hidden here. -/
theorem halfLine_eq_interval (a : ℝ) (ha : a ≤ 0) (g : ℝ → ℝ)
    (hg : ∀ u, u ≤ a → g u = 0) :
    (∫ u in Iic (0 : ℝ), g u) = ∫ u in a..0, g u := by
  rw [intervalIntegral.integral_of_le ha]
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Iic
    (fun _ hu => hu.2)
  intro u hu
  apply hg u
  have hn : ¬ a < u := by intro h; exact hu.2 ⟨h, hu.1⟩
  exact le_of_not_gt hn

/-- The whole negative-half-line dilation identity for compactly supported C² data
without a boundary condition at zero: its weighted boundary term vanishes.
The full parameter family is reduced
to a fixed finite interval using its stationary factors. -/
theorem halfLine_dilation_symplectic_derivative (c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (hs : HasCompactSupport f) :
    HasDerivAt (fun t : ℝ => ∫ u in Iic (0 : ℝ),
      f (Real.exp (c*t)*u) * f' u -
      f u * (Real.exp (c*t) * f' (Real.exp (c*t)*u)))
      (2*c * ∫ u in Iic (0 : ℝ), u*(f' u)^2) 0 := by
  obtain ⟨b, hb⟩ := bddBelow_def.mp hs.isCompact.bddBelow
  let a := min b 0 - 1
  have ha : a ≤ 0 := by dsimp [a]; linarith [min_le_right b 0]
  have hoff (u : ℝ) (hu : u ≤ a) : u ∉ tsupport f := by
    intro h
    have := hb u h
    dsimp [a] at hu
    linarith [min_le_left b 0]
  have hfa : f a = 0 := image_eq_zero_of_notMem_tsupport (hoff a le_rfl)
  have hfun : (fun t : ℝ => ∫ u in Iic (0 : ℝ),
      f (Real.exp (c*t)*u)*f' u - f u*(Real.exp (c*t)*f' (Real.exp (c*t)*u))) =
      (fun t : ℝ => ∫ u in a..0,
      f (Real.exp (c*t)*u)*f' u - f u*(Real.exp (c*t)*f' (Real.exp (c*t)*u))) := by
    funext t
    apply halfLine_eq_interval a ha
    intro u hu
    exact dilation_density_zero_off_support c t u f f' (hf u) (hoff u hu)
  have henergy : (∫ u in Iic (0 : ℝ), u*(f' u)^2) = ∫ u in a..0, u*(f' u)^2 := by
    apply halfLine_eq_interval a ha
    intro u hu
    have h1 : f' u = 0 := by rw [← (hf u).deriv]; exact deriv_of_notMem_tsupport (hoff u hu)
    simp [h1]
  rw [hfun, henergy]
  exact dilation_symplectic_derivative_boundary a 0 c f f' f'' hf hf' hfc hf'c hf''c
    (by rw [hfa]; ring) (by ring)

/-- Open-half-line version; removing the endpoint changes no Lebesgue integral. -/
theorem openHalfLine_dilation_symplectic_derivative (c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (hs : HasCompactSupport f) :
    HasDerivAt (fun t : ℝ => ∫ u in Iio (0 : ℝ),
      f (Real.exp (c*t)*u) * f' u -
      f u * (Real.exp (c*t) * f' (Real.exp (c*t)*u)))
      (2*c * ∫ u in Iio (0 : ℝ), u*(f' u)^2) 0 := by
  simpa only [integral_Iic_eq_integral_Iio] using
    halfLine_dilation_symplectic_derivative c f f' f'' hf hf' hfc hf'c hf''c hs

/-- Actual integrability rules out reliance on Lean's zero-valued undefined integral. -/
theorem halfLine_energy_integrable (f f' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u) (hc : Continuous f')
    (hs : HasCompactSupport f) :
    IntegrableOn (fun u => u*(f' u)^2) (Iic (0 : ℝ)) := by
  have hs' : HasCompactSupport (fun u => u*(f' u)^2) := by
    apply hs.mono'
    intro u hu
    by_contra hn
    have hz : f' u = 0 := by rw [← (hf u).deriv]; exact deriv_of_notMem_tsupport hn
    exact hu (by simp [hz])
  have hc' : Continuous (fun u => u*(f' u)^2) := by fun_prop
  exact (hc'.integrable_of_hasCompactSupport hs').integrableOn

/-- The entire parameter family is genuinely integrable, at every real t. -/
theorem halfLine_density_integrable (c t : ℝ) (f f' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u) (hc : Continuous f) (hc' : Continuous f')
    (hs : HasCompactSupport f) :
    IntegrableOn (fun u => f (Real.exp (c*t)*u)*f' u -
      f u*(Real.exp (c*t)*f' (Real.exp (c*t)*u))) (Iic (0 : ℝ)) := by
  have hsupport : HasCompactSupport (fun u => f (Real.exp (c*t)*u)*f' u -
      f u*(Real.exp (c*t)*f' (Real.exp (c*t)*u))) := by
    apply hs.mono'
    intro u hu
    by_contra hn
    exact hu (dilation_density_zero_off_support c t u f f' (hf u) hn)
  have hcont : Continuous (fun u => f (Real.exp (c*t)*u)*f' u -
      f u*(Real.exp (c*t)*f' (Real.exp (c*t)*u))) := by fun_prop
  exact (hcont.integrable_of_hasCompactSupport hsupport).integrableOn

/-- Orientation control: weighted energy on the negative half-line is nonpositive. -/
theorem halfLine_energy_nonpos (f' : ℝ → ℝ) :
    (∫ u in Iic (0 : ℝ), u*(f' u)^2) ≤ 0 := by
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  exact mul_nonpos_of_nonpos_of_nonneg hu (sq_nonneg _)

/-- Wrong-sign regression: whenever the coefficient is nonzero the opposite
coefficient cannot also be the derivative. This is not an existence claim. -/
theorem halfLine_wrong_sign_rejected (c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (hs : HasCompactSupport f)
    (hn : 2*c * (∫ u in Iic (0 : ℝ), u*(f' u)^2) ≠ 0) :
    ¬ HasDerivAt (fun t : ℝ => ∫ u in Iic (0 : ℝ),
      f (Real.exp (c*t)*u)*f' u - f u*(Real.exp (c*t)*f' (Real.exp (c*t)*u)))
      (-(2*c * ∫ u in Iic (0 : ℝ), u*(f' u)^2)) 0 := by
  intro h
  have he := h.unique (halfLine_dilation_symplectic_derivative c f f' f''
    hf hf' hfc hf'c hf''c hs)
  apply hn
  linarith

/-- The zero profile satisfies the whole-half-line formula, including compact support. -/
theorem halfLine_zero_control (c : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ _u in Iic (0 : ℝ),
      (0 : ℝ)*0 - 0*(Real.exp (c*t)*0)) 0 0 := by
  simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

#print axioms openHalfLine_dilation_symplectic_derivative
#print axioms halfLine_dilation_symplectic_derivative
#print axioms dilation_density_zero_off_support
#print axioms halfLine_zero_control
#print axioms halfLine_energy_integrable
#print axioms halfLine_density_integrable
#print axioms halfLine_energy_nonpos
#print axioms halfLine_wrong_sign_rejected
end HorizonCalculus
