import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic

open MeasureTheory Set
namespace HorizonCalculus

/-- The pointwise linearized symplectic density, for dilation generator c*u*d/du.
The symplectic pairing is sigma(f,g)=integral(f*g' - g*f'). -/
def linearizedDensity (c : ℝ) (f f' f'' : ℝ → ℝ) (u : ℝ) : ℝ :=
  c * u * f' u * f' u - f u * (c * f' u + c * u * f'' u)

/-- Integration-by-parts component of the dilation calculation.
This is not yet a differentiation-under-the-integral theorem. -/
theorem integral_linearizedDensity (a b c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (ha : f a = 0) (hb : f b = 0) :
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
  simp only [ha, hb, mul_zero, sub_zero] at hibp
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

/-- Actual pointwise derivative for the explicitly chosen dilation orientation. -/
theorem dilation_density_hasDerivAt (c u : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : HasDerivAt f (f' u) u) (hf' : HasDerivAt f' (f'' u) u) :
    HasDerivAt (fun t : ℝ => f (Real.exp (c*t)*u) * f' u -
      f u * (Real.exp (c*t) * f' (Real.exp (c*t)*u)))
      (linearizedDensity c f f' f'' u) 0 := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (c*t)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul c).exp
  have hd : HasDerivAt (fun t : ℝ => Real.exp (c*t)*u) (c*u) 0 := he.mul_const u
  have h1 : HasDerivAt (fun t : ℝ => f (Real.exp (c*t)*u)) (f' u * (c*u)) 0 := by
    have hf0 : HasDerivAt f (f' u) (Real.exp (c*0)*u) := by simpa using hf
    exact hf0.comp 0 hd
  have h2 : HasDerivAt (fun t : ℝ => f' (Real.exp (c*t)*u)) (f'' u * (c*u)) 0 := by
    have hf0 : HasDerivAt f' (f'' u) (Real.exp (c*0)*u) := by simpa using hf'
    exact hf0.comp 0 hd
  have h := (h1.mul_const (f' u)).sub ((he.mul h2).const_mul (f u))
  convert h using 1
  simp only [mul_zero, Real.exp_zero, one_mul, linearizedDensity]
  ring

/-- A reusable compact-interval interchange lemma: continuity supplies the domination,
so neither an integral derivative nor a uniform bound is postulated. -/
theorem interval_parameter_derivative (a b : ℝ) (F F' : ℝ → ℝ → ℝ)
    (hF : Continuous (fun z : ℝ × ℝ => F z.1 z.2))
    (hF' : Continuous (fun z : ℝ × ℝ => F' z.1 z.2))
    (hd : ∀ t u, HasDerivAt (fun t => F t u) (F' t u) t) :
    HasDerivAt (fun t => ∫ u in a..b, F t u) (∫ u in a..b, F' 0 u) 0 := by
  have hc : IsCompact ((Icc (-1 : ℝ) 1) ×ˢ (uIcc a b)) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hF'.continuousOn
  have hFu (t : ℝ) : Continuous (F t) := hF.comp (continuous_const.prodMk continuous_id)
  have hF'u (t : ℝ) : Continuous (F' t) := hF'.comp (continuous_const.prodMk continuous_id)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => C) (s := Ioo (-1) 1)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (hFu t).aestronglyMeasurable)
    ((hFu 0).intervalIntegrable a b)
    ((hF'u 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall ?_)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall ?_)).2
  · intro u hu t ht
    exact hC (t,u) ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, uIoc_subset_uIcc hu⟩
  · intro u _ t _
    exact hd t u

/-- The full bounded-interval dilation bridge, with no assumed integral derivative.
For sigma(f,g)=∫(f*g'−g*f'), positive dilation exp(c*t) produces +2c times
weighted energy. Reversing either order or c changes the sign. -/
theorem dilation_symplectic_derivative (a b c : ℝ) (f f' f'' : ℝ → ℝ)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : ∀ u, HasDerivAt f' (f'' u) u)
    (hfc : Continuous f) (hf'c : Continuous f') (hf''c : Continuous f'')
    (ha : f a = 0) (hb : f b = 0) :
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
  rw [heq, integral_linearizedDensity a b c f f' f'' hf hf' hfc hf'c hf''c ha hb] at h
  exact h

def testProfile (u : ℝ) : ℝ := (u+2)*(u+1)
def testProfile' (u : ℝ) : ℝ := 2*u+3

theorem testProfile_deriv (u : ℝ) : HasDerivAt testProfile (testProfile' u) u := by
  convert ((hasDerivAt_id u).add_const 2).mul ((hasDerivAt_id u).add_const 1) using 1
  simp only [testProfile', id_eq]
  ring

theorem testProfile_second_deriv (u : ℝ) : HasDerivAt testProfile' 2 u := by
  change HasDerivAt (fun u : ℝ => 2*u+3) 2 u
  simpa only [id_eq, mul_one] using ((hasDerivAt_id u).const_mul 2).add_const 3

theorem test_energy : (∫ u in (-2 : ℝ)..(-1 : ℝ), u * (testProfile' u)^2) = -1/2 := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => u^4+4*u^3+(9/2)*u^2) (u*(2*u+3)^2) u := by
    convert (((hasDerivAt_id u).pow 4).add (((hasDerivAt_id u).pow 3).const_mul 4)).add
      (((hasDerivAt_id u).pow 2).const_mul (9/2)) using 1
    simp only [id_eq]
    ring
  have hc : Continuous (fun u : ℝ => u*(2*u+3)^2) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-2 : ℝ)) (b := (-1 : ℝ)) (fun u _ => hd u) (hc.intervalIntegrable _ _)
  norm_num [testProfile'] at h ⊢
  exact h

/-- Nonzero control: derivative is -c, so c=1 and c=-1 give opposite results. -/
theorem test_dilation_derivative (c : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ u in (-2 : ℝ)..(-1 : ℝ),
      testProfile (Real.exp (c*t)*u) * testProfile' u -
      testProfile u * (Real.exp (c*t) * testProfile' (Real.exp (c*t)*u))) (-c) 0 := by
  have h := dilation_symplectic_derivative (-2) (-1) c testProfile testProfile' (fun _ => 2)
    testProfile_deriv testProfile_second_deriv
    (by unfold testProfile; fun_prop) (by unfold testProfile'; fun_prop) continuous_const
    (by norm_num [testProfile]) (by norm_num [testProfile])
  rw [test_energy] at h
  convert h using 1
  ring

/-- A regression control for the originally proposed wrong sign. -/
theorem wrong_sign_rejected :
    ¬ HasDerivAt (fun t : ℝ => ∫ u in (-2 : ℝ)..(-1 : ℝ),
      testProfile (Real.exp (1*t)*u) * testProfile' u -
      testProfile u * (Real.exp (1*t) * testProfile' (Real.exp (1*t)*u))) 1 0 := by
  intro h
  have hn := h.unique (test_dilation_derivative 1)
  norm_num at hn

/-- Zero profile is a valid control, independently of the value of c. -/
example (a b c : ℝ) : HasDerivAt (fun t : ℝ => ∫ _u in a..b,
    (0 : ℝ) * 0 - 0 * (Real.exp (c*t)*0)) 0 0 := by
  simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

#print axioms test_dilation_derivative
#print axioms wrong_sign_rejected
#print axioms dilation_symplectic_derivative
#print axioms interval_parameter_derivative
#print axioms dilation_density_hasDerivAt
#print axioms integral_linearizedDensity
end HorizonCalculus
