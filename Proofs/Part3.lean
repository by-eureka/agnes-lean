/-
  Nesterov acceleration despite very noisy gradients -- formalization.

  Part 3: stochastic gradient descent for reference (Theorems 17 and 22 of
  Appendices E.1 and F.1).  This is the comparison baseline of Figure 1.

  * Theorem 17 (`gd_convex`) is stated in the paper's scope: the reference point
    `x*` is an **arbitrary** point of `ℝᵐ`, not necessarily a minimizer.  The
    minimizing case with the optimal step size is the separate corollary
    `gd_convex_min`, which is the "in particular" clause of the paper.
  * Theorem 22 states the geometric decay of the objective values *and* the
    almost sure / `L²` convergence of the iterates (see `gd_pl_convergence`,
    which is proved, and `gd_pl_iterates`, which records the two convergence
    conclusions).

  All expectations are with respect to the probability measure of the shared
  model (`GDRun.prob`).
-/
import Proofs.Part2

noncomputable section

open MeasureTheory

namespace AGNES

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {f : E → ℝ} {grad : E → E}

/-- A run of the stochastic gradient descent scheme
`x_{n+1} = x_n - η g(x_n, ω_n)` of Theorems 17 / 22. -/
structure GDRun (f : E → ℝ) (grad : E → E) where
  mu : Measure Ω
  prob : IsProbabilityMeasure mu
  sigma : ℝ
  hsigma : 0 ≤ sigma
  filt : ℕ → MeasurableSpace Ω
  X : ℕ → Ω → E
  G : ℕ → Ω → E
  eta : ℝ
  adapted_X : ∀ n, Adapted (filt n) (X n)
  /-- The iterates are random variables (measurable for the ambient σ-algebra). -/
  ae_X : ∀ n, AEStronglyMeasurable (X n) mu
  adapted_grad : ∀ n, Adapted (filt n) (fun ω => grad (X n ω))
  unbiased : ∀ (n : ℕ) (z : Ω → E), Adapted (filt n) z →
    (∫ ω, inner ℝ (G n ω) (z ω) ∂mu) = ∫ ω, inner ℝ (grad (X n ω)) (z ω) ∂mu
  var_bound : ∀ n, (∫ ω, ‖G n ω - grad (X n ω)‖ ^ 2 ∂mu) ≤
    sigma ^ 2 * ∫ ω, ‖grad (X n ω)‖ ^ 2 ∂mu
  ae_G : ∀ n, AEStronglyMeasurable (G n) mu
  ae_grad : ∀ n, AEStronglyMeasurable (fun ω => grad (X n ω)) mu
  int_G : ∀ n, Integrable (fun ω => ‖G n ω‖ ^ 2) mu
  int_grad : ∀ n, Integrable (fun ω => ‖grad (X n ω)‖ ^ 2) mu
  step : ∀ n, X (n + 1) =ᵐ[mu] fun ω => X n ω - eta • G n ω
  int_f : ∀ n, Integrable (fun ω => f (X n ω)) mu
  int_sq : ∀ (n : ℕ) (v : E), Integrable (fun ω => ‖X n ω - v‖ ^ 2) mu

theorem gd_moment_cross (R : GDRun (Ω := Ω) f grad) (n : ℕ) :
    (∫ ω, inner ℝ (R.G n ω) (grad (R.X n ω)) ∂R.mu)
      = ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu := by
  rw [R.unbiased n (fun ω => grad (R.X n ω)) (R.adapted_grad n)]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun ω => real_inner_self_eq_norm_sq (grad (R.X n ω)))

theorem gd_moment_sq (R : GDRun (Ω := Ω) f grad) (n : ℕ) :
    (∫ ω, ‖R.G n ω‖ ^ 2 ∂R.mu)
      ≤ (1 + R.sigma ^ 2) * ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu := by
  have hGw2 : Integrable (fun ω => ‖R.G n ω - grad (R.X n ω)‖ ^ 2) R.mu :=
    integrable_norm_sq_sub (R.ae_G n) (R.ae_grad n) (R.int_G n) (R.int_grad n)
  have hinner : Integrable (fun ω => inner ℝ (R.G n ω) (grad (R.X n ω))) R.mu :=
    integrable_inner (R.ae_G n) (R.ae_grad n) (R.int_G n) (R.int_grad n)
  have hpt : ∀ ω, ‖R.G n ω‖ ^ 2 = ‖R.G n ω - grad (R.X n ω)‖ ^ 2
      + 2 * inner ℝ (R.G n ω) (grad (R.X n ω)) - ‖grad (R.X n ω)‖ ^ 2 := by
    intro ω
    have := norm_sub_sq_real (R.G n ω) (grad (R.X n ω))
    linarith
  have hcalc : (∫ ω, ‖R.G n ω‖ ^ 2 ∂R.mu)
      = (∫ ω, ‖R.G n ω - grad (R.X n ω)‖ ^ 2 ∂R.mu)
        + 2 * (∫ ω, inner ℝ (R.G n ω) (grad (R.X n ω)) ∂R.mu)
        - (∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu) := by
    have h1 : (∫ ω, ‖R.G n ω‖ ^ 2 ∂R.mu)
        = ∫ ω, ‖R.G n ω - grad (R.X n ω)‖ ^ 2
            + 2 * inner ℝ (R.G n ω) (grad (R.X n ω)) - ‖grad (R.X n ω)‖ ^ 2 ∂R.mu :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [h1, integral_sub, integral_add, integral_const_mul]
    all_goals
      first
      | exact hGw2
      | exact R.int_grad n
      | exact hinner
      | exact hinner.const_mul 2
      | exact hGw2.add (hinner.const_mul 2)
  rw [hcalc, gd_moment_cross R n]
  have hσ := R.var_bound n
  nlinarith [hσ]

/-- **Lemma 16'** (one step of gradient descent). -/
theorem gd_one_step (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hL : 0 ≤ L) (hη : 0 ≤ R.eta) (n : ℕ) :
    (∫ ω, f (R.X (n + 1) ω) ∂R.mu)
      ≤ (∫ ω, f (R.X n ω) ∂R.mu)
        - R.eta * (1 - L * (1 + R.sigma ^ 2) * R.eta / 2) *
            (∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu) := by
  have hmove : (fun ω => f (R.X (n + 1) ω)) =ᵐ[R.mu] (fun ω => f (R.X n ω - R.eta • R.G n ω)) :=
    (R.step n).fun_comp f
  rw [integral_congr_ae hmove]
  have hint : Integrable (fun ω => f (R.X n ω - R.eta • R.G n ω)) R.mu :=
    (R.int_f (n + 1)).congr hmove
  have hpt : ∀ ω, f (R.X n ω - R.eta • R.G n ω) ≤
      f (R.X n ω) - R.eta * inner ℝ (R.G n ω) (grad (R.X n ω))
        + L * R.eta ^ 2 / 2 * ‖R.G n ω‖ ^ 2 := by
    intro ω
    have h := hs (R.X n ω) (R.X n ω - R.eta • R.G n ω)
    have hstep : R.X n ω - R.eta • R.G n ω - R.X n ω = -(R.eta • R.G n ω) := by abel
    rw [hstep, inner_neg_right, inner_smul_right, norm_neg, norm_smul_sq] at h
    have hin : inner ℝ (grad (R.X n ω)) (R.G n ω) = inner ℝ (R.G n ω) (grad (R.X n ω)) :=
      real_inner_comm _ _
    rw [hin] at h
    nlinarith [h]
  have hinner : Integrable (fun ω => inner ℝ (R.G n ω) (grad (R.X n ω))) R.mu :=
    integrable_inner (R.ae_G n) (R.ae_grad n) (R.int_G n) (R.int_grad n)
  have hcomb : Integrable (fun ω => f (R.X n ω)
      - R.eta * inner ℝ (R.G n ω) (grad (R.X n ω))
      + L * R.eta ^ 2 / 2 * ‖R.G n ω‖ ^ 2) R.mu :=
    ((R.int_f n).sub (hinner.const_mul R.eta)).add
      ((R.int_G n).const_mul (L * R.eta ^ 2 / 2))
  have hle := integral_mono_ae hint hcomb (Filter.Eventually.of_forall hpt)
  have hsplit : (∫ ω, f (R.X n ω)
      - R.eta * inner ℝ (R.G n ω) (grad (R.X n ω))
      + L * R.eta ^ 2 / 2 * ‖R.G n ω‖ ^ 2 ∂R.mu)
      = (∫ ω, f (R.X n ω) ∂R.mu)
        - R.eta * (∫ ω, inner ℝ (R.G n ω) (grad (R.X n ω)) ∂R.mu)
        + L * R.eta ^ 2 / 2 * (∫ ω, ‖R.G n ω‖ ^ 2 ∂R.mu) := by
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
    all_goals
      first
      | exact R.int_f n
      | exact R.int_G n
      | exact hinner
      | exact hinner.const_mul R.eta
      | exact (R.int_G n).const_mul (L * R.eta ^ 2 / 2)
      | exact (R.int_f n).sub (hinner.const_mul R.eta)
  rw [hsplit] at hle
  rw [gd_moment_cross R n] at hle
  have hσ := gd_moment_sq R n
  have hc : (0 : ℝ) ≤ L * R.eta ^ 2 / 2 := by nlinarith
  have hkey : L * R.eta ^ 2 / 2 * (∫ ω, ‖R.G n ω‖ ^ 2 ∂R.mu)
      ≤ L * R.eta ^ 2 / 2 * ((1 + R.sigma ^ 2) *
          ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu) :=
    mul_le_mul_of_nonneg_left hσ hc
  linarith [hle, hkey]

/-- The PL bound in integrated form. -/
theorem gd_pl_integrated (R : GDRun (Ω := Ω) f grad) {mu m : ℝ} (hPL : PL f grad mu m)
    (hmin : ∀ x, m ≤ f x) (n : ℕ) :
    mu * ((∫ ω, f (R.X n ω) ∂R.mu) - m)
      ≤ (1 / 2) * ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu := by
  haveI := R.prob
  have hle : ∀ ω, mu * (f (R.X n ω) - m) ≤ ‖grad (R.X n ω)‖ ^ 2 / 2 := fun ω => hPL _
  have h3 : (∫ ω, mu * (f (R.X n ω) - m) ∂R.mu)
      ≤ ∫ ω, ‖grad (R.X n ω)‖ ^ 2 / 2 ∂R.mu :=
    integral_mono_ae (((R.int_f n).sub (integrable_const m)).const_mul mu)
      ((R.int_grad n).div_const 2) (Filter.Eventually.of_forall hle)
  have h4 : (∫ ω, mu * (f (R.X n ω) - m) ∂R.mu)
      = mu * ((∫ ω, f (R.X n ω) ∂R.mu) - m) := by
    rw [integral_const_mul, integral_sub (R.int_f n) (integrable_const m), integral_const]
    simp
  have h5 : (∫ ω, ‖grad (R.X n ω)‖ ^ 2 / 2 ∂R.mu)
      = (1 / 2) * ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu := by
    rw [show (fun ω => ‖grad (R.X n ω)‖ ^ 2 / 2)
        = (fun ω => (1 / 2) * ‖grad (R.X n ω)‖ ^ 2) from by
      funext ω; ring]
    rw [integral_const_mul]
  rw [h4, h5] at h3
  exact h3

/-! ### Theorem 17: gradient descent in the convex case

Theorem 17 of Appendix E.1 is stated for an **arbitrary** reference point
`x* ∈ ℝᵐ`; the minimizing case is only the "in particular" clause at the end of
the statement (there `x*` a minimizer replaces `E[f(x₀) - f(x*)]` by
`(L/2)E‖x₀ - x*‖²` using Lemma 12).  The Lyapunov argument itself only uses
convexity, and `f(x*) - inf f ≥ 0` is simply discarded, so the theorem is stated
here for an arbitrary `x*`; the minimizing corollary is `gd_convex_min`.

The four expectations of the proof are named (`Gval`, `Gdist`, `Ggrad`,
`Gnoise`) so that the bookkeeping is linear algebra on atoms, and the cross
terms `Gcross`, `GcrossG`. -/

/-- `E[f(x_n) - f(x*)]`. -/
def Gval (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) : ℝ :=
  ∫ ω, f (R.X n ω) - f xstar ∂R.mu

/-- `E‖x_n - x*‖²`. -/
def Gdist (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) : ℝ :=
  ∫ ω, ‖R.X n ω - xstar‖ ^ 2 ∂R.mu

/-- `E‖∇f(x_n)‖²`. -/
def Ggrad (R : GDRun (Ω := Ω) f grad) (n : ℕ) : ℝ :=
  ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu

/-- `E‖g_n‖²`. -/
def Gnoise (R : GDRun (Ω := Ω) f grad) (n : ℕ) : ℝ :=
  ∫ ω, ‖R.G n ω‖ ^ 2 ∂R.mu

/-- `E⟪∇f(x_n), x_n - x*⟫`. -/
def Gcross (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) : ℝ :=
  ∫ ω, inner ℝ (grad (R.X n ω)) (R.X n ω - xstar) ∂R.mu

/-- `E⟪g_n, x_n - x*⟫`. -/
def GcrossG (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) : ℝ :=
  ∫ ω, inner ℝ (R.G n ω) (R.X n ω - xstar) ∂R.mu

/-- `E[η(n+n₀)(f(x_n) - f(x*)) + ½‖x_n - x*‖²]`, the Lyapunov sequence of the
proof of Theorem 17. -/
def Glyap (R : GDRun (Ω := Ω) f grad) (xstar : E) (n0 : ℝ) (n : ℕ) : ℝ :=
  R.eta * ((n : ℝ) + n0) * Gval R xstar n + 1 / 2 * Gdist R xstar n

theorem Gval_eq (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) :
    Gval R xstar n = (∫ ω, f (R.X n ω) ∂R.mu) - f xstar := by
  haveI := R.prob
  rw [Gval, integral_sub (R.int_f n) (integrable_const (f xstar)), integral_const]
  simp

theorem Ggrad_nonneg (R : GDRun (Ω := Ω) f grad) (n : ℕ) : 0 ≤ Ggrad R n :=
  integral_nonneg fun ω => sq_nonneg _

theorem Gdist_nonneg (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) :
    0 ≤ Gdist R xstar n :=
  integral_nonneg fun ω => sq_nonneg _

theorem Gnoise_nonneg (R : GDRun (Ω := Ω) f grad) (n : ℕ) : 0 ≤ Gnoise R n :=
  integral_nonneg fun ω => sq_nonneg _

/-- **Theorem 17** (GD, convex case), first step: one step of gradient descent
in the form used by the Lyapunov argument,
`E[f(x_{n+1}) - f(x*)] ≤ E[f(x_n) - f(x*)] - (η/2) E‖∇f(x_n)‖²`.  This is
Lemma 16 with `η L (1+σ²) ≤ 1`. -/
theorem gd_val_step (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hL : 0 ≤ L) (hη : 0 ≤ R.eta) (hηL : R.eta * (L * (1 + R.sigma ^ 2)) ≤ 1)
    (xstar : E) (n : ℕ) :
    Gval R xstar (n + 1) ≤ Gval R xstar n - R.eta / 2 * Ggrad R n := by
  haveI := R.prob
  simp only [Gval, Ggrad]
  have h1 := gd_one_step R hs hL hη n
  have hC : (0 : ℝ) ≤ ∫ ω, ‖grad (R.X n ω)‖ ^ 2 ∂R.mu :=
    integral_nonneg fun ω => sq_nonneg _
  have hcoef : R.eta / 2 ≤ R.eta * (1 - L * (1 + R.sigma ^ 2) * R.eta / 2) := by
    nlinarith [hη, hηL, hL]
  have hmul := mul_le_mul_of_nonneg_right hcoef hC
  have e1 : (∫ ω, f (R.X (n + 1) ω) - f xstar ∂R.mu)
      = (∫ ω, f (R.X (n + 1) ω) ∂R.mu) - f xstar := by
    rw [integral_sub (R.int_f (n + 1)) (integrable_const (f xstar)), integral_const]
    simp
  have e0 : (∫ ω, f (R.X n ω) - f xstar ∂R.mu)
      = (∫ ω, f (R.X n ω) ∂R.mu) - f xstar := by
    rw [integral_sub (R.int_f n) (integrable_const (f xstar)), integral_const]
    simp
  linarith [h1, hmul, e1, e0]

/-- **Theorem 17** (GD, convex case), second step: expanding the squared distance
to the reference point, using `x_{n+1} = x_n - η g_n`. -/
theorem gd_dist_step (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) :
    Gdist R xstar (n + 1)
      = Gdist R xstar n - 2 * R.eta * GcrossG R xstar n + R.eta ^ 2 * Gnoise R n := by
  haveI := R.prob
  simp only [Gdist, GcrossG, Gnoise]
  have hpt : (fun ω => ‖R.X (n + 1) ω - xstar‖ ^ 2)
      =ᵐ[R.mu] (fun ω => ‖R.X n ω - xstar‖ ^ 2
        - 2 * R.eta * inner ℝ (R.G n ω) (R.X n ω - xstar)
        + R.eta ^ 2 * ‖R.G n ω‖ ^ 2) := by
    filter_upwards [R.step n] with ω hω
    rw [hω, sub_right_comm, norm_sub_sq_real, inner_smul_right, norm_smul_sq,
      real_inner_comm (R.X n ω - xstar) (R.G n ω)]
    ring
  rw [integral_congr_ae hpt]
  have hu : Integrable (fun ω => ‖R.X n ω - xstar‖ ^ 2) R.mu := R.int_sq n xstar
  have hin : Integrable (fun ω => inner ℝ (R.G n ω) (R.X n ω - xstar)) R.mu :=
    integrable_inner (R.ae_G n) ((R.ae_X n).sub aestronglyMeasurable_const)
      (R.int_G n) (R.int_sq n xstar)
  have hG2 : Integrable (fun ω => ‖R.G n ω‖ ^ 2) R.mu := R.int_G n
  have hAB : Integrable (fun ω => ‖R.X n ω - xstar‖ ^ 2
      - 2 * R.eta * inner ℝ (R.G n ω) (R.X n ω - xstar)) R.mu :=
    (hu.sub (hin.const_mul (2 * R.eta))).congr (Filter.Eventually.of_forall (fun ω => by simp))
  have hC2 : Integrable (fun ω => R.eta ^ 2 * ‖R.G n ω‖ ^ 2) R.mu :=
    (hG2.const_mul (R.eta ^ 2)).congr (Filter.Eventually.of_forall (fun ω => by simp))
  rw [integral_add hAB hC2, integral_sub hu (hin.const_mul (2 * R.eta)),
    integral_const_mul, integral_const_mul]

/-- **Theorem 17** (GD, convex case), third step: convexity relates the excess
value to the gradient at the current point. -/
theorem gd_cross (R : GDRun (Ω := Ω) f grad) (hc : ConvexG f grad) (xstar : E) (n : ℕ) :
    Gval R xstar n ≤ Gcross R xstar n := by
  haveI := R.prob
  simp only [Gval, Gcross]
  have hpt : ∀ ω, f (R.X n ω) - f xstar
      ≤ inner ℝ (grad (R.X n ω)) (R.X n ω - xstar) := by
    intro ω
    have h := hc (R.X n ω) xstar
    have h2 : inner ℝ (grad (R.X n ω)) (xstar - R.X n ω)
        = -inner ℝ (grad (R.X n ω)) (R.X n ω - xstar) := by
      rw [show xstar - R.X n ω = -(R.X n ω - xstar) from by abel, inner_neg_right]
    linarith
  exact integral_mono_ae ((R.int_f n).sub (integrable_const (f xstar)))
    (integrable_inner (R.ae_grad n) ((R.ae_X n).sub aestronglyMeasurable_const)
      (R.int_grad n) (R.int_sq n xstar)) (Filter.Eventually.of_forall hpt)

/-- **Theorem 17** (GD, convex case), fourth step: unbiasedness of the gradient
oracle against the predictable test vector `x_n - x*`. -/
theorem gd_unbiased_cross (R : GDRun (Ω := Ω) f grad) (xstar : E) (n : ℕ) :
    GcrossG R xstar n = Gcross R xstar n := by
  simp only [GcrossG, Gcross]
  exact R.unbiased n (fun ω => R.X n ω - xstar) ((R.adapted_X n).sub (Adapted.const xstar))

/-- The arithmetic of the Lyapunov step of the proof of Theorem 17: if the value
decreases by `(η/2)C`, the squared distance evolves by the bias–variance
expansion with cross term `E`, convexity gives `A ≤ E` and the variance bound
gives `D ≤ (1+σ²)C`, then the Lyapunov sequence with weight `η(n+n₀)` decreases
provided `n₀ ≥ 1+σ²`. -/
theorem lyap_arith {eta sig n0 : ℝ} {k : ℕ} {A A' B B' C D E : ℝ}
    (heta : 0 ≤ eta) (hC : 0 ≤ C) (hn0 : 1 + sig ^ 2 ≤ n0) (hk : 0 ≤ (k : ℝ))
    (hA : A' ≤ A - eta / 2 * C) (hB : B' = B - 2 * eta * E + eta ^ 2 * D)
    (hE : A ≤ E) (hD : D ≤ (1 + sig ^ 2) * C) :
    eta * ((k : ℝ) + 1 + n0) * A' + 1 / 2 * B' ≤ eta * ((k : ℝ) + n0) * A + 1 / 2 * B := by
  have hfac : (0 : ℝ) ≤ eta * ((k : ℝ) + 1 + n0) := by nlinarith [hk, hn0, heta, sq_nonneg sig]
  have hA2 := mul_le_mul_of_nonneg_left hA hfac
  have hEM := mul_le_mul_of_nonneg_left hE heta
  have hDM : eta ^ 2 / 2 * D ≤ eta ^ 2 / 2 * ((1 + sig ^ 2) * C) :=
    mul_le_mul_of_nonneg_left hD (by positivity)
  have hkey : (0 : ℝ) ≤ eta ^ 2 / 2 * (((k : ℝ) + 1 + n0) - (1 + sig ^ 2)) * C :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) hC
  linarith [hA2, hEM, hB, hDM, hkey]

/-- The Lyapunov sequence of the proof of Theorem 17 decreases by one step. -/
theorem gd_lyapunov_step (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hη : 0 < R.eta)
    (hσ : 0 ≤ R.sigma) (hηL : R.eta * (L * (1 + R.sigma ^ 2)) ≤ 1)
    (xstar : E) {n0 : ℝ} (hn0 : 1 + R.sigma ^ 2 ≤ n0) (n : ℕ) :
    Glyap R xstar n0 (n + 1) ≤ Glyap R xstar n0 n := by
  have hA := gd_val_step R hs hL.le hη.le hηL xstar n
  have hB := gd_dist_step R xstar n
  have hE := gd_cross R hc xstar n
  have hEc := gd_unbiased_cross R xstar n
  have hD : Gnoise R n ≤ (1 + R.sigma ^ 2) * Ggrad R n := by
    simp only [Gnoise, Ggrad]
    exact gd_moment_sq R n
  rw [hEc] at hB
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
  simp only [Glyap]
  rw [hcast]
  exact lyap_arith hη.le (Ggrad_nonneg R n) hn0 (Nat.cast_nonneg n) hA hB hE hD

/-- **Theorem 17** (gradient descent, convex case).  For **any** reference point
`x*` and any `n₀ ≥ 1 + σ²`, with `η L (1+σ²) ≤ 1`,
`E[f(x_n) - f(x*)] ≤ (η n₀ E[f(x_0) - f(x*)] + ½ E‖x_0 - x*‖²) / (η (n + n₀))`.

The reference point is *not* assumed to be a minimizer: the proof discards
`f(x*) - inf f ≥ 0` only, which is exactly what is needed for Theorem 7
(convexity without minimizers). -/
theorem gd_convex (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hη : 0 < R.eta)
    (hσ : 0 ≤ R.sigma) (hηL : R.eta * (L * (1 + R.sigma ^ 2)) ≤ 1)
    {xstar : E} {n0 : ℝ} (hn0 : 1 + R.sigma ^ 2 ≤ n0) (n : ℕ) :
    (∫ ω, f (R.X n ω) - f xstar ∂R.mu)
      ≤ (R.eta * n0 * (∫ ω, f (R.X 0 ω) - f xstar ∂R.mu)
          + (1 / 2) * (∫ ω, ‖R.X 0 ω - xstar‖ ^ 2 ∂R.mu)) / (R.eta * ((n : ℝ) + n0)) := by
  haveI := R.prob
  have hmono : ∀ k : ℕ, Glyap R xstar n0 k ≤ Glyap R xstar n0 0 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hstep := gd_lyapunov_step R hs hc hL hη hσ hηL xstar hn0 j
        linarith [hstep, ih]
  have h0 := hmono n
  simp only [Glyap, Gval, Gdist] at h0 ⊢
  have hB : (0 : ℝ) ≤ ∫ ω, ‖R.X n ω - xstar‖ ^ 2 ∂R.mu :=
    integral_nonneg fun ω => sq_nonneg _
  have hpos : (0 : ℝ) < (n : ℝ) + n0 := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith [hn0, hσ]
  rw [le_div_iff₀ (mul_pos hη hpos)]
  linarith [h0, hB]

/-- **Theorem 17**, "in particular" clause, verbatim as printed: with the optimal
step size `η = 1/(L(1+σ²))`, `n₀ = 1+σ²` and `x*` a minimizer,
`E[f(x_n) - f(x*)] ≤ L(1+σ²) E‖x_0 - x*‖² / (2 (n + 1 + σ²))`.

**Remaining obligation / discrepancy.**  This is the constant printed in the
paper (it is the sharp classical rate for gradient descent).  Warning: the
estimate obtained by *directly* evaluating the Lyapunov bound `gd_convex` at
`η = 1/(L(1+σ²))`, `n₀ = 1+σ²` and `E[f(x₀)-f(x*)] ≤ (L/2)E‖x₀-x*‖²` (Lemma 12)
only gives
`E[f(x_n)-f(x*)] ≤ L(1+σ²) E‖x₀-x*‖² / (n+1+σ²)`,
twice the constant printed here: the two terms of the numerator are
`½E‖x₀-x*‖² + ½E‖x₀-x*‖² = E‖x₀-x*‖²`.  The sharper constant therefore needs the
refined analysis of the *sum* of the Lyapunov decrements rather than the crude
`ℒ_n ≥ 0`, which is not carried out here.  We keep the printed statement and
flag it as an identified obligation rather than silently weakening it. -/
theorem gd_convex_min (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hσ : 0 ≤ R.sigma)
    (hη : R.eta = 1 / (L * (1 + R.sigma ^ 2)))
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) :
    (∫ ω, f (R.X n ω) - f xstar ∂R.mu)
      ≤ L * (1 + R.sigma ^ 2) * (∫ ω, ‖R.X 0 ω - xstar‖ ^ 2 ∂R.mu)
        / (2 * ((n : ℝ) + (1 + R.sigma ^ 2))) := by
  sorry

/-! ### Theorem 22: gradient descent under a PL condition -/

/-- **Theorem 22**, objective rate: with step size `η ≤ 1/(L(1+σ²))`,
`E[f(x_n) - inf f] ≤ (1 - μη)^n E[f(x_0) - inf f]`. -/
theorem gd_pl_convergence (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hL : 0 ≤ L) (hη0 : 0 ≤ R.eta) (hηL : R.eta * (L * (1 + R.sigma ^ 2)) ≤ 1)
    {mu m : ℝ} (hmu : 0 ≤ mu) (hμη : mu * R.eta ≤ 1)
    (hPL : PL f grad mu m) (hmin : ∀ x, m ≤ f x) (n : ℕ) :
    (∫ ω, f (R.X n ω) ∂R.mu) - m
      ≤ (1 - mu * R.eta) ^ n * ((∫ ω, f (R.X 0 ω) ∂R.mu) - m) := by
  haveI := R.prob
  have hGr : ∀ k, 0 ≤ ∫ ω, ‖grad (R.X k ω)‖ ^ 2 ∂R.mu := fun k =>
    integral_nonneg fun ω => sq_nonneg _
  have hval : 0 ≤ (∫ ω, f (R.X 0 ω) ∂R.mu) - m := by
    have : (0 : ℝ) ≤ ∫ ω, f (R.X 0 ω) - m ∂R.mu := integral_nonneg fun ω => sub_nonneg.mpr (hmin _)
    rw [integral_sub (R.int_f 0) (integrable_const m), integral_const] at this
    simpa using this
  have hnc : (0 : ℝ) ≤ 1 - mu * R.eta := by linarith
  have hc1 : R.eta / 2 ≤ R.eta * (1 - L * (1 + R.sigma ^ 2) * R.eta / 2) := by nlinarith
  have hstep : ∀ k, (∫ ω, f (R.X (k + 1) ω) ∂R.mu) - m
      ≤ (1 - mu * R.eta) * ((∫ ω, f (R.X k ω) ∂R.mu) - m) := by
    intro k
    have h1 := gd_one_step R hs hL hη0 k
    have h2 := gd_pl_integrated R hPL hmin k
    have h2' : mu * R.eta * ((∫ ω, f (R.X k ω) ∂R.mu) - m)
        ≤ R.eta * (1 - L * (1 + R.sigma ^ 2) * R.eta / 2) *
            (∫ ω, ‖grad (R.X k ω)‖ ^ 2 ∂R.mu) := by
      have hA : 0 ≤ (∫ ω, f (R.X k ω) ∂R.mu) - m := by
        have : (0 : ℝ) ≤ ∫ ω, f (R.X k ω) - m ∂R.mu :=
          integral_nonneg fun ω => sub_nonneg.mpr (hmin _)
        rw [integral_sub (R.int_f k) (integrable_const m), integral_const] at this
        simpa using this
      nlinarith [h2, hc1, hGr k, hA, hη0]
    nlinarith [h1, h2']
  have hmain : ∀ k, (∫ ω, f (R.X k ω) ∂R.mu) - m
      ≤ (1 - mu * R.eta) ^ k * ((∫ ω, f (R.X 0 ω) ∂R.mu) - m) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc (∫ ω, f (R.X (k + 1) ω) ∂R.mu) - m
            ≤ (1 - mu * R.eta) * ((∫ ω, f (R.X k ω) ∂R.mu) - m) := hstep k
          _ ≤ (1 - mu * R.eta) * ((1 - mu * R.eta) ^ k *
                ((∫ ω, f (R.X 0 ω) ∂R.mu) - m)) := mul_le_mul_of_nonneg_left ih hnc
          _ = (1 - mu * R.eta) ^ (k + 1) * ((∫ ω, f (R.X 0 ω) ∂R.mu) - m) := by ring
  exact hmain n

/-- **Theorem 22**, convergence of the iterates.  In addition to the objective
rate of `gd_pl_convergence`, the paper concludes: there is a limiting random
variable `x_∞` such that `x_n → x_∞` almost surely and in `L²`, and
`f(x_∞) = inf f` almost surely.

**Remaining obligation.**  This is the published conclusion of Theorem 22; it is
recorded here rather than weakened.  A formal proof needs
* the Borel–Cantelli lemma, applied to `P(f(x_n) - m > ε) ≤ C(1-μη)^n/ε`
  (summability of the geometric series) for the almost sure convergence;
* the `L²`-Cauchy estimate: `E‖x_{k+1} - x_k‖² = η²E‖g_k‖² ≤ 2L(1+σ²)η²E[f(x_k)-m]`,
  which is geometrically summable, whence
  `E‖x_n - x_∞‖² ≤ (∑_{k≥n} √(E‖x_{k+1}-x_k‖²))² → 0` by Fatou and Minkowski;
together with completeness of `L²`.  None of these tools is developed here, so
the statement is left as an identified obligation. -/
theorem gd_pl_iterates (R : GDRun (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hL : 0 < L) (hη : 0 < R.eta) (hσ : 0 ≤ R.sigma)
    (hηL : R.eta * (L * (1 + R.sigma ^ 2)) ≤ 1)
    {mu m : ℝ} (hmu : 0 < mu) (hμη : mu * R.eta ≤ 1)
    (hPL : PL f grad mu m) (hmin : ∀ x, m ≤ f x) :
    ∃ xinf : Ω → E, AEStronglyMeasurable xinf R.mu ∧
      (∀ᵐ ω ∂R.mu, Filter.Tendsto (fun n => R.X n ω) Filter.atTop (nhds (xinf ω))) ∧
      Filter.Tendsto (fun n => ∫ ω, ‖R.X n ω - xinf ω‖ ^ 2 ∂R.mu) Filter.atTop (nhds 0) ∧
      (∀ᵐ ω ∂R.mu, f (xinf ω) = m) := by
  sorry

end AGNES
