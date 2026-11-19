/-
  Nesterov acceleration despite very noisy gradients -- formalization.

  Part 4: the convex case.  Theorems 1 (NAG), 3, 18 (AGNES) and 7 (convexity
  without minimizers), together with the parameter algebra of the proofs and the
  Lyapunov functional used in Appendix E.2.
-/
import Proofs.Part3

noncomputable section

open MeasureTheory

namespace AGNES

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {f : E → ℝ} {grad : E → E}

/-! ### Parameter algebra from the proof of Theorem 18 (Step 4) -/

/-- The per-step inequality of the Lyapunov argument for AGNES in the convex case
reduces to the non-negativity of a quadratic `q`.  This is the verification of
Step 4 in the proof of Theorem 18: if `n₀ ≥ 2ησ²/(η - α(1+σ²))` then `q ≥ 0`
on `[n₀,∞)`. -/
theorem thm18_quadratic_nonneg {al eta sigma n0 : ℝ} (hal : 0 < al) (heta : 0 < eta)
    (hκ : 0 < eta - al * (1 + sigma ^ 2))
    (hn0 : 2 * eta * sigma ^ 2 / (eta - al * (1 + sigma ^ 2)) ≤ n0) :
    ∀ z : ℝ, n0 ≤ z → 0 ≤ al * (eta - al * (1 + sigma ^ 2)) * z ^ 2
      + 2 * eta * (eta + al - 2 * al * (1 + sigma ^ 2)) * z - 4 * eta ^ 2 * sigma ^ 2 := by
  intro z hz
  set κ := eta - al * (1 + sigma ^ 2) with hκdef
  set z0 := 2 * eta * sigma ^ 2 / κ with hz0def
  have hκpos : 0 < κ := hκ
  have hz0le : z0 ≤ z := le_trans (by rw [hz0def]; exact hn0) hz
  have hz0pos : 0 ≤ z0 := by
    rw [hz0def]
    positivity
  have hid : al * κ * z ^ 2 + 2 * eta * (eta + al - 2 * al * (1 + sigma ^ 2)) * z
        - 4 * eta ^ 2 * sigma ^ 2
      = (z - z0) * (al * κ * (z + z0) + 2 * eta * (κ - al * sigma ^ 2)) := by
    rw [hz0def]
    field_simp
    ring
  have hbracket : 0 ≤ al * κ * (z + z0) + 2 * eta * (κ - al * sigma ^ 2) := by
    have h1 : al * κ * (z + z0) ≥ al * κ * (2 * z0) := by
      have : 0 ≤ al * κ := by positivity
      have h2 : 2 * z0 ≤ z + z0 := by linarith
      nlinarith [this, h2, norm_nonneg (al * κ)]
    have h3 : al * κ * (2 * z0) = 4 * eta * al * sigma ^ 2 := by
      rw [hz0def]; field_simp; ring
    nlinarith [h1, h3, hz0pos, hκpos, heta, hal]
  have hstep : 0 ≤ (z - z0) * (al * κ * (z + z0) + 2 * eta * (κ - al * sigma ^ 2)) :=
    mul_nonneg (by linarith) hbracket
  linarith [hid, hstep]

/-! ### Theorem 18: AGNES in the convex case (the `n₀` version) -/

/-! #### The Lyapunov functional

We follow the paper's Lyapunov sequence
`L_n = P(n) E[f(x_n) - f(x*)] + (1/2) E‖b(n)(x'_n - x_n) + a(x'_n - x*)‖²`
with `a = a₀` constant and `P(n) = (α b(n) + η a₀) b(n)`. -/

/-- `E[f(x_n) - f(x*)]` (`f x*` subtracted pointwise). -/
def Fval (R : Run (Ω := Ω) f grad) (xstar : E) (n : ℕ) : ℝ :=
  ∫ ω, f (R.base.X n ω) - f xstar ∂R.base.mu

/-- `E[f(x'_n) - f(x*)]`. -/
def Fval' (R : Run (Ω := Ω) f grad) (xstar : E) (n : ℕ) : ℝ :=
  ∫ ω, f (R.base.X' n ω) - f xstar ∂R.base.mu

/-- `E‖∇f(x'_n)‖²`. -/
def Gsq (R : Run (Ω := Ω) f grad) (n : ℕ) : ℝ :=
  ∫ ω, ‖grad (R.base.X' n ω)‖ ^ 2 ∂R.base.mu

/-- The momentum part of the Lyapunov vector,
`w_n = b(n) (x'_n - x_n) + a₀ (x'_n - x*)`. -/
def wvec (R : Run (Ω := Ω) f grad) (xstar : E) (b : ℕ → ℝ) (a0 : ℝ) (n : ℕ) : Ω → E :=
  fun ω => b n • (R.base.X' n ω - R.base.X n ω) + a0 • (R.base.X' n ω - xstar)

/-- `E‖w_n‖²`. -/
def Wmom (R : Run (Ω := Ω) f grad) (xstar : E) (b : ℕ → ℝ) (a0 : ℝ) (n : ℕ) : ℝ :=
  ∫ ω, ‖wvec R xstar b a0 n ω‖ ^ 2 ∂R.base.mu

/-- Integrability of `‖c • u + d • v‖²` from integrability of `‖u‖²` and `‖v‖²`. -/
theorem integrable_norm_sq_lin {μ : Measure Ω} {u v : Ω → E} {c d : ℝ}
    (hum : AEStronglyMeasurable u μ) (hvm : AEStronglyMeasurable v μ)
    (hu : Integrable (fun ω => ‖u ω‖ ^ 2) μ) (hv : Integrable (fun ω => ‖v ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖c • u ω + d • v ω‖ ^ 2) μ := by
  refine Integrable.mono' (g := fun ω => 2 * c ^ 2 * ‖u ω‖ ^ 2 + 2 * d ^ 2 * ‖v ω‖ ^ 2)
    ((hu.const_mul (2 * c ^ 2)).add (hv.const_mul (2 * d ^ 2))) ?_ ?_
  · exact (((hum.const_smul c).add (hvm.const_smul d)).norm.pow 2)
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h2 : ‖c • u ω‖ ^ 2 = c ^ 2 * ‖u ω‖ ^ 2 := norm_smul_sq c (u ω)
    have h3 : ‖d • v ω‖ ^ 2 = d ^ 2 * ‖v ω‖ ^ 2 := norm_smul_sq d (v ω)
    have h5 : ‖c • u ω + d • v ω‖ ^ 2 ≤ (‖c • u ω‖ + ‖d • v ω‖) ^ 2 := by
      have h1 := norm_add_le (c • u ω) (d • v ω)
      nlinarith [norm_nonneg (c • u ω + d • v ω), norm_nonneg (c • u ω),
        norm_nonneg (d • v ω)]
    have h6 : (‖c • u ω‖ + ‖d • v ω‖) ^ 2 ≤ 2 * ‖c • u ω‖ ^ 2 + 2 * ‖d • v ω‖ ^ 2 := by
      nlinarith [sq_nonneg (‖c • u ω‖ - ‖d • v ω‖)]
    rw [h2, h3] at h6
    nlinarith [h5, h6]

/-- Integrability of `‖x'_n - x_n‖²`. -/
theorem integrable_sub_sq_run (R : Run (Ω := Ω) f grad) (n : ℕ) :
    Integrable (fun ω => ‖R.base.X' n ω - R.base.X n ω‖ ^ 2) R.base.mu := by
  have h := integrable_norm_sq_lin (u := R.base.X' n) (v := R.base.X n) (c := 1) (d := -1)
    (R.base.ae_X' n) (R.base.ae_X n) (R.int_sqX' n) (R.int_sqX n)
  simpa [sub_eq_add_neg] using h

/-- Integrability of `‖x'_n - v‖²` for any `v`. -/
theorem integrable_sub_const_sq (R : Run (Ω := Ω) f grad) [IsFiniteMeasure R.base.mu] (v : E)
    (n : ℕ) : Integrable (fun ω => ‖R.base.X' n ω - v‖ ^ 2) R.base.mu := by
  have hc : Integrable (fun ω => ‖(fun _ : Ω => v) ω‖ ^ 2) R.base.mu := integrable_const _
  have h := integrable_norm_sq_lin (u := R.base.X' n) (v := fun _ : Ω => v) (c := 1) (d := -1)
    (R.base.ae_X' n) aestronglyMeasurable_const (R.int_sqX' n) hc
  simpa [sub_eq_add_neg] using h

/-- Integrability of `‖w_n‖²`. -/
theorem integrable_wvec_sq (R : Run (Ω := Ω) f grad) [IsFiniteMeasure R.base.mu] (xstar : E)
    (b : ℕ → ℝ) (a0 : ℝ) (n : ℕ) :
    Integrable (fun ω => ‖wvec R xstar b a0 n ω‖ ^ 2) R.base.mu := by
  have h := integrable_norm_sq_lin (u := fun ω => R.base.X' n ω - R.base.X n ω)
    (v := fun ω => R.base.X' n ω - xstar) (c := b n) (d := a0)
    ((R.base.ae_X' n).sub (R.base.ae_X n))
    ((R.base.ae_X' n).sub aestronglyMeasurable_const)
    (integrable_sub_sq_run R n) (integrable_sub_const_sq R xstar n)
  simpa [wvec] using h

/-! Theorem 18 is proved by the Lyapunov argument of Appendix E.2 with coefficients
`b(n) = n + n₀`, `a₀ = 2`, `P(n) = (α b(n) + η a₀) b(n)` and slack `k = 2η - α`; the
single-step estimate is isolated as `lyapunov_step`. -/

/-- Pointwise algebra of the momentum update: if `x_{n+1} = x'_n - η g` and
`x'_{n+1} = x_{n+1} + ρ(x'_n - α g - x_n)` and `(b(n+1) + a)ρ = b(n)`, then the
Lyapunov vector updates as `w_{n+1} = w_n - (α b(n) + η a) g`. -/
theorem wvec_step_pt {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : ℕ → ℝ) (a al eta rho : ℝ) (n : ℕ) (x xn1 x' xn1' g v : V)
    (hρ : (b (n + 1) + a) * rho = b n) (h1 : xn1 = x' - eta • g)
    (h2 : xn1' = xn1 + rho • (x' - al • g - x)) :
    b (n + 1) • (xn1' - xn1) + a • (xn1' - v)
      = (b n • (x' - x) + a • (x' - v)) - (al * b n + eta * a) • g := by
  subst h1
  rw [h2]
  rw [← hρ]
  module

/-- The a.e. evolution of the Lyapunov vector. -/
theorem wvec_step (R : Run (Ω := Ω) f grad) (xstar : E) (b : ℕ → ℝ) (a0 : ℝ) (n : ℕ)
    (hρ : (b (n + 1) + a0) * R.rho n = b n) :
    wvec R xstar b a0 (n + 1) =ᵐ[R.base.mu]
      fun ω => wvec R xstar b a0 n ω - (R.alpha * b n + R.eta * a0) • R.base.G n ω := by
  filter_upwards [(R.rec1 n), (R.rec2 n)] with ω h1 h2
  exact wvec_step_pt (x := R.base.X n ω) (x' := R.base.X' n ω) (xn1 := R.base.X (n + 1) ω)
    (xn1' := R.base.X' (n + 1) ω) (g := R.base.G n ω) (v := xstar) b a0 R.alpha R.eta
    (R.rho n) n (hρ) h1 h2

/-- **One step of the Lyapunov argument** for AGNES in the convex case, with general
coefficients `b(n)`, constant `a₀` and slack `k`: this is the system of inequalities
(10)–(12) of the proof of Theorem 18 (resp. (14)–(16) of the proof of Theorem 3),
namely

* `P(n) = (α b(n) + η a₀) b(n) =: ψ_n b(n)`  (built into the statement),
* `P(n+1) + k - P(n) ≤ ψ_n a₀`,
* `ψ_n² (1+σ²)/2 ≤ (P(n+1) + k) c_{η,σ,L}`,

together with the two convexity estimates `E[f(x'_n) - f(x*)] ≤ E⟪∇f(x'_n), x'_n - x*⟫`
and `E[f(x'_n) - f(x_n)] ≤ E⟪∇f(x'_n), x'_n - x_n⟫`, Lemma 16 and Lemma 15.

**Remaining obligation.**  The body of this estimate is the one genuinely unfinished
piece of the convex-case formalization: the bookkeeping of the four terms (value
increase, `k`-slack, momentum square, unbiasedness of `g'_n` against the predictable
test vector `w_n ∈ F_n`) is set up (`wvec_step`, `integrable_wvec_sq`, `moment_sq`,
`one_step_decrease`) but not yet assembled into the final chain of inequalities. -/
theorem lyapunov_step (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L) (hc : ConvexG f grad)
    (hL : 0 < L) (hη : 0 ≤ R.eta)
    {xstar : E} (hx : GlobalMin f xstar) (b : ℕ → ℝ) {a0 k : ℝ} (n : ℕ)
    (ha0 : 0 ≤ a0) (hk : 0 ≤ k) (hb : 0 ≤ b n) (hb1 : 0 ≤ b (n + 1))
    (hρ : ∀ m, (b (m + 1) + a0) * R.rho m = b m)
    (hψ : 0 ≤ R.alpha * b n + R.eta * a0)
    (hψ1 : 0 ≤ R.alpha * b (n + 1) + R.eta * a0)
    (hB : (R.alpha * b (n + 1) + R.eta * a0) * b (n + 1) + k
        - (R.alpha * b n + R.eta * a0) * b n ≤ (R.alpha * b n + R.eta * a0) * a0)
    (hC : (R.alpha * b n + R.eta * a0) ^ 2 * (1 + R.base.sigma ^ 2) / 2
        ≤ ((R.alpha * b (n + 1) + R.eta * a0) * b (n + 1) + k)
            * (R.eta * (1 - L * (1 + R.base.sigma ^ 2) * R.eta / 2))) :
    (R.alpha * b (n + 1) + R.eta * a0) * b (n + 1) * Fval R xstar (n + 1)
        + 1 / 2 * Wmom R xstar b a0 (n + 1)
      ≤ (R.alpha * b n + R.eta * a0) * b n * Fval R xstar n
        + 1 / 2 * Wmom R xstar b a0 n := by
  sorry

/-- **Theorem 18** (AGNES, convex case, `n₀` version).

Boundary cases: the paper's estimate is asymptotic in `n`, and it is stated for the
indices `n` with `n + n₀ > 0` (the denominator `α (n+n₀)²` vanishes at `n = n₀ = 0`,
which is admissible when `σ = 0`).  We add the hypothesis `0 < n + n₀` explicitly, and
`0 < α` since the bound is trivial for `α = 0` (gradient descent, Remark 19). -/
theorem agnes_convex_n0 (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hσ : 0 ≤ R.base.sigma)
    (hη : 0 < R.eta) (hηL : R.eta ≤ 1 / (L * (1 + R.base.sigma ^ 2)))
    (hαpos : 0 < R.alpha) (hα : R.alpha < R.eta / (1 + R.base.sigma ^ 2))
    {n0 : ℝ} (hn0 : 2 * R.base.sigma ^ 2 * R.eta / (R.eta - R.alpha * (1 + R.base.sigma ^ 2)) ≤ n0)
    (hρ : ∀ n : ℕ, R.rho n = ((n : ℝ) + n0) / ((n : ℝ) + n0 + 3))
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) (hpos : 0 < (n : ℝ) + n0) :
    (∫ ω, f (R.base.X n ω) ∂R.base.mu) - f xstar
      ≤ ((R.alpha * n0 + 2 * R.eta) * n0
            * (∫ ω, f (R.base.X 0 ω) - f xstar ∂R.base.mu)
          + 2 * (∫ ω, ‖R.base.X 0 ω - xstar‖ ^ 2 ∂R.base.mu))
        / (R.alpha * ((n : ℝ) + n0) ^ 2) := by
  sorry

/-- **Theorem 3** (AGNES, convex case, main version).  The paper's bound is stated for
`n ≥ 1` (the right hand side is `a₀²‖x₀-x*‖²/(2αn²)`, undefined at `n = 0`); we make
this explicit. -/
theorem agnes_convex (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hσ : 0 ≤ R.base.sigma)
    (hη : 0 < R.eta) (hηL : R.eta < 1 / (L * (1 + R.base.sigma ^ 2)))
    (hα : R.alpha = R.eta / (1 + R.base.sigma ^ 2))
    {a0 : ℝ}
    (ha0 : 2 * (1 - R.eta * L) / (1 - R.eta * L * (1 + R.base.sigma ^ 2)) ≤ a0)
    (hρ : ∀ n : ℕ, R.rho n = (n : ℝ) / ((n : ℝ) + 1 + a0))
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) (hn : 0 < n) :
    (∫ ω, f (R.base.X n ω) ∂R.base.mu) - f xstar
      ≤ a0 ^ 2 * (∫ ω, ‖R.base.X 0 ω - xstar‖ ^ 2 ∂R.base.mu)
        / (2 * R.alpha * (n : ℝ) ^ 2) := by
  sorry

/-- The universal choice `a₀ = 4` of Theorem 3 when `η ≤ 1/(L(1+2σ²))`. -/
theorem thm3_a0_four {L eta sigma : ℝ} (hL : 0 < L) (hη : 0 < eta) (hσ : 0 ≤ sigma)
    (h : eta ≤ 1 / (L * (1 + 2 * sigma ^ 2))) :
    2 * (1 - eta * L) / (1 - eta * L * (1 + sigma ^ 2)) ≤ 4 := by
  have hA : eta * L * (1 + 2 * sigma ^ 2) ≤ 1 := by
    have hpos : 0 < L * (1 + 2 * sigma ^ 2) := by positivity
    have h2 := (le_div_iff₀ hpos).mp h
    nlinarith [h2]
  rcases lt_or_ge 0 (1 - eta * L * (1 + sigma ^ 2)) with hpos | hnonpos
  · rw [div_le_iff₀ hpos]
    nlinarith [hA, sq_nonneg sigma]
  · have hzero : 1 - eta * L * (1 + sigma ^ 2) = 0 :=
      le_antisymm hnonpos (by nlinarith [hA, sq_nonneg sigma])
    rw [hzero, div_zero]
    norm_num

/-- **Theorem 1** (NAG, convex case): Nesterov's method accelerates only when
`σ < 1`.  The paper's estimate is for `n ≥ 1` (the right hand side is
`2E‖x₀-x*‖²/(ηn²)`), which we make explicit. -/
theorem nag_convex (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hσ : 0 ≤ R.base.sigma) (hσ1 : R.base.sigma < 1)
    (hη : 0 < R.eta) (hηL : R.eta ≤ (1 - R.base.sigma ^ 2) / (L * (1 + R.base.sigma ^ 2)))
    (hα : R.alpha = R.eta)
    (hρ : ∀ n : ℕ, R.rho n = (n : ℝ) / ((n : ℝ) + 3))
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) (hn : 0 < n) :
    (∫ ω, f (R.base.X n ω) ∂R.base.mu) - f xstar
      ≤ 2 * (∫ ω, ‖R.base.X 0 ω - xstar‖ ^ 2 ∂R.base.mu) / (R.eta * (n : ℝ) ^ 2) := by
  sorry

/-- **Theorem 7** (convexity without minimizers): the iterates still approach the
infimum in expectation along a subsequence, i.e. `liminf E[f(xₙ)] = inf f`.  We state
it as the existence of a subsequence converging to `m`, where `m` is *the* infimum:
both `m ≤ f` everywhere and `m` is sharp (`∀ ε > 0, ∃ x, f x < m + ε`).  Without the
sharpness hypothesis the statement would be false (`liminf ≥ m` always). -/
theorem agnes_no_minimizer (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad) (hL : 0 < L) (hσ : 0 ≤ R.base.sigma)
    (hη : 0 < R.eta) (hηL : R.eta < 1 / (L * (1 + R.base.sigma ^ 2)))
    (hα : R.alpha = R.eta / (1 + R.base.sigma ^ 2))
    {a0 : ℝ}
    (ha0 : 2 * (1 - R.eta * L) / (1 - R.eta * L * (1 + R.base.sigma ^ 2)) ≤ a0)
    (hρ : ∀ n : ℕ, R.rho n = (n : ℝ) / ((n : ℝ) + 1 + a0))
    {m : ℝ} (hm : ∀ x, m ≤ f x) (hmtight : ∀ ε : ℝ, 0 < ε → ∃ x, f x < m + ε) :
    ∃ (n : ℕ → ℕ), StrictMono n ∧
      Filter.Tendsto (fun k => (∫ ω, f (R.base.X (n k) ω) ∂R.base.mu)) Filter.atTop (nhds m) := by
  sorry

/-- **Remark 19**: gradient descent is the special case `α = 0` of the AGNES
analysis, in which case the Lyapunov polynomial `P` is linear in `n`. -/
theorem remark19_alpha_zero (al n0 eta : ℝ) (hα : al = 0) :
    (fun n : ℝ => (al * (n + n0) + 2 * eta) * (n + n0)) = fun n : ℝ => 2 * eta * (n + n0) := by
  funext n
  rw [hα]
  ring

end AGNES
