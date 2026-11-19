/-
  Nesterov acceleration despite very noisy gradients -- formalization.

  Part 6: miscellaneous results -- the equivalence of the two AGNES
  formulations (Lemma 9), invariance under reparametrization (Lemma 10),
  the minibatch noise bound (Lemma 8), the non-convex case (Theorem 23),
  almost sure convergence (Corollary 5), the last iterate (Lemma 24) and
  batching (Remark 6).

  ### Status of the paper's claims in this development

  Proved (from the model of Part 2, `#print axioms` clean):
  * Appendix D: Lemmas 11, 12, 13 (convex case), 21, the gradient bound
    `‖∇f‖² ≤ 2L(f - inf f)` (Part 1); Lemmas 15 (3), (4) and 16 (Part 2).
  * Theorem 17 (GD, convex case, **any** reference point) and Theorem 22's
    objective rate (Part 3).
  * The parameter algebra of Theorem 18 (`thm18_quadratic_nonneg`) and the
    universal choice `a₀ = 4` of Theorem 3 (Part 4).
  * Fermat's rule at a minimizer, the decay-rate identity `1-√μψ = 2ρ/(1+ρ)`
    (Part 5).
  * Lemmas 9, 10 and 24, Remark 19 (this file).

  Outstanding (identifiable `sorry`s, statements as in the paper):
  * Theorem 17's "in particular" clause (`gd_convex_min`) and Theorem 22's
    almost sure / `L²` convergence of the iterates (`gd_pl_iterates`), Part 3.
  * The convex AGNES Lyapunov step (`lyapunov_step`) and Theorems 18, 3, 1, 7
    (Part 4).
  * Theorems 4, 2 and the parameter system (23)--(29) of Appendix F.2 (Part 5).
  * Lemma 8, Theorem 23 in both readings, Corollary 5, Remark 6 (this file).

  The two open points which are *not* merely a matter of bookkeeping are
  `agnes_nonconvex_printed` (the printed minimum is over `x_i`, the proof gives
  `x'_i`) and `gd_convex_min` (the printed constant is a factor `2` sharper than
  the direct Lyapunov consequence); both are documented at their declarations.
-/
import Proofs.Part5

noncomputable section

open MeasureTheory

namespace AGNES

/-! ### Lemma 9: equivalence of the two formulations of AGNES -/

section Formulations

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- **Lemma 9**: the two-step formulation (2) of AGNES is the elimination of the
velocity variable from the three-step formulation (3). -/
theorem agnes_formulations_equiv (al eta : ℝ) (rho : ℕ → ℝ) (g x x' v : ℕ → F)
    (hv0 : v 0 = 0) (hx' : ∀ n, x' n = x n + al • v n)
    (hstep : ∀ n, x (n + 1) = x' n - eta • g n)
    (hv : ∀ n, v (n + 1) = rho n • (v n - g n)) :
    x' 0 = x 0 ∧ ∀ n, x' (n + 1) = x (n + 1) + rho n • (x' n - al • g n - x n) := by
  constructor
  · rw [hx' 0, hv0, smul_zero, add_zero]
  · intro n
    have hαv : al • v n = x' n - x n := by rw [hx' n]; abel
    calc x' (n + 1) = x (n + 1) + al • v (n + 1) := hx' (n + 1)
      _ = x (n + 1) + al • (rho n • (v n - g n)) := by rw [hv n]
      _ = x (n + 1) + rho n • (al • (v n - g n)) := by rw [smul_comm]
      _ = x (n + 1) + rho n • (x' n - al • g n - x n) := by
            rw [smul_sub, hαv]
            congr 1
            abel

/-- **Lemma 10**: the scheme (5) depends on `γ₁, γ₂` only through the product
`γ₁γ₂` (the scheme (3) of AGNES is the case `γ₁ = α`, `γ₂ = 1`, and the
continuous-time scaling `γ₁ = γ₂ = √α` produces the same iterates). -/
theorem agnes_reparam_invariant (rho : ℕ → ℝ) (eta : ℝ) (g : ℕ → F)
    (x x' v xt xt' vt : ℕ → F) (c1 c2 C1 C2 : ℝ)
    (hprod : c1 * c2 = C1 * C2) (hx0 : x 0 = xt 0) (hv0 : c1 • v 0 = C1 • vt 0)
    (hx' : ∀ n, x' n = x n + c1 • v n) (hxt' : ∀ n, xt' n = xt n + C1 • vt n)
    (hstep : ∀ n, x (n + 1) = x' n - eta • g n)
    (hstept : ∀ n, xt (n + 1) = xt' n - eta • g n)
    (hv : ∀ n, v (n + 1) = rho n • (v n - c2 • g n))
    (hvt : ∀ n, vt (n + 1) = rho n • (vt n - C2 • g n)) (n : ℕ) :
    x n = xt n ∧ x' n = xt' n ∧ c1 • v n = C1 • vt n := by
  induction n with
  | zero =>
      exact ⟨hx0, by rw [hx' 0, hxt' 0, hx0, hv0], hv0⟩
  | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have h4 : x (n + 1) = xt (n + 1) := by rw [hstep n, hstept n, h2]
      have hvel : c1 • v (n + 1) = C1 • vt (n + 1) := by
        rw [hv n, hvt n, smul_comm c1 (rho n), smul_comm C1 (rho n)]
        congr 1
        rw [smul_sub, smul_sub, smul_smul, smul_smul, hprod, h3]
      refine ⟨h4, ?_, hvel⟩
      rw [hx' (n + 1), hxt' (n + 1), h4, hvel]

end Formulations

/-! ### Lemma 8: the minibatch noise bound -/

/-- **Lemma 8** (noise intensity), in the scalar-output case `k = 1`: for the
square loss `ℓ(h,y) = ‖h-y‖²` the variance of the single-sample gradient estimator
is bounded by `4C²(1+‖w‖)^{2p} R(w)`.

Faithfulness note: the bound of Lemma 8 is derived from the *global* bound
`‖∇_w h(w,x_i)‖² ≤ C²(1+‖w‖)^{2p}` on the parameter-gradient of the model (the
paper's statement reads `≤ C(1+‖w‖)^p`, but its proof multiplies two such factors
and ends with `4C²(1+‖w‖²)^{2p}`; with `≤ C(1+‖w‖)^p` the computation gives only
`4C(1+‖w‖)^p R(w)`).  We state the hypothesis in the form which makes the paper's
conclusion correct verbatim. -/
theorem lemma8_noise_intensity {W ι : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [Fintype ι] [Nonempty ι]
    (h : W → ι → ℝ) (dh : W → ι → W) (y : ι → ℝ) (C p : ℝ) (w : W)
    (hC : 0 ≤ C) (hgrad : ∀ i, ‖dh w i‖ ^ 2 ≤ C ^ 2 * (1 + ‖w‖) ^ (2 * p)) :
    (1 / (Fintype.card ι : ℝ)) *
        ∑ i, ‖(2 * (h w i - y i)) • dh w i
          - (1 / (Fintype.card ι : ℝ)) • ∑ j, (2 * (h w j - y j)) • dh w j‖ ^ 2
      ≤ 4 * C ^ 2 * (1 + ‖w‖) ^ (2 * p) *
        ((1 / (Fintype.card ι : ℝ)) * ∑ i, (h w i - y i) ^ 2) := by
  sorry

/-! ### Theorem 23: the non-convex case -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {f : E → ℝ} {grad : E → E}

/-- **Theorem 23** (non-convex case), **in the form justified by the proof of
Appendix G**: for suitable parameters the minimum of the squared gradient norms at
the *gradient evaluation points* `x'_i` over the first `n+1` steps decays like
`1/n`.

Faithfulness note: the telescoping identity of the proof bounds
`∑_{i≤n} E‖∇f(x'_i)‖²`, not `∑ E‖∇f(x_i)‖²`, so the minimum is taken over the
points `x'_i`; the printed statement of Theorem 23 has `x_i` and is recorded
separately as `agnes_nonconvex_printed`.  The initial velocity term is
`‖x'_0 - x_0‖²/(2αρ²)`, which is the value of the Lyapunov function
`f(x_0) + (1/(2αρ²))‖x'_0-x_0‖²` at `n = 0` in the form (2) of the scheme (the
paper writes `‖v_0‖²/(αρ²)` with `x'_0 - x_0 = α v_0`; the two agree as soon as
the scheme is initialized with `v_0 = 0`, and differ by a factor `2/α²` for a
general initial velocity, which the algorithm never uses). -/
theorem agnes_nonconvex (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hL : 0 ≤ L) (hσ : 0 ≤ R.base.sigma) (hη : 0 ≤ R.eta)
    (hηL : R.eta ≤ 1 / (L * (1 + R.base.sigma ^ 2)))
    (hα0 : 0 < R.alpha) (hα : R.alpha < R.eta / (1 + R.base.sigma ^ 2))
    {rho : ℝ} (hρ : ∀ n : ℕ, R.rho n = rho)
    (hρ1 : (L * R.alpha + 1) * rho ^ 2 ≤ 1)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (n : ℕ) :
    ∃ i, i ≤ n ∧
      (∫ ω, ‖grad (R.base.X' i ω)‖ ^ 2 ∂R.base.mu)
        ≤ 2 * (∫ ω, f (R.base.X 0 ω) - m
              + 1 / (2 * R.alpha * rho ^ 2) * ‖R.base.X' 0 ω - R.base.X 0 ω‖ ^ 2
            ∂R.base.mu)
          / ((n + 1) * (R.eta - R.alpha * (1 + R.base.sigma ^ 2))) := by
  sorry

/-- **Theorem 23** (non-convex case), **verbatim as printed**: the minimum of
`E‖∇f(x_i)‖²` over the returned iterates `x_0, …, x_n` decays like `1/n`.

**Remaining obligation.**  This is the paper's claim.  The proof printed in
Appendix G telescopes the Lyapunov decrements against `E‖∇f(x'_i)‖²`, i.e. it
establishes `agnes_nonconvex` for the gradient evaluation points.  Replacing
`x'_i` by `x_i` needs the "last iterate" comparison of Appendix I.1
(`E[f(x'_i)-f(x*)] ≤ E[f(x_{i+1})-f(x*)]/(1-3Lη)`, Lemma 24), which requires
`η < 1/(3L)`, a condition that is *not* among the hypotheses of Theorem 23.
Consequently the printed statement is recorded as an identified obligation, not
as a consequence of the displayed proof.  (As in `agnes_nonconvex`, the term
`E‖v_0‖²/(αρ²)` of the printed estimate vanishes for the algorithm, which starts
with `v_0 = 0`; we write the expectation of the objective alone.) -/
theorem agnes_nonconvex_printed (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hL : 0 ≤ L) (hσ : 0 ≤ R.base.sigma) (hη : 0 ≤ R.eta)
    (hηL : R.eta ≤ 1 / (L * (1 + R.base.sigma ^ 2)))
    (hα0 : 0 < R.alpha) (hα : R.alpha < R.eta / (1 + R.base.sigma ^ 2))
    {rho : ℝ} (hρ : ∀ n : ℕ, R.rho n = rho)
    (hρ1 : (L * R.alpha + 1) * rho ^ 2 ≤ 1)
    {m : ℝ} (hm : ∀ x, m ≤ f x) (n : ℕ) :
    ∃ i, i ≤ n ∧
      (∫ ω, ‖grad (R.base.X i ω)‖ ^ 2 ∂R.base.mu)
        ≤ 2 * (∫ ω, f (R.base.X 0 ω) - m ∂R.base.mu)
          / (((n : ℝ) + 1) * (R.eta - R.alpha * (1 + R.base.sigma ^ 2))) := by
  sorry

/-! ### Corollary 5: almost sure convergence -/

/-- **Corollary 5**: since the expected excess values are summable (`C/n²` or a
geometric sequence), the values converge to the infimum almost surely.

The hypotheses `0 ≤ C` and the integrability of `f ∘ xₙ` are the (implicit)
measurability/integrability assumptions needed to apply the Markov inequality
step of the proof; `(Ω,A,P)` is of course a probability space. -/
theorem corollary5_almost_sure (R : Run (Ω := Ω) f grad) {m C : ℝ}
    (hint : ∀ n, Integrable (fun ω => f (R.base.X n ω)) R.base.mu)
    (hC : 0 ≤ C) (hm : ∀ x, m ≤ f x)
    (hbound : ∀ n, (∫ ω, f (R.base.X n ω) ∂R.base.mu) - m ≤ C / ((n : ℝ) + 1) ^ 2) :
    ∀ᵐ ω ∂R.base.mu, Filter.Tendsto (fun n => f (R.base.X n ω)) Filter.atTop (nhds m) := by
  sorry

/-! ### Lemma 24: the last iterate -/

/-- **Lemma 24**: for small step sizes (`η < 1/(3L)`) the value at the gradient
evaluation point `x'_n` is comparable to the value at the returned point
`x_{n+1}`.  Hence the convergence guarantees stated for `x_n` transfer to `x'_n`
up to the factor `1/(1-3Lη)`.

The proof (see Appendix I.1) needs the *lower* estimate
`f(x-ηg) ≥ f(x) - η⟪g,∇f(x)⟫`, which is a consequence of convexity (the paper
states the lemma "in convex and strongly convex optimization"), so convexity is a
hypothesis; it is also used for `x = x_n`. -/
theorem lemma24_last_iterate (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hc : ConvexG f grad)
    (hL : 0 < L) (hη : 0 ≤ R.eta) (hη3 : 3 * L * R.eta < 1)
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) :
    (∫ ω, f (R.base.X' n ω) ∂R.base.mu) - f xstar
      ≤ ((∫ ω, f (R.base.X (n + 1) ω) ∂R.base.mu) - f xstar) / (1 - 3 * L * R.eta) := by
  haveI := R.base.prob
  have hden : 0 < 1 - 3 * L * R.eta := by linarith
  have hinner : Integrable (fun ω => inner ℝ (R.base.G n ω) (grad (R.base.X' n ω))) R.base.mu :=
    integrable_inner (R.base.ae_G n) (R.base.ae_grad n) (R.base.int_G n) (R.base.int_grad n)
  -- `‖∇f(x'_n)‖² ≤ 2L (f(x'_n) - f(x*))` in expectation
  have hgradb : (∫ ω, ‖grad (R.base.X' n ω)‖ ^ 2 ∂R.base.mu)
      ≤ 2 * L * ((∫ ω, f (R.base.X' n ω) ∂R.base.mu) - f xstar) := by
    have h1 : (∫ ω, ‖grad (R.base.X' n ω)‖ ^ 2 ∂R.base.mu)
        ≤ ∫ ω, 2 * L * (f (R.base.X' n ω) - f xstar) ∂R.base.mu :=
      integral_mono_ae (R.base.int_grad n)
        (((R.int_f' n).sub (integrable_const _)).const_mul (2 * L))
        (Filter.Eventually.of_forall fun ω => by
          have h := norm_grad_sq_le hs hL hx (R.base.X' n ω)
          linarith)
    have h2 : (∫ ω, 2 * L * (f (R.base.X' n ω) - f xstar) ∂R.base.mu)
        = 2 * L * ((∫ ω, f (R.base.X' n ω) ∂R.base.mu) - f xstar) := by
      rw [integral_const_mul, integral_sub (R.int_f' n) (integrable_const _), integral_const]
      simp
    rw [h2] at h1
    exact h1
  -- one step of gradient descent, lower bound: convexity
  have hlow : (∫ ω, f (R.base.X' n ω) ∂R.base.mu)
      - R.eta * (∫ ω, ‖grad (R.base.X' n ω)‖ ^ 2 ∂R.base.mu)
      ≤ ∫ ω, f (R.base.X (n + 1) ω) ∂R.base.mu := by
    rw [show (∫ ω, f (R.base.X (n + 1) ω) ∂R.base.mu)
        = ∫ ω, f (R.base.X' n ω - R.eta • R.base.G n ω) ∂R.base.mu from
      integral_congr_ae ((R.rec1 n).fun_comp f)]
    have hpt : ∀ ω, f (R.base.X' n ω)
        - R.eta * inner ℝ (R.base.G n ω) (grad (R.base.X' n ω))
        ≤ f (R.base.X' n ω - R.eta • R.base.G n ω) := by
      intro ω
      have h := hc (R.base.X' n ω) (R.base.X' n ω - R.eta • R.base.G n ω)
      have hstep : R.base.X' n ω - R.eta • R.base.G n ω - R.base.X' n ω
          = -(R.eta • R.base.G n ω) := by abel
      rw [hstep, inner_neg_right, inner_smul_right] at h
      have hcomm : inner ℝ (grad (R.base.X' n ω)) (R.base.G n ω)
          = inner ℝ (R.base.G n ω) (grad (R.base.X' n ω)) := real_inner_comm _ _
      rw [hcomm] at h
      linarith
    have hcomb : Integrable (fun ω => f (R.base.X' n ω)
        - R.eta * inner ℝ (R.base.G n ω) (grad (R.base.X' n ω))) R.base.mu :=
      (R.int_f' n).sub (hinner.const_mul R.eta)
    have hint2 : Integrable (fun ω => f (R.base.X' n ω - R.eta • R.base.G n ω)) R.base.mu :=
      (R.int_f (n + 1)).congr ((R.rec1 n).fun_comp f)
    have hle := integral_mono_ae hcomb hint2 (Filter.Eventually.of_forall hpt)
    rw [integral_sub (R.int_f' n) (hinner.const_mul R.eta), integral_const_mul] at hle
    rw [moment_cross R.base n] at hle
    exact hle
  have hFL : 0 ≤ (∫ ω, f (R.base.X' n ω) ∂R.base.mu) - f xstar := by
    have h1 : 0 ≤ ∫ ω, f (R.base.X' n ω) - f xstar ∂R.base.mu :=
      integral_nonneg fun ω => sub_nonneg.mpr (hx _)
    rw [integral_sub (R.int_f' n) (integrable_const _), integral_const] at h1
    simpa using h1
  have hmain : (1 - 3 * L * R.eta) * ((∫ ω, f (R.base.X' n ω) ∂R.base.mu) - f xstar)
      ≤ (∫ ω, f (R.base.X (n + 1) ω) ∂R.base.mu) - f xstar := by
    nlinarith [hlow, hgradb, hFL, hη, hL, mul_nonneg hη hFL,
      mul_le_mul_of_nonneg_left hgradb hη]
  rw [le_div_iff₀ hden]
  linarith [hmain]

/-! ### Remark 6: batching -/

/-- **Remark 6** (batching): with `c = √(μ/L) ∈ (0,1)` and batch size `n_b ≥ 1`,
`(1 - c/(1+σ²))^{n_b} ≤ 1 - c/(1+σ²/n_b)` provided
`n_b ≥ log(1 - c/(1+σ²/n_b)) / log(1 - c/(1+σ²))`; in particular the non-batched
bound is favourable. -/
theorem remark6_batching {c sigma : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hσ : 0 ≤ sigma)
    {nb : ℕ} (hnb : 1 ≤ nb)
    (hlog : Real.log (1 - c / (1 + sigma ^ 2 / nb))
      / Real.log (1 - c / (1 + sigma ^ 2)) ≤ (nb : ℝ)) :
    (1 - c / (1 + sigma ^ 2)) ^ nb ≤ 1 - c / (1 + sigma ^ 2 / nb) := by
  sorry

end AGNES
