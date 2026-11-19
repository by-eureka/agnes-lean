/-
  Nesterov acceleration despite very noisy gradients -- formalization.

  Part 5: the strongly convex case.  Theorem 4 (general `ψ` version of AGNES),
  Theorem 2 (NAG) and the parameter algebra of Step 5 of the proof of Theorem 4.
-/
import Proofs.Part4

noncomputable section

open MeasureTheory

namespace AGNES

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {f : E → ℝ} {grad : E → E}

/-! The paper uses `∇f(x*) = 0` at a minimizer `x*` (in Lemma 12 and in the
expansion of the Lyapunov functional).  We *derive* it from `GlobalMin` and
smoothness (Fermat's rule) instead of assuming it, so that the strongly convex
theorems below only assume that `x*` minimizes `f`. -/
theorem grad_xstar_eq_zero {L : ℝ} (hs : Smooth f grad L) (hL : 0 < L) {xstar : E}
    (hx : GlobalMin f xstar) : grad xstar = 0 :=
  grad_eq_zero_of_smooth_min hs hL hx

/-- **Theorem 4** (AGNES, strongly convex case, general version).  With
`0 < ψ ≤ √(η/(1+σ²))`, `ρ = (1-√μψ)/(1+√μψ)` and `α = ψ(ψ-η√μ)/(1-√μψ)` the
values converge geometrically with rate `1 - √μ ψ`.

Technical condition made explicit: the paper assumes `ρ ∈ (0,1)`, i.e. `√μ ψ < 1`
(the formulas for `ρ` and `α` degenerate in the limiting case `√μψ = 1`).  We also
assume `μ ≤ L`, as in the paper (`μ`-strong convexity together with `L`-smoothness). -/
theorem agnes_strong_convex (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hsc : StrongConvexG f grad mu) (hL : 0 < L) (hmu : 0 < mu)
    (hmuL : mu ≤ L) (hσ : 0 ≤ R.base.sigma) (hη : 0 < R.eta)
    (hηL : R.eta ≤ 1 / (L * (1 + R.base.sigma ^ 2)))
    {psi : ℝ} (hpsi : 0 < psi) (hpsi2 : psi ≤ Real.sqrt (R.eta / (1 + R.base.sigma ^ 2)))
    (hpsi1 : Real.sqrt mu * psi < 1)
    (hρ : ∀ n : ℕ, R.rho n = (1 - Real.sqrt mu * psi) / (1 + Real.sqrt mu * psi))
    (hα : R.alpha = (psi - R.eta * Real.sqrt mu) / (1 - Real.sqrt mu * psi) * psi)
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) :
    (∫ ω, f (R.base.X n ω) ∂R.base.mu) - f xstar
      ≤ (1 - Real.sqrt mu * psi) ^ n
        * (∫ ω, f (R.base.X 0 ω) - f xstar + mu / 2 * ‖R.base.X 0 ω - xstar‖ ^ 2
            ∂R.base.mu) := by
  sorry

/-- **Theorem 4** in the form stated in the main text (optimal parameters).  The
main-text formulas for `ρ` and `α` are those obtained by substituting the *optimal*
step size `η = 1/(L(1+σ²))` into the general version (Appendix F.2, item 2); we make
this hypothesis explicit (it is not claimed for smaller `η`, for which the general
version with the general `α` applies instead). -/
theorem agnes_strong_convex_main (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hsc : StrongConvexG f grad mu) (hL : 0 < L) (hmu : 0 < mu)
    (hmuL : mu ≤ L) (hσ : 0 ≤ R.base.sigma) (hη : 0 < R.eta)
    (hηopt : R.eta = 1 / (L * (1 + R.base.sigma ^ 2)))
    (hlt : Real.sqrt (mu * R.eta / (1 + R.base.sigma ^ 2)) < 1)
    (hρ : ∀ n : ℕ, R.rho n = (1 - Real.sqrt (mu * R.eta / (1 + R.base.sigma ^ 2)))
      / (1 + Real.sqrt (mu * R.eta / (1 + R.base.sigma ^ 2))))
    (hα : R.alpha = (1 - Real.sqrt (mu / L)) / (1 - Real.sqrt (mu / L) + R.base.sigma ^ 2)
      * R.eta)
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) :
    (∫ ω, f (R.base.X n ω) ∂R.base.mu) - f xstar
      ≤ 2 * (1 - Real.sqrt (mu * R.eta / (1 + R.base.sigma ^ 2))) ^ n
        * (∫ ω, f (R.base.X 0 ω) - f xstar ∂R.base.mu) := by
  sorry

/-- **Theorem 2** (NAG, strongly convex case): Nesterov's method accelerates only
for `σ < 1`; the parameter range is `η ≤ (1-σ²)/(L(1+σ²))` and
`ρ = (1-√(μη))/(1+√(μη))`.  As for Theorem 4 we assume `ρ > 0`, i.e. `√(μη) < 1`,
and `μ ≤ L`. -/
theorem nag_strong_convex (R : Run (Ω := Ω) f grad) (hs : Smooth f grad L)
    (hsc : StrongConvexG f grad mu) (hL : 0 < L) (hmu : 0 < mu)
    (hmuL : mu ≤ L) (hσ : 0 ≤ R.base.sigma) (hσ1 : R.base.sigma < 1) (hη : 0 < R.eta)
    (hlt : Real.sqrt (mu * R.eta) < 1)
    (hηL : R.eta ≤ (1 - R.base.sigma ^ 2) / (L * (1 + R.base.sigma ^ 2)))
    (hρ : ∀ n : ℕ, R.rho n = (1 - Real.sqrt (mu * R.eta)) / (1 + Real.sqrt (mu * R.eta)))
    (hα : R.alpha = R.eta)
    {xstar : E} (hx : GlobalMin f xstar) (n : ℕ) :
    (∫ ω, f (R.base.X n ω) ∂R.base.mu) - f xstar
      ≤ 2 * (1 - Real.sqrt (mu * R.eta)) ^ n
        * (∫ ω, f (R.base.X 0 ω) - f xstar ∂R.base.mu) := by
  sorry

/-! ### Step 5 of the proof of Theorem 4: verifying the parameter system -/

/-- The system of inequalities (23)–(29) of the proof of Theorem 4 is satisfied by
the parameter choices of the theorem, with `b = 1/ψ`, `a = √μ`, `c = b - a`.
(Inequality (29) of the paper, `(1+σ²)ψ²/2 ≤ η(1 - L(1+σ²)η/2)`, is weakened to
`(1+σ²)ψ² ≤ η`, which is what `ψ ≤ √(η/(1+σ²))` provides and what the proof
uses.) -/
theorem thm4_parameters {mu psi eta sigma : ℝ} (hmu : 0 < mu) (hpsi : 0 < psi)
    (hfac : Real.sqrt mu * psi < 1)
    (h29 : psi ^ 2 * (1 + sigma ^ 2) ≤ eta) :
    let b := 1 / psi
    let a := Real.sqrt mu
    let c := b - a
    let rho := (1 - Real.sqrt mu * psi) / (1 + Real.sqrt mu * psi)
    let alpha := psi * (psi - eta * Real.sqrt mu) / (1 - Real.sqrt mu * psi)
    c = (b + a) * rho ∧ psi = alpha * c + eta * a ∧ (c + a) * psi = 1 ∧
      c ^ 2 - c * psi * mu ≤ c * psi * b ^ 2 ∧ a * c = c * psi * a * b ∧
      a ^ 2 - a * psi * mu ≤ c * psi * a ^ 2 := by
  sorry

/-- The decay rate can be read off the momentum parameter: with
`ρ = (1-√μψ)/(1+√μψ)` one has `1 - √μ ψ = 2ρ/(1+ρ)` (Appendix F.2). -/
theorem decay_from_momentum {mu psi : ℝ} (hpsi : 0 < psi) (h : Real.sqrt mu * psi < 1) :
    (1 - Real.sqrt mu * psi) =
      2 * ((1 - Real.sqrt mu * psi) / (1 + Real.sqrt mu * psi))
        / (1 + (1 - Real.sqrt mu * psi) / (1 + Real.sqrt mu * psi)) := by
  have hs : 0 ≤ Real.sqrt mu := Real.sqrt_nonneg mu
  set s := Real.sqrt mu * psi with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hd : (1 + (1 - s) / (1 + s)) = 2 / (1 + s) := by
    field_simp
    ring
  rw [hd]
  field_simp

end AGNES
