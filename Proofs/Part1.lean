/-
  Nesterov acceleration despite very noisy gradients -- formalization.

  Part 1: basic definitions (L-smoothness, convexity, strong convexity, PL
  condition) and the deterministic auxiliary results of Appendix D
  (Lemmas 11, 12, 13 (convex case), Lemma 21, and the gradient bound
  `‖∇f‖² ≤ 2L(f - inf f)`).

  Throughout, `f : E → ℝ` is an objective function and `grad : E → E` is a
  *choice of gradient* for it.  Instead of assuming differentiability we assume
  the first order conditions (the descent lemma (6), convexity, strong
  convexity) which are the only properties used in the paper's arguments.
-/
import Mathlib

noncomputable section

namespace AGNES

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {f : E → ℝ} {grad : E → E} {L mu : ℝ} {xa x y v : E}

/-- `f` is `L`-smooth with gradient `grad`: the descent lemma (6) of the paper. -/
def Smooth (f : E → ℝ) (grad : E → E) (L : ℝ) : Prop :=
  ∀ x y, f y ≤ f x + inner ℝ (grad x) (y - x) + L / 2 * ‖y - x‖ ^ 2

/-- The first order characterization of convexity. -/
def ConvexG (f : E → ℝ) (grad : E → E) : Prop :=
  ∀ x y, f x + inner ℝ (grad x) (y - x) ≤ f y

/-- `μ`-strong convexity, first order form.  For `μ = 0` this is convexity. -/
def StrongConvexG (f : E → ℝ) (grad : E → E) (mu : ℝ) : Prop :=
  ∀ x y, f x + inner ℝ (grad x) (y - x) + mu / 2 * ‖y - x‖ ^ 2 ≤ f y

/-- `x` is a global minimizer of `f`. -/
def GlobalMin (f : E → ℝ) (x : E) : Prop := ∀ y, f x ≤ f y

/-- The Polyak–Łojasiewicz condition (21) with constant `mu` and minimum value `m`. -/
def PL (f : E → ℝ) (grad : E → E) (mu m : ℝ) : Prop :=
  ∀ x, mu * (f x - m) ≤ ‖grad x‖ ^ 2 / 2

/-- The elementary AM–GM bound `a z - (μ/2) z² ≤ a²/(2μ)` for `μ > 0`. -/
theorem amgm_sq {mu a z : ℝ} (hmu : 0 < mu) : a * z - mu / 2 * z ^ 2 ≤ a ^ 2 / (2 * mu) := by
  have hpos : (0 : ℝ) < 2 * mu := by linarith
  have key : a ^ 2 / (2 * mu) - (a * z - mu / 2 * z ^ 2) = (a - mu * z) ^ 2 / (2 * mu) := by
    field_simp
    ring
  have hnn : 0 ≤ (a - mu * z) ^ 2 / (2 * mu) := div_nonneg (sq_nonneg _) hpos.le
  linarith

/-- The scaling identity `‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2`. -/
theorem norm_smul_sq (c : ℝ) (v : E) : ‖c • v‖ ^ 2 = c ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-! ### Elementary consequences of convexity -/

/-- Convexity upgrades to monotonicity of the gradient. -/
theorem inner_grad_sub_nonneg (hc : ConvexG f grad) (x y : E) :
    0 ≤ inner ℝ (grad x - grad y) (x - y) := by
  have h1 := hc x y
  have h2 := hc y x
  rw [show y - x = -(x - y) from by abel, inner_neg_right] at h1
  rw [inner_sub_left]
  linarith

/-- Fermat's rule: at a global minimizer of a smooth function the gradient vanishes. -/
theorem grad_eq_zero_of_smooth_min (hs : Smooth f grad L) (hL : 0 < L) (hmin : GlobalMin f x) :
    grad x = 0 := by
  have h := hs x (x - (1 / L) • grad x)
  have hdiff : x - (1 / L) • grad x - x = -((1 / L) • grad x) := by abel
  rw [hdiff] at h
  have hinner : inner ℝ (grad x) (-((1 / L) • grad x)) = -(1 / L) * ‖grad x‖ ^ 2 := by
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖-((1 / L) • grad x)‖ ^ 2 = (1 / L) ^ 2 * ‖grad x‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / L)]
    ring
  rw [hinner, hnorm] at h
  have hmin' := hmin (x - (1 / L) • grad x)
  have hpos : (0 : ℝ) < 2 * L := by linarith
  have hsimpl : f x + -(1 / L) * ‖grad x‖ ^ 2 + L / 2 * ((1 / L) ^ 2 * ‖grad x‖ ^ 2) =
      f x - ‖grad x‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [hsimpl] at h
  have key : ‖grad x‖ ^ 2 / (2 * L) ≤ 0 := by linarith
  have hle : ‖grad x‖ ^ 2 ≤ 0 := by
    have := (div_le_iff₀ hpos).mp key
    simpa using this
  have hzero : ‖grad x‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hzero)

/-- **Lemma 12** (first part): at a minimizer, `f(x) - f(x*) ≤ (L/2)‖x - x*‖²`. -/
theorem value_sub_le (hs : Smooth f grad L) (hL : 0 < L) (hmin : GlobalMin f xa) (x : E) :
    f x - f xa ≤ L / 2 * ‖x - xa‖ ^ 2 := by
  have hg : grad xa = 0 := grad_eq_zero_of_smooth_min hs hL hmin
  have h := hs xa x
  rw [hg, inner_zero_left, add_zero] at h
  nlinarith [h]

/-- **Lemma 12** (second part): for a strongly convex function,
`(μ/2)‖x - x*‖² ≤ f(x) - f(x*)` at a minimizer. -/
theorem le_value_sub (hsc : StrongConvexG f grad mu) (hgrad : grad xa = 0) (x : E) :
    mu / 2 * ‖x - xa‖ ^ 2 ≤ f x - f xa := by
  have h := hsc xa x
  rw [hgrad, inner_zero_left, add_zero] at h
  nlinarith [h]

/-- The gradient bound `‖∇f‖² ≤ 2L (f - inf f)`, recorded after Lemma 12 in
Appendix D.  It is derived from the descent lemma applied to the point
`x - ∇f(x)/L`. -/
theorem norm_grad_sq_le (hs : Smooth f grad L) (hL : 0 < L) (hmin : GlobalMin f xa) (x : E) :
    ‖grad x‖ ^ 2 ≤ 2 * L * (f x - f xa) := by
  have h := hs x (x - (1 / L) • grad x)
  have hdiff : x - (1 / L) • grad x - x = -((1 / L) • grad x) := by abel
  rw [hdiff] at h
  have hinner : inner ℝ (grad x) (-((1 / L) • grad x)) = -(1 / L) * ‖grad x‖ ^ 2 := by
    rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hnorm : ‖-((1 / L) • grad x)‖ ^ 2 = (1 / L) ^ 2 * ‖grad x‖ ^ 2 := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / L)]
    ring
  rw [hinner, hnorm] at h
  have hmin' := hmin (x - (1 / L) • grad x)
  have hpos : (0 : ℝ) < 2 * L := by linarith
  have hsimpl : f x + -(1 / L) * ‖grad x‖ ^ 2 + L / 2 * ((1 / L) ^ 2 * ‖grad x‖ ^ 2) =
      f x - ‖grad x‖ ^ 2 / (2 * L) := by
    field_simp
    ring
  rw [hsimpl] at h
  have key : ‖grad x‖ ^ 2 / (2 * L) ≤ f x - f xa := by linarith
  have heq : ‖grad x‖ ^ 2 = (‖grad x‖ ^ 2 / (2 * L)) * (2 * L) := by
    field_simp
  rw [heq]
  calc ‖grad x‖ ^ 2 / (2 * L) * (2 * L) ≤ (f x - f xa) * (2 * L) :=
        mul_le_mul_of_nonneg_right key hpos.le
    _ = 2 * L * (f x - f xa) := by ring

/-- **Lemma 21**: `μ`-strong convexity implies the PL condition with constant `μ`. -/
theorem pl_of_strong_convex (hsc : StrongConvexG f grad mu) (hmu : 0 < mu)
    (hgrad : grad xa = 0) (x : E) :
    mu * (f x - f xa) ≤ ‖grad x‖ ^ 2 / 2 := by
  have key : f x - f xa ≤ ‖grad x‖ ^ 2 / (2 * mu) := by
    have h := hsc x xa
    have h1 : f x - f xa ≤ -inner ℝ (grad x) (xa - x) - mu / 2 * ‖xa - x‖ ^ 2 := by
      nlinarith [h]
    have h3 := abs_real_inner_le_norm (grad x) (xa - x)
    have h4 : -inner ℝ (grad x) (xa - x) ≤ |inner ℝ (grad x) (xa - x)| := neg_le_abs _
    have h5 : ‖grad x‖ * ‖xa - x‖ - mu / 2 * ‖xa - x‖ ^ 2 ≤ ‖grad x‖ ^ 2 / (2 * mu) :=
      amgm_sq hmu
    nlinarith [h1, h3, h4, h5]
  have hmul : mu * (f x - f xa) ≤ mu * (‖grad x‖ ^ 2 / (2 * mu)) :=
    mul_le_mul_of_nonneg_left key hmu.le
  have heq : mu * (‖grad x‖ ^ 2 / (2 * mu)) = ‖grad x‖ ^ 2 / 2 := by
    field_simp
  rwa [heq] at hmul

/-! ### Lemma 11: convex and smooth functions have Lipschitz gradients -/

/-- The affine modification `f - ⟪v, · - y⟫` used in the proof of Lemma 11. -/
def affineShift (f : E → ℝ) (v y : E) : E → ℝ := fun z => f z - inner ℝ v (z - y)

theorem affineShift_smooth (hs : Smooth f grad L) (v y : E) :
    Smooth (affineShift f v y) (fun z => grad z - v) L := by
  intro z z'
  have h := hs z z'
  have h1 : inner ℝ v (z' - y) = inner ℝ v (z' - z) + inner ℝ v (z - y) := by
    rw [← inner_add_right]; congr 1; abel
  have h2 : inner ℝ (grad z - v) (z' - z) = inner ℝ (grad z) (z' - z) - inner ℝ v (z' - z) :=
    inner_sub_left _ _ _
  show f z' - inner ℝ v (z' - y) ≤
    f z - inner ℝ v (z - y) + inner ℝ (grad z - v) (z' - z) + L / 2 * ‖z' - z‖ ^ 2
  linarith

theorem affineShift_convex (hc : ConvexG f grad) (v y : E) :
    ConvexG (affineShift f v y) (fun z => grad z - v) := by
  intro z z'
  have h := hc z z'
  have h1 : inner ℝ v (z' - y) = inner ℝ v (z' - z) + inner ℝ v (z - y) := by
    rw [← inner_add_right]; congr 1; abel
  have h2 : inner ℝ (grad z - v) (z' - z) = inner ℝ (grad z) (z' - z) - inner ℝ v (z' - z) :=
    inner_sub_left _ _ _
  show f z - inner ℝ v (z - y) + inner ℝ (grad z - v) (z' - z) ≤ f z' - inner ℝ v (z' - y)
  linarith

theorem affineShift_self (f : E → ℝ) (v y : E) : affineShift f v y y = f y := by
  simp [affineShift]

/-- Auxiliary estimate for Lemma 11: for the affine modification based at `u`, the
value at `z` exceeds the value at `u` by at least `‖∇f z - ∇f u‖²/(2L)`. -/
theorem shifted_bound (hs : Smooth f grad L) (hL : 0 < L) (hc : ConvexG f grad) (u z : E) :
    ‖grad z - grad u‖ ^ 2 / (2 * L) ≤ f z - inner ℝ (grad u) (z - u) - f u := by
  set g := affineShift f (grad u) u with hgd
  set G : E → E := fun w => grad w - grad u with hGd
  have hsg : Smooth g G L := affineShift_smooth hs (grad u) u
  have hcg : ConvexG g G := affineShift_convex hc (grad u) u
  have hG0 : G u = 0 := by simp [hGd]
  have hmin : GlobalMin g u := by
    intro w
    have h := hcg u w
    rw [hG0, inner_zero_left, add_zero] at h
    exact h
  have h := norm_grad_sq_le hsg hL hmin z
  have hz : g z = f z - inner ℝ (grad u) (z - u) := rfl
  have hu : g u = f u := affineShift_self f (grad u) u
  rw [hz, hu, hGd] at h
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * L)]
  linarith

/-- **Lemma 11**: a convex differentiable function satisfying (6) has `L`-Lipschitz
gradient. -/
theorem lipschitz_of_smooth_convex (hs : Smooth f grad L) (hL : 0 < L) (hc : ConvexG f grad)
    (x y : E) : ‖grad x - grad y‖ ≤ L * ‖x - y‖ := by
  have hA : ‖grad x - grad y‖ ^ 2 / (2 * L) ≤ f x - inner ℝ (grad y) (x - y) - f y :=
    shifted_bound hs hL hc y x
  have hB : ‖grad y - grad x‖ ^ 2 / (2 * L) ≤ f y - inner ℝ (grad x) (y - x) - f x :=
    shifted_bound hs hL hc x y
  rw [norm_sub_rev (grad y) (grad x)] at hB
  have hinner : inner ℝ (grad x - grad y) (x - y) =
      -inner ℝ (grad y) (x - y) - inner ℝ (grad x) (y - x) := by
    rw [inner_sub_left]
    have hxy : inner ℝ (grad x) (x - y) = -inner ℝ (grad x) (y - x) := by
      rw [← inner_neg_right]; congr 1; abel
    rw [hxy]; ring
  have hsum : ‖grad x - grad y‖ ^ 2 / L ≤ inner ℝ (grad x - grad y) (x - y) := by
    have heq : ‖grad x - grad y‖ ^ 2 / L =
        ‖grad x - grad y‖ ^ 2 / (2 * L) + ‖grad x - grad y‖ ^ 2 / (2 * L) := by
      field_simp; ring
    linarith [hA, hB, hinner, heq]
  have hcs : inner ℝ (grad x - grad y) (x - y) ≤ ‖grad x - grad y‖ * ‖x - y‖ :=
    real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (grad x - grad y)) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hL.le (norm_nonneg _)
  · have h1 : ‖grad x - grad y‖ ^ 2 / L ≤ ‖grad x - grad y‖ * ‖x - y‖ := by linarith
    rw [div_le_iff₀ hL] at h1
    nlinarith [hpos, norm_nonneg (x - y), hL]

/-- **Lemma 13** (convex case): the gradient may be evaluated at the *endpoint* of
the step.  For convex `f` this follows from (6) and monotonicity of the gradient. -/
theorem descent_endpoint_convex (hs : Smooth f grad L) (hc : ConvexG f grad) (x v : E) (al : ℝ) :
    f (x + al • v) ≤ f x + al * inner ℝ (grad (x + al • v)) v + L * al ^ 2 / 2 * ‖v‖ ^ 2 := by
  have h := hs x (x + al • v)
  have hstep : x + al • v - x = al • v := by abel
  rw [hstep, inner_smul_right, norm_smul_sq] at h
  have hmono := inner_grad_sub_nonneg hc (x + al • v) x
  rw [show (x + al • v) - x = al • v from by abel, inner_sub_left, inner_smul_right,
    inner_smul_right] at hmono
  linarith

end AGNES
