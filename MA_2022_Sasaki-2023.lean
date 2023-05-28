
import analysis.calculus.deriv analysis.special_functions.exp_deriv ring_theory.non_zero_divisors algebra.group.basic
/-
analysis.calculus.deriv contains definitions and theorems about derivatives
analysis.special_functions.exp_deriv contains definitions and theorems about the exponential function and its derivatives
ring_theory.non_zero_divisors contains definitions and theorems about domains (of which ℝ is one)
algebra.group.basic contains definitions and theorems about groups (of which ℝ is one)
-/

open real
/-
this line lets us use definitions and theorems about the real numbers, previously formalized in lean by others of the community
-/

noncomputable def D (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x : ℝ, deriv f x
/-
the derivative is defined in Lean differently than the derivative in a usual calculus class
this definition above treats the derivative as an operator on functions
it was easier to formalize the theorem in Lean with the derivative as we expect it
-/

lemma D_add {f g : ℝ → ℝ} (df : differentiable ℝ f) (dg : differentiable ℝ g) : D (f + g) = D f + D g :=
  funext (λ x, calc
      _ = deriv (λ y : ℝ, f y + g y) x  : by refl
    ... = deriv f x + deriv g x         : by rw deriv_add (df x) (dg x))
/-
this lemma states that the D operator behaves as we expect on a sum of functions
-/

lemma D_mul {f g : ℝ → ℝ} (df : differentiable ℝ f) (dg : differentiable ℝ g) : D (f * g) = D f * g + f * D g :=
  funext (assume x, calc
      _ = deriv (λ y : ℝ, f y * g y) x           : by refl -- this line is necessary for some reason
    ... = (deriv f x) * g x + (f x) * deriv g x  : by rw deriv_mul (df x) (dg x))
/-
this lemma states that the D operator behaves as we expect on a product of functions, via the product rule
-/

lemma second_D_mul {f g : ℝ → ℝ} (df : differentiable ℝ f) (d₂f : differentiable ℝ (D f)) (dg : differentiable ℝ g) (d₂g : differentiable ℝ (D g)) :
D (D (f * g)) = D (D f) * g + 2 * D f * D g + f * D (D g) :=
  let f' := D f in
  let f'' := D f' in
  let g' := D g in
  let g'' := D g' in
  have h₁ : differentiable ℝ (f' * g), from differentiable.mul d₂f dg,
  have h₂ : differentiable ℝ (f * g'), from differentiable.mul df d₂g,
  show D (D (f * g)) = f'' * g + 2 * f' * g' + f * g'', from calc
    D (D (f * g)) = D (f' * g + f * g')            : by rw D_mul (df) (dg)
    ... = D (f' * g) + D (f * g')                  : by rw D_add h₁ h₂
    ... = f'' * g + f' * g' + D (f * g')           : by rw D_mul d₂f dg
    ... = f'' * g + f' * g' + (f' * g' + f * g'')  : by rw D_mul df d₂g
    ... = f'' * g + f' * g' + f' * g' + f * g''    : by rw add_assoc (f'' * g + f' * g') (f' * g') (f * g'')
    ... = f'' * g + 2 * (f' * g') + f * g''        : begin rw two_mul (f' * g'), rw add_assoc (f'' * g) (f' * g') (f' * g') end
    ... = f'' * g + 2 * f' * g' + f * g''          : by rw mul_assoc 2 f' g'
/-
this lemma states that the D operator behaves as we expect when applied twice to a product of functions
-/

lemma exp_D {f : ℝ → ℝ} (df : differentiable ℝ f) : D (λ x : ℝ, exp (f x)) = λ x : ℝ, exp (f x) * D f x :=
  funext (assume x, deriv_exp (df x))
/-
this lemma states that the D operator behaves as we expect on the exponential function
-/

lemma const_mul_D (a : ℝ) : D (λ x : ℝ, a * x) = λ x : ℝ, a :=
  have h₁ : ∀ x : ℝ, (a * id x = (λ y : ℝ, a * y) x), begin assume x, rw id.def end,
  funext (assume y, (calc
      _ = deriv (λ x : ℝ, a * x) y                    : by refl
    ... = deriv (λ x : ℝ, a * (id x)) y               : by rw (funext h₁)
    ... = a * (deriv id y)                            : by rw (deriv_const_mul a (differentiable_id y) )
    ... = a * 1                                       : by rw deriv_id
    ... = a                                           : by rw mul_one))
/-
this lemma states that the D operator behaves as we expect on the function a*x, returning the constant a function
-/

def redington (f : ℝ → ℝ) (x : ℝ) : Prop := f x = 0 ∧ D f x = 0 ∧ D (D f) x > 0
/-
this definition defines what it means for a function to satisfy Redington immunization at a point
-/

lemma redington_implies {f : ℝ → ℝ} {x : ℝ} (h0: f x = 0) (h1: D f x = 0)  (h2:D (D f) x > 0) : redington f x :=
  and.intro h0 (and.intro h1 h2)
/-
this thing I've called a "theorem" just rewrites the conditions for satisfying Redington immunization as nested conditional statements instead of a nested conjunction
if you're familiar with the terminology, all I've done here is a form of "currying"
-/


lemma hf2_justification  {f g₀ : ℝ → ℝ} {δ : ℝ}
(df : differentiable ℝ f) (dg₀ : differentiable ℝ g₀) (hf : f δ = 0) (hg₀ : 0 < g₀ δ)
(hg : (D (f * g₀)) δ = 0) :
(D f) δ = 0 := 

  let g := (f * g₀) in
  have h₁ : D g = D f * g₀ + f * D g₀,            begin apply (D_mul df dg₀) end,
  have h₂ : D g δ = (D f * g₀ + f * D g₀) δ,      begin rw h₁ end,
  have h₃ : D f δ * g₀ δ + f δ * D g₀ δ = D g δ,  begin apply eq.symm, rw h₂, refl end,
  have h₄ : D f δ * g₀ δ = 0,                     begin rw hf at h₃, simp at h₃, rw hg at h₃, rw h₃ end,
  have g₀_ne_zero : g₀ δ ≠ 0, from                ne_of_gt hg₀,
  eq_zero_of_ne_zero_of_mul_right_eq_zero g₀_ne_zero h₄
  
lemma d₂g_form_simplified_justification {f g₀ : ℝ → ℝ} {δ : ℝ}
(df : differentiable ℝ f) (d₂f : differentiable ℝ (D f))
(dg₀ : differentiable ℝ g₀) (d₂g₀ : differentiable ℝ (D g₀)) (hf : f δ = 0) (hf' : (D f) δ = 0) :
let g := f * g₀ in (D (D g)) δ = (D (D f)) δ * g₀ δ := 
let g := f * g₀ in
  show (D (D g)) δ = (D (D f)) δ * g₀ δ, from calc
    (D (D g)) δ = D (D (f * g₀)) δ : rfl
    ... = (D (D f) * g₀    + 2 * D f * D g₀     + f * D (D g₀)) δ   : by rw second_D_mul df d₂f dg₀ d₂g₀
    ... = D (D f) δ * g₀ δ + 2 * D f δ * D g₀ δ + f δ * D (D g₀) δ  : by refl
    ... = D (D f) δ * g₀ δ + 2 * D f δ * D g₀ δ +   0 * D (D g₀) δ  : by rw hf
    ... = D (D f) δ * g₀ δ + 2 * 0     * D g₀ δ +   0 * D (D g₀) δ  : by rw hf'
    ... = (D (D f)) δ * g₀ δ : by ring

lemma hf1_justification  {f g₀ : ℝ → ℝ} {δ : ℝ}
  (hg : (f * g₀) δ = 0) (g₀_pos : 0 < g₀ δ):
  f δ = 0 :=
let g := f * g₀ in
  have h₁ : f δ * g₀ δ = 0, begin apply eq.symm, rw ←hg, refl end,
  have g₀_ne_zero : g₀ δ ≠ 0, from ne_of_gt g₀_pos,
  eq_zero_of_ne_zero_of_mul_right_eq_zero g₀_ne_zero h₁

/-
now the above four lemmas state things very specific to the proof below, and were mostly moved out as lemmas to save space/readability and to prevent a recurrent "deterministic timeout" error that occurs sometimes when a single proof gets too long
-/

theorem g_form_implies_redington_f_iff_g {f : ℝ → ℝ} {t δ: ℝ}
  (df : differentiable ℝ f)
  (d₂f : differentiable ℝ (D f)):
  let g := λ x : ℝ, (f x) * exp (t * x) in (redington f δ ↔ redington g δ) :=
let g := λ x : ℝ, (f x) * exp (t * x) in
  -- these lines allow me to use shorthands for pieces of the function g and shorthands for derivatives
  let g₀_arg   := λ x : ℝ, t * x        in
  let g₀_arg'  := D g₀_arg              in
  let g₀       := λ x : ℝ, exp (t * x)  in
  let g₀'      := D g₀                  in
  let g₀''     := D g₀'                 in
  let f'       := D f                   in
  let f''      := D f'                  in
  let g'       := D g                   in
  let g''      := D g'                  in


  have g_form_at_δ : g δ = (f δ) * (g₀ δ), begin refl,end, -- g(δ) = f(δ) * g₀(δ)

  -- these "have" statements prove a bunch of facts about the differentiability of pieces of g
  have dg₀_arg : differentiable ℝ g₀_arg, from differentiable.const_mul (differentiable_id) t,
  have dg₀ : differentiable ℝ g₀, from differentiable.exp dg₀_arg,
  have dg₀_arg_form : D g₀_arg = λ x : ℝ, t, begin rw (const_mul_D t) end,
  have dg₀_form_lemma : ∀ y : ℝ, (λ (x : ℝ), exp (g₀_arg x) * (λ (x : ℝ), t) x) y = (λ (x : ℝ), t * exp (t * x)) y, from
    (assume y, calc
      (λ (x : ℝ), exp (g₀_arg x) * (λ (x : ℝ), t) x) y = exp (g₀_arg y) * t  : by refl
      ... = exp (t * y) * t                                                  : by refl
      ... = t * exp (t * y)                                                  : by rw mul_comm t (exp (t * y))
      ... = (λ x : ℝ, t * exp (t * x)) y                                     : by refl),
  have dg₀_form : D g₀ = λ x : ℝ, t * exp (t * x), begin rw (exp_D dg₀_arg), repeat {rw dg₀_arg_form}, apply funext dg₀_form_lemma end,
  have d₂g₀ : differentiable ℝ (D g₀), begin rw dg₀_form, apply differentiable.mul (differentiable_const t) (dg₀) end,

  have g₀_pos : 0 < g₀ δ , from exp_pos (t * δ), -- this line proves that e^(t * x) is positive for x = δ

  /-
  from here, two main "have" statements are proved: one establishes the forward direction of the proof, and the other the reverse
  -/

  -- proving the forward direction
  have forward_dir : redington f δ → redington g δ, from
    assume hf : redington f δ,
    
    -- these three lines are from the premise that f satisfies Redington immunization at δ
    have hf1 : f δ = 0, from hf.1,
    have hf2 : f' δ = 0, from hf.2.1,
    have hf3 : f'' δ > 0, from hf.2.2,

    -- these statements prove that g satisfies the three conditions for Redington immunization at δ
    have hg1 : g δ = 0, begin rw g_form_at_δ, rw hf1, rw zero_mul end,
    have hg2 : g' δ = 0, from calc
      g' δ = D g δ                           : by refl
      ... = D (f * g₀) δ                     : by {refl,}
      ... = (D f * g₀ + f * D g₀) δ          : by rw (D_mul df dg₀)
      ... = (D f) δ * g₀ δ + f δ * (D g₀) δ  : by simp
      ... = 0 * g₀ δ + f δ * (D g₀) δ        : by rw ← hf2
      ... = 0 * g₀ δ + 0 * (D g₀) δ          : by rw hf1
      ... = 0 + 0                            : by repeat {rw zero_mul}
      ... = 0                                : by rw add_zero,
    have d₂g_form_simplified : g'' δ = f'' δ * g₀ δ, from (d₂g_form_simplified_justification df d₂f dg₀ d₂g₀ hf1 hf2),
    have hg3 : 0 < g'' δ, begin rw d₂g_form_simplified, apply (mul_pos hf3 g₀_pos) end,

    show redington g δ, from redington_implies hg1 hg2 hg3, -- this line uses the previous "have" statements to finish the proof of the forward direction

  -- proving the reverse direction
  have reverse_dir : redington g δ → redington f δ, from
    assume hg : redington g δ,

    have hg3 : g'' δ > 0, from hg.2.2,

    -- these statements prove that f satisfies the three conditions for Redington immunization at δ
    have hf1 : f δ = 0, from (hf1_justification hg.1 g₀_pos),
    have hf2 : f' δ = 0, from (hf2_justification df dg₀ hf1 g₀_pos hg.2.1),
    have d₂g_form_simplified : g'' δ = f'' δ * g₀ δ, from
      (d₂g_form_simplified_justification df d₂f dg₀ d₂g₀ hf1 hf2),
    have hf3 : f'' δ > 0, begin
      rw d₂g_form_simplified at hg3,
      apply pos_of_mul_pos_left (gt.lt hg3) (le_of_lt g₀_pos)
      end,

    redington_implies hf1 hf2 hf3, -- this line uses the previous "have" statements to finish the proof of the reverse direction
    
  iff.intro forward_dir reverse_dir -- this line combines the proof of the forward and reverse directions to finish the proof of the theorem
