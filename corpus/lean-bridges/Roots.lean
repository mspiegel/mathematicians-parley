module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Parser.Command
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Roots and angles put in one form

What decides the page's arithmetic of square roots and of sine and cosine
at multiples of π, which `parley_real` calls (`RealTactics`).

Roots of distinct primes are independent over ℚ, so a number built from
roots of numerals has one form as a sum of rational multiples of products of
distinct prime roots. `parley_roots` puts each side in that form: each √n
of a numeral as k·√p·√q·…, the primes of n's square-free part
(`parley_roots_split`); denominators cleared; each side multiplied out, and
every √p·√p put as p (`sqrt_pow_ge_two`). An identity that holds is then
`ring`'s, and one that does not is left unproved. `parley_roots_order`
does the same for an order, squaring a side under a root and leaving
`nlinarith` each root's square and that it is not negative.

`parley_angles` puts each angle qπ of a sine or a cosine in the first
quadrant, its whole turns taken off and then π − x, x + π or 2π − x as its
quadrant has it, so that Mathlib's values at 0, π/6, π/4, π/3 and π/2
apply: sin(9π/4) = sin(π/4).
-/

public section

namespace Roots

/-- A power of a root brought down by two: √a^n = a·√a^(n − 2). -/
theorem sqrt_pow_ge_two (a : ℝ) (h : 0 ≤ a) (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt a ^ n = a * Real.sqrt a ^ (n - 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add, Real.sq_sqrt h]

/-- A root of a quotient as a root over a whole denominator:
√(a/b) = √(a·b)/b. -/
theorem sqrt_div_eq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt (a / b) = Real.sqrt (a * b) / b := by
  rw [Real.sqrt_eq_iff_mul_self_eq (div_nonneg ha hb.le) (by positivity)]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- n as k² times the primes of its square-free part, each once. -/
meta def squareFree (n : ℕ) : ℕ × List ℕ := Id.run do
  let mut k := 1
  let mut rest := n
  let mut primes : List ℕ := []
  let mut p := 2
  while p * p ≤ rest do
    if rest % (p * p) == 0 then
      k := k * p
      rest := rest / (p * p)
    else if rest % p == 0 then
      primes := primes ++ [p]
      rest := rest / p
      p := p + 1
    else
      p := p + 1
  if rest > 1 then primes := primes ++ [rest]
  return (k, primes)

open Lean Meta Elab Tactic

/-- The numerals n of each √n in an expression. -/
meta partial def sqrtNumerals (e : Expr) : MetaM (Array ℕ) := do
  let mut out := #[]
  if e.isAppOfArity ``Real.sqrt 1 then
    if let some n := e.appArg!.numeral? then
      out := out.push n
  match e with
  | .app f a => out := out ++ (← sqrtNumerals f) ++ (← sqrtNumerals a)
  | .lam _ t b _ | .forallE _ t b _ => out := out ++ (← sqrtNumerals t) ++ (← sqrtNumerals b)
  | .mdata _ b => out := out ++ (← sqrtNumerals b)
  | _ => pure ()
  return out

/-- Every √e in an expression. -/
meta partial def sqrtTerms (e : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  if e.isAppOfArity ``Real.sqrt 1 then out := out.push e.appArg!
  match e with
  | .app f a => out := out ++ (← sqrtTerms f) ++ (← sqrtTerms a)
  | .lam _ t b _ | .forallE _ t b _ => out := out ++ (← sqrtTerms t) ++ (← sqrtTerms b)
  | .mdata _ b => out := out ++ (← sqrtTerms b)
  | _ => pure ()
  return out

/-- Each √n of a numeral in the goal as k·√p·√q·…, the primes of n's
square-free part: √12 = 2·√3, √6 = √2·√3. -/
elab "parley_roots_split" : tactic => do
  let goal ← getMainTarget
  let found := (← sqrtNumerals (← instantiateMVars goal)).toList.eraseDups
  for n in found do
    let (k, primes) := squareFree n
    if k == 1 && primes.length ≤ 1 then continue
    let lit (m : ℕ) : TSyntax `term := Syntax.mkNumLit (toString m)
    let inner : TSyntax `term ← match primes with
      | [] => `((1 : ℝ))
      | p :: ps => ps.foldlM (fun acc q => `($acc * $(lit q))) (← `(($(lit p) : ℝ)))
    let product ← `((($(lit k) : ℝ) ^ 2 * $inner))
    let nlit := lit n
    evalTactic (← `(tactic|
      rw [show Real.sqrt ($nlit : ℝ) = Real.sqrt $product by norm_num]))
  evalTactic (← `(tactic|
    try simp (disch := first | positivity | norm_num) only
      [Real.sqrt_mul, Real.sqrt_sq, Real.sqrt_one]))

/-- For each √e of the goal, that it is not negative and that its square is
e, as hypotheses for `nlinarith`. -/
elab "parley_root_facts" : tactic => do
  let goal ← instantiateMVars (← getMainTarget)
  let mut seen : Array Expr := #[]
  for e in (← sqrtTerms goal) do
    if seen.any (· == e) then continue
    seen := seen.push e
    let s ← Lean.Elab.Term.exprToSyntax e
    evalTactic (← `(tactic| have := Real.sqrt_nonneg $s))
    evalTactic (← `(tactic| (try have := Real.sq_sqrt (show (0 : ℝ) ≤ $s by positivity))))

/-- The rational q of an angle qπ as the build writes one: π, n * π, π / d,
n * π / d. None for any other term. -/
meta def angleOf (e : Expr) : Option ℚ :=
  let isPi (x : Expr) := x.isConstOf ``Real.pi
  match e.getAppFnArgs with
  | (``HDiv.hDiv, #[_, _, _, _, a, d]) =>
    match d.numeral? with
    | some dn =>
      if isPi a then some (1 / (dn : ℚ))
      else match a.getAppFnArgs with
        | (``HMul.hMul, #[_, _, _, _, n, p]) =>
          if isPi p then (n.numeral?).map (fun nn => (nn : ℚ) / dn) else none
        | _ => none
    | none => none
  | (``HMul.hMul, #[_, _, _, _, n, p]) =>
    if isPi p then (n.numeral?).map (fun nn => (nn : ℚ)) else none
  | _ => if isPi e then some 1 else none

/-- Every sin(qπ) and cos(qπ) of an expression: the angle and q. -/
meta partial def angles (e : Expr) : Array (Expr × ℚ) := Id.run do
  let mut out := #[]
  if e.isAppOfArity ``Real.sin 1 || e.isAppOfArity ``Real.cos 1 then
    if let some q := angleOf e.appArg! then out := out.push (e.appArg!, q)
  match e with
  | .app f a => out := out ++ angles f ++ angles a
  | .lam _ t b _ | .forallE _ t b _ => out := out ++ angles t ++ angles b
  | .mdata _ b => out := out ++ angles b
  | _ => pure ()
  return out

/-- The angle rπ as Lean text, r a fraction. -/
meta def angleText (r : ℚ) : String :=
  if r == 0 then "0"
  else if r.num == 1 && r.den == 1 then "Real.pi"
  else if r.den == 1 then s!"{r.num} * Real.pi"
  else if r.num == 1 then s!"Real.pi / {r.den}"
  else s!"{r.num} * Real.pi / {r.den}"

/-- Each angle qπ of a sine or a cosine in the goal put in the first
quadrant, and Mathlib's values put in. -/
elab "parley_angles" : tactic => do
  let goal ← instantiateMVars (← getMainTarget)
  for (a, q) in angles goal do
    let turns := (q / 2).floor
    let r := q - 2 * turns
    -- The reference angle s in [0, π/2], and the way from it to r.
    let (s, way) :=
      if r ≤ 1/2 then (r, "")
      else if r ≤ 1 then (1 - r, "pi_sub")
      else if r ≤ 3/2 then (r - 1, "add_pi")
      else (2 - r, "two_pi_sub")
    let st := angleText s
    let rhs := match way with
      | "pi_sub" => s!"Real.pi - ({st})"
      | "add_pi" => s!"({st}) + Real.pi"
      | "two_pi_sub" => s!"-({st}) + 2 * Real.pi"
      | _ => st
    let full := if turns == 0 then rhs else s!"({rhs}) + ({turns} : ℕ) * (2 * Real.pi)"
    let aStx ← Lean.Elab.Term.exprToSyntax a
    let some eqn := (Parser.runParserCategory (← getEnv) `term full).toOption | continue
    let eqnStx : TSyntax `term := ⟨eqn⟩
    evalTactic (← `(tactic| rw [show $aStx = $eqnStx by ring]))
  evalTactic (← `(tactic| try simp only [Real.sin_add_nat_mul_two_pi,
    Real.cos_add_nat_mul_two_pi, Real.sin_pi_sub, Real.cos_pi_sub, Real.sin_add_pi,
    Real.cos_add_pi, Real.sin_add_two_pi, Real.cos_add_two_pi, Real.sin_neg, Real.cos_neg,
    Real.sin_pi_div_six, Real.cos_pi_div_six, Real.sin_pi_div_four, Real.cos_pi_div_four,
    Real.sin_pi_div_three, Real.cos_pi_div_three, Real.sin_pi_div_two, Real.cos_pi_div_two,
    Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi]))
  evalTactic (← `(tactic| try ring_nf))

end Roots

/-- Real arithmetic of roots: each root put as roots of primes, the
denominators cleared, each side multiplied out with every √p·√p as p. -/
macro "parley_roots" : tactic =>
  `(tactic| (
    (try simp (disch := first | positivity | norm_num) only [Roots.sqrt_div_eq])
    (try simp only [zpow_neg, zpow_ofNat, one_div])
    (try norm_num only)
    (try parley_roots_split)
    (try field_simp)
    (try ring_nf)
    (try simp (disch := first | positivity | norm_num) only
      [Roots.sqrt_pow_ge_two, Nat.reduceSub, pow_one, pow_zero, Real.sq_sqrt])
    (try ring_nf)
    (try norm_num)
    done))

/-- An order of roots: a side under a root squared, each product of roots
joined into one, and `nlinarith` with each root's facts. -/
macro "parley_roots_order" : tactic =>
  `(tactic| (
    (try rw [Real.lt_sqrt (by positivity)])
    (try rw [Real.sqrt_lt' (by positivity)])
    (try ring_nf)
    (try simp (disch := first | positivity | norm_num) only
      [Roots.sqrt_pow_ge_two, Nat.reduceSub, pow_one, pow_zero, Real.sq_sqrt])
    (try simp (disch := positivity) only [← Real.sqrt_mul])
    (try norm_num)
    parley_root_facts
    nlinarith))
