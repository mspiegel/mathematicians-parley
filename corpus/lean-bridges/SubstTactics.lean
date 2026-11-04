module

public import Mathlib
public import Tactics

/-!
# What a `substitute` step leaves to rewriting

`parley_subst e` puts a term for another into the goal by the equation `e`,
and `parley_subst_at e h` into the line `h`, either way round. A generated
file imports this module only when it calls one of them.
-/

public section

/-- `substitute`, into the goal: the goal is what the equation `e` makes of
a term in it, either way round. -/
macro "parley_subst " e:term:max : tactic =>
  `(tactic| first
    | (rw [$e:term]; done)
    | (rw [← $e:term]; done)
    | (rw [$e:term]; ring1; done)
    | (rw [← $e:term]; ring1; done)
    | (simp only [$e:term]; done)
    | (simp only [← $e:term]; done)
    | (simp only [$e:term]; ring1; done)
    | (simp only [← $e:term]; ring1; done)
    | (linear_combination $e:term; done)
    | (linear_combination (-1 : _) * $e:term; done)
    | (have h := $e:term; norm_cast at h; rw [h]; done)
    | (have h := $e:term; norm_cast at h; rw [← h]; done)
    | (have h := $e:term; norm_cast at h; simp only [h]; done)
    -- A power put to an integer exponent beside one to a natural, x^0 of
    -- (m + 1) − (m + 1) beside x^0: each worked out.
    | (rw [$e:term]; norm_num; done))

/-- `parley_subst_at e h` by rewriting, with no `simp` by `e`. That loops where one side of
`e` stands inside the other, b in gcd(a, b), and `first` does not go on past
a loop, so a step offering several lines tries this on each before
`parley_subst_at` on any. -/
macro "parley_put_at " e:term:max h:ident : tactic =>
  `(tactic| first
    | (rw [$e:term] at $h:ident; exact $h; done)
    | (rw [← $e:term] at $h:ident; exact $h; done)
    -- `rw` closes a goal its rewriting leaves reflexive, b ∣ b, itself.
    | (rw [$e:term]; (try exact $h); done)
    | (rw [← $e:term]; (try exact $h); done)
    -- A fact of naturals, b > 0 as `0 < b`, put into by an equation of
    -- integers: the fact is taken up to ℤ first.
    | (have h' := $h; zify at h'; rw [← $e:term] at h'; exact h'; done)
    | (have h' := $h; zify at h'; rw [$e:term] at h'; exact h'; done)
    -- A fact or an equation of numerals alone, written in ℚ, put where
    -- the other is in ℝ, (√(1/4))² for 1/4: taken up to ℝ first.
    | (have h' := $h; rify at h'; first | (rw [← $e:term] at h'; exact h') | (rw [$e:term] at h'; exact h'); done)
    | (have e' := $e; rify at e'; first | (rw [← e'] at $h:ident; exact $h) | (rw [e'] at $h:ident; exact $h); done)
    -- An equation of naturals cast up to ℤ, put where ℕ is wanted, an
    -- exponent, is taken back down first.
    | (have e := $e; norm_cast at e; rw [← e] at $h:ident; exact $h; done)
    | (have e := $e; norm_cast at e; rw [e] at $h:ident; exact $h; done)
    | (rw [$e:term] at $h:ident; linarith; done)
    | (rw [← $e:term] at $h:ident; linarith; done)
    -- What the putting leaves to tidy, a 0 + x of a term put to 0.
    | (rw [$e:term] at $h:ident; simpa using $h; done)
    | (rw [$e:term] at $h:ident; parley_side; done)
    | (rw [← $e:term] at $h:ident; parley_side; done)
    | (rw [$e:term] at $h:ident; exact_mod_cast $h; done)
    | (rw [← $e:term] at $h:ident; exact_mod_cast $h; done)
    | (rw [← $e:term]; exact $h _; done)
    | (rw [$e:term]; exact $h _; done)
    | (exact $h _; done))

/-- `substitute` into the line `h`: the goal is `h` with a term put for
another by the equation `e`, either way round. -/
macro "parley_subst_at " e:term:max h:ident : tactic =>
  `(tactic| first
    | (parley_put_at $e $h; done)
    | (simp only [$e:term] at $h:ident ⊢; exact $h; done)
    | (simp only [← $e:term] at $h:ident ⊢; exact $h; done)
    | (simp only [$e:term] at $h:ident ⊢; linarith; done)
    | (simp only [← $e:term] at $h:ident ⊢; linarith; done)
    -- A listed set put into a subset, its members in another order than
    -- the claim's: member by member.
    | (rw [$e:term] at $h:ident; intro x hx; apply $h:ident;
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto))

end
