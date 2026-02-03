import Mathlib
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex

-- Zeta series expansion (Re(s) > 1)
#find _ (riemannZeta ?s = ∑' n : ℕ, (n : ℂ) ^ (-?s))
#find _ (riemannZeta ?s = ∑' n : ℕ, if n = 0 then 0 else (n : ℂ) ^ (-?s))
#find _ (riemannZeta ?s = ∑' n : ℕ, (Nat.succ n : ℂ) ^ (-?s))

-- Functional equation / completed zeta
#find _ (riemannZeta (1 - ?s) = _)
#find _ (_ = riemannZeta (1 - ?s))
#find _ (_ = _ (1 - ?s))

-- Zero-free regions / non-vanishing statements
#find _ (0 < ?s.re → riemannZeta ?s ≠ 0)
#find _ (?s.re > 1 → riemannZeta ?s ≠ 0)
#find _ (riemannZeta ?s ≠ 0)
