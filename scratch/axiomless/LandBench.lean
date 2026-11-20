import Tower

/-!
# What `Nat.land` costs the kernel, and what replacing it would cost

The certificate parts of this library's Linnik theorems depend on `propext` only through core's `Nat.land`
(LOG.md, entry 11). This file times, in the kernel, a loop of 200 000 steps that at each step calls nothing,
`Nat.land`, `Nat.mod`, or a 14-bit `and` written by recursion on a bound, which is what a replacement of
`Nat.land` inside the library would be. LOG.md, entry 12, has the reading.

The times are for one `example` at a time (keep one, comment out the others); the whole file takes 80 s.
`check.sh` does not run it.
-/

namespace LandBench

open Ax

/-- A 14-bit `and` by recursion on a bound. It depends on no axiom, and the kernel cannot hand it to GMP. -/
def andF : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, a, b => 2 * andF f (a / 2) (b / 2) + (a % 2) * (b % 2)

/-- It agrees with `Nat.land` on a sample. This theorem depends on `propext`: its statement names `Nat.land`. -/
theorem andF_eq_land : ∀ a : Fin 300, andF 14 (a.val * 53 % 16384) 5461 = Nat.land (a.val * 53 % 16384) 5461 := by
  decide +kernel

/-- `n` steps; each adds `op a` to the total, with both numbers evaluated before the next step. -/
def loop (op : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n + 1, a, acc => strict (acc + op a) (fun acc' => strict ((a * 7 + 3) % 16384) (fun a' => loop op n a' acc'))

set_option maxRecDepth 100000000

/-- 19.5 s: the loop alone. -/
example : loop (fun _ => 1) 200000 1 0 = loop (fun _ => 1) 200000 1 0 + 0 := by decide +kernel

/-- 19.6 s: `Nat.land` costs nothing that can be measured. The kernel computes it with GMP and never unfolds
`Nat.bitwise`, whose termination proof holds the axiom. -/
example : loop (fun a => Nat.land a 5461) 200000 1 0 = loop (fun a => Nat.land a 5461) 200000 1 0 + 0 := by
  decide +kernel

/-- 18.9 s: a mask by `2^k - 1` can be a remainder, which depends on no axiom, at the same cost. -/
example : loop (fun a => Nat.mod a 16) 200000 1 0 = loop (fun a => Nat.mod a 16) 200000 1 0 + 0 := by
  decide +kernel

/-- 22.3 s: the hand-written `and` adds 2.8 s over the 200 000 steps, about 10 µs a call. -/
example : loop (fun a => andF 14 a 5461) 200000 1 0 = loop (fun a => andF 14 a 5461) 200000 1 0 + 0 := by
  decide +kernel

end LandBench

#axiom_free LandBench.andF LandBench.loop
