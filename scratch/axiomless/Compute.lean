import Tower

/-!
# Proofs that run

`Ax.nextPrime` is Euclid's proof that there is a prime above `n`, and `Ax.factor` the proof that a positive number
is a product of primes. They depend on no axiom, so the kernel can evaluate them: each line below is checked by
the kernel reducing the proof term to a numeral or a list (`decide +kernel`).
-/

open Ax

/-! The prime that Euclid's proof finds above `n`: the least prime factor of `n! + 1`. -/
example : (nextPrime 1).val = 2 := by decide +kernel
example : (nextPrime 2).val = 3 := by decide +kernel
example : (nextPrime 3).val = 7 := by decide +kernel
example : (nextPrime 4).val = 5 := by decide +kernel
example : (nextPrime 5).val = 11 := by decide +kernel
example : (nextPrime 6).val = 7 := by decide +kernel
example : (nextPrime 7).val = 71 := by decide +kernel
example : (nextPrime 8).val = 61 := by decide +kernel
example : (nextPrime 9).val = 19 := by decide +kernel
example : (nextPrime 10).val = 11 := by decide +kernel
theorem nextPrime_12 : (nextPrime 12).val = 13 := by decide +kernel

/-! Factorizations. -/
theorem factor_360 : (factor 360 (by decide)).val = [2, 2, 2, 3, 3, 5] := by decide +kernel
theorem factor_5041 : (factor 5041 (by decide)).val = [71, 71] := by decide +kernel
theorem factor_30030 : (factor 30030 (by decide)).val = [2, 3, 5, 7, 11, 13] := by decide +kernel
theorem factor_1000001 : (factor 1000001 (by decide)).val = [101, 9901] := by decide +kernel

/-! Primality. -/
theorem prime_9901 : Prime 9901 := by decide +kernel
theorem not_prime_5041 : ¬ Prime 5041 := by decide +kernel

/-! `10! + 1 = 11 · 329891`. The kernel takes about two minutes: 329891 steps of the search. Uncomment to check.
theorem factor_fact10 : (factor 3628801 (by decide)).val = [11, 329891] := by decide +kernel
-/

#axiom_free nextPrime_12 factor_360 factor_5041 factor_30030 factor_1000001 prime_9901 not_prime_5041
