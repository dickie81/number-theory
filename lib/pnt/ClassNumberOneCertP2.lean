/-
# The finite search of the class number one problem: part 2

Imports `ClassNumberOneCertDefs` only. Written by `scripts/gen_class_number_cert.py`. Each theorem is one kernel
computation, `decide +kernel`: `good n` for the `100 000` numbers `n = base + 8j`, `j < 100 000`. Parts `0` to `3`
together cover every `n ≡ 3 (mod 8)` from `171` to `25 600 163` (`ClassNumberOne.good_of_mod`).
-/
import ClassNumberOneCertDefs

namespace ClassNumberOneCert

theorem check_16 : checkDown 12800171 100000 = true := by decide +kernel
theorem check_17 : checkDown 13600171 100000 = true := by decide +kernel
theorem check_18 : checkDown 14400171 100000 = true := by decide +kernel
theorem check_19 : checkDown 15200171 100000 = true := by decide +kernel
theorem check_20 : checkDown 16000171 100000 = true := by decide +kernel
theorem check_21 : checkDown 16800171 100000 = true := by decide +kernel
theorem check_22 : checkDown 17600171 100000 = true := by decide +kernel
theorem check_23 : checkDown 18400171 100000 = true := by decide +kernel

end ClassNumberOneCert
