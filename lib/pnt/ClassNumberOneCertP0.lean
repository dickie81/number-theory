/-
# The finite search of the class number one problem: part 0

Imports `ClassNumberOneCertDefs` only. Written by `scripts/gen_class_number_cert.py`. Each theorem is one kernel
computation, `decide +kernel`: `good n` for the `100 000` numbers `n = base + 8j`, `j < 100 000`. Parts `0` to `3`
together cover every `n ≡ 3 (mod 8)` from `171` to `25 600 163` (`ClassNumberOne.good_of_mod`).
-/
import ClassNumberOneCertDefs

namespace ClassNumberOneCert

theorem check_0 : checkDown 171 100000 = true := by decide +kernel
theorem check_1 : checkDown 800171 100000 = true := by decide +kernel
theorem check_2 : checkDown 1600171 100000 = true := by decide +kernel
theorem check_3 : checkDown 2400171 100000 = true := by decide +kernel
theorem check_4 : checkDown 3200171 100000 = true := by decide +kernel
theorem check_5 : checkDown 4000171 100000 = true := by decide +kernel
theorem check_6 : checkDown 4800171 100000 = true := by decide +kernel
theorem check_7 : checkDown 5600171 100000 = true := by decide +kernel

end ClassNumberOneCert
