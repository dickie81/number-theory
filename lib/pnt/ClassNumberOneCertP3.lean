/-
# The finite search of the class number one problem: part 3

Imports `ClassNumberOneCertDefs` only. Written by `scripts/gen_class_number_cert.py`. Each theorem is one kernel
computation, `decide +kernel`: `good n` for the `100 000` numbers `n = base + 8j`, `j < 100 000`. Parts `0` to `3`
together cover every `n ≡ 3 (mod 8)` from `171` to `25 600 163` (`ClassNumberOne.good_of_mod`).
-/
import ClassNumberOneCertDefs

namespace ClassNumberOneCert

theorem check_24 : checkDown 19200171 100000 = true := by decide +kernel
theorem check_25 : checkDown 20000171 100000 = true := by decide +kernel
theorem check_26 : checkDown 20800171 100000 = true := by decide +kernel
theorem check_27 : checkDown 21600171 100000 = true := by decide +kernel
theorem check_28 : checkDown 22400171 100000 = true := by decide +kernel
theorem check_29 : checkDown 23200171 100000 = true := by decide +kernel
theorem check_30 : checkDown 24000171 100000 = true := by decide +kernel
theorem check_31 : checkDown 24800171 100000 = true := by decide +kernel

end ClassNumberOneCert
