namespace Outer
open A (pick missing1 missing2)
open B (nothing_here)
theorem uses3 : 1 + 1 = 2 := pick
end Outer
