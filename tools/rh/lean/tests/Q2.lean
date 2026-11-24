open NS
open Chart (a b c)
theorem Q2.t : a + b = 3 := rfl
namespace Deep
open _root_.NS.Chart (a c) in
theorem t2 : a = 1 := rfl
end Deep
