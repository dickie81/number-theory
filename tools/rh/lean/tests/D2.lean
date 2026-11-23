theorem NS.dup : 2 = 2 := _root_.Other.dup
namespace NS
def loop : Nat → Nat
  | 0 => 1
  | n + 1 => loop n + 1
theorem uses_loop : loop 2 = 3 := rfl
end NS
