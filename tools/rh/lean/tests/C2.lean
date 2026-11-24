namespace NS
theorem dup : 1 = 1 := rfl
def loop : Nat → Nat
  | 0 => 0
  | n + 1 => loop n
end NS
namespace Other
theorem dup : 2 = 2 := rfl
end Other
