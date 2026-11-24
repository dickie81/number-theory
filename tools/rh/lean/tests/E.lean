namespace Outer
def pick (n : Nat) : Nat := n
end Outer
namespace A
theorem pick : 1 + 1 = 2 := rfl
end A
namespace B
def pick (s : String) : String := s
end B
