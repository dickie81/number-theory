import Batteries.Tactic.OpenPrivate
namespace Foo
private theorem secret : 1 + 1 = 2 := rfl
private theorem other (n : Nat) : n + 0 = n := rfl
end Foo
