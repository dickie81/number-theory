namespace Low.Inner
private theorem pick : 1 + 1 = 2 := rfl
end Low.Inner
namespace Low
open Low.Inner in
theorem uses : 1 + 1 = 2 := pick
end Low
