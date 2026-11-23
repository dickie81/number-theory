def slowSum : Nat → Nat
  | 0 => 0
  | n + 1 => slowSum n + 1
