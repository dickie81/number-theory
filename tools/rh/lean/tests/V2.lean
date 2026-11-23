set_option maxHeartbeats 2 in
theorem sum_eq : slowSum 30 = 30 := by
  simp [slowSum]
theorem again : slowSum 20 = 20 := by
  set_option maxHeartbeats 2 in
  simp [slowSum]
