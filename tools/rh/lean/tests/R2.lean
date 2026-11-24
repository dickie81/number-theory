open NS
def s : S :=
  { cpt := cpt
    val := f (cpt := cpt) }
theorem s_cpt : s.cpt = 5 := rfl
theorem s_val : s.val = 5 := rfl
