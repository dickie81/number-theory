import A
open private Foo.secret other from A
theorem uses : 1 + 1 = 2 := Foo.secret
theorem uses2 : 5 + 0 = 5 := other 5
