import DHBallDefs

/-!
# The zero of the second Davenport–Heilbronn function at height `1650`: the states of the evaluator

`ctr` is the centre, and `st{i}` the state of `DHBall.run ctr` after the blocks `0, …, 1000·i − 1`. Written by
`scripts/gen_dh_ball_cert.py`; `DHSecondCert0` has the kernel recompute each state from the one
before.
-/

namespace DHBall.Sec

/-- The centre `23747444/10000000 + (16498708285/10000000) i`, with `5` squarings. -/
def ctr : Ctr := ⟨23747444, 10000000, 16498708285, 10000000, 5⟩

/-- The state after the blocks `0, …, 999`. -/
def st1 : St :=
  ⟨⟨10296896520737643875226875, 121955⟩,
    ⟨⟨1136137452555063915143358, 535247004270446⟩, ⟨6195332146392631189604, 535247010077578⟩⟩,
    ⟨⟨322752828875987069509602, 223149404741880⟩, ⟨1759963691844833218674, 223149429333318⟩⟩,
    ⟨⟨119154127789966378070793, 118955993006588⟩, ⟨-9939089216435702212483, 118956002737732⟩⟩,
    ⟨⟨-259546080140305919638895, 243658515270877⟩, ⟨-13482054525562891107443, 243658536420463⟩⟩,
    375228148735548644005403,
    508653249298457110784041⟩

end DHBall.Sec
