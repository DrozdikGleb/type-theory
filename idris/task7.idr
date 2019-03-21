%default total

sqr: Nat -> Nat
sqr a = a * a

lteSum: LTE a b -> LTE a' b' -> LTE (a + a') (b + b')
lteSum {a} {b} {a' = Z} first second =
    rewrite plusZeroRightNeutral a in
      lteTransitive first (lteAddRight b)
lteSum {a} {b} {a' = S x} {b' = S y} first second =
      let prev_proof = lteSum first (fromLteSucc second) in
          rewrite sym (plusSuccRightSucc a x) in
            rewrite sym (plusSuccRightSucc b y ) in
              LTESucc prev_proof

lteSqr: LTE a b -> LTE (sqr a) (sqr b)
lteSqr {a = Z} l = LTEZero
lteSqr {a = S x} {b = S y} l =
  let prev_proof = lteSqr (fromLteSucc l) in
    let prev_lte = fromLteSucc l in
      rewrite (multRightSuccPlus x x) in
        rewrite (multRightSuccPlus y y) in
          LTESucc (lteSum prev_lte (lteSum prev_lte prev_proof))

toMinusBack: LTE a b -> minus a b = 0
toMinusBack {a = Z} {b} l = Refl
toMinusBack {a = (S x)} {b = (S y)} l = toMinusBack (fromLteSucc l)

fromMinusToLTE: (a: Nat) -> (b: Nat) -> LTE (minus a b) (plus a b)
fromMinusToLTE Z b = LTEZero
fromMinusToLTE a Z = rewrite minusZeroRight a in
                      rewrite plusZeroRightNeutral a in lteRefl
fromMinusToLTE (S k) (S b) =
          rewrite plusSuccRightSucc k (S b) in
            rewrite plusCommutative k (S (S b)) in
              rewrite plusCommutative b k in
                lteSuccRight (lteSuccRight (fromMinusToLTE k b))

main: minus (sqr (minus a b)) (sqr (plus a b)) = 0
main {a} {b} = toMinusBack (lteSqr (fromMinusToLTE a b))
