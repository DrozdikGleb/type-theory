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

plusConstantLeft : (c: Nat) -> LTE a b -> LTE (c + a) (c + b)
plusConstantLeft Z l = l
plusConstantLeft (S x) l = LTESucc (plusConstantLeft x l)

helper: LTE (S (sqr x)) (sqr (S x))
helper {x} = LTESucc (
      rewrite multDistributesOverPlusRight x 1 x in
        rewrite multOneRightNeutral x in
          rewrite sym (multRightSuccPlus x x) in
            rewrite sym (plusZeroRightNeutral (sqr x)) in
              rewrite multRightSuccPlus x x in
                rewrite plusCommutative x (sqr x) in
                  rewrite plusCommutative x (plus (sqr x)  x) in
                    rewrite sym (plusAssociative (sqr x) x x) in
                      plusConstantLeft (sqr x) LTEZero )

-- [x^2 + 1 <= (x + 1) ^ 2] and [(x + 1)^2 <= b ^ 2] => [x ^ 2 + 1 <= b ^ 2]
fromLteSqrToAns: LTE (sqr (S x)) (sqr b) -> LTE (S (sqr x)) (sqr b)
fromLteSqrToAns l = lteTransitive helper l

main : GT a b -> GT (sqr a) (sqr b)
main l = fromLteSqrToAns (lteSqr l)
