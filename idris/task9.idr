%default total

main: (a: Nat) -> (b: Nat) -> maximum a (minimum a b) = a
main Z b = Refl
main a Z = rewrite minimumZeroZeroLeft a in
            rewrite maximumZeroNLeft a in Refl
main (S x) (S y) = rewrite main x y in Refl
