type polarity = Pos | Neg

let polneg = function Pos -> Neg | Neg -> Pos
let polmul = function Pos -> (fun p -> p) | Neg -> polneg

let pol_flip f pol x y = match pol with Pos -> f x y | Neg -> f y x

type variance =
| VPos | VNeg | VNegPos | VNone

let vjoin a b = match a, b with
  | VNone, x
  | x, VNone -> a
  | VPos, VPos -> VPos
  | VNeg, VNeg -> VNeg
  | VNeg, VPos
  | VPos, VNeg -> VNegPos
  | VNegPos, _
  | _, VNegPos -> VNegPos

let variance_of_pol = function Pos -> VPos | Neg -> VNeg

let vlte a b = (vjoin a b = b)
