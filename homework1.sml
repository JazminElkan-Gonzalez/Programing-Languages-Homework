(*
Jazmin Gonzalez-Rivero
Jazmin.Gonzalez-Rivero@students.olin.edu
*)

fun scaleVec a [] = []
  | scaleVec a (x::xs) = (a*x)::(scaleVec a xs)

fun addVec [] [] = []
  | addVec (x::xs) (y::ys) = (x+y)::(addVec xs ys)
  | addVec _ _ = []

fun inner [] [] = 0
  | inner (x::xs) (y::ys) = (x*y) + (inner xs ys)
  | inner _ _ = 0


fun gcd 0 a = abs(a)
  | gcd b 0 = abs(b)
  | gcd a b = if abs(a) < abs(b) then gcd a (b mod a) else gcd b (a mod b)

fun lcm a b =  abs(a*b) div (gcd a b)

fun exp a 0 = 1
  | exp 0 n = 0
  | exp a n = if n > 0 then a * (exp a (n-1)) else 1

fun tetra a 0 = 1
  | tetra a n = if n > 0 then exp a (tetra a (n-1)) else 1

(* Qestion 2 *)

fun sum [] = 0
  | sum [x] = x
  | sum (x::xs) = x + sum (xs)

fun prod [] = 1
  | prod [x] = x
  | prod (x::xs) = x * prod(xs)

fun every_other [] = []
  | every_other [x] = [x]
  | every_other [x,y] = [x]
  | every_other (x::y::xs) = x::every_other xs

fun flatten [] = []
  | flatten [[]] = []
  | flatten (xs::xss) = xs @ flatten(xss) 

fun heads [] = []
  | heads [[]] = []
  | heads ([]::xss) = heads xss
  | heads ((x::xs)::xss) = x::(heads xss) 

fun tails [] = []
  | tails [[]] = []
  | tails ([]::xss) = tails xss
  | tails ((x::xs)::xss) = xs::(tails xss)

fun scaleMat y [] = []
  | scaleMat y (xs::xss) = (scaleVec y xs)::(scaleMat y xss)

fun addMat [] [] = []
    | addMat x [] = []
    | addMat [] y = []
    | addMat (x::xs) (y::ys) = (addVec x y)::(addMat xs ys)


exception TypeError of string

exception DivisionByZero of string

datatype value = VInt of int
         | VVec of int list
         | VMat of int list list
         | VRat of int * int

datatype expr = EInt of int
        | EVec of int list
        | EMat of int list list
        | EAdd of expr * expr
        | ESub of expr * expr
        | EMul of expr * expr
        | ENeg of expr
        | EDiv of expr * expr
 
fun simplifyRat (n,0) = raise DivisionByZero "simplifyRat"
  | simplifyRat (0,d) = VInt(0)
  | simplifyRat (n, 1) = VInt(n)
  | simplifyRat (n, d) = let val z = (gcd n d) in 
    if abs(d) = z then VInt(n div d) else if d < 0 then VRat (~(n div z), ~(d div z) ) else VRat (n div z, d div z ) end 

fun addRat (n1, d1) (n2, d2) = simplifyRat (n1 * d2 + n2 * d1 , d1 * d2)

fun mulRat (n1, d1) (n2, d2)  = simplifyRat (n1*n2, d1 * d2)

fun negRat (n1, d1) = simplifyRat ( ~n1, d1)

fun applyAdd (VInt i) (VInt j) = VInt (i+j)
  | applyAdd (VVec v) (VVec w) = VVec (addVec v w)
  | applyAdd (VMat m) (VMat n) = VMat (addMat m n)
  | applyAdd (VRat r) (VRat s) = (addRat r s)
  | applyAdd (VInt i) (VRat s) = (addRat (i,1) s)
  | applyAdd (VRat r) (VInt j) = (addRat r (j,1))
  | applyAdd _ _ = raise TypeError "applyAdd"

fun applyMul (VInt i) (VInt j) = VInt (i*j)
  | applyMul (VInt i) (VVec v) = VVec (scaleVec i v)
  | applyMul (VVec v) (VVec w) = VInt (inner v w)
  | applyMul (VInt i) (VMat n) = VMat (scaleMat i n)
  | applyMul (VRat r) (VRat s) = (mulRat r s)
  | applyMul (VInt i) (VRat s) = (mulRat (i,1) s)
  | applyMul (VRat r) (VInt j) = (mulRat r (j,1))
  | applyMul _ _ = raise TypeError "applyMul"

fun applyNeg (VInt i) = VInt (~ i)
  | applyNeg (VVec v) = VVec (scaleVec ~1 v)
  | applyNeg (VMat m) = VMat (scaleMat ~1 m)
  | applyNeg (VRat r) = (negRat r)

fun applySub a b = applyAdd a (applyNeg b)

fun applyDiv (VInt i) (VInt j) = simplifyRat (i, j)
  | applyDiv (VRat i) (VRat (jn, jd)) = mulRat i (jd,jn)
  | applyDiv (VInt i) (VRat (jn, jd)) = mulRat (i,1) (jd, jn)
  | applyDiv (VRat j) (VInt i) = mulRat j (1,i)
  | applyDiv _ _ = raise TypeError "applyDiv"


fun eval (EInt i) = VInt i
  | eval (EAdd (e,f)) = applyAdd (eval e) (eval f)
  | eval (ESub (e,f)) = applySub (eval e) (eval f)
  | eval (EMul (e,f)) = applyMul (eval e) (eval f)
  | eval (ENeg e) = applyNeg (eval e)
  | eval (EVec v) = VVec v
  | eval (EMat m) = VMat m
  | eval (EDiv (e,f)) = applyDiv (eval e) (eval f)