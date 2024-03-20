module NameResolution

import Data.Fin
import Data.Vect
import Data.Vect.Elem
import Data.List.Elem
import Data.Nat
import Decidable.Equality
-- import Generics.Derive

-- %language ElabReflection

-- Convert a language with names to use De Bruijn indices

Identifier = String

namespace Source

  public export
  data Expression : Type where
    Variable : String -> Expression
    Literal : Integer -> Expression
    Plus : Expression -> Expression -> Expression
    Let : String -> Expression -> Expression -> Expression
    Return : Expression -> Expression
    -- TODO more expresions
  %name Expression expr, expr1, expr2
  -- %runElab derive "Expression" [Generic, Meta, Eq, Show]

  public export
  example0 : Expression
  example0 = Let "x" (Plus (Literal 1) (Literal 1)) (Return (Plus (Variable "x") (Literal 2)))

  public export
  example1 : Expression
  example1 = Let "x" (Literal 1) (Let "x" (Literal 2) (Return (Variable "x")))


namespace Resolved

  public export
  data Expression : Nat -> Type where
    Variable : Fin n -> Expression n
    Literal : Integer -> Expression n
    Plus : Expression n -> Expression n -> Expression n
    Let : Expression n -> Expression (S n) -> Expression n
    Return : Expression n -> Expression n
    -- TODO more expresions
    
  implementation Show (Expression n) where
    show (Variable x) = "Variable " ++ show x
    show (Literal i) = "Literal " ++ show i
    show (Plus x y) = "Plus (" ++ show x ++ ") (" ++ show y ++ ")"
    show (Let x y) = "Let " ++ show x ++ " (" ++ show y ++ ")"
    show (Return x) = "Return (" ++ show x ++ ")"
  
  export
  testVect : String
  testVect = show $ the (Vect _ _) $ 1 :: 2 :: []
  testExpr : String
  testExpr = show $ the (Resolved.Expression 5) $ Literal 1
  Eq (Resolved.Expression n) where
  
    Variable idx1 == Variable idx2 = idx1 == idx2
    Literal lit1  == Literal lit2  = lit1 == lit2
    Plus l1 r1    == Plus l2 r2    = l1 == l2 && r1 == r2
    Let {n} ss1 e1   == Let {n} ass2 e2   = ?sdfkk
    Return e1     == Return e2     = e1 == e2
    _             == _             = False
  testEq : Bool
  testEq = (Resolved.Literal 1) == (Resolved.Literal {n=4} 1)

  public export
  example0 : Expression 0
  example0 = Let (Plus (Literal 1) (Literal 1)) (Return (Plus (Variable FZ) (Literal 2)))

  public export
  example1 : Expression 0
  example1 = Let (Literal 1) (Let (Literal 2) (Return (Variable FZ)))

namespace Set
  public export
  data Unique : Vect n a -> Type where
    IsUnique : {x: a} -> {xs: Vect n a} -> (prfHead: Not $ Elem x xs) -> (prfTail: Unique xs) -> Unique (x::xs)
    Empty : Unique []

  public export
  Set : Nat -> Type -> Type
  Set n a = (n ** xs: Vect n a ** Unique xs)

  public export
  data ElemSet : a -> Set n a -> Type where
    Here : {x: a} -> {xs: Vect k a} -> {prf: Unique (x::xs)} -> ElemSet x (S k ** x::xs ** prf)
    There : {x: a} -> {prfHead: Unique(y::xs)} -> ElemSet x (k ** xs ** prfTail) -> ElemSet x (S k ** y::xs ** prfHead)

  public export
  data SubsetSet : Set n a -> Set m a -> Type where
    IsIn : {xs: Vect k a} -> {prf: Unique (x::xs)} -> ElemSet x superset -> SubsetSet (S k ** x::xs ** prf) superset
    IsEmpty : SubsetSet (0 ** [] ** Empty) superset

  public export
  union : DecEq a => (in1: Set n a) -> (in2: Set m a) -> (k ** out: Set k a ** (SubsetSet in1 out, SubsetSet in2 out))

elemLengthPred : {n: Nat} -> {xs: Vect n a} -> (elem: Elem x xs) -> (m ** n = S m)
elemLengthPred {n = (S pred)} Here = (pred ** Refl)
elemLengthPred {n = (S pred)} (There later) = (pred ** Refl)

NilNoElems : Elem x [] -> Void
NilNoElems Here impossible
NilNoElems (There later) impossible

-- TODO: namespace resoluts in unresolved holes?
-- -- namespace FreeProofSet
-- data FreeSet : (free: Set n Identifier) -> (expr: Source.Expression) -> Type where
--   Variable : FreeSet (1 ** [name] ** IsUnique NilNoElems Empty) (Variable name)
--   Literal : FreeSet (0 ** [] ** Empty) (Literal i)
--   -- Plus : {lfree: Set k Identifier} -> {rfree: Set l Identifier} -> (FreeSet lfree lexpr) -> (FreeSet rfree rexpr) -> let (_ ** set ** _) = union lfree rfree in FreeSet set (Plus lexpr rexpr)
--   -- TODO: Could add random elements to free, what to do?
--   Plus : {lfree: Set k Identifier} -> {rfree: Set l Identifier} -> (FreeSet lfree lexpr) -> (FreeSet rfree rexpr) -> (free: Set m Identifier) -> (SubsetSet lfree free) -> (SubsetSet rfree free) -> FreeSet free (Plus lexpr rexpr)
--
-- getFreeSet : (expr: Source.Expression) -> (n: Nat ** free: Set n Identifier ** FreeSet free expr)
-- getFreeSet (Variable str) = (1 ** (1 ** [str] ** IsUnique NilNoElems Empty) ** Variable)
-- getFreeSet (Literal i) = (0 ** (0 ** [] ** Empty) ** Literal)
-- getFreeSet (Plus expr expr1) = let (_ ** lfree ** lprf) = getFreeSet expr
--                                    (_ ** rfree ** rprf) = getFreeSet expr1
--                                    (k ** free ** (lsubPrf, rsubPrf)) = union lfree rfree in
--                                    (k ** free ** (Plus lprf rprf free lsubPrf rsubPrf))
-- getFreeSet (Let str expr expr1) = ?getFreeSet_rhs_3
-- getFreeSet (Return expr) = ?getFreeSet_rhs_4
  

data Subset : (sub: Vect n a) -> (super: Vect m a) -> Type where
  IsIn : (Elem x super) -> Subset sub super -> Subset (x::sub) super
  IsEmpty : Subset [] super

data Free : (free: Vect n Identifier) -> (expr: Source.Expression) -> Type where
  Variable : Free [name] (Variable name)
  Literal : Free [] (Literal i)
  Plus : {lfree: Vect m Identifier} -> {rfree: Vect o Identifier} -> (Free lfree lexpr) -> (Free rfree rexpr) -> Free (lfree ++ rfree) (Plus lexpr rexpr)
  LetUsed : {pred: Nat} -> {afree: Vect m Identifier} -> {efree: Vect o Identifier} -> {name: Identifier} -> {assig: Source.Expression} -> {expr: Source.Expression}
         -> (Free afree assig) -> (Free efree expr) -> (prf: Elem name (afree++efree)) -> (predPrf: plus m o = S pred)
         -- -> let x = 1 in Free (dropElem (afree++efree) prf) (Let name assig expr)
         -> Free (dropElem (afree++efree) prf) (Let name assig expr)
  LetUnused : {afree: Vect n Identifier} -> {efree: Vect m Identifier} -> (Free afree assig) -> (Free efree assig) -> (prf: Not $ Elem name (afree++efree)) -> Free (afree++efree) (Let name assig expr)
  Return : (Free free expr) -> Free free (Return expr)

getFree : (expr: Source.Expression) -> (n: Nat ** free: Vect n Identifier ** Free free expr)
getFree (Variable str) = (1 ** [str] ** Variable)
getFree (Literal i) = (0 ** [] ** Literal)
getFree (Plus expr1 expr2) = case (getFree expr1, getFree expr2) of
                                 ((n1 ** free1 ** prf1), (n2 ** free2 ** prf2)) => (n1 + n2 ** free1 ++ free2 ** Plus prf1 prf2)
getFree (Let str expr expr1) = case getFree expr1 of
                                    (n' ** free' ** prf') => case (isElem str free') of
                                                                  (Yes prf) => let (S n'sub) = n' in (n'sub ** dropElem free' prf ** LetUsed prf' prf)
                                                                  (No contra) => (n' ** free' ** LetUnused prf' contra)
getFree (Return expr) = case getFree expr of
                             (n' ** free' ** prf') => (n' ** free' ** Return prf')

sdf_1 : {n : Nat} -> {succPrf: IsSucc n} -> {free: Vect n Identifier} -> Free free expr -> Free [] expr -> Void
sdf_1 Variable Literal impossible
sdf_1 Literal Literal impossible
sdf_1 (Plus x y) Literal impossible
sdf_1 (LetUsed x prf) Literal impossible
sdf_1 (LetUnused x prf) Literal impossible
sdf_1 (Return x) Literal impossible
sdf_1 {n = n@(S _)} {succPrf = ItIsSucc} {free = (dropElem free z)} (LetUsed y z) (LetUnused x prf) = sdf_1 {succPrf = ItIsSucc} y x
sdf_1 {n = n@(S _)} {succPrf = ItIsSucc} {free = free} (LetUnused y f) (LetUnused x prf) = sdf_1 {succPrf = ItIsSucc} y x
sdf_1 {n = n@(S _)} {succPrf = ItIsSucc} {free = free} (Return y) (Return x) = sdf_1 {succPrf = ItIsSucc} y x

AllBound : (expr: Source.Expression) -> Type
AllBound expr = Free [] expr
decAllBound : (expr: Source.Expression) -> Dec (AllBound expr)
decAllBound expr = case getFree expr of
                        (Z ** [] ** prf) => Yes prf
                        (S _ ** free ** prf) => No (sdf_1 {succPrf = ItIsSucc} prf)

superElem : (Subset sub super) -> (Elem x sub) -> (Elem x super)
superElem (IsIn y z) Here = y
superElem (IsIn y z) (There later) = superElem z later

subsetTransitive : (Subset subsub sub) -> (Subset sub super) -> (Subset subsub super)
subsetTransitive (IsIn elem z) y = ?subsetTransitive_rhs_0
subsetTransitive IsEmpty y = IsEmpty

concatIsSubset : {lxs: Vect n a} -> {rxs: Vect m a} -> {xs: Vect (n+m) a} -> ((lxs++rxs) = xs) -> Subset l xs

resolveWith : (expr: Source.Expression) -> (prf: Free [] expr) -> Resolved.Expression 0
resolveWith = resolveWith' [] [] IsEmpty
  where
    resolveWith' : (vars: Vect n Identifier) -> (free: Vect m Identifier) -> (subPrf: Subset free vars) -> (expr: Source.Expression) -> (prf: Free free expr) -> Resolved.Expression n
    resolveWith' free [name] subPrf (Variable name) Variable = Variable (elemToFin $ superElem subPrf $ Here) 
    resolveWith' vars [] subPrf (Literal i) Literal = ?resolveWith'_rhs_1
    resolveWith' vars (lfree ++ rfree) subPrf (Plus expr rexpr) (Plus {lfree} {rfree} x y) = Plus (resolveWith' vars lfree lSubPrf expr x) (resolveWith' vars rfree rSubPrf rexpr y)
      where lSubPrf : Subset lfree vars
            lSubPrf = subsetTransitive (concatIsSubset Refl) subPrf
            rSubPrf : Subset rfree vars
            rSubPrf = subsetTransitive (concatIsSubset Refl) subPrf
    resolveWith' vars (dropElem vars prf) subPrf (Let name assig expr) (LetUsed x prf) = ?lsdkjfl
    resolveWith' vars free subPrf (Let name assig expr) (LetUnused x prf) = ?resolveWith'_rhs_4
    resolveWith' free prffree subPrf (Return expr) (Return x) = Return (resolveWith' free prffree subPrf expr x)

||| Convert source epxression to de bruijin expressions
|||
||| @n number of currently available variables in the expression 
resolve : Source.Expression -> Vect n String -> Maybe (Resolved.Expression n)
resolve (Variable var) bound = case isElem var bound of
                                    (Yes prf) => pure $ Variable $ elemToFin prf
                                    (No contra) => Nothing
resolve (Literal i) bound = pure $ Literal i
resolve (Plus l r) bound = do
  l' <- resolve l bound
  r' <- resolve r bound
  pure $ Plus l' r'
resolve (Let var ass e) bound = do
  ass' <- resolve ass bound
  e' <- resolve e (var :: bound)
  pure $ Let ass' e'
resolve (Return e) bound = do
  e' <- resolve e bound
  pure $ Return e'

interpret : Resolved.Expression n -> Vect n Integer -> Integer
interpret (Variable x) xs = index x xs
interpret (Literal i) xs = i
interpret (Plus x y) xs = interpret x xs + interpret y xs
interpret (Let x y) xs = interpret y $ interpret x xs :: xs
interpret (Return x) xs = interpret x xs

testResolve : Bool
testResolve = and $ map (uncurry compareInterpretation) $ the (List _) $
  [ (Source.example0, Resolved.example0)
  , (Source.example1, Resolved.example1)
  ]
  where
    compareInterpretation : Source.Expression -> Resolved.Expression 0 -> Lazy Bool
    compareInterpretation source resolved = (flip interpret [] <$> resolve source []) == Just (interpret resolved [])

