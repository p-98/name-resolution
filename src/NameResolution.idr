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

