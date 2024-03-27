module NameResolution

import Control.Monad.Error.Either
import Control.Monad.Error.Interface
import Control.Monad.Identity
import Data.Fin
import Data.List
import Data.List.Elem
import Data.Nat
import Data.String
import Data.Vect
import Data.Vect.Elem
import Debug.Trace
import Decidable.Equality
-- import Generics.Derive

-- %language ElabReflection

-- Convert a language with names to use De Bruijn indices

{- In welche Richtung?

  Entweder proof oder Viele Expressions?
  Functions?
  Unterschiedliche Typen?

  Allgemein: Was ist der Erwartungshorizont für eine gute und eine sehr gute Note?
             Wie weit bin ich?
-}

namespace Helpers

  public export
  mapWithProof : (f: (a -> b)) -> (inp: Vect n a) -> (out: Vect n b ** out = map f inp)
  mapWithProof f inp = (map f inp ** Refl)

  public export
  implementation Uninhabited (x = y) => Uninhabited (y = x) where
    uninhabited eq = absurd (sym eq)

  public export
  decEqToEq : DecEq a => a -> a -> Bool
  decEqToEq x y with (decEq x y)
    decEqToEq x y | Yes _ = True
    decEqToEq x y | No _  = False

Identifier = String

namespace Core

  public export
  data Tyqe : Type where
    TInt : Tyqe
    TBool : Tyqe
  public export
  Show Tyqe where
    show TInt = "TInt"
    show TBool = "TBool"
  Uninhabited (TInt = TBool) where uninhabited Refl impossible
  public export
  DecEq Tyqe where
    decEq TInt TInt = Yes Refl
    decEq TBool TInt = No uninhabited
    decEq TInt TBool = No uninhabited
    decEq TBool TBool = Yes Refl

  public export
  data Value : Tyqe -> Type where
    VInt : Integer -> Value TInt
    VBool : Bool -> Value TBool
  %name Value v, w
  Injective VInt  where injective Refl = Refl
  Injective VBool where injective Refl = Refl
  public export
  Show (Value t) where
    show (VInt i) = show i
    show (VBool i) = show i
  public export
  DecEq (Value t) where
    decEq (VInt i) (VInt j) = decEqCong $ decEq i j
    decEq (VBool x) (VBool y) = decEqCong $ decEq x y
  public export
  Eq (Value t) where
    (==) = decEqToEq

  public export
  vtype : Value t -> (t' ** t' = t)
  vtype (VInt i) = (TInt ** Refl)
  vtype (VBool i) = (TBool ** Refl)

namespace Source

  public export
  data Expression : Type where
    Variable : (name: String) -> Expression
    Literal : Value t -> Expression
    Equals : (expr1: Expression) -> (expr2: Expression) -> Expression
    Plus : (expr1: Expression) -> (expr2: Expression) -> Expression
    Let : (name: String) -> (assig: Expression) -> Expression -> Expression
    Return : Expression -> Expression
    -- TODO more expresions
  %name Source.Expression expr, expr1, expr2
  -- %runElab derive "Expression" [Generic, Meta, Eq, Show]
  public export
  implementation Show Expression where
    show (Variable name) = "Variable " ++ name
    show (Literal v) = "Literal " ++ show v
    show (Equals expr1 expr2) = "Equals (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Plus expr1 expr2) = "Plus (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Let name assig expr) = "Let " ++ name ++ "=(" ++ show assig ++ ") in (" ++ show expr ++ ")"
    show (Return expr) = "Return (" ++ show expr ++ ")"
  public export
  implementation Eq Expression where
    (Variable n1) == (Variable n2) = n1 == n2
    (Literal (VInt i1)) == (Literal (VInt i2)) = i1 == i2
    (Literal (VBool x1)) == (Literal (VBool x2)) = x1 == x2
    (Equals e1 e2) == (Equals e3 e4) = e1 == e3 && e2 == e4
    (Plus e1 e2) == (Plus e3 e4) = e1 == e3 && e2 == e4
    (Let n1 a1 e1) == (Let n2 a2 e2) = n1 == n2 && a1 == a2 && e1 == e2
    (Return e1) == (Return e2) = e1 == e2
    _ == _ = False

  public export
  example0 : Expression
  example0 = Let "x" (Plus (Literal $ VInt 1) (Literal $ VInt 1)) (Return (Plus (Variable "x") (Literal $ VInt 2)))

  public export
  example1 : Expression
  example1 = Let "x" (Literal $ VInt 1) (Let "x" (Literal $ VInt 2) (Return (Variable "x")))

  public export
  example2 : Expression
  example2 = Let "a" (Literal $ VInt 1) (Equals (Return (Variable "a")) (Let "b" (Variable "a") (Plus (Variable "b") (Variable "a"))))

namespace Resolved

  public export
  data Expression : Nat -> Type where
    Variable : (i: Fin n) -> Expression n
    Literal : Value t -> Expression n
    Equals : (expr1: Expression n) -> (expr2: Expression n) -> Expression n
    Plus : (expr1: Expression n) -> (expr2: Expression n) -> Expression n
    Let : (assig: Expression n) -> (expr: Expression (S n)) -> Expression n
    Return : Expression n -> Expression n
    -- TODO more expresions
  %name Resolved.Expression expr, expr1, expr2
  public export
  implementation Show (Expression n) where
    show (Variable i) = "Variable " ++ show i
    show (Literal v) = "Literal " ++ show v
    show (Equals expr1 expr2) = "Equals (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Plus expr1 expr2) = "Plus (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Let assig expr) = "Let (" ++ show assig ++ ") in (" ++ show expr ++ ")"
    show (Return expr) = "Return (" ++ show expr ++ ")"
  public export
  Eq (Expression n) where
    (Variable i1) == (Variable i2) = i1 == i2
    (Literal (VInt i1)) == (Literal (VInt i2)) = i1 == i2
    (Literal (VBool x1)) == (Literal (VBool x2)) = x1 == x2
    (Equals e1 e2) == (Equals e3 e4) = e1 == e3 && e2 == e4
    (Plus e1 e2) == (Plus e3 e4) = e1 == e3 && e2 == e4
    (Let a1 e1) == (Let a2 e2) = a1 == a1 && e1 == e2
    (Return e1) == (Return e2) = e1 == e2
    _ == _ = False

  public export
  example0 : Expression 0
  example0 = Let (Plus (Literal $ VInt 1) (Literal $ VInt 1)) (Return (Plus (Variable FZ) (Literal $ VInt 2)))

  public export
  example1 : Expression 0
  example1 = Let (Literal $ VInt 1) (Let (Literal $ VInt 2) (Return (Variable FZ)))

  public export
  example2 : Expression 0
  example2 = Let (Literal $ VInt 1) (Equals (Return (Variable 0)) (Let (Variable 0) (Plus (Variable 0) (Variable 1))))

namespace Checked
  public export
  data Expression : Vect n Tyqe -> Tyqe -> Type where
    Variable : {t: _} -> (elem: Elem t ts) -> Expression ts t
    Literal : Value t -> Expression ts t
    Equals : (expr1: Expression ts TInt) -> (expr2: Expression ts TInt) -> Expression ts TBool
    Plus : (expr1: Expression ts TInt) -> (expr2: Expression ts TInt) -> Expression ts TInt
    Let : {tassig: _} -> (assig: Expression ts tassig) -> Expression (tassig::ts) treturn -> Expression ts treturn
    Return : Expression ts t -> Expression ts t
  %name Checked.Expression expr, expr1, expr2
  public export
  implementation Show (Expression ts t) where
    show (Variable {t} elem) = "Variable " ++ show (elemToFin elem) ++ ":" ++ show t
    show (Literal v) = "Literal " ++ show v
    show (Equals expr1 expr2) = "Equals (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Plus expr1 expr2) = "Plus (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Let assig expr) = "Let (" ++ show assig ++ ") in (" ++ show expr ++ ")"
    show (Return expr) = "Return (" ++ show expr ++ ")"
  public export
  Eq (Expression ts t) where
    (Variable el1) == (Variable el2) = elemToFin el1 == elemToFin el2
    (Literal (VInt i1)) == (Literal (VInt i2)) = i1 == i2
    (Literal (VBool x1)) == (Literal (VBool x2)) = x1 == x2
    (Equals e1 e2) == (Equals e3 e4) = e1 == e3 && e2 == e4
    (Plus e1 e2) == (Plus e3 e4) = e1 == e3 && e2 == e4
    (Let {tassig=ta1} a1 e1) == (Let {tassig=ta2} a2 e2) = do
      case decEq ta1 ta2 of
           (Yes Refl) => a1 == a2 && e1 == e2
           (No contra) => False
    (Return e1) == (Return e2) = e1 == e2
    _ == _ = False

  public export
  example0 : Expression [] TInt
  example0 = Let (Plus (Literal $ VInt 1) (Literal $ VInt 1)) (Return (Plus (Variable Here) (Literal $ VInt 2)))

  public export
  example1 : Expression [] TInt
  example1 = Let (Literal $ VInt 1) (Let (Literal $ VInt 2) (Return (Variable Here)))

  public export
  example2 : Expression [] TBool
  example2 = Let (Literal $ VInt 1) (Equals (Return (Variable Here)) (Let (Variable Here) (Plus (Variable Here) (Variable $ There Here))))

||| Convert source epxression to de bruijin expressions
|||
||| @n number of currently available variables in the expression
resolve : Source.Expression -> (names: Vect n String) -> Maybe (Resolved.Expression n)
resolve (Variable name) names = do
  case isElem name names of
       Yes prf => Just $ Variable (elemToFin prf)
       No _    => Nothing
resolve (Literal v) names = Just $ Literal v
resolve (Equals expr1 expr2) names = do
  expr1' <- resolve expr1 names
  expr2' <- resolve expr2 names
  Just $ Equals expr1' expr2'
resolve (Plus expr1 expr2) names = do
  expr1' <- resolve expr1 names
  expr2' <- resolve expr2 names
  Just $ Plus expr1' expr2'
resolve (Let name assig expr) names = do
  assig' <- resolve assig names
  expr' <- resolve expr (name::names)
  Just $ Let assig' expr'
resolve (Return expr) names = do
  expr' <- resolve expr names
  Just $ Return expr'

check : Resolved.Expression n -> (ts: Vect n Tyqe) -> Maybe (t ** Checked.Expression ts t)
check (Variable i) ts = do
  let (t ** elem) = indexElem i ts
  Just (t ** Variable elem)
check (Literal v) ts = do
  let (t ** Refl) = vtype v
  Just (t ** Literal v)
check (Equals expr1 expr2) ts = do
  (t1 ** expr1') <- check expr1 ts
  (t2 ** expr2') <- check expr2 ts
  case decEq (t1, t2) (TInt, TInt) of
       Yes Refl => Just (TBool ** Equals expr1' expr2')
       No contra => Nothing
check (Plus expr1 expr2) ts = do
  (t1 ** expr1') <- check expr1 ts
  (t2 ** expr2') <- check expr2 ts
  case decEq (t1, t2) (TInt, TInt) of
       Yes Refl => Just (TInt ** Plus expr1' expr2')
       No contra => Nothing
check (Let assig expr) ts = do
  (tassig ** assig') <- check assig ts
  (texpr ** expr') <- check expr $ tassig::ts
  Just $ (texpr ** Let assig' expr')
check (Return expr) ts = do
  (t ** expr') <- check expr ts
  Just (t ** Return expr')

types : Vect n (String, Tyqe) -> Vect n Tyqe
types = map snd

checkAll : Source.Expression -> (vars: Vect n (String, Tyqe)) -> Maybe (t ** Checked.Expression (types vars) t)
checkAll (Variable name) vars = do
  let (ts ** mapPrf) = mapWithProof snd vars
      ns = map fst vars
  case isElem name ns of
       (Yes prf) => do
         let (t ** myprf) = indexElem (elemToFin prf) ts
         Just (t ** Variable (rewrite sym mapPrf in myprf))
       (No contra) => Nothing
checkAll (Literal v) vars = do
  let (t ** Refl) = vtype v
  Just (t ** Literal v)
checkAll (Equals expr1 expr2) vars = do
  (t1 ** expr1') <- checkAll expr1 vars
  (t2 ** expr2') <- checkAll expr2 vars
  case decEq (t1, t2) (TInt, TInt) of
       (Yes Refl) => Just (TBool ** Equals expr1' expr2')
       (No contra) => Nothing
checkAll (Plus expr1 expr2) vars = do
  (t1 ** expr1') <- checkAll expr1 vars
  (t2 ** expr2') <- checkAll expr2 vars
  case decEq (t1, t2) (TInt, TInt) of
       (Yes Refl) => Just (TInt ** Plus expr1' expr2')
       (No contra) => Nothing
checkAll (Let name assig expr) vars = do
  (tassig ** assig') <- checkAll assig vars
  (texpr ** expr') <- checkAll expr $ (name, tassig) :: vars
  Just (texpr ** Let assig' expr')
checkAll (Return expr) vars = do
  (t ** expr') <- checkAll expr vars
  Just (t ** Return expr')

envTypes : Vect n (t: Tyqe ** Value t) -> Vect n Tyqe
envTypes = map fst

getEnvValue : (env : Vect n (t : Tyqe ** Value t)) -> Elem t (envTypes env) -> Value t
getEnvValue ((t**v)::env) Here          = v
getEnvValue (_     ::env) (There later) = getEnvValue env later

||| Interpret a checked expression
|||
||| @env the environment (values of variables) the expression is interpretet it
||| @expr the expression to interpret
|||
||| Even though using a seperate Env type like this
||| > data Env : Vect n Tpe -> Type where
||| >   Nil : Env []
||| >   (::) : Value t -> Env ts -> Env (t::ts)
||| might even be semantically clearer, I wanted to test whether it is possible
||| to express the relations properly without introducing an extra type.
|||
||| Turns out it is indeed possible and I found the following to be noteworthy:
|||   - In getEnvValue idris could not autocomplete anything (Not even caseSplit on env/elem or find the recursive call!).
|||     But if you write everything down Idris can unify and prove it.
|||   - If you write `map fst env` instead of `envTypes env` idris interprets fst as implicit variable.
|||     So a new helper function only taking the variables has to be introduced
interpret : (env: Vect n (t: Tyqe ** Value t)) -> Expression (envTypes env) t -> Value t
interpret env (Variable elem) = getEnvValue env elem
interpret env (Literal v) = v
interpret env (Equals expr1 expr2) = do
  let VInt i1 = interpret env expr1
      VInt i2 = interpret env expr1
  VBool $ i1 == i2
interpret env (Plus expr1 expr2) = do
  let VInt i1 = interpret env expr1
      VInt i2 = interpret env expr2
  VInt $ i1 + i2
interpret env (Let {tassig} assig expr) = do
  let vassig = interpret env assig
  interpret ((tassig ** vassig)::env) expr
interpret env (Return expr) = interpret env expr

namespace Test

  public export
  data TestErr : Type where
    AssertionErr : (msg: String) -> TestErr

  public export
  Assertion : Type
  Assertion = EitherT TestErr Identity ()

  public export
  assertFailure : (msg: String) -> Assertion
  assertFailure msg = throwError $ AssertionErr msg
  public export
  assertBool : (msg: String) -> (cond: Bool) -> Assertion
  assertBool msg cond = when cond $ throwError $ AssertionErr msg
  public export
  assertEqual : (Eq a, Show a) => (preface: String) -> (expected: a) -> (actual: a) -> Assertion
  assertEqual preface expected actual = do
    unless (expected == actual) $
      throwError $ AssertionErr $ msg
    where
      msg : String
      msg = preface ++ "\n"
         ++ "expected: " ++ show expected ++ "\n"
         ++ " but got: " ++ show actual

  infix 1 @=?, @?=
  public export
  (@=?) : (Eq a, Show a) => a -> a -> Assertion
  expected @=? actual = assertEqual "" expected actual

  public export
  (@?=) : (Eq a, Show a) => a -> a -> Assertion
  actual @?= expected = assertEqual "" expected actual

  public export
  data Test : Type where
    TestCase : (ass: Assertion) -> Test
    TestList : List Test -> Test
    TestLabel : (label: String) -> Test -> Test
  %name Test test, test1, test2

  public export
  interface Testable t where
    test : t -> Test
  public export
  Testable Test where test = id
  public export
  Testable t => Testable (List t) where test = TestList . map test
  public export
  Testable Assertion where test = TestCase

  infix 1 ~=?, ~?=
  infixr 0 ~:
  public export
  (~=?) : (Eq a, Show a) => a -> a -> Test
  expected ~=? actual = TestCase $ expected @=? actual
  public export
  (~?=) : (Eq a, Show a) => a -> a -> Test
  actual ~?= expected = TestCase $ expected @?= actual
  public export
  (~:) : Testable t => String -> t -> Test
  label ~: t = TestLabel label $ test t

  runTest' : (labelStack: List String) -> Test -> IO ()
  runTest' labelStack (TestCase ass) = do
    case runIdentity $ runEitherT ass of
         (Left (AssertionErr msg)) => do
           putStrLn $ "AssertionError: " ++ msg
           putStrLn $ "@" ++ showStack labelStack
         (Right ()) => pure ()
    where
      showStack : List String -> String
      showStack = joinBy "/" . reverse
  runTest' labelStack (TestList tests) = do
    for_ tests $ runTest' labelStack
  runTest' labelStack (TestLabel label test) = do
    runTest' (label::labelStack) test

  public export
  runTest : Test -> IO ()
  runTest = runTest' []

||| Type of an example
|||
||| Every example consists of
|||   return type of the expression
|||   return value of the expression
|||   source, resolved, checked version of the same expression
Example : Type
Example = (t: Tyqe ** (String, Value t, Source.Expression, Resolved.Expression 0, Checked.Expression [] t))
examples : List Example
examples =
  [ (TInt  ** ("example0", VInt 4    , example0, example0, example0))
  , (TInt  ** ("example1", VInt 2    , example1, example1, example1))
  , (TBool ** ("example2", VBool True, example2, example2, example2))
  ]

resolveTests = "resolve" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    let Just (resolved') = resolve source []
      | Nothing => assertFailure "resolve returned Nothing."
    resolved' @?= resolved
checkTests = "check" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    let Just (t' ** checked') = check resolved []
      | Nothing => assertFailure "check returned Nothing."
    case decEq t t' of
         Yes Refl => checked' @?= checked
         No _ => assertFailure "check resturned wrong type"
checkAllTests = "checkAll" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    let Just (t'' ** checked'') = checkAll source [] | Nothing => assertFailure "checkAll returned Nothing."
    case decEq t t'' of
         Yes Refl => checked'' @?= checked
         No _ => assertFailure "checkAll returned wrong type"
interpretTests = "interpret" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    interpret [] checked @?= v

tests : Test
tests = TestList [resolveTests, checkTests, checkAllTests, interpretTests]
