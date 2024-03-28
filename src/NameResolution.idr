module NameResolution

import Control.App
import Control.App.Console
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
  Uninhabited (x = y) => Uninhabited (y = x) where
    uninhabited eq = absurd (sym eq)

  public export
  decEqToEq : DecEq a => a -> a -> Bool
  decEqToEq x y with (decEq x y)
    decEqToEq x y | Yes _ = True
    decEqToEq x y | No _  = False

  public export
  whenLeft : Applicative f => Either a b -> (a -> f ()) -> f ()
  whenLeft (Left x) a = a x
  whenLeft (Right _) _ = pure ()

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

  ||| Source expressions
  |||
  ||| Variables are names. No guarantees can be made.
  public export
  data Expression : Type where
    Variable : (name: String) -> Expression
    Literal : Value t -> Expression
    Equals : (expr1: Expression) -> (expr2: Expression) -> Expression
    Plus : (expr1: Expression) -> (expr2: Expression) -> Expression
    Let : (name: String) -> (assig: Expression) -> Expression -> Expression
    Return : Expression -> Expression
  %name Source.Expression expr, expr1, expr2
  public export
  Show Expression where
    show (Variable name) = "Variable " ++ name
    show (Literal v) = "Literal " ++ show v
    show (Equals expr1 expr2) = "Equals (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Plus expr1 expr2) = "Plus (" ++ show expr1 ++ ") (" ++ show expr2 ++ ")"
    show (Let name assig expr) = "Let " ++ name ++ "=(" ++ show assig ++ ") in (" ++ show expr ++ ")"
    show (Return expr) = "Return (" ++ show expr ++ ")"
  public export
  Eq Expression where
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

  ||| Resolved expressions
  |||
  ||| Variables are De Bruijn indices. Guaranteed to reference a variable, since Fin is used.
  ||| @n the number of variables in the context of the expession
  public export
  data Expression : (n: Nat) -> Type where
    Variable : (i: Fin n) -> Expression n
    Literal : Value t -> Expression n
    Equals : (expr1: Expression n) -> (expr2: Expression n) -> Expression n
    Plus : (expr1: Expression n) -> (expr2: Expression n) -> Expression n
    Let : (assig: Expression n) -> (expr: Expression (S n)) -> Expression n
    Return : Expression n -> Expression n
  %name Resolved.Expression expr, expr1, expr2
  public export
  Show (Expression n) where
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
  -- comment the above line and uncomment the below line to see some tests failing (below is a modified version of the above)
  -- example2 = Let (Literal $ VInt 1) (Equals (Return (Literal $ VBool False)) (Let (Variable 0) (Plus (Variable 0) (Variable 1))))

namespace Checked

  ||| Checked expressions
  |||
  ||| Variables are proofs containing the type. Guaranteed to interpret without errors.
  ||| @ts the types of the variables in the context of the expression
  ||| @t the type the expression evaluates to
  public export
  data Expression : (ts: Vect n Tyqe) -> (t: Tyqe) -> Type where
    Variable : {t: _} -> (elem: Elem t ts) -> Expression ts t
    Literal : Value t -> Expression ts t
    Equals : (expr1: Expression ts TInt) -> (expr2: Expression ts TInt) -> Expression ts TBool
    Plus : (expr1: Expression ts TInt) -> (expr2: Expression ts TInt) -> Expression ts TInt
    Let : {tassig: _} -> (assig: Expression ts tassig) -> Expression (tassig::ts) treturn -> Expression ts treturn
    Return : Expression ts t -> Expression ts t
  %name Checked.Expression expr, expr1, expr2
  public export
  Show (Expression ts t) where
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

||| Convert source epxression to resolved expression.
|||
||| Checks names exist and creates De Bruijn indices.
||| @names the names of currently available variable names in the expression
resolve : (names: Vect n String) -> Source.Expression -> Maybe (Resolved.Expression n)
resolve names (Variable name) = do
  let Yes prf = isElem name names
    | No _ => Nothing
  Just $ Variable (elemToFin prf)
resolve names (Literal v) = Just $ Literal v
resolve names (Equals expr1 expr2) = do
  expr1' <- resolve names expr1
  expr2' <- resolve names expr2
  Just $ Equals expr1' expr2'
resolve names (Plus expr1 expr2) = do
  expr1' <- resolve names expr1
  expr2' <- resolve names expr2
  Just $ Plus expr1' expr2'
resolve names (Let name assig expr) = do
  assig' <- resolve names assig
  expr' <- resolve (name::names) expr
  Just $ Let assig' expr'
resolve names (Return expr) = do
  expr' <- resolve names expr
  Just $ Return expr'


||| Convert resolved expression to checked expression
|||
||| Checks types are correct and creates proofs containing the type of variables.
||| @ts the types of currently available variables in the expression
check : (ts: Vect n Tyqe) -> Resolved.Expression n -> Maybe (t ** Checked.Expression ts t)
check ts (Variable i) = do
  let (t ** elem) = indexElem i ts
  Just (t ** Variable elem)
check ts (Literal v) = do
  let (t ** Refl) = vtype v
  Just (t ** Literal v)
check ts (Equals expr1 expr2) = do
  (t1 ** expr1') <- check ts expr1
  (t2 ** expr2') <- check ts expr2
  let Yes Refl = decEq (t1, t2) (TInt, TInt)
    | No _ => Nothing
  Just (TBool ** Equals expr1' expr2')
check ts (Plus expr1 expr2) = do
  (t1 ** expr1') <- check ts expr1
  (t2 ** expr2') <- check ts expr2
  let Yes Refl = decEq (t1, t2) (TInt, TInt)
    | No _ => Nothing
  Just (TInt ** Plus expr1' expr2')
check ts (Let assig expr) = do
  (tassig ** assig') <- check ts assig
  (texpr ** expr') <- check (tassig::ts) expr
  Just $ (texpr ** Let assig' expr')
check ts (Return expr) = do
  (t ** expr') <- check ts expr
  Just (t ** Return expr')


||| Extract types from map of variable names to types
types : Vect n (String, Tyqe) -> Vect n Tyqe
types = map snd

||| Convert source expression to checked expression
|||
||| Checks variable names exist and types are correct. Creates proofs containing the type of variables.
||| Need to use `types` helper because in types only functions with arity 1 work.
||| @vars the map of variable names to their types currently available in the expression
checkAll : (vars: Vect n (String, Tyqe)) -> Source.Expression -> Maybe (t ** Checked.Expression (types vars) t)
checkAll vars (Variable name) = do
  let (ts ** mapPrf) = mapWithProof snd vars
  let names = map fst vars
  let Yes prf = isElem name names
    | No _ => Nothing
  let (t ** elem) = indexElem (elemToFin prf) ts
  Just (t ** Variable (rewrite sym mapPrf in elem))
checkAll vars (Literal v) = do
  let (t ** Refl) = vtype v
  Just (t ** Literal v)
checkAll vars (Equals expr1 expr2) = do
  (t1 ** expr1') <- checkAll vars expr1
  (t2 ** expr2') <- checkAll vars expr2
  let Yes Refl = decEq (t1, t2) (TInt, TInt)
    | No _ => Nothing
  Just (TBool ** Equals expr1' expr2')
checkAll vars (Plus expr1 expr2) = do
  (t1 ** expr1') <- checkAll vars expr1
  (t2 ** expr2') <- checkAll vars expr2
  let Yes Refl = decEq (t1, t2) (TInt, TInt)
    | No _ => Nothing
  Just (TInt ** Plus expr1' expr2')
checkAll vars (Let name assig expr) = do
  (tassig ** assig') <- checkAll vars assig
  (texpr ** expr') <- checkAll ((name, tassig) :: vars) expr
  Just (texpr ** Let assig' expr')
checkAll vars (Return expr) = do
  (t ** expr') <- checkAll vars expr
  Just (t ** Return expr')


||| Extract types from map of variables to their types and values
envTypes : Vect n (t: Tyqe ** Value t) -> Vect n Tyqe
envTypes = map fst

||| Get the value of an variable by the proof on the variable type
getEnvValue : (env : Vect n (t : Tyqe ** Value t)) -> Elem t (envTypes env) -> Value t
getEnvValue ((t**v)::env) Here          = v
getEnvValue (_     ::env) (There later) = getEnvValue env later

||| Interpret checked expression
|||
||| Cannot fail because checked expressions guarantee formal correctness of the program.
||| @env the environment (map of variables to their type and value) currently available in the expression
|||
||| Even though using a seperate Env type like this
||| > data Env : Vect n Tpe -> Type where
||| >   Nil : Env []
||| >   (::) : Value t -> Env ts -> Env (t::ts)
||| might even be semantically clearer, I wanted to test whether it is possible
||| to express the relations properly without introducing an extra type.
|||
||| Turns out it is indeed possible and I found the following to be noteworthy:
|||   - In getEnvValue idris could not autocomplete anything (not even caseSplit on env/elem or find the recursive call!).
|||     But if you write everything down Idris can unify and prove it.
|||   - If you write `map fst env` instead of `envTypes env` idris interprets fst as implicit type variable.
|||     So a new helper function with arity one has to be introduced
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

||| Testing library
|||
||| This is essentially a port of HUnit to Idris2.
||| Some interesting modifications:
|||   - Assertion type uses the exception monad instead of IO,
|||     since in idris errors thrown in IO cannot be catched!
|||   - runTests' uses the new App type introduced by idris
|||     to simplify state and error handling.
namespace Test

  public export
  data TestErr : Type where
    AssertionErr : (msg: String) -> TestErr

  public export
  Assertion : Type
  Assertion = EitherT TestErr Identity ()
  runAssertion : Assertion -> Either TestErr ()
  runAssertion = runIdentity . runEitherT

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
      msg = (if null preface then "" else preface ++ "\n")
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

  summaryMsg : (tried: Integer) -> (failures: Integer) -> String
  summaryMsg tried failures = "Tried: " ++ show tried ++ "  Failures: " ++ show failures ++ "\n"
  AssertionErrMsg : (msg: String) -> (stackTrace: String) -> String
  AssertionErrMsg msg stackTrace = "### AssertionErr in " ++ stackTrace ++ "\n" ++ msg ++ "\n"

  data Tried : Type where
  data Failures : Type where
  runTest' : Has [Console, State Tried Integer, State Failures Integer] es => (labelStack: List String) -> Test -> App es ()
  runTest' labelStack (TestCase ass) = do
    whenLeft (runAssertion ass) $ \(AssertionErr msg) => do
      putStr $ AssertionErrMsg msg (showStack labelStack)
      modify Failures (+1)
    modify Tried (+1)
    where
      showStack : List String -> String
      showStack = joinBy "/" . reverse
  runTest' labelStack (TestList tests) = do
    for_ tests $ runTest' labelStack
  runTest' labelStack (TestLabel label test) = do
    runTest' (label::labelStack) test

  public export
  runTest : Test -> IO ()
  runTest t = run $ new {tag=Tried} 0 $ new {tag=Failures} 0 $ do
    runTest' [] t
    putStr =<< summaryMsg <$> (get Tried) <*> (get Failures)


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
    let Just (resolved') = resolve [] source
      | Nothing => assertFailure "resolve returned Nothing."
    resolved' @?= resolved
checkTests = "check" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    let Just (t' ** checked') = check [] resolved
      | Nothing => assertFailure "check returned Nothing."
    let Yes Refl = decEq t t'
      | No _ => assertFailure "check returned wrong type"
    checked' @?= checked
checkAllTests = "checkAll" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    let Just (t' ** checked') = checkAll [] source
      | Nothing => assertFailure "checkAll returned Nothing."
    let Yes Refl = decEq t t'
      | No _ => assertFailure "checkAll returned wrong type"
    checked' @?= checked
interpretTests = "interpret" ~: flip map examples
  \(t ** (label, v, source, resolved, checked)) => label ~: do
    interpret [] checked @?= v

tests : Test
tests = TestList [ resolveTests, checkTests, checkAllTests, interpretTests ]
