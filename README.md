# Nameresolution to De Bruijn indices

This project provides an example of practical uses of dependent types.
They are used to create a simple expression language that cannot fail during evaluation because the guarantees that all referenced variables exist and have the correct type are enforced by the AST.

## Structure

All contents are in `src/NameResolution.idr`. The important elements:

- namespace Helpers
  - general purpose helper functions
- namespace Core
  - Tyqe (Show, Uninhabited (TInt = TBool), DecEq)
  - Value (Injective VInt, Injective VBool, Show, DecEq, Eq)
- namespace Source
  - Expression (Show, Eq)
  - example0-2
- namespace Resolved
  - Expression (Show, Eq)
  - example0-2
- namespace Checked
  - Expression (Show, Eq)
  - example0-2
- resolve
- check
- checkAll
- interpret
- namespace Test
  - HUnit port
- examples
- tests
  - resolveTests
  - checkTests
  - checkAllTests
  - interpretTests

## Usage

Open the repl in the `NameResolution` module:

```Shell
pack repl src/NameResolution.idr
```

To run Tests:

```Idris
:exec runTest tests
```

To resolve/check/resolve & check/interpret an expression:

```Idris
resolve [] $ <Source.Expression>
```

```Idris
check [] $ <Resolved.Expression>
```

```Idris
checkAll [] $ <Source.Expression>
```

```Idris
interpret [] $ <Checked.Expression>
```

There are three example expressions `example0`, `example1`, `example2` available in every variant.
