# Nameresolution to De Bruijn indices

The project provides an example of practical uses of dependent types.
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
- type Example
- examples
- tests
  - resolveTests
  - checkTests
  - checkAllTests
  - interpretTests
