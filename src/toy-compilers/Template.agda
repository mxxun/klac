module toy-compilers.Template where

module toy-compilers.Ex1 where

-- in which we will define a toy language, a toy stack machine, 
-- a toy interpreter for both, a compiler of first into the second,
-- and a proof that compiler is correct.

open import Data.Nat
open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

data Expr : Set where

interpret : Expr -> ℕ
interpret = {!   !}

---

data Instr : Set where

Stack = List ℕ
Program = List Instr

run : List Instr -> Stack -> Stack
run = {!   !}

---

compile : Expr -> Program
compile = {!   !}

compile-is-correct : 
  ∀ expr -> run (compile expr) [] ≡ [ interpret expr ]
compile-is-correct = {!   !}