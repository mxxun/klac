module toy-compilers.Ex1 where

-- in which we will define a toy language, a toy stack machine, 
-- a toy interpreter for both, a compiler of first into the second,
-- and a proof that compiler is correct.

open import Data.Nat as Nat using (ℕ)
open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Function using (_∘_; _$_)

-- the first expression type is: nats, _+_, _*_, _-_.

data Expr : Set where
  val : ℕ -> Expr
  _+_ : Expr -> Expr -> Expr
  _*_ : Expr -> Expr -> Expr
  _∸_ : Expr -> Expr -> Expr

⟦_⟧ : Expr -> ℕ
⟦ val x        ⟧ = x
⟦ left + right ⟧ = ⟦ left ⟧ Nat.+ ⟦ right ⟧
⟦ left * right ⟧ = ⟦ left ⟧ Nat.* ⟦ right ⟧
⟦ left ∸ right ⟧ = ⟦ left ⟧ Nat.∸ ⟦ right ⟧

---

data Instr : Set where
  PUSH : ℕ -> Instr
  POP : Instr
  ADD : Instr
  MUL : Instr
  SUB : Instr


Stack = List ℕ
Program = List Instr

mutual
-- this is just a fold really, but later on it'll be worse.
  run : Program -> Stack -> Stack
  run [] s = s
  run (x ∷ p) s = run p $ step x s
  -- Q: what's our exception handling strategy here?
  -- A: I think in the first exercise we do something simple like 
  -- "stack is implicitly padded with zeros", and later on we expand.
  binop : (ℕ -> ℕ -> ℕ) -> Stack -> Stack
  binop _<>_ [] = [ 0 <> 0 ]
  binop _<>_ (x ∷ []) = [ x <> 0 ]
  binop _<>_ (l ∷ r ∷ s) = l <> r ∷ s

  step : Instr -> Stack -> Stack
  step (PUSH x) s = x ∷ s
  step POP [] = []
  step POP (x ∷ s) = s
  step ADD s = binop Nat._+_ s
  step MUL s = binop Nat._*_ s
  step SUB s = binop Nat._∸_ s

---

-- compile should create a program that leaves a single value on the stack:
-- the expression evaluation result.
-- programs are ran left-to-right, so: first put on the stack the final operand,
-- then the next operand, then...finally the operation.
⟪_⟫ : Expr -> Program
⟪ val x ⟫ = [ PUSH x ]
⟪ l + r ⟫ = ⟪ r ⟫ ++ ⟪ l ⟫ ++ [ ADD ]
⟪ l * r ⟫ = ⟪ r ⟫ ++ ⟪ l ⟫ ++ [ MUL ]
⟪ l ∸ r ⟫ = ⟪ r ⟫ ++ ⟪ l ⟫ ++ [ SUB ]

-- ok, so the idea of proof follows from how compilation works.
-- the idea is that any n-ary expr compiles into 
-- a) subprograms that leave its operands on the stack
-- b) the single instruction that will compute the final expression from operands.
-- so we should be able to proceed by induction on the structure of the expr:
-- if it's val, done. if it's a binop, by definition of ⟪_⟫ it'll compile as etc,
-- leave operation and (by induction) computed operands, 
-- and on the final step be computed to the expression.

-- except we'll need a lemma that running programs partially is valid. well, yeah, ok.
-- and obviously we'll need to generalize to any stack, not just empty one.

-- and also if we want to decouple binop work into a helper, we'll need to define
-- these guys mutually, because recursion ultimately goes through compile-is-correct.

compile-is-correct : ∀ {s} expr -> run ⟪ expr ⟫ s ≡ ⟦ expr ⟧ ∷ s

run-partial : ∀ {s} pr1 pr2 -> run (pr1 ++ pr2) s ≡ run pr2 (run pr1 s)
run-partial [] pr2 = Eq.refl
run-partial (x ∷ pr1) pr2 = run-partial pr1 pr2

-- apparently we overgeneralized, and `p` wasn't necessary? ah well.
binop-helper : 
     {s : Stack} -> {p : Program}
  -> (_<>_ : Expr -> Expr -> Expr) -> (l r : Expr) -> (i : Instr)
  -> ⟪ l <> r ⟫ ≡ ⟪ r ⟫ ++ ⟪ l ⟫ ++ [ i ] -- splitting assumption
  -> run [ i ] (⟦ l ⟧ ∷ ⟦ r ⟧ ∷ s) ≡ ⟦ l <> r ⟧ ∷ s -- step semantics
  -> run (⟪ l <> r ⟫ ++ p) s ≡ run p (⟦ l <> r ⟧ ∷ s)
binop-helper {s} {p} _<>_ l r i prog-split step-semantics = 
  begin 
  run (⟪ l <> r ⟫ ++ p) s ≡⟨ run-partial ⟪ l <> r ⟫ p ⟩ 
  run p (run ⟪ l <> r ⟫ s) ≡⟨ Eq.cong (run p) $
    begin 
    run ⟪ l <> r ⟫ s ≡⟨ Eq.cong (λ t -> run t s) prog-split ⟩
    run (⟪ r ⟫ ++ ⟪ l ⟫ ++ i ∷ []) s ≡⟨ run-partial ⟪ r ⟫ (⟪ l ⟫ ++ i ∷ []) ⟩ 
    run (⟪ l ⟫ ++ i ∷ []) (run ⟪ r ⟫ s) ≡⟨ 
      Eq.cong (run (⟪ l ⟫ ++ i ∷ [])) $ compile-is-correct r ⟩
    run (⟪ l ⟫ ++ i ∷ []) (⟦ r ⟧ ∷ s) ≡⟨ run-partial ⟪ l ⟫ (i ∷ []) ⟩
    run (i ∷ []) (run ⟪ l ⟫ (⟦ r ⟧ ∷ s)) ≡⟨ 
      Eq.cong (run (i ∷ [])) $ compile-is-correct l ⟩
    run (i ∷ []) (⟦ l ⟧ ∷ ⟦ r ⟧ ∷ s) ≡⟨ step-semantics ⟩
    ⟦ l <> r ⟧ ∷ s ∎
  ⟩
  run p (⟦ l <> r ⟧ ∷ s) ∎
  where open Eq.≡-Reasoning

binop-helper′ 
  :  {s : Stack}
  -> (_<>_ : Expr -> Expr -> Expr) -> (l r : Expr) -> (i : Instr)
  -> ⟪ l <> r ⟫ ≡ ⟪ r ⟫ ++ ⟪ l ⟫ ++ [ i ] 
  -> step i (⟦ l ⟧ ∷ ⟦ r ⟧ ∷ s) ≡ ⟦ l <> r ⟧ ∷ s
  -> run (⟪ l <> r ⟫) s ≡ ⟦ l <> r ⟧ ∷ s
binop-helper′ {s} _<>_ l r i prog-split step-sem = 
  begin 
  run ⟪ l <> r ⟫ s ≡⟨ 
    Eq.cong (λ t -> run t s) 
      (Eq.sym $ ++-identityʳ ⟪ l <> r ⟫) 
    ⟩ 
  run (⟪ l <> r ⟫ ++ []) s ≡⟨ binop-helper _<>_ l r i prog-split step-sem ⟩ 
  ⟦ l <> r ⟧ ∷ s ∎
  where 
    open Eq.≡-Reasoning
    open import Data.List.Properties using (++-identityʳ)


compile-is-correct (val x) = Eq.refl
compile-is-correct (left + right) = binop-helper′ _+_ left right _ Eq.refl Eq.refl
compile-is-correct (left * right) = binop-helper′ _*_ left right _ Eq.refl Eq.refl
compile-is-correct (left ∸ right) = binop-helper′ _∸_ left right _ Eq.refl Eq.refl

-- it is of note that all of this depends merely on:
-- a) the run-partial lemma
-- b) single-step semantics of ops
-- c) splitting of compiled exprs
-- d) that running a single instr on a sufficiently nonempty stack 
-- _is_ the same as stepping it.
-- which leaves us with a question: just how much of this we could generalize 
-- to a more abstract expr/stack machine?
-- rather a lot, methinks!
-- in the next exercise, where stack short-circuits on insufficient operands,
-- the proof is _exactly_ the same, with a tiny wrinkle:
-- we'll need a property P of programs that holds for all compiled exprs,
-- holds for shorter programs (P i ∷ p -> P p), and makes run-partial work
-- in the recursive case: `run (i ∷ pr1 ++ pr2) s ≡ run pr2 (run i ∷ pr1 s)`
-- now, here, run is just a step, so we get 
-- `run (pr1 ++ pr2) (step i s) ≡ run pr2 (run pr1 (step i s))`
-- ....but if run wasn't just a step -- e.g. if it checked args & dropped 
-- steps -- then we'd have a slightly harder time.
