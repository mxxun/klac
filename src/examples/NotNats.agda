{-# OPTIONS --guardedness #-}

module examples.NotNats where

open import Data.Bool

record IBox (A : Set) : Set where
  inductive
  pattern
  constructor MkIBox
  field
    ready : Bool
    content : if ready then A else IBox A

---

open import Data.Nat
open import Data.Unit

ℕtoIBox : ℕ -> IBox ⊤
ℕtoIBox zero = MkIBox true tt
ℕtoIBox (suc n) = MkIBox false (ℕtoIBox n)

IBoxtoℕ : IBox ⊤ -> ℕ
IBoxtoℕ (MkIBox false content) = suc (IBoxtoℕ content)
IBoxtoℕ (MkIBox true tt) = zero

import Relation.Binary.PropositionalEquality as Eq
open Eq
open import Function using (IsInverse)

there : (x : IBox ⊤) → ℕtoIBox (IBoxtoℕ x) ≡ x
there (MkIBox false content) = cong (MkIBox false) (there content)
there (MkIBox true tt) = refl

back : (x : ℕ) → IBoxtoℕ (ℕtoIBox x) ≡ x
back zero = refl
back (suc x) = cong suc (back x)

ℕ≈IBox : IsInverse _≡_ _≡_ ℕtoIBox IBoxtoℕ
ℕ≈IBox = record
  { isLeftInverse = record
  { isCongruent = record { cong = Eq.cong ℕtoIBox ; isEquivalence₁ = Eq.isEquivalence ; isEquivalence₂ = Eq.isEquivalence }
  ; from-cong = Eq.cong IBoxtoℕ
  ; inverseˡ = there }
  ; inverseʳ = back
  }

---

record CoiBox (A : Set) : Set where
  coinductive
  constructor MkCoiBox
  field
    ready : Bool
    content : if ready then A else CoiBox A

open CoiBox

ℕtoCoiBox : ℕ -> CoiBox ⊤
ℕtoCoiBox zero = MkCoiBox true tt
ℕtoCoiBox (suc n) = MkCoiBox false (ℕtoCoiBox n)

-- can't do that! agda refuses to split.
-- CoiBoxtoℕ : CoiBox ⊤ -> ℕ
-- CoiBoxtoℕ box = {!!}

-- smh we can guard-check this via copatterns and not via constructor. weird.
weirdBox : CoiBox ⊤
CoiBox.ready weirdBox = false
CoiBox.content weirdBox = weirdBox

weirdBox2 : CoiBox ⊤
CoiBox.ready weirdBox2 = false
CoiBox.content weirdBox2 = weirdBox2

P : Bool -> Set
P b = if b then ⊤ else CoiBox ⊤

content' : (b : CoiBox ⊤) -> ready b ≡ false -> CoiBox ⊤
ready (content' b prf) = ready b
content (content' b prf) = subst P (sym prf) {!content b!}

weird-apart : ∀ n -> ℕtoCoiBox n ≢ weirdBox
weird-apart zero eq with cong ready eq
... | ()
weird-apart (suc n) eq = weird-apart n ({!!}) -- uh?

Coi-refl? : (b1 : CoiBox ⊤) -> MkCoiBox (ready b1) (content b1) ≡ b1
Coi-refl? box = {!!}

-- definable via Coi-refl?, but...
Coi-cong : (b1 b2 : CoiBox ⊤) ->
  (r : ready b1 ≡ ready b2) ->
  subst P r (content b1) ≡ content b2 ->
  b1 ≡ b2
Coi-cong b1 b2 ready≡ content≡ =
  begin
  b1 ≡⟨ Eq.sym (Coi-refl? b1) ⟩
  MkCoiBox (ready b1) (content b1) ≡⟨ Eq.dcong₂ MkCoiBox ready≡ content≡ ⟩
  MkCoiBox (ready b2) (content b2) ≡⟨ Coi-refl? b2 ⟩  
  b2 ∎
--  Eq.trans (Eq.sym (Coi-refl? b1)) (Eq.trans {!!} (Coi-refl? b2))
 where open Eq.≡-Reasoning

-- fails termination-check, sure, but the problem's worse: we can't even define Coi-conf!
what : weirdBox ≡ weirdBox2
what = (Coi-cong weirdBox weirdBox2 refl what)

