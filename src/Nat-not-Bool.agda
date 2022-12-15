module Nat-not-Bool where

open import Prelude
open import Day1

Injective : {A B : Set} -> (A -> B) -> Set
Injective {A = A} f = (x y : A) -> f x ≡ f y -> x ≡ y

idℕ-Injective : Σ f ꞉ (ℕ -> ℕ) , Injective f
idℕ-Injective = (λ x → x) , λ x y → λ z → z

data Treither A B C : Set where
  Left : A -> Treither A B C
  Middle : B -> Treither A B C
  Right : C -> Treither A B C

ℕ-to-𝔹-not-Injective : (T : Set) -> 𝔹 ≡ T -> ¬ (Σ f ꞉ (ℕ -> T) , Injective f)
ℕ-to-𝔹-not-Injective _ (refl _) (f , Injf) = h (g 0 1 2)
 where 
  h : Treither (0 ≡ 1) (0 ≡ 2) (1 ≡ 2) -> ⊥
  h (Left ())
  h (Middle ())
  h (Right ())
  g : (x y z : ℕ) -> Treither (x ≡ y) (x ≡ z) (y ≡ z)
  g x y z = k (f x) (f y) (f z) (refl _) (refl _) (refl _)
    where
      k : (a b c : 𝔹) -> (a ≡ f x) -> b ≡ f y -> c ≡ f z -> Treither (x ≡ y) (x ≡ z) (y ≡ z)
      k false false c a≡fx b≡fy c≡fz = Left (Injf x y (trans (sym a≡fx) b≡fy))
      k false true false a≡fx b≡fy c≡fz = Middle (Injf x z (trans (sym a≡fx) c≡fz))
      k false true true a≡fx b≡fy c≡fz = Right (Injf y z (trans (sym b≡fy) c≡fz))
      k true false false a≡fx b≡fy c≡fz = Right (Injf y z (trans (sym b≡fy) c≡fz))
      k true false true a≡fx b≡fy c≡fz = Middle (Injf x z (trans (sym a≡fx) c≡fz))
      k true true c a≡fx b≡fy c≡fz = Left (Injf x y (trans (sym a≡fx) b≡fy))

¬𝔹≡ℕ : 𝔹 ≡ ℕ -> ⊥
¬𝔹≡ℕ proof = ℕ-to-𝔹-not-Injective ℕ proof idℕ-Injective
