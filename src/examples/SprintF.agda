{-# OPTIONS --safe #-}
module examples.SprintF where

open import Data.Char
open import Data.Integer
open import Data.Float
open import Data.String

-- ....ok, so first of all it should always return a string. ...ok, fine, we'll return a "" if the format is ill-formed.

data FormatDirective : Set where
  verbatim : Char -> FormatDirective
  char integer float : FormatDirective

open import Data.List
parseFormat : String -> List FormatDirective
parseFormat str = go (toList str) where
  go : List Char -> List FormatDirective
  go [] = []
  go ('%' ∷ '%' ∷ chars) = verbatim '%' ∷ go chars
  go ('%' ∷ 'c' ∷ chars) = char ∷ go chars
  go ('%' ∷ 'd' ∷ chars) = integer ∷ go chars
  go ('%' ∷ 'f' ∷ chars) = float ∷ go chars
  go ('%' ∷ _ ∷ chars) = [] -- failed parse
  go (x ∷ chars) = verbatim x ∷ go chars

retType : List FormatDirective -> Set₀ -> Set₀
retType [] t = t
retType (verbatim x ∷ fs) t = retType fs t
retType (char ∷ fs) t = Char -> retType fs t
retType (integer ∷ fs) t = ℤ -> retType fs t
retType (float ∷ fs) t = Float -> retType fs t

argsType : List FormatDirective -> List Set₀
argsType fs = {!!}

retType' : List FormatDirective -> Set₀ -> Set₀
retType' fs ret = go (argsType fs)
  -- ouch! -- foldr _→_ ret fs doesn't work because -> can't be used as a thing! annoying.
  where
  go : List Set₀ -> Set₀
  go [] = ret
  go (t ∷ ts) = t -> go ts
--...| [] = ret
--...| t ∷ ts = {!t -> retType' ts!}

-- _∘_ : ∀ {A B} -> (A -> B) -> ∀ {fs} retType fs A -> retType fs B
-- f ∘ ret = {!!}

format : (fs : List FormatDirective) -> retType' fs String
format fs with argsType fs 
...| [] = ""
...| t ∷ ts = {!fromList ∘ (go (f ∷ fs))!} where
  open import Function using (_∘_)
  go : List FormatDirective -> retType' fs (List Char)
  go fs = {!!}

sprintf : (str : String) -> retType' (parseFormat str) String
sprintf str = format (parseFormat str)

open import Relation.Binary.PropositionalEquality
  renaming (_≡_ to  _`shouldBe`_)

-- Should accept no arg when no fmt
_ : sprintf "" `shouldBe` ""
_ = refl

-- Should format integers/char/float/%
_ : sprintf "%d %f" -[1+ 3 ] 666.6 `shouldBe` "-4 666.6"
_ = refl
