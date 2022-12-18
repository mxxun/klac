module homework.1001-syntax-representations where

module FreshList where

  -- ok, the idea here is that we want to have a list 
  -- that also contains evidence that the new element is not already present.

  -- that's the datatype
  data FreshList (A : Set) : Set

  -- that's gonna be---not the proof that a is not in as, 
  -- but the type of that proof.
  _#_ : ∀ {A} -> A -> FreshList A -> Set

  data FreshList A where
    [] : FreshList A
    _∷_<_> : (a : A) -> (as : FreshList A) -> (a # as) -> FreshList A

  open import Prelude
  open import Day1 using (⊤; ⊥; ℕ)

  -- the type of proof that a is not in the empty list is: trivial
  a # [] = ⊤
  -- the type of proof that a is not in a cons: it's not the head, 
  -- and also it's not in the tail. ...ok.
  a # (b ∷ as < _ >) = (a ≡ b -> ⊥) × (a # as)

  _∷_ : ∀ {A} (a : A) (as : FreshList A) {a#as : a # as} -> FreshList A
  (a ∷ as) {a#as} = a ∷ as < a#as >

  infixr 20 _∷_

  _ : FreshList ℕ
  _ = 0 ∷ (1 ∷ (2 ∷ []) < (λ ()) , Day1.tt > ) < (λ ()) , (λ ()) , Day1.tt >

module AbstractScopeGraphs where
  open import Prelude
  open import Day1
  
  -- yeah yeah; I don't want to figure how to import stdlib strings right now.
  Name = ℕ

  _≢_ : ∀ {l} {A : Set l} (x y : A) -> Set _
  x ≢ y = x ≡ y -> ⊥

  record ScopeGraph : Set₁ where
    field
      Scope : Set
      _∈_ : Name -> Scope -> Set
      bind : Name -> Scope -> Scope
      here : ∀ {x s} -> x ∈ bind x s
      there : ∀ {x y s} -> x ∈ s -> x ≢ y -> x ∈ bind y s
  
  -- what does {{...}} mean? "everything"? "public"?
  -- presumably something to do w/ ...it being an instance variable?
  -- "open the module ScopeGraph, converting everything to use ScopeGraph
  -- as an instance variable"? mmmrgh.
  open ScopeGraph {{...}}
  

  module _ {{_ : ScopeGraph}} where
    data Term (s : Scope) : Set where
      var : ∀ x -> x ∈ s -> Term s
      lam : ∀ x -> Term (bind x s) -> Term s
      app : Term s -> Term s -> Term s

    ex : ∀ {s} -> Term s
    ex = 
      lam 0 -- f
        (lam 1 -- x
          (app (var 0 0inS) (var 1 1inS))
        ) 
      where
        0inS = there here (λ ())
        -- ok, note that types of here and ScopeGraph.here are different
        -- ....moreover, `here` is not in scope at all? but _kinda_ is, when 
        -- we're in holes? weird!
        -- ----ah; the disparity is that C-c C-d infers type from the top-level view
        -- which is outside of AbstractScopeGraphs and therefore doesn't have 
        -- anything we opened there!
        -- but when we're in holes, we do have the instance of ScopeGraph 
        -- (as demanded in the module declaration), which agda happily resolves.
        -- (But it can't fill these in itself; if we C-c C-a it uses explicit versions
        -- and also needs the instance var to have a name to pass.)
        1inS = here