module homework.Day4.SortedListHard where

-- All right, let's start with the beginning. it....should be self-contained, I think.

-- ....I dunno if McBride lies about this or just never had to deal with it, but:
-- the original code flatly does not compile due to levels.
-- so we need to generalize them somewhat.
open import Level

module Prelude where

  data 𝟘 : Set where
  record 𝟙 : Set where constructor ⟨⟩
  data 𝟚 : Set where tt ff : 𝟚

  So : 𝟚 -> Set
  So tt = 𝟙
  So ff = 𝟘

  -- kata: we didn't quite understand the "truncation".
    -- %%NB: I think we'll need the level here; also I think it should be preserved?%%
    -- ##Take two: we _don't_, actually, because we don't need to raise the level if we put P and _≤_ into module parameters instead of variables.##
  record ⌜_⌝ (P : Set) : Set where
  -- so: this thing is supposed to be constructable implicitly; there should be a constructor !
  -- all of arguments of which are implicit.
    constructor !
  -- arguments of the constructor are fields. what does this pack? a proof of P. so....
  -- ...a single field, P-typed, but.....the field is implicit?
  -- at this point I don't understand record fields enough, but: they're both accessor-funcs
  -- and....constructor-args. as a constructor arg it should be implicit, and....syntax allows for that? huh.
    field ⦃ prf ⦄ : P

  -- the bold-arrow, to use for args that should be supplied implicitly.
    --%%Levels: no need to specialize to a single one%%
    --##Drop levels back##
  _⇒_ : Set -> Set -> Set
  -- when we have a term of type P ⇒ T, we want it to not work like a function; we want it to be
  -- T-shaped. which kinda means that we want it to be a function w/ an implicit argument, which...
  -- is filled automagically by agda.
  -- so....not _just_ {{ P }} -> T; something that also supplies ! to that?
  -- (looks at the paper) no, just {{ P }} -> T! ok then.
  P ⇒ T = ⦃ P ⦄ -> T
  -- do we understand why fixities are thus? No we do not.
  infixr 3 _⇒_

  -- ....I have no idea what's the point of this? but ok.
  -- what it _does_ is acquire the truncated proof of P explicitly, and supply it to the T
  -- w/ P-obligation (implicitly).
    --%%Levels: if P and T's universes are implicit, agda fails to solve their levels)%%
    --##Drop levels back##
  _∴_ : ∀ {P : Set} {T : Set} -> ⌜ P ⌝ -> (P ⇒ T) -> T
  ! ∴ t = t

  -- ok, again: I don't _quite_ understand why we defined our own bools (except for self-containedness), but, fair: here goes a not
  ¬_ : 𝟚 -> 𝟚; ¬ tt = ff; ¬ ff = tt

  -- and an ifThenElse ofc!
  -- but wait, theirs is not A -> A -> A! theirs is, uh....
  -- ...._ah_, theirs is...capable of discharging proof obligations! we can have demands of
  -- "something is true" and "something is false" in branches, and output the A w/o demands.
  -- ok, that's cool even if we dunno why we want it like this yet.

  instance SoTrueBestie : So tt
  SoTrueBestie = ⟨⟩

    --%%Levels: whyever not%%
    --##Drop levels again##
  if_then_else_ : ∀ {A : Set} -> (b : 𝟚) -> (So b ⇒ A) -> (So (¬ b) ⇒ A) -> A
  -- this....doesn't work for some reason? "no instance of type So tt".
  -- do we need to do an explicit instance of that? like, why not, but....
  -- ...we're missing something.
  if tt then l else _ = l
  if ff then _ else r = r

  -- ok, fair enough, 0-elims are useful.
    --%%Levels: if implicit, X's level is unsolved%%
    --##Drop back##
  magic : ∀ {X : Set} -> 𝟘 ⇒ X
  magic ⦃()⦄

  -- oh, and some postulates so we can paper over holes.
  postulate BS : {X Y : Set} -> X -> Y
open Prelude

module STRange-and-friends (P : Set) (_≤_ : P -> P -> 𝟚) where
  --%%Levels for P: I _think_ we don't need level-polymorphism here.%%

  -- ok, so: standard trees, then we'll define STRanges of empty and pivot-to-pivot, then BSTs,
  -- then we'll try to write insert and fail. ok, let's go.

  -- Q: ....how did they parametrize over P without raising Tree to Set₁?
  -- A: Set : Set? but there's Set₁ mentioned later, no?
  -- A: maybe it just....didn't compile.
  -- A: or maybe earlier agda was more permissive? who even knows!
  -- A2: _actually_ if we parametrize it explicitly it's just a Set! wtf, agda!!
  -- A3: .....oh, hm, P in module signature is different from P as a variable.
  data Tree : Set where
    leaf : Tree
    node : (lt : Tree) -> (p : P) -> (rt : Tree) -> Tree

  data STRange : Set where
    ø : STRange
    -- oh right the first one is not even checked!
    -- NB: that's an N-dash
    _–_ : (l r : P) -> STRange
  infix 9 _–_

  -- ok, so...we want to convert trees into their STRanges, and that may..fail if pivots
  -- are incorrect; ok, we'll need a maybe as usual.

  data Maybe (A : Set) : Set where
    no : Maybe A; yes : A -> Maybe A

  _?⟩_ : ∀ {A} -> 𝟚 -> Maybe A -> Maybe A
  b ?⟩ ma = if b then ma else no
  infixr 4 _?⟩_

  -- ok, now we can validate a tree into a range.
  valid : Tree -> Maybe STRange
  valid leaf = yes ø
  valid (node lt p rt) with (valid lt) | (valid rt)
  ... | yes ø | yes ø = yes (p – p)
  -- oh right if pivot is inside the right that violates the invariant
  ... | yes ø | yes (l – r) = p ≤ l ?⟩ yes (p – r)
  ... | yes (l – r) | yes ø = r ≤ p ?⟩ yes (l – p)
  ... | yes (ll – lu) | yes (rl – ru) = lu ≤ p ?⟩ p ≤ rl ?⟩ yes (ll – ru)
  -- yea yea I know catchall pattern. convenient though.
  ... | _ | _ = no


  -- Q: how should the evidence look like for maximal convenience?
  -- A: ....I...dunno. that left is mergeable with p and then the result is mergeable with right? sounds bad.
  -- A2: that they're both mergeable? also sounds bad, but on the rOut side. ...ok fine let's try lOK and rOK.
  lOK : STRange -> P -> 𝟚
  lOK ø p = tt
  lOK (l – r) p = r ≤ p

  rOK : P -> STRange -> 𝟚
  rOK p ø = tt
  rOK p (l – r) = p ≤ l

  -- wait, this also does not check its args for validity? weird!!
  rOut : STRange -> P -> STRange -> STRange
  -- we'll just.....assume that we were passed a valid triple, and merge as if it is.
  rOut ø p ø = p – p
  rOut ø p (l – r) = p – r
  rOut (l – r) p ø = l – p
  rOut (l – _) p (_ – r) = l – r

  -- ok, now let's internalize that into a tree that demands validity at construction.
  data BST : STRange -> Set where
    leafB : BST ø
    nodeB : ∀ {l r} -> (lt : BST l) -> (p : P) -> (rt : BST r) ->
      -- aha; we want a....func that merges l p and r into a merged range unconditionally
      -- but that can only happen if it gets some evidence; of pivot being between them in particular.
      So (lOK l p) ⇒ So (rOK p r) ⇒ BST (rOut l p r)
      
  -- ok, now: insertion and how it fails.
  -- first, insertion for ordinary trees, so that we have a reference.

  insert : P -> Tree -> Tree
  insert x leaf = node leaf x leaf
  insert x (node lt p rt) = if x ≤ p
    then node (insert x lt) p rt
    else node lt p (insert x rt)

  -- ...oh yeah we'll need to return a fancier type for the inserted tree.
  oInsert : STRange -> P -> STRange
  oInsert ø x = x – x
  oInsert (l – r) x =
    if x ≤ l then x – r else
    if r ≤ x then l – x else (l – r)

  insertR : ∀ {r} (x : P) -> BST r -> BST (oInsert r x)
  insertR x leafB = nodeB leafB x leafB
  insertR x (nodeB lt p rt) = if x ≤ p
    -- whoops! `rOut (oInsert l x) p r != oInsert (rOut l p r) x`
    -- ...and moreover, `No instance of type So (lOK (oInsert l x) p) was found in scope`, which
    -- requires us to hide these from agda entirely.
    then (BS tt) -- (nodeB (insertR x lt) p rt))
    -- and likewise `rOut l p (oInsert r x) != oInsert (rOut l p r) x`
    -- and `No instance of type So (rOK p (oInsert r x)) was found in scope.`
    else (BS tt) -- (nodeB lt p (insertR x rt)))
--
-- now, for something different.

module ⊤⊥ where
  -- right, so let's extend pivots with tops and bottoms.
  --%%_and_ we'll need this disjoint from Better-Trees, so as to not catch the ≤ argument.%%

  data _⊤⊥ (P : Set) : Set where
    ⊤ ⊥ : P ⊤⊥
    # : P -> P ⊤⊥
open ⊤⊥

module Better-Trees (P : Set) (_≤_ : P -> P -> 𝟚) where
  _≤'_ : P ⊤⊥ -> P ⊤⊥ -> 𝟚
  ⊥ ≤' _ = tt
  _ ≤' ⊤ = tt
  # l ≤' # r = l ≤ r
  _ ≤' _ = ff

  -- now we can have BSTs indexed by pairs of pivots directly, and...demand that subtrees fit inside the upper one.
  data BST (l u : P ⊤⊥) : Set where
    -- wait, no demand of l ≤' u for the leaf? isn't that weird!
    -- ..I suppose invalid leaves can't be used for anything? or rather, can't be a part of anything?
    -- still.
    leaf : BST l u
    -- ok, _here_ we want left and right subtrees to respect the bound on the node.
    -- ...or rather, McBride does not permit them arbitrary respectful bounds; instead, he forces l p and p u bounds downwards, and demands only that this is valid: l ≤ p, p ≤ u. all right then.
    pnode : (p : P) -> BST l (# p) -> BST (# p) u ->
      So (l ≤' # p) ⇒ So (# p ≤' u) ⇒ BST l u

  pattern node lt p rt = pnode p lt rt

  -- can we insert now? ...and what's the input and output type of insert?
  -- Iiiii think the output should be l u, and input..should validate that p fits in that.
  -- ......does order of x matter somehow? ..no it does not.
  insert : ∀ {l u} x -> BST l u -> So (l ≤' # x) ⇒ So (# x ≤' u) ⇒ BST l u
  -- Q: how is agda supposed to solve `BST _l_126 _u_127 !=< So (l ≤' # x) ⇒ So (# x ≤' u) → BST l u` here?
  -- A: we're dumb and the last arrow should've been fat.
  insert x leaf = node leaf x leaf 
  insert x (node lt p rt) = if x ≤ p
    then node (insert x lt) p rt
    -- `No instance of type (So (# p ≤' # x)) was found in scope.`
    -- yeah, what we have is `So (¬ (x ≤ p))`, which is not quite that, because...
    -- ...that's how we defined ifthenelse, pretty much? so we can't have a proper dihotomy-splitting
    -- conditional. and to do that we'd need.......well, the next machinery from the paper.
    -- ...I think I'll abstain from inventing it ourselves, and just active-recall whatever was there.
    else node lt p (BS tt) -- {!insert x rt!}

---
-- now, let's do some more standard definitions.
module Prelude2 where
  record Σ (A : Set) (B : A -> Set) : Set where
    constructor _,_
    field fst : A; snd : B fst
  _×_ : Set -> Set -> Set
  A × B = Σ A \ _ -> B
  infixr 5 _×_ _,_

  -- and we'll need + for OWOTO, of course.

  data _+_ (L R : Set) : Set where
    inl : L -> L + R
    inr : R -> L + R
open Prelude2

module Rel where
  -- that's....not 𝟚.
  Rel : Set → Set₁
  Rel A = A × A -> Set

  module ℕ where
    data ℕ : Set where z : ℕ; s : ℕ -> ℕ
  module Lℕ where
    open ℕ public
    Lℕ : Rel ℕ
    Lℕ (m , n) = m ≤ n where
      _≤_ : ℕ -> ℕ -> Set
      z   ≤ n   = 𝟙
      s m ≤ z   = 𝟘
      s m ≤ s n = m ≤ n

  -- and now....we want Dichotomy for _≤_, but also we don't care about specific evidence.
  -- (or rather, we want to hide evidence so it propagates automagically.)
  -- in that case:
  -- %%oh, we missed that OWOTO is...also a relation on A. hm.
  OWOTO : ∀ {A} -> Rel A -> Rel A
  OWOTO R (x , y) = ⌜ R (x , y) ⌝ + ⌜ R (y , x) ⌝

  pattern le = inl !
  pattern ge = inr !

  -- and now, let's see for ourselves how Lℕ does admit a dichotomy
  module Lℕ-owoto where
    open Lℕ
    owoto : ∀ x y -> OWOTO Lℕ (x , y)
    owoto z y = le
    owoto (s x) z = ge
    -- aaaaand yeah, OWOTO Lℕ (s x , s y) = Lℕ (s x , s y) + Lℕ (s y , s x) = Lℕ (x , y) + Lℕ (y , x)
    -- = OWOTO Lℕ (x , y); that's..convenient.
    -- and the way we got that is via making ≤ output Sets (which required 𝟙 and 𝟘 to be sets).
    -- ....or rather.. we _could_ make it output 𝟚 and then lift that via So, but....
    -- ....but So (s x ≤ s y) is not, definitionally, So (x ≤ y)? ...really? uh let's maybe try that.
    owoto (s x) (s y) = owoto x y
  module Lℕᵇ where
    open ℕ public
    Lℕᵇ : Rel ℕ
    Lℕᵇ (m , n) = So (m ≤ n) where
      _≤_ : ℕ -> ℕ -> 𝟚
      z   ≤ n   = tt
      s m ≤ z   = ff
      s m ≤ s n = m ≤ n
    owoto : ∀ x y -> OWOTO Lℕᵇ (x , y)
    owoto z y = le
    owoto (s x) z = ge
    owoto (s x) (s y) = owoto x y
  -- that works! so what the fuck.

  -- ....extension of relations to ⊤⊥ I understand; simultaneous truncation/implicitation....slightly less so, but fine, let's go.

  _⊤⊥R_ ⌜_⌝R : ∀ {P} -> Rel P -> Rel (P ⊤⊥)
  R ⊤⊥R (_ , ⊤) = 𝟙
  R ⊤⊥R (⊥ , _) = 𝟙
  R ⊤⊥R (# x , # y) = R (x , y)
  R ⊤⊥R _ = 𝟘

  --%% is this...a relation whose underlying sets are supposed to move along proofs implicitly?
  --%% think so, but (confusion)
  ⌜ R ⌝R (x , y) = ⌜ R ⊤⊥R (x , y) ⌝
open Rel

-- anyway, onwards to....indexed things.
module Indexed where
  -- ......yeah ok I'm not doing microscopic dots above.
  𝟘∙ 𝟙∙ : {I : Set} -> I -> Set
  𝟘∙ i = 𝟘
  𝟙∙ i = 𝟙

  _+∙_ _×∙_ _-∙>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> I -> Set
  (L +∙ R) i = L i + R i
  (L ×∙ R) i = L i × R i
  (L -∙> R) i = L i -> R i
  infixr 3 _+∙_; infixr 4 _×∙_; infixr 2 _-∙>_

  --..also do not understand use-cases of "always works" really, but: forging on
  [_] : {I : Set} -> (I -> Set) -> Set
  [ F ] = ∀ {i} -> F i

  -- the point of this all is.....to be able to talk about indexed things w/o mentioning indices?
  -- which....is kinda convenient, I suppose. and...I think we don't care to change indices, mostly?
  -- & instead want them to be preserved.

-- I think this is also part of Indexed really, but can do separate; separate is good really.
module PivotedSum where
  -- pivoted sum? well kiiinda.
  -- ...the point is that p which pivots the two _exists_. --or rather, that it's Sigma's fst.
  -- %%....oh, and it's immediately on extended pivots? hm, ok.%%
  _/∙\_ : ∀ {P} -> Rel (P ⊤⊥) -> Rel (P ⊤⊥) -> Rel (P ⊤⊥)
  _/∙\_ {P} L R (x , y) = Σ P λ p → L (x , # p) × R (# p , y)

  pattern _،_،_ l p r = p , l , r
  infixr 5 _،_،_
  
  -- ......ok, somewhere here I start to realize the point of Rel
  -- when we have P -> P -> 𝟚, we can express...computable things on pairs of P×P,
  -- but we can't express more complicated things; e.g. rich evidence for _how_ something holds
  -- for a particular pair.
  -- sure sure we ultimately want all proofs hidden, but often they do need to exist; just, implicitly.

  -- the fuck is an interval?
  -- definitionally, it's....for a given pair (x , y), there's a pivot p for which
  -- L x p and L p y hold, but...we ~~don't care how they hold~~ want to get the way
  -- they hold from context. right? ...something like that.
  _∙ : ∀ {P} -> Rel P -> Rel (P ⊤⊥)
  R ∙ = ⌜ R ⌝R /∙\ ⌜ R ⌝R

  -- and with that, we can...match on _∙ without cruft, extracting only p explicitly and letting
  -- implicit evidence propagate? I suppose!!!
  pattern _° p = ! ، p ، !

module MBST (P : Set) (R : Rel P) (owoto : ∀ x y -> OWOTO R (x , y)) where
  -- Iiiiii think this should work just as before? with adjustments, but w/e, those should be obvious
  -- except I recall McBride doing some voodoo bullshit right off the bat, so er

  -- ok, plan: redo BST, retry insert.

  module Plain-BST where
    data BST (l u : P ⊤⊥) : Set where
      leaf : BST l u
      pnode : (p : P) -> BST l (# p) -> BST (# p) u ->
        -- `So (_ ≤ _)` is now R; ⊤⊥R upgrades R from P to P ⊤⊥
        R ⊤⊥R (l , # p) ⇒ R ⊤⊥R (# p , u) ⇒ BST l u
    pattern node lt p rt = pnode p lt rt

    insert : ∀ {l u} x -> BST l u -> R ⊤⊥R (l , # x) ⇒ R ⊤⊥R (# x , u) ⇒ BST l u
    insert x leaf = node leaf x leaf
    insert x (node lt p rt) with owoto x p
    -- oh good this is a type error for us too.
    -- ...| le = insert x lt
    ...| le = node (insert x lt) p rt
    ...| ge = node lt p (insert x rt)

    -- woohoo!

  -- .....ok, I kinda see how and why they do everything indexedly.
  -- it's a natural-ish way to bundle ≈relations on same indices,
  -- ...and then also to implicify some of them, and then to ≈extract pivots...
  -- ok, now let's do the thing above indexedly.
  module Indexed-BST where
    open Indexed
    open PivotedSum
    
    data BST (lu : P ⊤⊥ × P ⊤⊥) : Set where
      leaf : BST lu
      pnode : (((⌜ R ⌝R ×∙ BST) /∙\ (⌜ R ⌝R ×∙ BST)) -∙> BST) lu
    pattern node lt p rt = pnode (p , (! , lt) , (! , rt))

    -- -∙> chain just like ->, sure; [ ] means "∀ {lu} (...) lu", so, yeah, checks out.
    insert : [ (R ∙) -∙> BST -∙> BST ]
    insert (x °) leaf = node leaf x leaf
    insert (x °) (node lt p rt) with owoto x p
    ...| le = node (insert (x °) lt) p rt
    ...| ge = node lt p (insert (x °) rt)

  -- ok, so in Indexed we built a...library of type combinators uniform-in-indexes,
  -- and then in PivotedSum a combinator for..like, joining-rels-at-a-pivot?
  -- and then of course for "there's a pivot between 2 points of the relation, hide the proofs".

open MBST
-- All right; let's move on.

module Rot (P : Set) (R : Rel P) (owoto : ∀ x y -> OWOTO R (x , y)) where
  module Fail-Rot where
    open Plain-BST P R owoto

    rotR : ∀ {l u} -> BST l u -> BST l u
    -- we know, generally, that l ≤ lt ≤ m ≤ mt ≤ p ≤ rt ≤ u.
    -- ...some of these things are demanded, some are...construction-inductive:
    -- l ≤ m ≤ p and l ≤ p ≤ u are direct; l ≤ lt ≤ m are by implication — any pivot inside lt will need to satisfy l ≤ x ≤ m, and from there "by transitivity".
    -- what we _don't_ know is that m ≤ u. transitively it'd hold, certainly, but, y'know. don't wanna involve proofs of transitivity or anything.
    rotR (node (node lt m mt) p rt) = BS tt -- {!node lt m (node mt m rt)!}
    rotR t = t
    
  -- Q: so what do we do?
  -- A: from hints from the paper, I think we need to cut down on requisite ≤s we need to know in the tree.
  -- (paper paper) ----ok, I see how there are n+1 leaves (out of 2n+1 nodes & n branches), and......I pretty much see directly how they ≈directly correspond to evidence that pivots are correctly ordered?
  -- like, draw an example 2-node tree to rotR and draw its bounds, and bounds<->leaves correspondence falls out.
  -- ok, now let's try to implement this.

  module Plain-Rot where
    data BST (l u : P ⊤⊥) : Set where
      leaf : R ⊤⊥R (l , u) ⇒ BST l u
      pnode : (p : P) -> BST l (# p) -> BST (# p) u -> BST l u
    pattern node lt p rt = pnode p lt rt

    rotR : ∀ {l u} -> BST l u -> BST l u
    -- it even caught mistyped m in the right subtree! awesome.
    rotR (node (node lt m mt) p rt) = node lt m (node mt p rt)
    rotR t = t
    
    -- insert still works, right?
    insert : ∀ {l u} x -> BST l u -> R ⊤⊥R (l , # x) ⇒ R ⊤⊥R (# x , u) ⇒ BST l u
    insert x leaf = node leaf x leaf
    insert x (node lt p rt) with owoto x p
    ...| le = node (insert x lt) p rt
    ...| ge = node lt p (insert x rt) 

  module Indexed-Rot where
    open Indexed; open PivotedSum
    data BST (lu : P ⊤⊥ × P ⊤⊥) : Set where
      pleaf : (⌜ R ⌝R -∙> BST) lu
      pnode : (BST /∙\ BST -∙> BST) lu
    pattern leaf = pleaf !
    pattern node lt p rt = pnode (p , lt , rt)

    rotR : [ BST -∙> BST ]
    -- it even caught mistyped m in the right subtree! awesome.
    rotR (node (node lt m mt) p rt) = node lt m (node mt p rt)
    rotR t = t

    insert : [ R ∙ -∙> BST -∙> BST ]
    insert (x °) leaf = node leaf x leaf
    insert (x °) (node lt p rt) with owoto x p
    ...| le = node (insert (x °) lt) p rt
    ...| ge = node lt p (insert (x °) rt)

open Rot

-- All right! now, can we figure lists ≈just from the hint that it's an unbalanced tree, whose left subtree is always leaf? let's see!
module List (P : Set) (R : Rel P) (owoto : ∀ x y -> OWOTO R (x , y)) where
  module Plain-List where
    data List (l u : P ⊤⊥) : Set where
      [] : R ⊤⊥R (l , u) ⇒ List l u
      -- ..well, not a direct translation: we need to inline the data held in the empty leaves;
      -- namely, that R l (# p). well then!
      _∷_ : (p : P) -> List (# p) u -> R ⊤⊥R (l , # p) ⇒ List l u
    infixr 5 _∷_

    -- ...ok, plain lists are boring. let's at least concat them.
    -- .....I _think_ we won't be able to concat lists w/ unequal middle bound?
    -- let's see how it works as-is though.
    _++_ : ∀ {l m u} -> List l m -> List m u -> List l u
    -- ...doesn't work! at least not naively, and we want naiviete.
    -- Section 14 hints how to type this bullshit such that it works, but I don't think I want to figure it out today.
    [] ++ r = {!!}
    (p ∷ l) ++ r = {!!}

    -- ...ok, then merge, maybe?
    {-# TERMINATING #-}
    merge : ∀ {l u} -> List l u -> List l u -> List l u
    merge [] r = r
    merge l [] = l
    merge (xl ∷ l) (xr ∷ r) with owoto xl xr
    ...| le = xl ∷ merge l (xr ∷ r)
    ...| ge = xr ∷ merge (xl ∷ l) r
    -- aha, yeah, termination problems. ok, let's try for a properly terminating one.

    mergeT : ∀ {l u} -> List l u -> List l u -> List l u
    mergeT [] = \r -> r
    mergeT {l} {u} (lx ∷ ls) = go where
      -- that was.....horrible. can we, iunno, reduce the type somewhat.
      -- ........yes, and then uh........why in the fuck ⦃ _ : T ⦄ different from ⦃ T ⦄ ???
      go : ∀ {m} ⦃ _ : R ⊤⊥R (m , # lx) ⦄ -> List m u → List m u
      go [] = lx ∷ ls
      go (rx ∷ rs) with owoto lx rx
      ...| le = lx ∷ mergeT ls (rx ∷ rs)
      ...| ge = rx ∷ go rs
    -- .....ok, got it, slapping TERMINATING on this bullshit is fine and appropriate.

  module Indexed-List where
    open Indexed; open PivotedSum
    data List (lu : P ⊤⊥ × P ⊤⊥) : Set where
      pnil : (⌜ R ⌝R -∙> List) lu
      pcons : (⌜ R ⌝R /∙\ List -∙> List) lu
    pattern nil = pnil !
    pattern cons x xs = pcons (x , ! , xs )

open List

-- ....and from there, there's...the universe of containers, which: LATER
