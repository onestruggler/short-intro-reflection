-- A very short introduction to Agda's reflection mechanism.

-- This code is self contained and checked by Agda version 2.6.4.3

-- Suppose we have a term (program) "t", we can evaluate it to get say
-- "t'", that is what we normally do about a term. We can also
-- manipulate its syntactic expression "s", rewrite "s" to "s'"
-- somehow, and then turn "s'" back to some program "t''" somehow. The
-- second way is called "reflection", since we manipulate "t" by
-- reflecting on "t" using "s" and "s'" to get "t''".

-- There are two kinds of reflection:

-- 1) The kind that are supported by Agda's builtin keywords (quote,
-- unquote ...), which reflects on an Agda term by manipulating its
-- Agda-AST representation. No parsing needed here, we can just quote
-- the term's to get Agda-AST.

-- 2) The kind that doesn't need keyword support, which reflects on an
-- Agda term by manipulating a user-defined AST that is somehow
-- "isomorphic" to the term's structure (or, that captures the main
-- structure of the term). E.g. the structure of the term "x + y * z"
-- with x y z being variables, can be captured by a syntax tree. The
-- parsing from term to AST is by hand, i.e., we have to mannually
-- type "x :+ y :* z" to build the AST for the term.

-- Both share "reflection" i.e. manipulating the term (program) by
-- AST, and not excuting the term directly.

-- Both 1) and 2) are used in Agda programming. Combing two seems
-- good, and actually, many have done so, just search "agda
-- reflection" in github, you will see a couple of interesting repos.

-- By combining two, I mean, use 1) to get Agda-AST automatically, and
-- then translate AGDA-AST to user-defined AST and then doing proof
-- under 2). This save's 2)'s mannually typing part. We will see there
-- is complications in this combining.

-- We only explain the first kind. For the second kind, there is a
-- very short and nice explanation in Section 4 of:
-- https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Documentation?action=download&upname=AgdaOverview2009.pdf

{-# OPTIONS --without-K --safe --cubical-compatible #-}
module ShortIntroReflection where 

-- Assume we have Booleans and Natural numbers, with addition and
-- boolean equality test defined.
data Bool : Set where
  true : Bool
  false : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

infixr 7 _+_
_+_ : ℕ -> ℕ -> ℕ
zero + y = y
succ x + y = succ (x + y)

infix 6 _=?_
_=?_ : ℕ -> ℕ -> Bool
zero =? zero = true
zero =? succ y = false
succ x =? zero = false
succ x =? succ y = x =? y

-- Equality, and equality is an equivalence relation, and a
-- congruence.
infix 6 _==_
data _==_ {A : Set} (a : A) : A -> Set where
  refl : a == a

sym : ∀ {A : Set} {a b : A} -> a == b -> b == a
sym refl = refl

trans : ∀ {A : Set} {a b c : A} -> a == b -> b == c -> a == c
trans refl refl = refl

cong : ∀ {A B : Set} {a a' : A} ->
       (f : A -> B) -> a == a' -> f a == f a'
cong f refl = refl

cong2 : ∀ {A B C : Set} {a a' : A} {b b' : B} ->
        (f : A -> B -> C) -> a == a' -> b == b' -> f a b == f a' b'
cong2 f refl refl = refl

-- A lemma says n + 0 = 0 for all n.
lemma-n+0 : ∀ {n : ℕ} -> n + zero == n
lemma-n+0 {zero} = refl
lemma-n+0 {(succ n)} with lemma-n+0 {n}
... | ih = cong succ ih

-- Suppose now, given a term (n + zero) : ℕ, we want rewrite it to
-- (n). One way to do it mannual is:

--  n + 0 ≡< lemma-n+0 >
--  n

rewrite-manually : ∀ n -> succ (n + zero) == succ n
rewrite-manually n = cong succ lemma-n+0

-- If we have == as the builtin equality, we can use rewrite
-- keyword. But imagine that we are doing setoid reasoing, then we
-- dont have rewrite keyword anymore.

-- If we have many such rewritings, it would be too much trouble to do
-- it mannually. Another way is to translate it to, say, a string, and
-- we write a program that search for "n + 0" and replace it with
-- "n". Then we tranlate the string back to terms, and somehow we
-- insert "lemma-n+0" at right place. We probably need some structure
-- that is better than string to support recording places where
-- "lemma-n+0" needed.

-- So we use an AST such as
infixr 8 _:+_
data AST : Set where
  Leaf : ℕ -> AST
  _:+_ : AST -> AST -> AST
  
-- We parse expressions like x + y in as x :+ y and do rewriting on
-- it. Note we can not rewrite directly on "n + 0" since + is a
-- fuction, and "n + 0" is a number without using a AST. Let f be

f : ℕ -> AST -> AST
f n (Leaf m) = Leaf m
f n t@(Leaf m :+ Leaf zero) with m =? n
... | true = Leaf m
... | false = t
f n (l :+ r) = f n l :+ f n r

-- So "f n" rewrites all "Leaf n :+ Leaf 0" to "Leaf n".

test-f : (f (succ zero) (Leaf zero :+ Leaf zero :+ Leaf (succ zero) :+ Leaf zero))
  == (Leaf zero :+ Leaf zero :+ Leaf (succ zero))
test-f = refl

-- how should we parse expression to AST? At least we can do mannual
-- parsing for finitely many expressions..... For now, suppose we have
-- the translations:

-- [_] : arithmetic expression -> AST
-- ⟦_⟧ : AST -> arithemtic expression

-- AST to expression is always easy:
⟦_⟧ : AST -> ℕ
⟦ Leaf x ⟧ = x
⟦ x :+ x₁ ⟧ = ⟦ x ⟧ + ⟦ x₁ ⟧

-- If we have properties about them:

-- ⟦_⟧ ∘ [_] = id     (1)
-- ⟦_⟧ ∘ f = ⟦_⟧      (2)

-- Then

-- e = id e = ⟦_⟧ ∘ [_] e = ⟦_⟧ ∘ f ∘ [_] e

-- The last is an expression with all "n + 0" replace by "n". Note
-- that we can prove (2) by induction on the AST.

lemma-⟦⟧ : ∀ n a ->  ⟦ a ⟧ == ⟦ f n a ⟧
lemma-⟦⟧ n (Leaf x) = refl
lemma-⟦⟧ n (Leaf x :+ Leaf zero) with x =? n
... | true = lemma-n+0
... | false = refl
lemma-⟦⟧ n (Leaf x :+ Leaf (succ x₁)) = refl
lemma-⟦⟧ n (Leaf x :+ a₁ :+ a₂) with lemma-⟦⟧ n (a₁ :+ a₂)
... | ih = cong (x +_) ih
lemma-⟦⟧ n ((a :+ a₂) :+ a₁) with lemma-⟦⟧ n (a :+ a₂) | lemma-⟦⟧ n a₁
... | ih1 | ih2 = cong2 _+_ ih1 ih2

-- But for (1), there seems no hope. Here comes the reflection to
-- rescue.

-- Using reflection, we can access (x + y)'s Agda-AST representation,
-- which is again is a term but like ((quote _+_) [quote x, quote y]
-- ):

open import Agda.Builtin.Reflection
open import Agda.Builtin.List

-- We use quoteTerm to get the Agda-AST of an expression.
eg-quote : quoteTerm (zero + zero) ==
  def (quote _+_)
      ( let modalityω = modality relevant quantity-ω in
        arg (arg-info visible modalityω) (con (quote zero) [])
      ∷ arg (arg-info visible modalityω) (con (quote zero) [])
      ∷ [])
eg-quote = refl

-- The important thing is if we do unquote to Agda's AST, we sort of
-- get things back like:

-- unquote ( (quote _+_) [quote x, quote y] ) = x + y ....

eg-unquote-refl : zero == zero
eg-unquote-refl = unquote (\h -> unify h (quoteTerm (refl {ℕ} {zero})))

-- It do seem unquote cancels quoteTerm, but *****only***** in Agda's TC
-- monad. TC is short for TypeChecking. So we can only have (1) inside
-- TC monad. Luckily, one of the side-effect of TC is that it make
-- some holes satisfied when used properly. So we don't really need
-- get (1) out of TC, we just use it inside and use the side-effect to
-- make a hole satisfied.

-- Let's see what's "unquote" doing under the hood:

open import Agda.Builtin.Unit

-- Break "eg-unquote-refl" into two parts:
refl0 : Term → TC ⊤
refl0 h = unify h (quoteTerm (refl {ℕ} {zero}))

eg-unquote' : zero == zero
eg-unquote' = unquote refl0

-- We see what we "unquote" is "refl0", which is of type "Term -> TC
-- ⊤". We can only unquote things of such type.

-- Here, "eg-unquote'" is wanting a value "refl", and more of less
-- refl0 "is" a quoted refl.... but, there is "unify" and "h" in the
-- way.

-- Actually, to unquote is to perform the computation "m : Term → TC
-- ⊤". (i.e. a TC monad computation with return type ⊤ parameterised
-- by Term). unquote will triggler the following sequence according to
-- agda mannual:

-- (1) Check if "m" is of type "Term → TC ⊤".

-- (2) Create a fresh hole at where the unquote clause is, we normally
-- know the type of the hole (because that is what we want to show. we
-- put unquote at where we put a proof term). A hole is also a
-- metavarible, say now Agda has "v : A" at disposal.

-- (3) Let "qv : Term" be the quoted representation of v, i.e., "qv =
-- quote v".

-- (4) Execute "m qv". Mainly excute "unify q v s". If qv and the
-- other quoted term "s" (e.g. "quoteTerm (refl {ℕ} {zero})") unifies,
-- then "s" is proof that fits in the hole, then Agda is satisfied.

-- If you want, you can think of that, now Agda put the unquoted "s"
-- (unquote from AST to expresssion or string in editor we read) in
-- place, in the hole. But this thingking is just a mnemonic. After
-- all Agda can only understand AST. The gives a way to hint Agda when
-- Agda is doing typechecking.

-- Is this reflection stuff still safe? Yes, it is. We didn't change
-- the typechecking algorithm at all, what we do is to only provide
-- extra inputs, extra infos to the algorithm.

-- Return to our problem: how to do automatically rewrting with having
-- equation (1) available only inside TC monad. First, we do the
-- promised translation from Agda-AST to our AST but where our AST is
-- also in quoted form (tis is the complication mentioned at the
-- begining).

-- commonly used argument info:
pattern ai = arg-info visible (modality relevant quantity-ω)

-- Note that this function only works for expression of the form "x +
-- y + z". It translate the quoted "x + y + z" to quoted "x :+ y :+
-- z".
myast-of : Term -> Term
myast-of (con (quote zero) []) = con (quote Leaf) (arg ai (con (quote zero) []) ∷ [])
myast-of (con (quote succ) (arg i a ∷ [])) with myast-of a
... | con (quote Leaf) args = con (quote Leaf) (arg ai (con (quote succ) args) ∷ [])
... | _ = unknown
myast-of (def (quote _+_) (arg i1 a1 ∷ arg i2 a2 ∷ [])) = con (quote _:+_) (arg ai (myast-of a1) ∷ arg ai (myast-of a2) ∷ [])
myast-of _ = unknown

-- Lets check it works as expected:
check1 : myast-of (quoteTerm ( zero + zero)) == quoteTerm (Leaf zero :+ Leaf zero)
check1 = refl

-- Note that check1 is a weaker form of equation (1): recall

-- ⟦_⟧ ∘ [_] = id (1), but here we have:

-- let [_] = unquote ∘ myast-of ∘ quoteTerm, we see by varing the
-- equation in check1, and by thinking of unquote as the inverse of
-- quoteTerm (only true in TC) that:

-- [ e ] = e' where e' is the corresponding term in our AST, i.e.,
-- such defined [ ] is indeed a translation:

-- [_] : arithmetic expression -> AST

-- Then we see (1) should follow, but without an agda proof.

-- We want to automatically rewrites many n + 0 while keeping
-- equality, so we also need to be able to syntactically manipulate
-- equality. E.g., we can extract the quoted lhs from quoted equality:

lhs : Term -> Term
lhs (def (quote _==_) ((arg i1 a1) ∷ (arg i2 a2) ∷ (arg i3 a3) ∷ [])) = a2 
lhs t = unknown

-- And we have quoted proof of ⟦ lhs ⟧ == ⟦ f n lhs ⟧, i.e., proof of
-- correctness of the rewriting "f n" in quoted form. (with all
-- arguments in quoted form).
q'⟦⟧ : Term -> Term → Term
q'⟦⟧ n lhs = def (quote lemma-⟦⟧) (arg ai n ∷ arg ai lhs ∷ [])

-- A parameterised TC computation that try to unify hole with provide
-- solution. We only use agda buitins, so it's a little mess. Using
-- do-notation will be cleaner. But still easy to see what's there:
-- normalize the type of the hole >>= take out lhs >>= using q'⟦⟧ on
-- lhs to generate a proof sol >>= unify hole and sol.
comp : Term -> Term -> TC ⊤
comp n hole =
  bindTC
    (bindTC
      (bindTC 
        (bindTC
          (inferType hole)
          (\h -> normalise h)
        )
        (\hole' -> returnTC (myast-of (lhs hole')))
      )
      (\l' ->  returnTC (q'⟦⟧ n l'))
    )
    ( \sol -> unify hole sol )
  -- note that if you "unify hole hole", unquote (comp n) will give
  -- you yellow backgroud meaning unsolved metavariable i.e., unsolved
  -- hole.

-- Finally,

finally1 : (succ zero + zero) + (succ zero + zero) == succ zero + succ zero
finally1 = unquote (comp (quoteTerm (succ zero)))

-- We can use macro to hide unquote and quoteTerm.
macro
  comp' : Term -> Term -> TC ⊤
  comp' = comp

finally2 : (succ zero + zero) + (succ zero + zero) == succ zero + succ zero
finally2 = comp' (succ zero)

-- Done! Thanks for reading.
