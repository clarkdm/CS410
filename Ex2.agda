module Ex2 where

----------------------------------------------------------------------------
-- EXERCISE 2 -- STRUCTURE WITH VECTORS
--
-- VALUE:     15%
-- DEADLINE:  5pm, Friday 23 October (week 5)
--
-- DON'T SUBMIT, COMMIT!
--
-- The purpose of this exercise is to introduce you to some useful
-- mathematical structures and build good tools for working with
-- vectors
----------------------------------------------------------------------------


open import CS410-Prelude
open import CS410-Monoid
open import CS410-Nat
open import CS410-Vec
open import CS410-Functor



-- HINT: your tasks are heralded with the eminently searchable tag, "???"


----------------------------------------------------------------------------
-- ??? 2.1 replicattion to make a constant vector             (score: ? / 1)
----------------------------------------------------------------------------

vec : forall {n X} -> X -> Vec X n
vec {zero} x = []
vec {suc n} x = x :: vec x

-- HINT: you may need to override default invisibility

-- SUSPICIOUS: no specification? why not?


----------------------------------------------------------------------------
-- ??? 2.2 vectorised application                             (score: ? / 1)
----------------------------------------------------------------------------

-- implement the operator which takes the same number of functions
-- and arguments and computes the applications in corresponding
-- positions

vapp : forall {n X Y} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
vapp [] xs = []
vapp (x :: fs) (y :: xs) = x y :: vapp fs xs


----------------------------------------------------------------------------
-- ??? 2.3 one-liners                                         (score: ? / 1)
----------------------------------------------------------------------------

-- implement map and zip for vectors using vec and vapp
-- no pattern matching or recursion permitted


vmap : forall {n X Y} -> (X -> Y) -> Vec X n -> Vec Y n
vmap f xs = vapp (vec f) xs

vzip : forall {n X Y} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vzip xs ys = vapp (vmap _,_ xs) ys


----------------------------------------------------------------------------
-- ??? 2.4 unzipping                                          (score: ? / 2)
----------------------------------------------------------------------------

-- implement unzipping as a view, showing that every vector of pairs
-- is given by zipping two vectors

-- you'll need to complete the view type yourselfiew type yourself

data Unzippable {X Y n} : Vec (X * Y) n -> Set where
     unzipped : (xs : Vec X n)(ys : Vec Y n) -> Unzippable (vzip xs ys)

  
unzip : forall {X Y n}(xys : Vec (X * Y) n) -> Unzippable xys
unzip [] = unzipped [] []
unzip (fst , snd :: []) = unzipped (fst :: []) (snd :: [])
unzip (fst , snd :: xys) with unzip xys
unzip (fst , snd :: .(vapp (vapp (vec _,_) xs) ys)) | unzipped xs ys = 
                                            unzipped (fst :: xs) (snd :: ys)

----------------------------------------------------------------------------
-- ??? 2.5 vectors are applicative                            (score: ? / 2)
----------------------------------------------------------------------------

-- prove the Applicative laws for vectors

VecApp : forall n -> Applicative \X -> Vec X n
VecApp n = record
  { pure         = vec
  ; _<*>_        = vapp
  ; identity     = \ {X} v -> VecAppIdentity v
  ; composition  = λ u v w →  VecAppComposition w v u 
  ; homomorphism = λ f x →  VecAppHomomorphism n x f
  ; interchange  = λ {X} {Y} u y → VecAppInterchange y u
  } where
  -- lemmas go here

  --  Goal: vapp (vec (λ x → x)) v == v
  VecAppIdentity : {X : Set} -> {n : Nat} -> (v : Vec X n) -> 
                                       vapp (vec (\ x -> x)) v == v 
  VecAppIdentity [] = refl
  VecAppIdentity (x :: v) rewrite VecAppIdentity v =  refl

  --  Goal: vapp (vapp (vapp (vec (λ f g x → f (g x))) u) v) w == vapp u (vapp v w)

  VecAppComposition : {Z : Set} -> {Y : Set} -> {X : Set} -> {n : Nat} -> 
                      (w : Vec X n) -> (v : Vec (X → Z) n) -> (u : Vec (Z → Y) n)-> 
                      vapp (vapp (vapp (vec (λ f g x → f (g x))) u) v) w == vapp u (vapp v w)
  VecAppComposition [] [] [] = refl
  VecAppComposition (x :: w) (x₁ :: v) (x₂ :: u)rewrite VecAppComposition w v u  = refl

  --  Goal: vec (f x) == vapp (vec f) (vec x)
  VecAppHomomorphism : {X : Set} -> {Y : Set} -> (q : Nat) -> (x : X) -> (f : X → Y) -> 
                       vec {q} (f x)  == vapp (vec f) (vec x)
  VecAppHomomorphism zero x f = refl
  VecAppHomomorphism (suc q) x f rewrite VecAppHomomorphism q x f =  refl

  --  Goal: vapp u (vec y) == vapp (vec (λ f → f y)) u
  VecAppInterchange : {Y : Set} -> {X : Set} -> {n : Nat} -> (y : X) -> (u : Vec (X → Y) n) -> vapp u (vec y) == vapp (vec (λ f → f y)) u

  VecAppInterchange u [] = refl
  VecAppInterchange u (x :: y)  rewrite VecAppInterchange u y = refl

----------------------------------------------------------------------------
-- ??? 2.6 vectors are traversable                            (score: ? / 1)
----------------------------------------------------------------------------

-- show that vectors are traversable; make sure your traverse function
-- acts on the elements of the input once each, left-to-right

  VecTrav : forall n -> Traversable \X -> Vec X n
  VecTrav zero = record { traverse = λ {F} z {A} {B} _ _ → Applicative.pure z [] }
  VecTrav (suc n) = record { traverse = λ x x₁ x₂ → {!!} } 
 
--VecTrav zero = record { traverse = λ {F} z {A} {B} _ _ → Applicative.pure z [] }
--VecTrav (suc n) =  record { traverse = λ {F} x y z → {!!} }


----------------------------------------------------------------------------
-- ??? 2.7 monoids make constant applicatives                 (score: ? / 1)
----------------------------------------------------------------------------

-- Show that every monoid gives rise to a degenerate applicative functor

MonCon : forall {X} -> Monoid X -> Applicative \_ -> X
MonCon M = record
             { pure          = λ x → Monoid.e M
             ; _<*>_         = op
             ; identity      = λ v → Monoid.lunit M v
             ; composition   = λ u v w → {!!}
             ; homomorphism  = λ f x → {!!}
             ; interchange   = λ u y → {!!}
             } where open Monoid M

       --MonConCoposition : (w : Set) -> (v : Set) -> (u : Set) -> op (op (op e u) v) w == op u (op v w)
       --MonConCoposition x = ?

----------------------------------------------------------------------------
-- ??? 2.8 vector combine                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Using your answers to 2.6 and 2.7, rather than any new vector recursion,
-- show how to compute the result of combining all the elements of a vector
-- when they belong to some monoid.

vcombine : forall {X} -> Monoid X -> forall {n} -> Vec X n -> X
vcombine M = {!!}


----------------------------------------------------------------------------
-- ??? 2.9 scalar product                                     (score: ? / 1)
----------------------------------------------------------------------------

-- Show how to compute the scalar ("dot") product of two vectors of numbers.
-- (Multiply elements in corresponding positions; compute total of products.)
-- HINT: think zippily, then combine

vdot : forall {n} -> Vec Nat n -> Vec Nat n -> Nat
vdot xs ys = ?


----------------------------------------------------------------------------
-- MATRICES
----------------------------------------------------------------------------

-- let's say that an h by w matrix is a column h high of rows w wide

Matrix : Set -> Nat * Nat -> Set
Matrix X (h , w) = Vec (Vec X w) h


----------------------------------------------------------------------------
-- ??? 2.11 identity matrix                                   (score: ? / 1)
----------------------------------------------------------------------------

-- show how to construct the identity matrix of a given size, with
-- 1 on the main diagonal and 0 everywhere else, e.g,
-- (1 :: 0 :: 0 :: []) ::
-- (0 :: 1 :: 0 :: []) ::
-- (0 :: 0 :: 1 :: []) ::
-- []

idMat : forall {n} -> Matrix Nat (n , n)
idMat = {!!}

-- HINT: you may need to do recursion on the side, but then you
-- can make good use of vec and vapp


----------------------------------------------------------------------------
-- ??? 2.10 transposition                                     (score: ? / 1)
----------------------------------------------------------------------------

-- show how to transpose matrices
-- HINT: use traverse, and it's a one-liner

transpose : forall {X m n} -> Matrix X (m , n) -> Matrix X (n , m)
transpose = {!!}


----------------------------------------------------------------------------
-- ??? 2.11 multiplication                                    (score: ? / 2)
----------------------------------------------------------------------------

-- implement matrix multiplication
-- HINT: transpose and vdot can be useful

matMult : forall {m n p} ->
          Matrix Nat (m , n) -> Matrix Nat (n , p) -> Matrix Nat (m , p)
matMult xmn xnp = {!!}
