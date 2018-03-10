{-
    Mastermind
    Copyright © 2013 Hegedűs Dénes (hegedenes@gmail.com)

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}

{-
    Mastermind.Auxiliary modul
    Segédfüggvények definíciói
-}

module Mastermind.Auxiliary where

{-
    Importok
-}

open import FRP.JS.Nat    using (ℕ ; suc ; zero ; show ; _+_ ; _∸_)
open import FRP.JS.Bool   using (Bool ; true ; false ; if_then_else_ ; not ; _∧_)
open import FRP.JS.List   using (List ; _∷_ ; [] ; foldl ; foldr ; map ; _++_ ; length)
open import FRP.JS.Maybe  using (Maybe ; nothing ; just)
open import FRP.JS.String using (String) renaming (_++_ to _++s_)

{-
    Direktszorzat
-}

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_

proj₁ : {A B : Set} → A × B → A
proj₁ (a , b) = a

proj₂ : {A B : Set} → A × B → B
proj₂ (a , b) = b

{-
    Lista
-}

and : List Bool → Bool
and = foldr _∧_ true

all : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
all p l = and (map p l)

unzip : ∀ {A B : Set} → List (A × B) → List A × List B
unzip = foldr f ([] , []) where
  f : ∀ {A B} → A × B → List A × List B → List A × List B
  f (a , b) (as , bs) = (a ∷ as) , (b ∷ bs)

deleteBy : ∀ {A : Set} → (A → A → Bool) → A → List A → List A
deleteBy _  _ []       = []
deleteBy eq x (y ∷ ys) = if (eq x y) then ys else (y ∷ deleteBy eq x ys)

flip : ∀ {A B : Set} {C : A → B → Set} →
       ((x : A) (y : B) → C x y) 
        → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

_\\_by_ : {A : Set} → List A → List A → (A → A → Bool) → List A 
a \\ b by f = foldl (flip (deleteBy f)) a b

zipWith : ∀ {A B C : Set} → (A → B → C) → List A → List B → List C
zipWith f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys
zipWith f _        _        = []

zip : ∀ {A B : Set} → List A → List B → List (A × B)
zip = zipWith (_,_)

gfilter : ∀ {A B : Set} → (A → Maybe B) → List A → List B
gfilter p []       = []
gfilter p (x ∷ xs) with p x
... | just y  = y ∷ gfilter p xs
... | nothing =     gfilter p xs

filter : ∀ {A : Set} → (A → Bool) → List A → List A
filter p = gfilter (λ x → if p x then just x else nothing)

uncurry : ∀ {A B C : Set} → (A → B → C) → (A × B → C)
uncurry f (a , b) = f a b

replicate : ∀ {A : Set} → (n : ℕ) → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

replace : ∀ {A : Set} → ℕ → List A → A → List A
replace zero [] y = []
replace zero (x ∷ xs) y = y ∷ xs
replace (suc n) [] y = []
replace (suc n) (x ∷ xs) y = x ∷ replace n xs y

count : ∀ {A : Set} → (p : A → Bool) → (v : List A) → ℕ
count p [] = 0
count p (x ∷ xs) = (if (p x) then 1 else 0) + count p xs

{-
    Vektor
-}

data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

infixr 4 _∷_

replacev : ∀ {A : Set} {n} → ℕ → Vec A n → A → Vec A n
replacev _       []       y = []
replacev zero    (x ∷ xs) y = y ∷ xs
replacev (suc n) (x ∷ xs) y = x ∷ replacev n xs y

replicatev : ∀ {a n} {A : Set a} → A → Vec A n
replicatev {n = zero}  x = []
replicatev {n = suc n} x = x ∷ replicatev x

infixl 4 _⊛_

_⊛_ : ∀ {a b n} {A : Set a} {B : Set b} →
      Vec (A → B) n → Vec A n → Vec B n
[]       ⊛ []       = []
(f ∷ fs) ⊛ (x ∷ xs) = f x ∷ (fs ⊛ xs)

mapv : ∀ {a b n} {A : Set a} {B : Set b} →
      (A → B) → Vec A n → Vec B n
mapv f xs = replicatev f ⊛ xs

zipWithv : ∀ {a b c n} {A : Set a} {B : Set b} {C : Set c} →
          (A → B → C) → Vec A n → Vec B n → Vec C n
zipWithv _⊕_ xs ys = replicatev _⊕_ ⊛ xs ⊛ ys

zipv : ∀ {n} {A : Set} {B : Set} →
      Vec A n → Vec B n → Vec (A × B) n
zipv = zipWithv _,_

toList : ∀ {a n} {A : Set a} → Vec A n → List A
toList []       = List.[]
toList (x ∷ xs) = List._∷_ x (toList xs)

fromList : ∀ {a} {A : Set a} → (xs : List A) → Vec A (length xs)
fromList []       = []
fromList (x ∷ xs) = x ∷ fromList xs

lookupv : ∀ {α} {A : Set α} {n : ℕ} → Vec A n → ℕ → Maybe A
lookupv []       x       = nothing
lookupv (a ∷ as) zero    = just a
lookupv (a ∷ as) (suc n) = lookupv as n

foldlv : ∀ {α β} {A : Set α} {B : Set β} {n} → (A → B → A) → A → Vec B n → A
foldlv c n []       = n
foldlv c n (x ∷ xs) = foldlv c (c n x) xs

{-
andv : ∀ {n} → Vec Bool n → Bool
andv = foldlv _∧_ true

allv : ∀ {a} {n} {A : Set a} → (A → Bool) → Vec A n → Bool
allv p l = andv (mapv p l)

countv : ∀ {A : Set} {n : ℕ} → (p : A → Bool) → (v : Vec A n) → ℕ
countv p [] = 0
countv p (x ∷ xs) = (if (p x) then 1 else 0) + countv p xs

filterv : ∀ {A : Set} {n : ℕ} → (p : A → Bool) → (v : Vec A n) → Vec A (countv p v)
filterv p []       = []
filterv p (x ∷ xs) with p x
... | true  = x ∷ filterv p xs
... | false =     filterv p xs

foldrv : ∀ {α β} {A : Set α} {B : Set β} {n} → (A → B → B) → B → Vec A n → B
foldrv c n []       = n
foldrv c n (x ∷ xs) = c x (foldrv c n xs)
-}

{-
    ℕ
-}

_<_ : ℕ → ℕ → Bool
n     < zero = false
zero  < suc y = true
suc n < suc m = n < m

_≟_ : ℕ → ℕ → Bool
zero  ≟ zero          = true
suc m ≟ suc n with m ≟ n
suc m ≟ suc n | true  = true
suc m ≟ suc n | false = false
n     ≟ m             = false

_⊓_ : ℕ → ℕ → ℕ
zero  ⊓ n     = zero
suc m ⊓ zero  = zero
suc m ⊓ suc n = suc (m ⊓ n)

{-
    Véges elemszámú típus
-}

module Fin where

  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (suc n)
    suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

  toℕ : ∀ {n} → Fin n → ℕ
  toℕ zero    = 0
  toℕ (suc i) = suc (toℕ i)

  fromℕ : (n : ℕ) → Fin (suc n)
  fromℕ zero    = zero
  fromℕ (suc n) = suc (fromℕ n)

  inc : ∀ {n} → Fin n → Fin n
  inc {zero} ()
  inc {suc zero} zero = zero
  inc {suc zero} (suc ())
  inc {suc (suc y)} zero = suc zero
  inc {suc (suc y)} (suc i) = suc (inc i)

  inject₁ : ∀ {m} → Fin m → Fin (suc m)
  inject₁ zero    = zero
  inject₁ (suc i) = suc (inject₁ i)

  pred : ∀ {n} → Fin n → Fin n
  pred zero    = zero
  pred (suc i) = inject₁ i