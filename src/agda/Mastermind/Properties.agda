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
    Mastermind.Properties modul
    Tesztelési terv megvalósítása és állítások bizonyítása
-}

module Mastermind.Properties where

{-
    Importok
-}

open import FRP.JS.Bool renaming (_≟_ to _≟b_)
open import FRP.JS.List
open import FRP.JS.Nat hiding (_≟_ ; _<_)
open import FRP.JS.Maybe

open import Mastermind.Auxiliary
open Mastermind.Auxiliary.Fin

open import Mastermind.Model
open import Mastermind.View
open import Mastermind.View.Base

{-
    Segéd definíciók
-}

-- Propozícionális ekvivalencia

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

infix 4 _≡_

data ⊥ : Set where

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ x ≡ y

sym : ∀ {A : Set} {a b : A} → (a ≡ b) → (b ≡ a)
sym refl = refl

trans : ∀ {A : Set} {a b c : A} → (a ≡ b) → (b ≡ c) → (a ≡ c)
trans refl refl = refl

cong : ∀ {A : Set} {B : Set} (f : A → B) {a₁ a₂ : A} → (a₁ ≡ a₂) → (f a₁ ≡ f a₂)
cong f refl = refl

{-
    Tesztelés
-}

-- Léptetés jelölése
_>>_ : State → Button → State
state >> button = step state button

infixl 10 _>>_

restart≡newGame : ∀ {s : State} → step s restart ≡ newGame s
restart≡newGame = refl

-- Teszteset₁: Amelyik 4 színt megadjuk az elején, az kerül a tippbe.
test₁ : {n : ℕ} {a b c d : Color} → 
  State.guess (init n >> color a >> color b >> color c >> color d) ≡ (a ∷ b ∷ c ∷ d ∷ [])
test₁ = refl

lemma-fin : ∀ {n} → (i : Fin n) → toℕ i < n ≡ true
lemma-fin zero    = refl
lemma-fin (suc i) = lemma-fin i

-- Teszteset₂: Nem léphetünk ki a tippből léptetésnél.
test₂ : (s : State) → toℕ (State.guesspos s) < 4 ≡ true
test₂ s = lemma-fin (State.guesspos s)

-- Teszteset₃: Ha véget ért a játék, akkor csak a restart gomb használható.
no-step-when-ended :
  ∀ {e : End} → (s : State) → (b : Button) →
  b ≢ restart → ‌State.gamestate s ≡ ended e →
  step s b ≡ s
no-step-when-ended s restart np p with np refl
no-step-when-ended s restart np p | ()
no-step-when-ended s (color y) np p  with State.gamestate s
no-step-when-ended s (color y) np () | active
no-step-when-ended s (color y) np refl | ended _ = refl
no-step-when-ended s (move y) np p  with State.gamestate s
no-step-when-ended s (move y) np () | active
no-step-when-ended s (move y) np refl | ended _ = refl
no-step-when-ended s ok np p with State.gamestate s
no-step-when-ended s ok np () | active
no-step-when-ended s ok np refl | ended _ = refl
no-step-when-ended s clear np p with State.gamestate s
no-step-when-ended s clear np () | active
no-step-when-ended s clear np refl | ended _ = refl

lemma-lookupv :
  ∀ {n : ℕ} {A : Set} {a : A}
  (fn : Fin n) (v : Vec A n) →
  lookupv (replacev (toℕ fn) v a) (toℕ fn) ≡ just a
lemma-lookupv () []
lemma-lookupv zero (x ∷ xs) = refl
lemma-lookupv (suc i) (x ∷ xs) = lemma-lookupv i xs

-- Teszteset₄: Szín megadása esetén a tipp aktuális pozíciójára a szín kerül
test-modifyColor : 
  ∀ {c : Color} (s : State) →
  lookupv (State.guess (modifyColor c s)) -- megváltozott állapot tippjének
          (toℕ (State.guesspos s))        -- az eredeti állapot tippjének
                                          -- aktuális pozícióján
  ≡ just c                                -- az új szín lesz
test-modifyColor s = lemma-lookupv (State.guesspos s) (State.guess s)

{-
    Bizonyítások
-}

-- Egyenlőségi érvelés

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ refl ⟩ refl = refl

infixr 2 _≡⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

infix 2 _∎

-- Állítás₁: A 4 fekete találat megoldás.
isSolved-law₁ : isSolved (black ∷ black ∷ black ∷ black ∷ []) ≡ true
isSolved-law₁ = refl

-- Tétel₁: Azonos tipp és megoldás 4 fekete találatot ad.
check-law₁ : (c : Colors) → check c c ≡ (black ∷ black ∷ black ∷ black ∷ [])
check-law₁ c =
  check c c
    ≡⟨ refl ⟩
  blacks ++ whites
    ≡⟨ cong (λ x → blacks ++ x) law₁ ⟩
  blacks ++ []
    ≡⟨ cong (λ x → x ++ []) law₂ ⟩
  black ∷ black ∷ black ∷ black ∷ []
    ∎
  where
    zipped = toList (zipv c c)

    rr     = unzip (filter (not ∘ uncurry _≟_) zipped)
    rg     = proj₁ rr
    rs     = proj₂ rr
    whitec = length (rg \\ (rg \\ rs by _≟_) by _≟_)
    whites = replicate whitec white

    fs     = filter (uncurry _≟_) zipped
    blacks = map (λ _ → black) fs


    ≟-preserves-suc : ∀ (n : ℕ) → n ≟ n ≡ true → suc n ≟ suc n ≡ true
    ≟-preserves-suc zero p = refl
    ≟-preserves-suc (suc n) p with n ≟ n
    ≟-preserves-suc (suc n) refl | true = refl
    ≟-preserves-suc (suc n) () | false

    ≟-refl : ∀ (n : ℕ) → n ≟ n ≡ true
    ≟-refl zero    = refl
    ≟-refl (suc y) = ≟-preserves-suc y (≟-refl y)

    {-
        Állítás₁: A fehérek száma 0.
    -}

    gf  = λ y → if (not (uncurry _≟_ y)) then just y else nothing

    gf-lemma : (x : Color) → gf (x , x) ≡ nothing
    gf-lemma zero = refl
    gf-lemma (suc n) with ≟-refl n
    ... | p with n ≟ n
    gf-lemma (suc n) | refl | true = refl
    gf-lemma (suc n) | () | false

    gfilter-lemma : {n : ℕ}
      (x : Color) → (xs : Vec Color n) →
      gf (x , x) ≡ nothing →
      gfilter gf (toList (zipv (x ∷ xs) (x ∷ xs))) ≡ gfilter gf (toList (zipv xs xs))
    gfilter-lemma x xs p with gf (x , x)
    gfilter-lemma x xs refl | .nothing = refl
  

    rg-ind : {n : ℕ} → (v : Vec Color n) → filter (not ∘ uncurry _≟_) (toList (zipv v v)) ≡ []
    rg-ind [] = refl
    rg-ind (x ∷ xs) =
      filter (not ∘ uncurry _≟_) (toList (zipv (x ∷ xs) (x ∷ xs)))
        ≡⟨ refl ⟩
      gfilter gf (toList (zipv (x ∷ xs) (x ∷ xs)))
        ≡⟨ gfilter-lemma x xs (gf-lemma x) ⟩
      gfilter gf (toList (zipv xs xs))
        ≡⟨ rg-ind xs ⟩
      []
        ∎

    rg≡[] : rg ≡ []
    rg≡[] = cong (proj₁ ∘ unzip) (rg-ind c)

    \\-lemma : (l : List Color) → ([] \\ l by _≟_) ≡ []
    \\-lemma [] = refl
    \\-lemma (x ∷ xs) = \\-lemma xs

    whitec≡0 : whitec ≡ 0
    whitec≡0 =
      whitec
        ≡⟨ refl ⟩
      length (rg \\ (rg \\ rs by _≟_) by _≟_)
        ≡⟨ cong (λ x → length (x \\ (rg \\ rs by _≟_) by _≟_)) rg≡[] ⟩
      length ([] \\ (rg \\ rs by _≟_) by _≟_)
        ≡⟨ cong length (\\-lemma (rg \\ rs by _≟_)) ⟩
      length {_} {Color} []
        ≡⟨ refl ⟩
      0
        ∎

    law₁ : whites ≡ []
    law₁ =
      whites
        ≡⟨ refl ⟩
      replicate whitec white
        ≡⟨ cong (λ x → replicate x white) whitec≡0 ⟩
      replicate 0 white
        ≡⟨ refl ⟩
      []
        ∎

    {-
        Állítás₂: A feketék száma 4.
    -}

    gf2 = λ y → if (uncurry _≟_ y) then just y else nothing

    gf2-lemma : (x : Color) → gf2 (x , x) ≡ just (x , x)
    gf2-lemma zero = refl
    gf2-lemma (suc n) with ≟-refl n
    ... | p with n ≟ n
    gf2-lemma (suc n) | refl | true = refl
    gf2-lemma (suc n) | () | false

    gfilter-lemma2 : {n : ℕ} (x : Color) → (xs : Vec Color n) →
      gf2 (x , x) ≡ just (x , x) →
      gfilter gf2 (toList (zipv (x ∷ xs) (x ∷ xs))) ≡ ((x , x) ∷ gfilter gf2 (toList (zipv xs xs)))
    gfilter-lemma2 x xs p with gf2 (x , x)
    gfilter-lemma2 x xs refl | .(just (x , x)) = refl

    fs-ind : {n : ℕ} → (v : Vec Color n) → filter (uncurry _≟_) (toList (zipv v v)) ≡ (toList (zipv v v))
    fs-ind [] = refl
    fs-ind (x ∷ xs) =
      filter (uncurry _≟_) (toList (zipv (x ∷ xs) (x ∷ xs)))
        ≡⟨ refl ⟩
      gfilter gf2 (toList (zipv (x ∷ xs) (x ∷ xs)))
        ≡⟨ gfilter-lemma2 x xs (gf2-lemma x) ⟩
      ((x , x) ∷ gfilter gf2 (toList (zipv xs xs)))
        ≡⟨ cong (λ e → (x , x) ∷ e) (fs-ind xs) ⟩
      (x , x) ∷ toList (zipv xs xs)
        ≡⟨ refl ⟩
      toList (zipv (x ∷ xs) (x ∷ xs))
        ∎

    replicate-lemma : {A : Set} → (n : ℕ) → (v : Vec A n) → map (λ _ → black) (toList v) ≡ replicate n black
    replicate-lemma .0 [] = refl
    replicate-lemma .(suc n) (_∷_ {n} x xs) = cong (_∷_ black) (replicate-lemma n xs)

    law₂ : blacks ≡ (black ∷ black ∷ black ∷ black ∷ [])
    law₂ =
      blacks
        ≡⟨ refl ⟩
      map (λ _ → black) fs
        ≡⟨ cong (λ e → map (λ _ → black) e) (fs-ind c) ⟩
      map (λ _ → black) zipped
        ≡⟨ replicate-lemma 4 (zipv c c) ⟩
      replicate 4 black
        ≡⟨ refl ⟩
      (black ∷ black ∷ black ∷ black ∷ [])
        ∎

check-law₁-solution : ∀ (c : Colors) → isSolved (check c c) ≡ true
check-law₁-solution c =
  isSolved (check c c)
    ≡⟨ cong isSolved (check-law₁ c) ⟩
  isSolved (black ∷ black ∷ black ∷ black ∷ [])
    ≡⟨ refl ⟩
  true
    ∎