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
    Mastermind.Model modul
    A játék belső adatszerkezeteinek és logikájának implementációja
-}

module Mastermind.Model where

{-
    Importok
-}

open import FRP.JS.Nat  using (ℕ ; zero ; suc ; +_ ; _+_ ; _∸_ ; _*_)
open import FRP.JS.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_ ; not) renaming (_≟_ to _≟b_)
open import FRP.JS.List using (List ; _∷_ ; [] ; map ; _++_ ; length)

open import Mastermind.Auxiliary

{-
    Konstansok
-}

codeLength = 4
maxGuesses = 12
colorCount = 6

{-
    Típusok
-}

-- Találatok jelölése
data Match : Set where
  black white none : Match

-- Játék végének esetei
data End : Set where
  won lost : End

-- Játék állapota
data GameState : Set where
  active : GameState
  ended : End → GameState

data Direction : Set where
  ⟵ ⟶ : Direction

Color : Set
Color = ℕ

Colors : Set
Colors = Vec Color codeLength

Matches : Set
Matches = List Match

HistElem : Set
HistElem = Colors × Matches

History : Set
History = List HistElem


_%_ : ℕ -> ℕ -> ℕ
n % m = 0

{-# COMPILED_JS _%_ function(x) { return function(y) { if (x < 0) { return (x % y) + x; } else { return x % y; } }; } #-}

{-
    Véletlenszám generátor
    Linear Congruential Generator (LCG)

    Park és Miller "Minimal Standard" - Numberical Recipes 278 o.

    seed = kezdeti érték
-}

module Random (seed : ℕ) where
  private
    -- konstansok
    a = 16807
    m = 2147483647
    c = 0

    -- A sorozat következő értéke
    -- n = előző érték
    next : (n : ℕ) → ℕ
    next n = (((a * n) + c) % m)

    -- n db véletlenszám generálása
    gen-n : (n : ℕ) → ℕ → Vec ℕ n
    gen-n zero s = []
    gen-n (suc i) s = val ∷ gen-n i val where
      val = next s

    step-n : ℕ → ℕ
    step-n    0    = seed
    step-n (suc n) = next (step-n n)

  inc : ℕ
  inc = step-n 1

  newSolution : Colors × ℕ
  newSolution = mapv (λ x → (x % colorCount) + 1) (gen-n 4 seed) , step-n 4

{-
    A program belső állapota
-}

record State : Set where
  field
    guess     : Colors
    solution  : Colors
    history   : History
    gamestate : GameState
    rand      : ℕ
    guesspos  : Fin.Fin 4

{-
    Állapot-módosító függvények
-}

-- Kezdeti tipp
private
  defGuess : Colors
  defGuess = 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

-- Kezdeti állapot
init : ℕ → State
init t with Random.newSolution t
... | solution , seed =
  record
  { guess     = defGuess
  ; history   = []
  ; gamestate = active
  ; solution  = solution
  ; rand      = seed
  ; guesspos  = Fin.zero
  }

-- Véletlenszámok kezdeti értékének növelése
incStateSeed : State → State
incStateSeed s = record s { rand = Random.inc (State.rand s) }

-- Léptetés a tippben
moveGuessPos : Direction → State → State
moveGuessPos ⟶ s =
  record s { guesspos = (Fin.inc (State.guesspos s))  }
moveGuessPos ⟵ s =
  record s { guesspos = Fin.pred (State.guesspos s) }

-- Szín változtatása
modifyColor : Color → State → State
modifyColor c s = incStateSeed (moveGuessPos ⟶ res) where
  open State s
  res : State
  res = record s { guess = replacev (Fin.toℕ guesspos) guess c }

-- Tipp törlése
clearGuess : State → State
clearGuess s =
  incStateSeed record s
  { guess = defGuess
  ; guesspos = Fin.zero }

-- Új játék kezdése
newGame : State → State
newGame s =
  init (Random.inc (State.rand s))

_≟m_ : Match → Match → Bool
black ≟m black = true
white ≟m white = true
_     ≟m _     = false

isSolved : Matches → Bool
isSolved g
   = all (_≟m_ black) g ∧ (length g ≟ codeLength)

{-
    Beírt tipp ellenőrzése
-}

check : Colors → Colors → Matches
check guess solution =
  blacks ++ whites
    where
      zipped = toList (zipv guess solution)

      diffs  = unzip (filter (not ∘ uncurry _≟_) zipped)
      rg     = proj₁ diffs
      rs     = proj₂ diffs
      whitec = length (rg \\ (rg \\ rs by _≟_) by _≟_)
      whites = replicate whitec white

      same   = filter (uncurry _≟_) zipped
      blacks = map (const black) same

checkGuess : State → State
checkGuess s =
  incStateSeed record s
  { history   = newhist
  ; gamestate = newstate
  ; guesspos  = Fin.zero
  } where
    open State s
    matched  = check guess solution
    newhist  = history ++ (guess , matched) ∷ []
    newstate =
      if isSolved matched then
        ended won
      else (
        if length newhist < maxGuesses then
          active
        else
          ended lost
      )
