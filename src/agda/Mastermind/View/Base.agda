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
    Mastermind.View.Base modul
    Nézet által használt függvények definíciói
-}

module Mastermind.View.Base where

{-
    Importok
-}

open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.Product   using ( _∧_ )
open import FRP.JS.Event     using ( Evt )
open import FRP.JS.RSet      using ( ⟦_⟧ ; ⟨_⟩ ; _⇒_ )
open import FRP.JS.DOM       using ( DOM )

open import FRP.JS.String using ( String ) renaming ( _++_ to _++s_ )
open import FRP.JS.Maybe  using ( Maybe ; just ; nothing )
open import FRP.JS.Bool   using ( if_then_else_ )
open import FRP.JS.List   using ( lookup )
open import FRP.JS.Nat    using ( ℕ ; show )

open import Mastermind.Auxiliary
open import Mastermind.Model

{-
    Típusok
-}

data Button : Set where
  color : Color → Button
  move  : Direction → Button
  ok clear restart : Button

UIElement : Set
UIElement = ∀ {w} → ⟦ Beh ⟨ State ⟩ ⇒ Beh (DOM w) ⟧

Model : Set
Model = ⟦ Evt ⟨ Button ⟩ ⇒ Beh ⟨ State ⟩ ⟧

View : Set
View = ∀ {w} → ⟦ Beh (DOM w) ⟧

InteractiveButtons : Set
InteractiveButtons = ∀ {w} → ⟦ Beh (DOM w) ∧ Evt ⟨ Button ⟩ ⟧

ButtonHandler : Set
ButtonHandler = Button → InteractiveButtons

{-
    Függvények
-}

match→str : Match → String
match→str black = "black_m"
match→str white = "white_m"
match→str none  = ""

vec→str : ∀ {A : Set} {n} → Vec A n → (A → String) → String
vec→str xs f = foldlv (_++s_) "[" (mapv f xs) ++s "]"

Vecℕ→str : ∀ {n} → Vec ℕ n → String
Vecℕ→str ns = vec→str ns show

histelemToStr : ℕ → (HistElem → String) → State → String
histelemToStr line f s with lookup (State.history s) line
... | just a  = f a
... | nothing = " "

histmatchtoStr : ℕ → HistElem → String
histmatchtoStr n (g , bw) with lookup bw n
... | just a  = match→str a
... | nothing = " "

button$ : Button → String
button$ (color c) = "" -- show c
button$ (move ⟵) = "<"
button$ (move ⟶) = ">"
button$ ok        = "Check"
button$ clear     = "Clear"
button$ restart   = "Restart"

state$ : State → String
state$ s with State.gamestate s
... | ended won  = "You won! :)"
... | ended lost = "You lost! :( Solution: " ++s Vecℕ→str (State.solution s)
... | active     = "" -- ++s Vecℕ→str (State.solution s)

colorClass : Color → String
colorClass c = "color" ++s show c

buttonClass : Button → String
buttonClass (color c) = "button_num " ++s colorClass c
buttonClass (move _)  = "button_num"
buttonClass     _     = "button_op"

guessElemID : ℕ → State → String
guessElemID n s =
  if n ≟ Fin.toℕ (State.guesspos s) then "guess_act" else ""

guessElemText : ℕ → State → String
guessElemText n s =
  if n ≟ Fin.toℕ (State.guesspos s) then "∘" else ""

getHistoryGuess-i : ℕ → State → Maybe Colors
getHistoryGuess-i line s with lookup (State.history s) line
... | just (a , bw) = just a
... | nothing = nothing