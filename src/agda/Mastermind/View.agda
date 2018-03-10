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
    Mastermind.View modul
    A játék nézete és az interakció megvalósítása
-}

module Mastermind.View where

{-
    Importok
-}

open import FRP.JS.Behaviour using ( [_] ; accumHoldBy ; map ; join )
open import FRP.JS.Product   using ( _,_ )
open import FRP.JS.Event     using ( tag )
open import FRP.JS.DOM       using ( element  ; attr    ; attr+ ; text
                                   ; text+    ; listen+ ; click ; _++_
                                   ; element+ ; _+++_   ) renaming ([] to []D)

open import FRP.JS.Delay  using ( _ms )
open import FRP.JS.Time   using ( Time ; epoch )

open import FRP.JS.String using ( String ) renaming (_++_ to _++s_)
open import FRP.JS.Maybe  using ( Maybe ; just ; nothing )
open import FRP.JS.Nat    using ( ℕ ; zero ; suc )

open import Mastermind.View.Base

open import Mastermind.Model
open import Mastermind.Auxiliary

{-
    Interakció
-}

-- Lépés a játékban
step : State → Button → State
step state restart = newGame state
step state button with State.gamestate state
... | ended _ = state
... | active with button
...    |    color c     = modifyColor c state
...    |       ok       = checkGuess state
...    |     clear      = clearGuess state
...    | move direction = moveGuessPos direction state
...    |       _        = state

-- A Modell definíciója
model : Model
model {epoch (time ms)} =
  accumHoldBy step (init time)


{-
    Gombok leírása
-}

-- Gomb hozzáadása
button : ButtonHandler
button button =
  listen+ click (λ _ → button) (              -- esemény
    element+ "button" (                       -- HTML gomb
      text+ [ button$ button ] +++            -- felirat
      attr+ "class" [ buttonClass button ]))  -- HTML osztály

-- Beviteli mezők leírása
keypad : InteractiveButtons
keypad =
  element+ "div" (
    button (color 1)  +++
    button (color 2)  +++
    button (color 3)  +++
    button (color 4)  +++
    button (color 5)  +++
    button (color 6)) +++
  element+ "div" (
    button (move ⟵)  +++
    button (move ⟶)) +++
  element+ "div" (
    button ok    +++
    button clear +++
    button restart)



addID : (State → String) → UIElement
addID fun σ = attr "id" (map fun σ)

displayColors : (ℕ → UIElement) → UIElement
displayColors display-fun σ =
  element "table" (
    attr "id" [ "guesstable" ] ++
    element "tr" (
      element "td" []D ++
      display-fun 0 σ ++
      display-fun 1 σ ++
      display-fun 2 σ ++
      display-fun 3 σ ++
      element "td" []D))

colorClass-i : Colors → ℕ → String
colorClass-i colors i with lookupv colors i
... | nothing = "color_none"
... | just c  = colorClass c

displayGuessPart : ℕ → UIElement
displayGuessPart i σ =
  element "td" (
    text (map (guessElemText i) σ) ++
    attr "class" (map (λ state → "color " ++s class state) σ) ++
    attr "id" (map (guessElemID i) σ))
  where
    class : State → String
    class state =
      colorClass-i (State.guess state) i

displayGuess : UIElement
displayGuess σ =
  displayColors displayGuessPart σ


displayHistoryGuessElem : ℕ → ℕ → UIElement
displayHistoryGuessElem line i σ =
  element "td" (
    attr "class" (map (λ state → "color " ++s class state) σ)) 
  where
    class : State → String
    class state with getHistoryGuess-i line state
    ... | nothing = "color_none"
    ... | just colors = colorClass-i colors i

-- A történet n-edik sorában lévő tipp megjelenítése
displayHistoryGuess : (n : ℕ) → UIElement
displayHistoryGuess n σ =
  displayColors (displayHistoryGuessElem n) σ

matchField : ℕ → ℕ → UIElement
matchField line i σ = 
  element "td" (
    addID (histelemToStr line (histmatchtoStr i)) σ ++
    text [ " " ])

-- A történet n-edik sorában lévő találatok megjelenítése
displayHistoryMatches : (n : ℕ) → UIElement
displayHistoryMatches n σ =
  element "table" (
    element "tr" (
      matchField n 0 σ  ++
      matchField n 1 σ) ++
    element "tr" (
      matchField n 2 σ  ++
      matchField n 3 σ) ++
    attr "id" [ "matchtable" ])

-- A történet n-edik sorának megjelenítése
displayHistoryLine : (n : ℕ) → UIElement
displayHistoryLine n σ =
  element "tr" (
    element "td" []D ++
    element "td" (
      displayHistoryGuess n σ ++
      attr "id" [ "histval" ] ) ++
    element "td" (
      displayHistoryMatches n σ ++
      attr "id" [ "hist_matches" ] ) ++
    element "td" []D)

-- Történet megjelenítése
displayHistory : ℕ → UIElement
displayHistory    0    σ = []D
displayHistory (suc n) σ =
  displayHistory n σ ++ displayHistoryLine n σ

-- A teljes GUI megjelenítése
display : UIElement
display σ =
  element "table" (
    displayHistory maxGuesses σ ++
    attr "id" [ "historytable" ] ) ++
  element "div" (
    displayGuess σ) ++
  element "div" (
    text (map state$ σ))

-- Nézet megadása
view : View
view with keypad
... | (dom , evt) = display (model evt) ++ dom