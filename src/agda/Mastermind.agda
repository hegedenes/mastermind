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

module Mastermind where

open import FRP.JS.Behaviour using ( Beh )
open import FRP.JS.DOM using ( DOM )
open import FRP.JS.RSet using ( ⟦_⟧ )

open import Mastermind.View using ( view )
open import Mastermind.Properties using ()

main : ∀ {w} → ⟦ Beh (DOM w) ⟧
main = view
