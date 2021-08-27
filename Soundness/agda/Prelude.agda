{-# OPTIONS --without-K --safe --erased-cubical --no-import-sorts #-}

module Prelude where

open import Agda.Primitive renaming (Set to Type) public
open import Agda.Builtin.Reflection hiding (Type) renaming (primQNameEquality to _==_) public
open import Reflection using (_>>=_) public

open import Agda.Builtin.String public
open import Agda.Builtin.Sigma public

open import Data.Bool using (Bool; not; true; false; if_then_else_) public
open import Data.List using (List; []; _∷_; map; concat; concatMap; _++_; foldr; zip; length; take) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fz) public
open import Data.Integer.Base using (ℤ; +_; -[1+_]) public
open import Data.Nat.Base using (ℕ; zero; suc; _^_) public
open import Data.Nat.DivMod using (_%_; _mod_) public
open import Data.Product using (_×_; _,_) public
open import Data.Unit using (⊤) public
open import Data.Vec using (Vec; []; _∷_; updateAt) public

open import Function using (id; _∘_; flip) public

open import Definition.Conversion.Soundness public

open import Interval public
open import Note public
open import Pitch using (Pitch; a; b; b♭; c; c♯; d; d♯; e; f; f♯; g; g♯) public
open import Transformation public

open import MidiEvent using (InstrumentNumber-1; maxChannels; MidiTrack) public

open import FarmCanon using () renaming (subject to canonsubject) public
open import FarmFugue using (b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; subject; countersubject; extra) public
