{-# OPTIONS --erased-cubical #-}

module SMain where

open import Data.List using (map)
open import Data.Nat  using (_*_)
open import Data.Unit using (⊤)

open import Midi      using (IO; exportTracks; track→htrack)

open import Soundness using (soundTracks)
open import Motif     using (multiplier)

main : IO ⊤
main =
  let ticksPerBeat = 4 * multiplier -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = soundTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
