{-# OPTIONS --erased-cubical #-}

module SMain where

open import Data.List using (map)
open import Data.Unit using (⊤)

open import Midi      using (IO; exportTracks; track→htrack)

open import Soundness using (soundTracks)

main : IO ⊤
main =
  let ticksPerBeat = 4 -- (1 = quarter notes; 4 = 16th notes)
      file         = "/Users/leo/Music/MusicTools/test.mid"
      song         = soundTracks
  in exportTracks file ticksPerBeat (map track→htrack song)
