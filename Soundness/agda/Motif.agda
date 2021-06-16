{-# OPTIONS --without-K --safe --erased-cubical --no-import-sorts #-}

module Motif where

open import Prelude

open import SUtil using (lookup)

import Definition.Conversion
import Definition.Conversion.Whnf
import Definition.Typed
import Definition.Untyped
import Definition.Typed.Consequences.InverseUniv
import Definition.Typed.Consequences.NeTypeEq
import Definition.Typed.Consequences.Syntactic
import Definition.Typed.Properties
import Relation.Binary.PropositionalEquality.Core

-- Number of levels of recursion
levels : ℕ
levels = 2

-- Factor to slow down base melody
multiplier : ℕ
multiplier = 2 ^ levels

-- slowed down prime, etc forms
p i r ri : List Note → List Note
p = map (slowDown multiplier)
i = inversion ∘ p
r = retrograde ∘ p
ri = retrograde ∘ i

w : Pitch → List Note
w n = slowDown multiplier (tone half n) ∷ []

-------------

soundness : List (Name × List Note)
soundness = 
  (quote soundness~↑ , p subject) ∷
  (quote soundness~↓ , i subject) ∷
  (quote soundnessConv↑ , p countersubject) ∷
  (quote soundnessConv↓ , i countersubject) ∷
  (quote soundnessConv↑Term , p extra) ∷
  (quote soundnessConv↓Term , i extra) ∷
  []

conversion : List (Name × List Note)
conversion =
  (quote Definition.Conversion.Whnf.ne~↓ , ri canonsubject) ∷
  (quote Definition.Conversion.[~] , r canonsubject) ∷
  (quote Definition.Conversion.[↑] , p canonsubject) ∷
  (quote Definition.Conversion.[↑] , i canonsubject) ∷

  (quote Definition.Conversion._⊢_[conv↓]_.Empty-refl , p b4) ∷
  (quote Definition.Conversion._⊢_[conv↓]_.U-refl , i b4) ∷
  (quote Definition.Conversion._⊢_[conv↓]_.Unit-refl , r b4) ∷
  (quote Definition.Conversion._⊢_[conv↓]_.ne , ri b4) ∷
  (quote Definition.Conversion._⊢_[conv↓]_.Π-cong , p b5) ∷
  (quote Definition.Conversion._⊢_[conv↓]_.Σ-cong , i b5) ∷
  (quote Definition.Conversion._⊢_[conv↓]_.ℕ-refl , r b5) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.Empty-ins , ri b5) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.Unit-ins , p b6) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.ne-ins , i b6) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.suc-cong , r b6) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.univ , ri b6) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.zero-refl , p b7) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.Σ-η , i b7) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.η-eq , r b7) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.η-unit , ri b7) ∷
  (quote Definition.Conversion._⊢_[conv↓]_∷_.ℕ-ins , p b8) ∷

  (quote Definition.Conversion._⊢_~_↑_.Emptyrec-cong , i b8) ∷
  (quote Definition.Conversion._⊢_~_↑_.app-cong , r b8) ∷
  (quote Definition.Conversion._⊢_~_↑_.fst-cong , ri b8) ∷
  (quote Definition.Conversion._⊢_~_↑_.natrec-cong , p b9) ∷
  (quote Definition.Conversion._⊢_~_↑_.snd-cong , i b9) ∷
  (quote Definition.Conversion._⊢_~_↑_.var-refl , r b9) ∷
  []

typed : List (Name × List Note)
typed = 
  (quote Definition.Typed.Consequences.InverseUniv.inverseUnivEq , ri b9) ∷
  (quote Definition.Typed.Consequences.NeTypeEq.neTypeEq , p b10) ∷
  (quote Definition.Typed.Consequences.Syntactic.syntacticEqTerm , i b10) ∷
  (quote Definition.Typed.Consequences.Syntactic.syntacticTerm , r b10) ∷
  (quote Definition.Typed.Consequences.Syntactic.syntacticΠ , ri b10) ∷
  (quote Definition.Typed.Consequences.Syntactic.syntacticΣ , p b11) ∷
  (quote Definition.Typed.Properties.subset* , i b11) ∷
  (quote Definition.Typed.Properties.subset*Term , r b11) ∷
  (quote Definition.Typed._⊢_.Emptyⱼ , ri b11) ∷
  (quote Definition.Typed._⊢_.Unitⱼ , p b12) ∷
  (quote Definition.Typed._⊢_.Uⱼ , i b12) ∷
  (quote Definition.Typed._⊢_.ℕⱼ , r b12) ∷
  (quote Definition.Typed._⊢_∷_.zeroⱼ , ri b12) ∷
  (quote Definition.Typed._⊢_≡_.refl , p b13) ∷
  (quote Definition.Typed._⊢_≡_.sym , i b13) ∷
  (quote Definition.Typed._⊢_≡_.trans , r b13) ∷
  (quote Definition.Typed._⊢_≡_.univ , ri b13) ∷
  (quote Definition.Typed._⊢_≡_.Π-cong , w (c 6)) ∷
  (quote Definition.Typed._⊢_≡_.Σ-cong , w (d 6)) ∷
  (quote Definition.Typed._⊢_≡_∷_.Emptyrec-cong , w (e 6)) ∷
  (quote Definition.Typed._⊢_≡_∷_.app-cong , w (f 6)) ∷
  (quote Definition.Typed._⊢_≡_∷_.conv , w (g 6)) ∷
  (quote Definition.Typed._⊢_≡_∷_.fst-cong , w (a 6)) ∷
  (quote Definition.Typed._⊢_≡_∷_.natrec-cong , w (b 6)) ∷
  (quote Definition.Typed._⊢_≡_∷_.refl , w (c 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.snd-cong , w (d 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.suc-cong , w (e 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.sym , w (f 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.trans , w (g 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.Σ-η , w (a 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.η-eq , w (b 7)) ∷
  (quote Definition.Typed._⊢_≡_∷_.η-unit , w (c 8)) ∷
  []

untyped : List (Name × List Note)
untyped = 
  (quote Definition.Untyped.Con._∙_ , w (d 8)) ∷
  (quote Definition.Untyped.Empty , w (e 8)) ∷
  (quote Definition.Untyped.Term.var , w (f 8)) ∷
  (quote Definition.Untyped.U , w (g 8)) ∷
  (quote Definition.Untyped.Unit , w (a 8)) ∷
  (quote Definition.Untyped._[_] , w (b 8)) ∷
  (quote Definition.Untyped._[_]↑ , w (c 3)) ∷
  (quote Definition.Untyped._∘_ , w (d 3)) ∷
  (quote Definition.Untyped._▹▹_ , w (e 3)) ∷
  (quote Definition.Untyped.fst , w (f 3)) ∷
  (quote Definition.Untyped.snd , w (g 3)) ∷
  (quote Definition.Untyped.suc , w (a 3)) ∷
  (quote Definition.Untyped.wk1 , w (b 3)) ∷
  (quote Definition.Untyped.zero , w (c 4)) ∷
  (quote Definition.Untyped.Π_▹_ , w (d 4)) ∷
  (quote Definition.Untyped.Σ_▹_ , w (e 4)) ∷
  (quote Definition.Untyped.ℕ , w (f 4)) ∷
  []

misc : List (Name × List Note)
misc = 
  (quote Fin , w (c 2)) ∷
  (quote Fin.zero , w (d 2)) ∷
  (quote Relation.Binary.PropositionalEquality.Core.subst , w (e 2)) ∷
  (quote fst , w (f 2)) ∷
  (quote lzero , w (g 2)) ∷
  (quote snd , w (a 2)) ∷
  (quote ℕ.suc , w (b 2)) ∷
  []

motives : List (Name × List Note)
motives = soundness ++ conversion ++ typed ++ untyped ++ misc

motif : Name → List Note
motif = lookup motives
