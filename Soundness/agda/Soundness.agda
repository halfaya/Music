{-# OPTIONS --without-K --erased-cubical --no-import-sorts #-}

module Soundness where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Reflection hiding (Type) renaming (primQNameEquality to _==_)
open import Reflection using (_>>=_)

open import Agda.Builtin.String
open import Agda.Builtin.Sigma

open import Data.Bool using (Bool; not; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; concatMap; _++_; foldr)
open import Data.Fin.Base using (Fin)
open import Data.Unit using (⊤)

open import Function using (id)

open import Definition.Conversion.Soundness

open import Interval

----------------

-- Utilities

_∈_ : Name → List Name → Bool
n ∈ []       = false
n ∈ (x ∷ ns) = if n == x then true else n ∈ ns

-- treat list as set
insert : Name → List Name → List Name
insert n ns = if n ∈ ns then ns else n ∷ ns

nameSet : List Name → List Name
nameSet = foldr insert []

----------------

macro
  getDef : Name → Term → TC ⊤
  getDef n h = do
    d ← getDefinition n
    t ← quoteTC d
    unify h t

record Line : Type where
  constructor line
  field
    lhs : List Name
    rhs : List Name
open Line

-- Get only visible constructor names
getNamesP : List (Arg Pattern) → List Name
getNamesP []       = []
getNamesP (arg (arg-info v m)         (Pattern.dot t) ∷ ps)     = getNamesP ps
getNamesP (arg (arg-info v m)         (Pattern.var x₁) ∷ ps)    = getNamesP ps
getNamesP (arg (arg-info v m)         (Pattern.lit l) ∷ ps)     = getNamesP ps
getNamesP (arg (arg-info v m)         (Pattern.proj f) ∷ ps)    = getNamesP ps
getNamesP (arg (arg-info v m)         (Pattern.absurd x₁) ∷ ps) = getNamesP ps
getNamesP (arg (arg-info hidden m)    (Pattern.con n _) ∷ ps)   = getNamesP ps
getNamesP (arg (arg-info instance′ m) (Pattern.con n _) ∷ ps)   = getNamesP ps
getNamesP (arg (arg-info visible m)   (Pattern.con n _) ∷ ps)   = n ∷ getNamesP ps

{-# TERMINATING #-}
getNamesT  : Term → List Name
getNamesAT : Arg Term → List Name

getNamesT (con n args)      = n ∷ concatMap getNamesAT args
getNamesT (def n args)      = n ∷ concatMap getNamesAT args
getNamesT (var x₁ args)     = concatMap getNamesAT args
getNamesT (pat-lam cs args) = concatMap getNamesAT args
getNamesT (lam v t)         = []
getNamesT (pi a b)          = []
getNamesT (agda-sort s)     = []
getNamesT (lit l)           = []
getNamesT (meta x₁ x₂)      = []
getNamesT unknown           = []

getNamesAT (arg i t) = getNamesT t

getNamesC : Clause → Line
getNamesC (Clause.clause tel ps t)      = line (getNamesP ps) (getNamesT t)
getNamesC (Clause.absurd-clause tel ps) = line (getNamesP ps) []

getNamesD : Definition → List Line
getNamesD (function cs)       = map getNamesC cs
getNamesD (data-type pars cs) = []
getNamesD (record-type c fs)  = []
getNamesD (data-cons d)       = []
getNamesD axiom               = []
getNamesD prim-fun            = []

----------------
x : Definition
x = getDef soundness~↑

y : List Line
y = getNamesD x

z : List Name
z = nameSet (quote soundness~↑ ∷ foldr (λ x xs → lhs x ++ rhs x ++ xs) [] y)

{-
quote soundness~↑ ∷
quote Definition.Conversion._⊢_~_↑_.var-refl ∷
quote Relation.Binary.PropositionalEquality.Core.subst ∷
quote Fin ∷
quote lzero ∷
quote Definition.Typed._⊢_≡_∷_.refl ∷
quote Definition.Conversion._⊢_~_↑_.app-cong ∷
quote Definition.Typed._⊢_≡_∷_.app-cong ∷
quote Definition.Conversion._⊢_~_↑_.fst-cong ∷
quote Definition.Typed._⊢_≡_∷_.fst-cong ∷
quote Definition.Conversion._⊢_~_↑_.snd-cong ∷
quote Definition.Typed._⊢_≡_∷_.snd-cong ∷
quote snd ∷
quote Definition.Typed.Consequences.Syntactic.syntacticΣ ∷
quote fst ∷
quote Definition.Typed.Consequences.Syntactic.syntacticEqTerm ∷
quote Definition.Untyped.Σ_▹_ ∷
quote Definition.Conversion._⊢_~_↑_.natrec-cong ∷
quote Definition.Typed._⊢_≡_∷_.natrec-cong ∷
quote Definition.Untyped.Con._∙_ ∷
quote Definition.Untyped._[_] ∷
quote Definition.Untyped.zero ∷
quote soundnessConv↑Term ∷
quote Definition.Untyped.Π_▹_ ∷
quote Definition.Untyped._▹▹_ ∷
quote Definition.Untyped._[_]↑ ∷
quote Definition.Untyped.suc ∷
quote Agda.Builtin.Nat.Nat.suc ∷
quote Definition.Untyped.Term.var ∷
quote Fin.zero ∷
quote Definition.Untyped.ℕ ∷
quote Definition.Conversion._⊢_~_↑_.Emptyrec-cong ∷
quote Definition.Typed._⊢_≡_∷_.Emptyrec-cong ∷
quote soundnessConv↑ ∷
quote soundness~↓ ∷ quote Definition.Untyped.Empty ∷ []
-}

{-
function
(Clause.clause
 (("Γ.n" , hArg (def (quote Agda.Builtin.Nat.Nat) [])) ∷
  ("Γ" ,
   hArg
   (def (quote Definition.Untyped.Con)
    (vArg (def (quote Definition.Untyped.Term) []) ∷
     vArg (var 0 []) ∷ [])))
  ∷
  ("A" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 1 []) ∷ [])))
  ∷
  ("x" , hArg (def (quote Fin) (vArg (var 2 []) ∷ []))) ∷
  ("y" , hArg (def (quote Fin) (vArg (var 3 []) ∷ []))) ∷
  ("x" ,
   vArg
   (def (quote Definition.Typed._⊢_∷_)
    (hArg (var 4 []) ∷
     vArg (var 3 []) ∷
     vArg
     (con (quote Definition.Untyped.Term.var)
      (hArg unknown ∷ vArg (var 1 []) ∷ []))
     ∷ vArg (var 2 []) ∷ [])))
  ∷
  ("x≡y" ,
   vArg
   (def (quote Agda.Builtin.Equality._≡_)
    (hArg (def (quote lzero) []) ∷
     hArg (def (quote Fin) (vArg (var 5 []) ∷ [])) ∷
     vArg (var 2 []) ∷ vArg (var 1 []) ∷ [])))
  ∷ [])
 (hArg (Pattern.var 6) ∷
  hArg (Pattern.var 5) ∷
  hArg
  (Pattern.con (quote Definition.Untyped.Term.var)
   (vArg (Pattern.var 3) ∷ []))
  ∷
  hArg
  (Pattern.con (quote Definition.Untyped.Term.var)
   (vArg (Pattern.var 2) ∷ []))
  ∷
  hArg (Pattern.var 4) ∷
  vArg
  (Pattern.con (quote Definition.Conversion._⊢_~_↑_.var-refl)
   (hArg (Pattern.dot (var 3 [])) ∷
    hArg (Pattern.dot (var 2 [])) ∷
    hArg (Pattern.dot (var 4 [])) ∷
    vArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []))
  ∷ [])
 (def (quote Relation.Binary.PropositionalEquality.Core.subst)
  (hArg (def (quote lzero) []) ∷
   hArg (def (quote Fin) (vArg (var 6 []) ∷ [])) ∷
   hArg (def (quote lzero) []) ∷
   vArg
   (lam visible
    (abs "y"
     (def (quote Definition.Typed._⊢_≡_∷_)
      (hArg (var 7 []) ∷
       vArg (var 6 []) ∷
       vArg
       (con (quote Definition.Untyped.Term.var)
        (hArg unknown ∷ vArg (var 4 []) ∷ []))
       ∷
       vArg
       (con (quote Definition.Untyped.Term.var)
        (hArg unknown ∷ vArg (var 0 []) ∷ []))
       ∷ vArg (var 5 []) ∷ []))))
   ∷
   hArg (var 3 []) ∷
   hArg (var 2 []) ∷
   vArg (var 0 []) ∷
   vArg
   (con (quote Definition.Typed._⊢_≡_∷_.refl)
    (hArg unknown ∷
     hArg unknown ∷
     hArg
     (con (quote Definition.Untyped.Term.var)
      (hArg unknown ∷ vArg (var 3 []) ∷ []))
     ∷ hArg (var 4 []) ∷ vArg (var 1 []) ∷ []))
   ∷ []))
 ∷
 Clause.clause
 (("Γ.n" , hArg (def (quote Agda.Builtin.Nat.Nat) [])) ∷
  ("Γ" ,
   hArg
   (def (quote Definition.Untyped.Con)
    (vArg (def (quote Definition.Untyped.Term) []) ∷
     vArg (var 0 []) ∷ [])))
  ∷
  ("k" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 1 []) ∷ [])))
  ∷
  ("l" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 2 []) ∷ [])))
  ∷
  ("t" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 3 []) ∷ [])))
  ∷
  ("v" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 4 []) ∷ [])))
  ∷
  ("F" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 5 []) ∷ [])))
  ∷
  ("G" ,
   hArg
   (def (quote Definition.Untyped.Term)
    (vArg (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 6 []) ∷ []))
     ∷ [])))
  ∷
  ("k~l" ,
   vArg
   (def (quote Definition.Conversion._⊢_~_↓_)
    (hArg (var 7 []) ∷
     vArg (var 6 []) ∷
     vArg (var 5 []) ∷
     vArg (var 4 []) ∷
     vArg
     (def (quote Definition.Untyped.Π_▹_)
      (hArg (var 7 []) ∷ vArg (var 1 []) ∷ vArg (var 0 []) ∷ []))
     ∷ [])))
  ∷
  ("x₁" ,
   vArg
   (def (quote Definition.Conversion._⊢_[conv↑]_∷_)
    (hArg (var 8 []) ∷
     vArg (var 7 []) ∷
     vArg (var 4 []) ∷ vArg (var 3 []) ∷ vArg (var 2 []) ∷ [])))
  ∷ [])
 (hArg (Pattern.var 9) ∷
  hArg (Pattern.var 8) ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped._∘_)
    (hArg (var 9 []) ∷ vArg (var 7 []) ∷ vArg (var 5 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped._∘_)
    (hArg (var 9 []) ∷ vArg (var 6 []) ∷ vArg (var 4 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped._[_])
    (hArg (var 9 []) ∷ vArg (var 2 []) ∷ vArg (var 5 []) ∷ [])))
  ∷
  vArg
  (Pattern.con (quote Definition.Conversion._⊢_~_↑_.app-cong)
   (hArg (Pattern.var 7) ∷
    hArg (Pattern.var 6) ∷
    hArg (Pattern.var 5) ∷
    hArg (Pattern.var 4) ∷
    hArg (Pattern.var 3) ∷
    hArg (Pattern.var 2) ∷
    vArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []))
  ∷ [])
 (con (quote Definition.Typed._⊢_≡_∷_.app-cong)
  (hArg unknown ∷
   hArg unknown ∷
   hArg (var 5 []) ∷
   hArg (var 4 []) ∷
   hArg (var 7 []) ∷
   hArg (var 6 []) ∷
   hArg (var 3 []) ∷
   hArg (var 2 []) ∷
   vArg
   (def (quote soundness~↓)
    (hArg (var 9 []) ∷
     hArg (var 8 []) ∷
     hArg (var 7 []) ∷
     hArg (var 6 []) ∷
     hArg
     (def (quote Definition.Untyped.Π_▹_)
      (hArg (var 9 []) ∷ vArg (var 3 []) ∷ vArg (var 2 []) ∷ []))
     ∷ vArg (var 1 []) ∷ []))
   ∷
   vArg
   (def (quote soundnessConv↑Term)
    (hArg (var 9 []) ∷
     hArg (var 8 []) ∷
     hArg (var 5 []) ∷
     hArg (var 4 []) ∷ hArg (var 3 []) ∷ vArg (var 0 []) ∷ []))
   ∷ []))
 ∷
 Clause.clause
 (("Γ.n" , hArg (def (quote Agda.Builtin.Nat.Nat) [])) ∷
  ("Γ" ,
   hArg
   (def (quote Definition.Untyped.Con)
    (vArg (def (quote Definition.Untyped.Term) []) ∷
     vArg (var 0 []) ∷ [])))
  ∷
  ("A" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 1 []) ∷ [])))
  ∷
  ("p" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 2 []) ∷ [])))
  ∷
  ("r" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 3 []) ∷ [])))
  ∷
  ("G" ,
   hArg
   (def (quote Definition.Untyped.Term)
    (vArg (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 4 []) ∷ []))
     ∷ [])))
  ∷
  ("x" ,
   vArg
   (def (quote Definition.Conversion._⊢_~_↓_)
    (hArg (var 5 []) ∷
     vArg (var 4 []) ∷
     vArg (var 2 []) ∷
     vArg (var 1 []) ∷
     vArg
     (def (quote Definition.Untyped.Σ_▹_)
      (hArg (var 5 []) ∷ vArg (var 3 []) ∷ vArg (var 0 []) ∷ []))
     ∷ [])))
  ∷ [])
 (hArg (Pattern.var 6) ∷
  hArg (Pattern.var 5) ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.fst)
    (hArg (var 6 []) ∷ vArg (var 3 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.fst)
    (hArg (var 6 []) ∷ vArg (var 2 []) ∷ [])))
  ∷
  hArg (Pattern.var 4) ∷
  vArg
  (Pattern.con (quote Definition.Conversion._⊢_~_↑_.fst-cong)
   (hArg (Pattern.var 3) ∷
    hArg (Pattern.var 2) ∷
    hArg (Pattern.dot (var 4 [])) ∷
    hArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []))
  ∷ [])
 (con (quote Definition.Typed._⊢_≡_∷_.fst-cong)
  (hArg unknown ∷
   hArg unknown ∷
   hArg (var 3 []) ∷
   hArg (var 2 []) ∷
   hArg (var 4 []) ∷
   hArg (var 1 []) ∷
   vArg
   (def (quote fst)
    (hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     vArg
     (def (quote Definition.Typed.Consequences.Syntactic.syntacticΣ)
      (hArg (var 6 []) ∷
       hArg (var 5 []) ∷
       hArg (var 4 []) ∷
       hArg (var 1 []) ∷
       vArg
       (def (quote fst)
        (hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         vArg
         (def
          (quote Definition.Typed.Consequences.Syntactic.syntacticEqTerm)
          (hArg (var 6 []) ∷
           hArg (var 5 []) ∷
           hArg (var 3 []) ∷
           hArg (var 2 []) ∷
           hArg
           (def (quote Definition.Untyped.Σ_▹_)
            (hArg (var 6 []) ∷ vArg (var 4 []) ∷ vArg (var 1 []) ∷ []))
           ∷
           vArg
           (def (quote soundness~↓)
            (hArg (var 6 []) ∷
             hArg (var 5 []) ∷
             hArg (var 3 []) ∷
             hArg (var 2 []) ∷
             hArg
             (def (quote Definition.Untyped.Σ_▹_)
              (hArg (var 6 []) ∷ vArg (var 4 []) ∷ vArg (var 1 []) ∷ []))
             ∷ vArg (var 0 []) ∷ []))
           ∷ []))
         ∷ []))
       ∷ []))
     ∷ []))
   ∷
   vArg
   (def (quote snd)
    (hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     vArg
     (def (quote Definition.Typed.Consequences.Syntactic.syntacticΣ)
      (hArg (var 6 []) ∷
       hArg (var 5 []) ∷
       hArg (var 4 []) ∷
       hArg (var 1 []) ∷
       vArg
       (def (quote fst)
        (hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         vArg
         (def
          (quote Definition.Typed.Consequences.Syntactic.syntacticEqTerm)
          (hArg (var 6 []) ∷
           hArg (var 5 []) ∷
           hArg (var 3 []) ∷
           hArg (var 2 []) ∷
           hArg
           (def (quote Definition.Untyped.Σ_▹_)
            (hArg (var 6 []) ∷ vArg (var 4 []) ∷ vArg (var 1 []) ∷ []))
           ∷
           vArg
           (def (quote soundness~↓)
            (hArg (var 6 []) ∷
             hArg (var 5 []) ∷
             hArg (var 3 []) ∷
             hArg (var 2 []) ∷
             hArg
             (def (quote Definition.Untyped.Σ_▹_)
              (hArg (var 6 []) ∷ vArg (var 4 []) ∷ vArg (var 1 []) ∷ []))
             ∷ vArg (var 0 []) ∷ []))
           ∷ []))
         ∷ []))
       ∷ []))
     ∷ []))
   ∷
   vArg
   (def (quote soundness~↓)
    (hArg (var 6 []) ∷
     hArg (var 5 []) ∷
     hArg (var 3 []) ∷
     hArg (var 2 []) ∷
     hArg
     (def (quote Definition.Untyped.Σ_▹_)
      (hArg (var 6 []) ∷ vArg (var 4 []) ∷ vArg (var 1 []) ∷ []))
     ∷ vArg (var 0 []) ∷ []))
   ∷ []))
 ∷
 Clause.clause
 (("Γ.n" , hArg (def (quote Agda.Builtin.Nat.Nat) [])) ∷
  ("Γ" ,
   hArg
   (def (quote Definition.Untyped.Con)
    (vArg (def (quote Definition.Untyped.Term) []) ∷
     vArg (var 0 []) ∷ [])))
  ∷
  ("p" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 1 []) ∷ [])))
  ∷
  ("r" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 2 []) ∷ [])))
  ∷
  ("F" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 3 []) ∷ [])))
  ∷
  ("G" ,
   hArg
   (def (quote Definition.Untyped.Term)
    (vArg (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 4 []) ∷ []))
     ∷ [])))
  ∷
  ("x" ,
   vArg
   (def (quote Definition.Conversion._⊢_~_↓_)
    (hArg (var 5 []) ∷
     vArg (var 4 []) ∷
     vArg (var 3 []) ∷
     vArg (var 2 []) ∷
     vArg
     (def (quote Definition.Untyped.Σ_▹_)
      (hArg (var 5 []) ∷ vArg (var 1 []) ∷ vArg (var 0 []) ∷ []))
     ∷ [])))
  ∷ [])
 (hArg (Pattern.var 6) ∷
  hArg (Pattern.var 5) ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.snd)
    (hArg (var 6 []) ∷ vArg (var 4 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.snd)
    (hArg (var 6 []) ∷ vArg (var 3 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped._[_])
    (hArg (var 6 []) ∷
     vArg (var 1 []) ∷
     vArg
     (def (quote Definition.Untyped.fst)
      (hArg (var 6 []) ∷ vArg (var 4 []) ∷ []))
     ∷ [])))
  ∷
  vArg
  (Pattern.con (quote Definition.Conversion._⊢_~_↑_.snd-cong)
   (hArg (Pattern.var 4) ∷
    hArg (Pattern.var 3) ∷
    hArg (Pattern.var 2) ∷
    hArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []))
  ∷ [])
 (con (quote Definition.Typed._⊢_≡_∷_.snd-cong)
  (hArg unknown ∷
   hArg unknown ∷
   hArg (var 4 []) ∷
   hArg (var 3 []) ∷
   hArg (var 2 []) ∷
   hArg (var 1 []) ∷
   vArg
   (def (quote fst)
    (hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     vArg
     (def (quote Definition.Typed.Consequences.Syntactic.syntacticΣ)
      (hArg (var 6 []) ∷
       hArg (var 5 []) ∷
       hArg (var 2 []) ∷
       hArg (var 1 []) ∷
       vArg
       (def (quote fst)
        (hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         vArg
         (def
          (quote Definition.Typed.Consequences.Syntactic.syntacticEqTerm)
          (hArg (var 6 []) ∷
           hArg (var 5 []) ∷
           hArg (var 4 []) ∷
           hArg (var 3 []) ∷
           hArg
           (def (quote Definition.Untyped.Σ_▹_)
            (hArg (var 6 []) ∷ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
           ∷
           vArg
           (def (quote soundness~↓)
            (hArg (var 6 []) ∷
             hArg (var 5 []) ∷
             hArg (var 4 []) ∷
             hArg (var 3 []) ∷
             hArg
             (def (quote Definition.Untyped.Σ_▹_)
              (hArg (var 6 []) ∷ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
             ∷ vArg (var 0 []) ∷ []))
           ∷ []))
         ∷ []))
       ∷ []))
     ∷ []))
   ∷
   vArg
   (def (quote snd)
    (hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     hArg unknown ∷
     vArg
     (def (quote Definition.Typed.Consequences.Syntactic.syntacticΣ)
      (hArg (var 6 []) ∷
       hArg (var 5 []) ∷
       hArg (var 2 []) ∷
       hArg (var 1 []) ∷
       vArg
       (def (quote fst)
        (hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         hArg unknown ∷
         vArg
         (def
          (quote Definition.Typed.Consequences.Syntactic.syntacticEqTerm)
          (hArg (var 6 []) ∷
           hArg (var 5 []) ∷
           hArg (var 4 []) ∷
           hArg (var 3 []) ∷
           hArg
           (def (quote Definition.Untyped.Σ_▹_)
            (hArg (var 6 []) ∷ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
           ∷
           vArg
           (def (quote soundness~↓)
            (hArg (var 6 []) ∷
             hArg (var 5 []) ∷
             hArg (var 4 []) ∷
             hArg (var 3 []) ∷
             hArg
             (def (quote Definition.Untyped.Σ_▹_)
              (hArg (var 6 []) ∷ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
             ∷ vArg (var 0 []) ∷ []))
           ∷ []))
         ∷ []))
       ∷ []))
     ∷ []))
   ∷
   vArg
   (def (quote soundness~↓)
    (hArg (var 6 []) ∷
     hArg (var 5 []) ∷
     hArg (var 4 []) ∷
     hArg (var 3 []) ∷
     hArg
     (def (quote Definition.Untyped.Σ_▹_)
      (hArg (var 6 []) ∷ vArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
     ∷ vArg (var 0 []) ∷ []))
   ∷ []))
 ∷
 Clause.clause
 (("Γ.n" , hArg (def (quote Agda.Builtin.Nat.Nat) [])) ∷
  ("Γ" ,
   hArg
   (def (quote Definition.Untyped.Con)
    (vArg (def (quote Definition.Untyped.Term) []) ∷
     vArg (var 0 []) ∷ [])))
  ∷
  ("k" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 1 []) ∷ [])))
  ∷
  ("l" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 2 []) ∷ [])))
  ∷
  ("h" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 3 []) ∷ [])))
  ∷
  ("g" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 4 []) ∷ [])))
  ∷
  ("a₀" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 5 []) ∷ [])))
  ∷
  ("b₀" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 6 []) ∷ [])))
  ∷
  ("F" ,
   hArg
   (def (quote Definition.Untyped.Term)
    (vArg (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 7 []) ∷ []))
     ∷ [])))
  ∷
  ("G" ,
   hArg
   (def (quote Definition.Untyped.Term)
    (vArg (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 8 []) ∷ []))
     ∷ [])))
  ∷
  ("x₁" ,
   vArg
   (def (quote Definition.Conversion._⊢_[conv↑]_)
    (hArg (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 9 []) ∷ []))
     ∷
     vArg
     (con (quote Definition.Untyped.Con._∙_)
      (hArg unknown ∷
       hArg (var 9 []) ∷
       vArg (var 8 []) ∷
       vArg (def (quote Definition.Untyped.ℕ) (hArg (var 9 []) ∷ [])) ∷
       []))
     ∷ vArg (var 1 []) ∷ vArg (var 0 []) ∷ [])))
  ∷
  ("x₂" ,
   vArg
   (def (quote Definition.Conversion._⊢_[conv↑]_∷_)
    (hArg (var 10 []) ∷
     vArg (var 9 []) ∷
     vArg (var 4 []) ∷
     vArg (var 3 []) ∷
     vArg
     (def (quote Definition.Untyped._[_])
      (hArg (var 10 []) ∷
       vArg (var 2 []) ∷
       vArg (def (quote Definition.Untyped.zero) (hArg (var 10 []) ∷ []))
       ∷ []))
     ∷ [])))
  ∷
  ("x₃" ,
   vArg
   (def (quote Definition.Conversion._⊢_[conv↑]_∷_)
    (hArg (var 11 []) ∷
     vArg (var 10 []) ∷
     vArg (var 7 []) ∷
     vArg (var 6 []) ∷
     vArg
     (def (quote Definition.Untyped.Π_▹_)
      (hArg (var 11 []) ∷
       vArg (def (quote Definition.Untyped.ℕ) (hArg (var 11 []) ∷ [])) ∷
       vArg
       (def (quote Definition.Untyped._▹▹_)
        (hArg
         (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 11 []) ∷ []))
         ∷
         vArg (var 3 []) ∷
         vArg
         (def (quote Definition.Untyped._[_]↑)
          (hArg (var 11 []) ∷
           vArg (var 3 []) ∷
           vArg
           (def (quote Definition.Untyped.suc)
            (hArg
             (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 11 []) ∷ []))
             ∷
             vArg
             (con (quote Definition.Untyped.Term.var)
              (hArg unknown ∷
               vArg (con (quote Fin.zero) (hArg (var 11 []) ∷ [])) ∷ []))
             ∷ []))
           ∷ []))
         ∷ []))
       ∷ []))
     ∷ [])))
  ∷
  ("k~l" ,
   vArg
   (def (quote Definition.Conversion._⊢_~_↓_)
    (hArg (var 12 []) ∷
     vArg (var 11 []) ∷
     vArg (var 10 []) ∷
     vArg (var 9 []) ∷
     vArg (def (quote Definition.Untyped.ℕ) (hArg (var 12 []) ∷ [])) ∷
     [])))
  ∷ [])
 (hArg (Pattern.var 13) ∷
  hArg (Pattern.var 12) ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.natrec)
    (hArg (var 13 []) ∷
     vArg (var 5 []) ∷
     vArg (var 7 []) ∷ vArg (var 9 []) ∷ vArg (var 11 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.natrec)
    (hArg (var 13 []) ∷
     vArg (var 4 []) ∷
     vArg (var 6 []) ∷ vArg (var 8 []) ∷ vArg (var 10 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped._[_])
    (hArg (var 13 []) ∷ vArg (var 5 []) ∷ vArg (var 11 []) ∷ [])))
  ∷
  vArg
  (Pattern.con (quote Definition.Conversion._⊢_~_↑_.natrec-cong)
   (hArg (Pattern.var 11) ∷
    hArg (Pattern.var 10) ∷
    hArg (Pattern.var 9) ∷
    hArg (Pattern.var 8) ∷
    hArg (Pattern.var 7) ∷
    hArg (Pattern.var 6) ∷
    hArg (Pattern.var 5) ∷
    hArg (Pattern.var 4) ∷
    vArg (Pattern.var 3) ∷
    vArg (Pattern.var 2) ∷
    vArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []))
  ∷ [])
 (con (quote Definition.Typed._⊢_≡_∷_.natrec-cong)
  (hArg unknown ∷
   hArg unknown ∷
   hArg (var 7 []) ∷
   hArg (var 6 []) ∷
   hArg (var 9 []) ∷
   hArg (var 8 []) ∷
   hArg (var 11 []) ∷
   hArg (var 10 []) ∷
   hArg (var 5 []) ∷
   hArg (var 4 []) ∷
   vArg
   (def (quote soundnessConv↑)
    (hArg
     (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 13 []) ∷ []))
     ∷
     hArg
     (con (quote Definition.Untyped.Con._∙_)
      (hArg unknown ∷
       hArg (var 13 []) ∷
       vArg (var 12 []) ∷
       vArg (def (quote Definition.Untyped.ℕ) (hArg (var 13 []) ∷ [])) ∷
       []))
     ∷ hArg (var 5 []) ∷ hArg (var 4 []) ∷ vArg (var 3 []) ∷ []))
   ∷
   vArg
   (def (quote soundnessConv↑Term)
    (hArg (var 13 []) ∷
     hArg (var 12 []) ∷
     hArg (var 7 []) ∷
     hArg (var 6 []) ∷
     hArg
     (def (quote Definition.Untyped._[_])
      (hArg (var 13 []) ∷
       vArg (var 5 []) ∷
       vArg (def (quote Definition.Untyped.zero) (hArg (var 13 []) ∷ []))
       ∷ []))
     ∷ vArg (var 2 []) ∷ []))
   ∷
   vArg
   (def (quote soundnessConv↑Term)
    (hArg (var 13 []) ∷
     hArg (var 12 []) ∷
     hArg (var 9 []) ∷
     hArg (var 8 []) ∷
     hArg
     (def (quote Definition.Untyped.Π_▹_)
      (hArg (var 13 []) ∷
       vArg (def (quote Definition.Untyped.ℕ) (hArg (var 13 []) ∷ [])) ∷
       vArg
       (def (quote Definition.Untyped._▹▹_)
        (hArg
         (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 13 []) ∷ []))
         ∷
         vArg (var 5 []) ∷
         vArg
         (def (quote Definition.Untyped._[_]↑)
          (hArg (var 13 []) ∷
           vArg (var 5 []) ∷
           vArg
           (def (quote Definition.Untyped.suc)
            (hArg
             (con (quote Agda.Builtin.Nat.Nat.suc) (vArg (var 13 []) ∷ []))
             ∷
             vArg
             (con (quote Definition.Untyped.Term.var)
              (hArg unknown ∷
               vArg (con (quote Fin.zero) (hArg (var 13 []) ∷ [])) ∷ []))
             ∷ []))
           ∷ []))
         ∷ []))
       ∷ []))
     ∷ vArg (var 1 []) ∷ []))
   ∷
   vArg
   (def (quote soundness~↓)
    (hArg (var 13 []) ∷
     hArg (var 12 []) ∷
     hArg (var 11 []) ∷
     hArg (var 10 []) ∷
     hArg (def (quote Definition.Untyped.ℕ) (hArg (var 13 []) ∷ [])) ∷
     vArg (var 0 []) ∷ []))
   ∷ []))
 ∷
 Clause.clause
 (("Γ.n" , hArg (def (quote Agda.Builtin.Nat.Nat) [])) ∷
  ("Γ" ,
   hArg
   (def (quote Definition.Untyped.Con)
    (vArg (def (quote Definition.Untyped.Term) []) ∷
     vArg (var 0 []) ∷ [])))
  ∷
  ("A" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 1 []) ∷ [])))
  ∷
  ("k" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 2 []) ∷ [])))
  ∷
  ("l" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 3 []) ∷ [])))
  ∷
  ("G" ,
   hArg (def (quote Definition.Untyped.Term) (vArg (var 4 []) ∷ [])))
  ∷
  ("x₁" ,
   vArg
   (def (quote Definition.Conversion._⊢_[conv↑]_)
    (hArg (var 5 []) ∷
     vArg (var 4 []) ∷ vArg (var 3 []) ∷ vArg (var 0 []) ∷ [])))
  ∷
  ("k~l" ,
   vArg
   (def (quote Definition.Conversion._⊢_~_↓_)
    (hArg (var 6 []) ∷
     vArg (var 5 []) ∷
     vArg (var 3 []) ∷
     vArg (var 2 []) ∷
     vArg (def (quote Definition.Untyped.Empty) (hArg (var 6 []) ∷ []))
     ∷ [])))
  ∷ [])
 (hArg (Pattern.var 7) ∷
  hArg (Pattern.var 6) ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.Emptyrec)
    (hArg (var 7 []) ∷ vArg (var 5 []) ∷ vArg (var 4 []) ∷ [])))
  ∷
  hArg
  (Pattern.dot
   (def (quote Definition.Untyped.Emptyrec)
    (hArg (var 7 []) ∷ vArg (var 2 []) ∷ vArg (var 3 []) ∷ [])))
  ∷
  hArg (Pattern.var 5) ∷
  vArg
  (Pattern.con (quote Definition.Conversion._⊢_~_↑_.Emptyrec-cong)
   (hArg (Pattern.var 4) ∷
    hArg (Pattern.var 3) ∷
    hArg (Pattern.dot (var 5 [])) ∷
    hArg (Pattern.var 2) ∷
    vArg (Pattern.var 1) ∷ vArg (Pattern.var 0) ∷ []))
  ∷ [])
 (con (quote Definition.Typed._⊢_≡_∷_.Emptyrec-cong)
  (hArg unknown ∷
   hArg unknown ∷
   hArg (var 5 []) ∷
   hArg (var 2 []) ∷
   hArg (var 4 []) ∷
   hArg (var 3 []) ∷
   vArg
   (def (quote soundnessConv↑)
    (hArg (var 7 []) ∷
     hArg (var 6 []) ∷
     hArg (var 5 []) ∷ hArg (var 2 []) ∷ vArg (var 1 []) ∷ []))
   ∷
   vArg
   (def (quote soundness~↓)
    (hArg (var 7 []) ∷
     hArg (var 6 []) ∷
     hArg (var 4 []) ∷
     hArg (var 3 []) ∷
     hArg (def (quote Definition.Untyped.Empty) (hArg (var 7 []) ∷ []))
     ∷ vArg (var 0 []) ∷ []))
   ∷ []))
 ∷ [])
 -}
