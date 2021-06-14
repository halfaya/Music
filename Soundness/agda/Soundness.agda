{-# OPTIONS --without-K --erased-cubical --no-import-sorts #-}

module Soundness where

open import Prelude

open import Motif using (motif)
open import SUtil

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

Proof : Type
Proof = List Line

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

data TopLevel : Type where
  s↑   : TopLevel
  s↓   : TopLevel
  sc↑  : TopLevel
  sc↓  : TopLevel
  sct↑ : TopLevel
  sct↓ : TopLevel

topLevelName : TopLevel → Name
topLevelName s↑ = quote soundness~↑
topLevelName s↓ = quote soundness~↓
topLevelName sc↑ = quote soundnessConv↑
topLevelName sc↓ = quote soundnessConv↓
topLevelName sct↑ = quote soundnessConv↑Term
topLevelName sct↓ = quote soundnessConv↓Term

isTopLevel : Name → Maybe TopLevel
isTopLevel n =
  if      n == quote soundness~↑ then just s↑
  else if n == quote soundness~↓ then just s↓
  else if n == quote soundnessConv↑ then just sc↑
  else if n == quote soundnessConv↓ then just sc↓
  else if n == quote soundnessConv↑Term then just sct↑
  else if n == quote soundnessConv↓Term then just sct↓
  else nothing

topLevelDef : TopLevel → Definition
topLevelDef s↑ = getDef soundness~↑
topLevelDef s↓ = getDef soundness~↓
topLevelDef sc↑ = getDef soundnessConv↑
topLevelDef sc↓ = getDef soundnessConv↓
topLevelDef sct↑ = getDef soundnessConv↑Term
topLevelDef sct↓ = getDef soundnessConv↓Term

topLevelProof : TopLevel → Proof
topLevelProof = getNamesD ∘ topLevelDef


{-
topLevelNames : List Name
topLevelNames = map fst topLevel

proofs : List Proof
proofs = map (λ x → proof (fst x) (getNamesD (snd x))) topLevel
-}

{-# TERMINATING #-}
proof→notes : ℕ → ℕ → TopLevel → List Note
line→notes  : ℕ → ℕ → Line → List Note
names→notes : ℕ → ℕ → List Name → List Note

-- starts with proof name
proof→notes n m t = map (iterate m doubleSpeed) (motif (topLevelName t) ++ concatMap (line→notes n m) (topLevelProof t))

-- just use rhs for now
line→notes n m (line lhs rhs) = names→notes n m rhs

names→notes _    m []         = []
names→notes zero m ns@(_ ∷ _) = map (iterate m doubleSpeed) (concatMap motif ns)
names→notes (suc k) m (n ∷ ns) with isTopLevel n
... | just t  = proof→notes k (suc m) t ++ names→notes (suc k) m ns 
... | nothing = map (iterate m doubleSpeed) (motif n) ++ names→notes (suc k) m ns 

---------------

music : Vec (List Note) 1
music = proof→notes 3 0 s↑ ∷ []

tempo : ℕ
tempo = 160

soundTracks : List MidiTrack
soundTracks = makeTrackList tempo music
