{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Bool
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Integer.Base
open import Data.Integer.Properties using (+-*-commutativeRing)

open import Tactic.RingSolver.Core.AlmostCommutativeRing using (fromCommutativeRing)
open import Tactic.RingSolver.NonReflective (fromCommutativeRing +-*-commutativeRing λ { +0 -> just refl; _ -> nothing}) public
