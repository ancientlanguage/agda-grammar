module Common.Sum where

open import Agda.Primitive

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left : (x : A) → A ⊎ B
  right : (y : B) → A ⊎ B

{-# HASKELL type AgdaEither a b c d = Either c d #-}
{-# COMPILED_DATA _⊎_ MAlonzo.Code.Data.Sum.AgdaEither Left Right #-}
