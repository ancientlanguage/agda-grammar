module Greek.Path where

open import Agda.Primitive
open import Core
open import Greek.Script
open import Agda.Builtin.List

open Equivalence
open Vector.Wrapper

root : List Script ≅ Vector Script
root = ListVector.list≅vector

