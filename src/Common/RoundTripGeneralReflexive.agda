module Common.RoundTripGeneralReflexive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Equality
open import Prelude.Function
open import Common.RoundTripGeneral

roundTripGeneralReflexive :
  {la : Level}
  {A : Set la}
  {F : {lf : Level} → Set lf → Set lf}
  {pure : {lx : Level} {X : Set lx} → X → F X}
  {liftDomain : {lx ly : Level} {X : Set lx} {Y : Set ly} → (X → F Y) → (F X → F Y)}
  {law : {lx ly : Level} {X : Set lx} {Y : Set ly} (f : X → F Y) (x : X) → liftDomain f (pure x) ≡ f x}
  → RoundTripGeneral A A F pure liftDomain law
roundTripGeneralReflexive {A = A} {pure = pure} {law = law} = roundTripGeneral pure id p
  where
    p : (x : A) → pure x ≡ pure (id x)
    p x = cong pure refl
