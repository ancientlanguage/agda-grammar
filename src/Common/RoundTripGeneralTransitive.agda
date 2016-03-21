module Common.RoundTripGeneralTransitive where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Prelude.Equality
open import Prelude.Function
open import Common.RoundTripGeneral

transitiveRTG
  : {F : {lf : Level} → Set lf → Set lf}
  → {pure : {lx : Level} {X : Set lx} → X → F X}
  → {liftDomain : {lx ly : Level} {X : Set lx} {Y : Set ly} → (X → F Y) → (F X → F Y)}
  → {law : {lx ly : Level} {X : Set lx} {Y : Set ly} (f : X → F Y) (x : X) → liftDomain f (pure x) ≡ f x}
  → {la lb lc : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → RoundTripGeneral F pure liftDomain law A B
  → RoundTripGeneral F pure liftDomain law B C
  → RoundTripGeneral F pure liftDomain law A C
transitiveRTG
  {F} {pure} {liftDomain} {law} {la} {lb} {lc} {A} {B} {C}
  (roundTripGeneral A→FB B→A pab)
  (roundTripGeneral B→FC C→B pbc)
  = roundTripGeneral A→FC C→A pac
  where
    FB→FC : F B → F C
    FB→FC = liftDomain B→FC

    A→FC : A → F C
    A→FC = FB→FC ∘ A→FB

    C→A : C → A
    C→A = B→A ∘ C→B

    pac
      : (c : C)
      → pure c ≡ A→FC (B→A (C→B c))
    pac c = trans pl pr
      where
      pl : pure c ≡ B→FC (C→B c)
      pl = pbc c

      paux : pure (C→B c) ≡ A→FB (B→A (C→B c))
      paux = pab (C→B c)

      pr : B→FC (C→B c) ≡ A→FC (B→A (C→B c))
      pr with cong FB→FC paux
      … | r rewrite law B→FC (C→B c) = r
