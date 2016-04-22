module Common.RoundTrip.Partial.Result where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Prelude.Applicative
  using (Applicative)
open import Prelude.Functor
  using (Functor)
open import Prelude.Monad
  using (Monad)
  using (_≫=_)
open import Prelude.Monoidal.Void
open import Prelude.Monoidal.Product.Indexed

open Π

data Result
  {le : Level}
  (E : Set le)
  {la : Level}
  (A : Set la)
  : Set (le ⊔ la)
  where
  defined : A → Result E A
  undefined : E → Result E A

syntax Result E A = A ⁇ E

Defined?
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → A ⁇ E
  → Set
Defined? (defined x) = ⊤
Defined? (undefined x) = 𝟘

extractDefined
  : {la le : Level}
  → {A : Set la}
  → {E : Set le}
  → (x : A ⁇ E)
  → {_ : Defined? x}
  → A
extractDefined (defined x) = x
extractDefined (undefined x) {}

mapUndefined
  : {la le1 le2 : Level}
  → {A : Set la}
  → {E1 : Set le1}
  → {E2 : Set le2}
  → (E1 → E2)
  → A ⁇ E1
  → A ⁇ E2
mapUndefined f (defined x) = defined x
mapUndefined f (undefined x) = undefined (f x)

liftDomain
  : {lb lc le : Level}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → (B → C ⁇ E)
  → (B ⁇ E)
  → (C ⁇ E)
liftDomain g (defined x) = g x
liftDomain g (undefined x) = undefined x

joinDefined
  : {la lb lc le : Level}
  → {A : Set la}
  → {B : Set lb}
  → {C : Set lc}
  → {E : Set le}
  → (A → B ⁇ E)
  → (B → C ⁇ E)
  → (A → C ⁇ E)
joinDefined f g = liftDomain g ∘ f

mapDefined
  : {le la lb : Level}
  → {E : Set le}
  → {A : Set la}
  → {B : Set lb}
  → (A → B)
  → A ⁇ E
  → B ⁇ E
mapDefined f (defined x) = defined (f x)
mapDefined f (undefined x) = undefined x

bindDefined
  : {le : Level}
  → {E : Set le}
  → {la lb : Level}
  → {A : Set la}
  → {B : Set lb}
  → (k : A → Result E B)
  → Result E A
  → Result E B
bindDefined f (defined x) = f x
bindDefined f (undefined x) = undefined x

instance
  functor
    : {le : Level}
    → {E : Set le}
    → {la : Level}
    → Functor (Result E {la})
  Functor.map functor = mapDefined

  monad
    : {le : Level}
    → {E : Set le}
    → {la : Level}
    → Monad (Result E {la})
  Monad.return monad = defined
  Monad.bind monad = bindDefined

  applicative
    : {le : Level}
    → {E : Set le}
    → {la : Level}
    → Applicative (Result E {la})
  applicative = Monad.applicative monad
