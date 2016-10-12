module AncientLanguage.Abstraction where

open import Agda.Builtin.Nat using (Nat; zero; suc) public
open import Agda.Builtin.Equality public

open import AncientLanguage.Abstraction.Applicative public
open import AncientLanguage.Abstraction.Function public
open import AncientLanguage.Abstraction.Monoid public
open import AncientLanguage.Abstraction.Monoid-Applicative public
open import AncientLanguage.Abstraction.Product public
open import AncientLanguage.Abstraction.List public
open import AncientLanguage.Abstraction.Traverse public


idApplicative : Applicative Function.id
idApplicative = applicative Function.id Function.id

module TraverseId = Traverse idApplicative


fwdAppendMonoid : {A : Set} → Monoid (Fwd A)
fwdAppendMonoid = monoid [] Fwd.append

inrApplicative/fwdAppend : {A : Set} → Applicative (Fwd A +_)
inrApplicative/fwdAppend {A} = inr where open Monoid-Applicative fwdAppendMonoid

module TraverseInr {A : Set} = Traverse (inrApplicative/fwdAppend {A})
