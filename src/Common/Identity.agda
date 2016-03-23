module Common.Identity where

id : ∀ {a} {A : Set a} → A → A
id x = x
{-# INLINE id #-}
