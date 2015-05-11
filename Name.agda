-- de Bruijn indices:
module Name where

   open import SharedModules

   open import Data.Fin public using (zero; suc; pred; fromℕ; toℕ) renaming (Fin to Name; _+_ to _ᴺ+_)
   open Data.Fin using (raise)
   open import Data.Nat as Nat public using (zero; suc) renaming (ℕ to Cxt; module ℕ to Cxt)

   -- More convenient definition.
   _+_ : Cxt → Cxt → Cxt
   _+_ = flip Nat._+_

   -- Useful for examples.
   _^_ : ∀ {Γ} → Name Γ → ∀ Γ′ → Name (Γ + Γ′)
   _^_ = flip raise
