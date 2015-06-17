-- de Bruijn indices.
module Name where

   open import SharedModules

   open import Data.Fin public
      using (zero; suc; pred; fromℕ; fromℕ≤; toℕ; inject+) renaming (Fin to Name; raise to shift)
   open Data.Fin using (raise)
   open import Data.Nat as Nat public using (zero; suc; _<_; _≤_; module _≤_)
      renaming (ℕ to Cxt; module ℕ to Cxt);
      open _≤_
   open import Data.Nat.Properties.Simple public using () renaming (+-right-identity to +-left-identity)

   -- More convenient definition given the convention of writing Γ + n.
   infixl 6 _+_
   _+_ : Cxt → Cxt → Cxt
   _+_ = flip Nat._+_

   +-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
   +-assoc m n zero = refl
   +-assoc m n (suc o) = cong suc (+-assoc m n o)
