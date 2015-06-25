-- de Bruijn indices.
module Name where

   open import SharedModules

   open import Data.Fin public
      using (zero; suc; fromℕ; toℕ) renaming (Fin to Name; raise to shift)
   open import Data.Nat as Nat public using (zero; suc) renaming (ℕ to Cxt; module ℕ to Cxt)

   -- More convenient definition given the convention of writing Γ + n.
   infixl 6 _+_
   _+_ : Cxt → Cxt → Cxt
   _+_ = flip Nat._+_

   +-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
   +-assoc m n zero = refl
   +-assoc m n (suc o) = cong suc (+-assoc m n o)
