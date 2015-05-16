-- de Bruijn indices.
module Name where

   open import SharedModules

   open import Data.Fin public
      using (zero; suc; pred; fromℕ; toℕ; inject+) renaming (Fin to Name; raise to shift)
   open Data.Fin using (raise)
   open import Data.Nat as Nat public using (zero; suc) renaming (ℕ to Cxt; module ℕ to Cxt)

   -- More convenient definition given the convention of writing Γ + n.
   infixl 6 _+_
   _+_ : Cxt → Cxt → Cxt
   _+_ = flip Nat._+_
