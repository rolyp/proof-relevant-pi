module SharedModules where

   open import Algebra.FunctionProperties public
   open import Algebra.Structures public
   open import Data.Bool public hiding (_≟_; decSetoid)
   open import Data.Empty public
   open import Data.Product public renaming (proj₁ to π₁; proj₂ to π₂; swap to ×-swap)
   open import Data.String public hiding (decSetoid; setoid)
   open import Data.Sum public hiding (map)
   open import Data.Unit public hiding (_≟_; decSetoid; preorder; setoid; _≤_; module _≤_)
   open import Ext public hiding (_-×-_)
   open import Ext.Relation.Binary.HeterogeneousEquality public
   open import Ext.Relation.Binary.PropositionalEquality public
   open import Function public
   open import IO public
   open import Relation.Nullary public
   open import Relation.Binary public
   open import Relation.Binary.PropositionalEquality public
   open import Relation.Binary.HeterogeneousEquality as ᴴ public
      using (module ≅-Reasoning; ≅-to-≡; ≡-to-≅; subst-removable; ≡-subst-removable)
      renaming (
         _≅_ to _≅_; refl to ≅-refl; sym to ≅-sym; trans to ≅-trans;
         cong to ≅-cong; cong₂ to ≅-cong₂; subst to ≅-subst; subst₂ to ≅-subst₂
      )
   open import Size public
