module Proc where

   open import ProofRelevantPiCommon

   open import Name as ᴺ using (Cxt; Name; _+_)

   -- The ∙ in the prefix forms is for syntactic disambiguation with actions.
   data Proc (Γ : Cxt) : Set where
      Ο : Proc Γ
      _•∙_ : Name Γ → Proc (Γ + 1) → Proc Γ
      •_〈_〉∙_ : Name Γ → Name Γ → Proc Γ → Proc Γ
      _➕_ _│_ : Proc Γ → Proc Γ → Proc Γ
      ν_ : Proc (Γ + 1) → Proc Γ
      !_ : Proc Γ → Proc Γ

   infixl 6 _➕_ _│_
   infixr 7 _•∙_ •_〈_〉∙_

   -- Useful shorthand when working with heterogeneous equality.
   Proc↱ = subst Proc
   Proc↲ = ≡-subst-removable Proc
