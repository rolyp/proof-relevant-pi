-- (Partial) monoid of actions sequences.
module Action.Seq2 where

   open import SharedModules
   open import Action using (Action; inc)
   open import Name as ᴺ using (Cxt; _+_)

   infixr 9 _⍮_

   data Action⋆ (Γ : Cxt) : Set
   inc⋆ : ∀ {Γ} → Action⋆ Γ → Cxt

   data Action⋆ Γ where
      [_] : Action Γ → Action⋆ Γ
      -- Monoid operations.
      [] : Action⋆ Γ
      _⍮_ : (a⋆ : Action⋆ Γ) (a′⋆ : Action⋆ (Γ + inc⋆ a⋆)) → Action⋆ Γ

   -- Shorthand for working with heterogeneous equality.
   Action⋆↱ = subst Action⋆
   Action⋆↲ = ≡-subst-removable Action⋆

   inc⋆ [ a ] = inc a
   inc⋆ [] = 0
   inc⋆ (a⋆ ⍮ a′⋆) = inc⋆ a⋆ + inc⋆ a′⋆
