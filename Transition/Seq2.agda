module Transition.Seq2 where

   open import SharedModules

   open import Action.Seq2 as ᴬ⋆ using (Action⋆; inc⋆); open ᴬ⋆.Action⋆
   open import Name using (_+_; +-assoc)
   open import Proc using (Proc)

   -- Use the APL operator ⍮ for diagrammatic-order composition, since Unicode seems to be lacking any useful
   -- semicolons other than the one already reserved by Agda.
   infixr 9 _⍮_

   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      _⍮_ : ∀ {a⋆ R a′⋆ S} → P —[ a⋆ ]→⋆ R → R —[ a′⋆ ]→⋆ S →
            P —[ a⋆ ⍮ a′⋆ ]→⋆ subst Proc (+-assoc Γ (inc⋆ a⋆) (inc⋆ a′⋆)) S
