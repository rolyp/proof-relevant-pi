-- Residual of transitions and renamings.
module Transition.Ren where

   open import SharedModules

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren
   open import Name using (toℕ; _+_)
   open import Proc using (Proc)
   open import Proc.Ren
   open import Ren as ᴿ using (Ren; suc; pop; push; _ᴿ+_; swap; Renameable; ᴺren); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; action); open ᵀ._—[_-_]→_

   _*ᶜ : ∀ {ι Γ Γ′} (ρ : Ren Γ Γ′) {P R} {a : Actionᶜ Γ} → P —[ a ᶜ - ι ]→ R → (ρ *) P —[ (ρ *) a ᶜ - ι ]→ (ρ *) R
   _*ᵇ : ∀ {ι Γ Γ′} (ρ : Ren Γ Γ′) {P R} {a : Actionᵇ Γ} → P —[ a ᵇ - ι ]→ R → (ρ *) P —[ (ρ *) a ᵇ - ι ]→ (suc ρ *) R

   (ρ *ᶜ) (• x 〈 y 〉∙ P) = • (ρ *) x 〈 (ρ *) y 〉∙ (ρ *) P
   (ρ *ᶜ) (E ➕₁ Q) = (ρ *ᶜ) E ➕₁ (ρ *) Q
   (ρ *ᶜ) (E ᶜ│ Q) = (ρ *ᶜ) E ᶜ│ (ρ *) Q
   (ρ *ᶜ) (P │ᶜ F) = (ρ *) P │ᶜ (ρ *ᶜ) F
   (ρ *ᶜ) (_│•_ {R = R} {y = y} E F) with (ρ *ᵇ) E
   ... | E′ rewrite pop-comm ρ y R = E′ │• (ρ *ᶜ) F
   (ρ *ᶜ) (_•│_ {S = S} {y = y} E F) with (ρ *ᵇ) F
   ... | F′ rewrite pop-comm ρ y S = (ρ *ᶜ) E •│ F′
   (ρ *ᶜ) (E │ᵥ F) = (ρ *ᵇ) E │ᵥ (ρ *ᵇ) F
   (ρ *ᶜ) (νᶜ_ {a = a} E) with (suc ρ *ᶜ) E
   ... | E′ rewrite ᴿ+-comm 1 ρ a = νᶜ E′
   (ρ *ᶜ) (! E) = ! (ρ *ᶜ) E

   (ρ *ᵇ) (x •∙ P) = (ρ *) x •∙ (suc ρ *) P
   (ρ *ᵇ) (E ➕₁ Q) = (ρ *ᵇ) E ➕₁ (ρ *) Q
   (ρ *ᵇ) (E ᵇ│ Q) with (push * ∘ ρ *) Q
   ... | _ rewrite ᴿ+-comm 1 ρ Q = (ρ *ᵇ) E ᵇ│ (ρ *) Q
   (ρ *ᵇ) (P │ᵇ F) with (push * ∘ ρ *) P
   ... | _ rewrite ᴿ+-comm 1 ρ P = (ρ *) P │ᵇ (ρ *ᵇ) F
   (ρ *ᵇ) (ν•_ {x = x} E) with (suc ρ *ᶜ) E; ... | E′ = ν• E′
   (ρ *ᵇ) (νᵇ_ {R = R} {a = a} E) with (suc ρ *ᵇ) E
   ... | E′ rewrite ᴿ+-comm 1 ρ a | sym (swap-suc-suc ρ R) = νᵇ E′
   (ρ *ᵇ) (! E) = ! (ρ *ᵇ) E

   _*′_ : ∀ {ι Γ Γ′} (ρ : Ren Γ Γ′) {P} {a : Action Γ} {R} → P —[ a - ι ]→ R → (ρ *) P —[ (ρ *) a - ι ]→
         subst Proc (sym (ren-preserves-inc ρ a)) (((ρ ᴿ+ toℕ (inc a)) *) R)
   ρ *′ E with action E
   ... | (_ •) ᵇ = (ρ *ᵇ) E
   ... | (• _) ᵇ = (ρ *ᵇ) E
   ... | • _ 〈 _ 〉 ᶜ = (ρ *ᶜ) E
   ... | τ ᶜ = (ρ *ᶜ) E

   infixl 5 _Δ_
   record _Δ′_ {ι Γ Γ′} {P} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (ρ : Ren Γ Γ′) : Set where
      constructor _Δ_
      n = toℕ (inc a)
      field
         ρ/E : Ren (Γ + n) (Γ′ + n)
         E/ρ : (ρ *) P —[ (ρ *) a - ι ]→ subst Proc (sym (ren-preserves-inc ρ a)) ((ρ/E *) R)

   _/_ : ∀ {ι Γ Γ′} (ρ : Ren Γ Γ′) {P} {a : Action Γ} {R} → P —[ a - ι ]→ R → let n = toℕ (inc a) in Ren (Γ + n) (Γ′ + n)
   _/_ ρ {a = a} E = ρ ᴿ+ toℕ (inc a)

   _⊖_ : ∀ {ι Γ Γ′} {P} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (ρ : Ren Γ Γ′) → E Δ′ ρ
   _⊖_ E ρ = ρ / E Δ ρ *′ E
