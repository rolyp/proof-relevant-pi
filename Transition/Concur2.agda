module Transition.Concur2 where

   open import SharedModules hiding ([_])

   open import Ext

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   import Action.Ren
   open import Name as ᴺ using (Name; Cxt; module Cxt; zero; _+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; ᴺren; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   _ᴬΔ_ : ∀ {Γ} (a a′ : Action Γ) → Set
   _ᴬΔ_ {Γ} a a′ = Action (Γ + inc a) × Action (Γ + inc a′)

   -- The 5 kinds of coinitial action residual.
   data coinitial {Γ} : (a a′ : Action Γ) → Set where
      ᵛ∇ᵛ : (x u : Name Γ) → coinitial ((• x) ᵇ) ((• u) ᵇ)
      ᵇ∇ᵇ : (a a′ : Actionᵇ Γ) → coinitial (a ᵇ) (a′ ᵇ)
      ᵇ∇ᶜ : (a : Actionᵇ Γ) (a′ : Actionᶜ Γ) → coinitial (a ᵇ) (a′ ᶜ)
      ᶜ∇ᵇ : (a : Actionᶜ Γ) (a′ : Actionᵇ Γ) → coinitial (a ᶜ) (a′ ᵇ)
      ᶜ∇ᶜ : (a a′ : Actionᶜ Γ) → coinitial (a ᶜ) (a′ ᶜ)

   -- The symmetric residual (a′/a, a/a′). Note that ᵇ∇ᵇ may also relate two bound outputs, but only if
   -- they represent extrusions of distinct binders.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} → coinitial a a′ → a ᴬΔ a′
   ᴬ⊖ (ᵛ∇ᵛ x u) = • ᴺ.suc u 〈 zero 〉 ᶜ , • ᴺ.suc x 〈 zero 〉 ᶜ
   ᴬ⊖ (ᵇ∇ᵇ a a′) = (push *) a′ ᵇ , (push *) a ᵇ
   ᴬ⊖ (ᵇ∇ᶜ a a′) = (push *) a′ ᶜ , a ᵇ
   ᴬ⊖ (ᶜ∇ᵇ a a′) = a′ ᵇ , (push *) a ᶜ
   ᴬ⊖ (ᶜ∇ᶜ a a′) = a′ ᶜ , a ᶜ

   -- Whether two coinitial evaluation contexts are concurrent. Only give the left rules, then symmetrise.
   -- Convenient to have this indexed by the residual actions. TODO: cases for •│ and ᵥ│.
   syntax Concur₁ E E′ a⊖a′ = E ⌣₁[ a⊖a′ ] E′

   data Concur₁ {Γ} : ∀ {a : Action Γ} {a′ : Action Γ} {P R R′} →
                P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → a ᴬΔ a → Set where
      _ᵇ│ᵇ_ : ∀ {P Q R S} {a a′ : Actionᵇ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᴬ⊖ (ᵇ∇ᵇ a a′) ] P │ᵇ F
