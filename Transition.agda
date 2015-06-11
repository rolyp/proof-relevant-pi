module Transition where

   open import SharedModules
   open import Ext

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   import Action.Ren
   open import Name as ᴺ using (Name; _+_; suc; zero; toℕ)
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Ren as ᴿ using (push; pop; swap; Renameable); open ᴿ.Renameable ⦃...⦄

   -- Transitions carry an explicit size index so we can define residuals to be size-preserving. Symmetric
   -- variants of _│•_ and _│ᵥ_ are omitted.
   data _—[_-_]→_ {Γ} : Proc Γ → (a : Action Γ) → Size → Proc (Γ + inc a) → Set where
      _•∙_ : ∀ {ι} (x : Name Γ) (P : Proc (Γ + 1)) → x •∙ P —[ x • ᵇ - ↑ ι ]→ P
      •_〈_〉∙_ : ∀ {ι} (x y : Name Γ) (P : Proc Γ) → • x 〈 y 〉∙ P —[ • x 〈 y 〉 ᶜ - ↑ ι ]→ P
      _➕₁_ : ∀ {ι P} {a : Action Γ} {R} → P —[ a - ι ]→ R → (Q : Proc Γ) → P ➕ Q —[ a - ↑ ι ]→ R
      _ᵇ│_ : ∀ {ι P} {a : Actionᵇ Γ} {R} → P —[ a ᵇ - ι ]→ R → (Q : Proc Γ) → P │ Q —[ a ᵇ - ↑ ι ]→ R │ (push *) Q
      _ᶜ│_ : ∀ {ι P} {a : Actionᶜ Γ} {R} → P —[ a ᶜ - ι ]→ R → (Q : Proc Γ) → P │ Q —[ a ᶜ - ↑ ι ]→ R │ Q
      _│ᵇ_ : ∀ {ι Q} {a : Actionᵇ Γ} {S} → (P : Proc Γ) → Q —[ a ᵇ - ι ]→ S → P │ Q —[ a ᵇ - ↑ ι ]→ (push *) P │ S
      _│ᶜ_ : ∀ {ι Q} {a : Actionᶜ Γ} {S} → (P : Proc Γ) → Q —[ a ᶜ - ι ]→ S → P │ Q —[ a ᶜ - ↑ ι ]→ P │ S
      _│•_ : ∀ {ι P R Q S} {x : Name Γ} {y : Name Γ} →
             P —[ x • ᵇ - ι ]→ R → Q —[ • x 〈 y 〉 ᶜ - ι ]→ S → P │ Q —[ τ ᶜ - ↑ ι ]→ (pop y *) R │ S
      _│ᵥ_ : ∀ {ι P R Q S} {x : Name Γ} → P —[ x • ᵇ - ι ]→ R → Q —[ (• x) ᵇ - ι ]→ S →
             P │ Q —[ τ ᶜ - ↑ ι ]→ ν (R │ S)
      ν•_ : ∀ {ι P R} {x : Name Γ} → P —[ • suc x 〈 zero 〉 ᶜ - ι ]→ R → ν P —[ (• x) ᵇ - ↑ ι ]→ R
      νᵇ_ : ∀ {ι P R} {a : Actionᵇ Γ} → P —[ (push *) a ᵇ - ι ]→ R → ν P —[ a ᵇ - ↑ ι ]→ ν (swap *) R
      νᶜ_ : ∀ {ι P R} {a : Actionᶜ Γ} → P —[ (push *) a ᶜ - ι ]→ R → ν P —[ a ᶜ - ↑ ι ]→ ν R
      !_ : ∀ {ι P} {a : Action Γ} {R} → P │ ! P —[ a - ι ]→ R → ! P —[ a - ↑ ι ]→ R

   infixl 0 _—[_-_]→_
   infixl 6 _➕₁_ _ᵇ│_ _ᶜ│_ _│ᵇ_ _│ᶜ_ _│•_ _│ᵥ_
   infixr 7 _•∙_ •_〈_〉∙_

   source : ∀ {ι Γ P} {a : Action Γ} {R} → P —[ a - ι ]→ R → Proc Γ
   source {P = P} _ = P

   out : ∀ {ι Γ P} {a : Action Γ} {R} → P —[ a - ι ]→ R → Σ[ a′ ∈ Action Γ ] Proc (Γ + inc a′)
   out {a = a} {R} _ = a , R

   action : ∀ {ι Γ P} {a : Action Γ} {R} → P —[ a - ι ]→ R → Action Γ
   action = π₁ ∘ out

   target : ∀ {ι Γ P} {a : Action Γ} {R} → P —[ a - ι ]→ R → Proc (Γ + inc a)
   target = π₂ ∘ out
