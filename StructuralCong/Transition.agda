module StructuralCong.Transition where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren
   open import Name as ᴺ using (Name; shift)
   open import Proc using (Proc); open Proc
   open import StructuralCong.Proc as ᴾ⁼ using (_≈_; module _≈_; _*⁼; ≈-sym; ≈-refl; ≈-reflexive);
      open _≈_ renaming (trans to ≈-trans)
   open import Proc.Ren
   open import Ren as ᴿ using (suc; push; pop; swap; ᴺren; module Renameable); open Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren

   -- The type of the symmetric residual (φ/E , E/φ) for a single transition.
   infixl 5 _Δ⁼_
   record _Δ⁼_ {ι Γ P P′} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (φ : P ≈ P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         φ/E : R ≈ R′
         E/φ : P′ —[ a - ι ]→ R′

   -- The symmetric residual. TODO: make infix.
   ⊖ : ∀ {ι Γ P P′} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (φ : P ≈ P′) → E Δ⁼ φ

   -- Structural congruences.
   ⊖ (ν•_ {x = x} (νᶜ E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P = ν ≈-reflexive (sym (swap-involutive _)) Δ νᵇ (ν• swap*E)
   ⊖ (νᵇ_ {a = • x} (ν• E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P = ≈-refl Δ ν• (νᶜ swap*E)
   ⊖ (νᵇ_ {a = x •} (νᵇ E)) (νν-swapₗ P) with (swap *ᵇ) E
   ... | swap*E rewrite swap-involutive P =
      ≈-trans (νν-swapᵣ _) (ν (ν ≈-reflexive (swap∘suc-swap∘swap _))) Δ νᵇ (νᵇ swap*E)
   ⊖ (νᵇ_ {a = • x} (νᵇ E)) (νν-swapₗ P) with (swap *ᵇ) E
   ... | swap*E rewrite swap-involutive P =
      ≈-trans (νν-swapᵣ _) (ν (ν ≈-reflexive (swap∘suc-swap∘swap _))) Δ νᵇ (νᵇ swap*E)
   ⊖ (νᶜ_ {a = a} (νᶜ E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P | swap∘push∘push a = νν-swapᵣ _ Δ νᶜ (νᶜ swap*E)
   ⊖ (ν•_ {x = x} (νᶜ E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E = ν ≈-reflexive (sym (swap-involutive _)) Δ νᵇ (ν• swap*E)
   ⊖ (νᵇ_ {a = • x} (ν• E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E = ≈-refl Δ ν• (νᶜ swap*E)
   ⊖ (νᵇ_ {a = x •} (νᵇ E)) (νν-swapᵣ P) with (swap *ᵇ) E
   ... | swap*E {-rewrite swap∘push∘push x-} =
      ≈-trans (νν-swapᵣ _) (ν (ν ≈-reflexive (swap∘suc-swap∘swap _))) Δ νᵇ (νᵇ swap*E)
   ⊖ (νᵇ_ {a = • x} (νᵇ E)) (νν-swapᵣ P) with (swap *ᵇ) E
   ... | swap*E {- rewrite swap∘push∘push x-} =
      ≈-trans (νν-swapᵣ _) (ν (ν ≈-reflexive (swap∘suc-swap∘swap _))) Δ νᵇ (νᵇ swap*E)
   ⊖ (νᶜ_ {a = a} (νᶜ E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap∘push∘push a = νν-swapᵣ _ Δ νᶜ (νᶜ swap*E)
   -- Compatibility.
   ⊖ (x •∙ P) (.x •∙ refl) = ≈-refl Δ (x •∙ P)
   ⊖ (• x 〈 y 〉∙ P) (• .x 〈 .y 〉∙ refl) = ≈-refl Δ (• x 〈 y 〉∙ P)
   ⊖ (E ➕₁ Q) (φ ➕₁ refl) = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ (E/φ ➕₁ Q)
   ⊖ (E ➕₁ Q) (P ➕₂ ψ) = ≈-refl Δ (E ➕₁ ᴾ⁼.target ψ)
   ⊖ (E ᵇ│ Q) (φ │₁ refl) = let φ/E Δ E/φ = ⊖ E φ in (φ/E │₁ refl) Δ (E/φ ᵇ│ Q)
   ⊖ (E ᶜ│ Q) (φ │₁ refl) = let φ/E Δ E/φ = ⊖ E φ in (φ/E │₁ refl) Δ (E/φ ᶜ│ Q)
   ⊖ (P │ᵇ F) (φ │₁ refl) = ((push *⁼) φ │₁ refl) Δ (ᴾ⁼.target φ │ᵇ F)

   ⊖ (ν• E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ ν• E/φ
   ⊖ (νᵇ E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in ν ((swap *⁼) φ/E) Δ νᵇ E/φ
   ⊖ (νᶜ E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in ν φ/E Δ νᶜ E/φ
   ⊖ (! E) (! φ) = ? --let φ/E Δ E/φ = ⊖ E (φ │ ! φ) in φ/E Δ ! E/φ
   -- Transitivity. Currently writing this in the paper as ∘ (and reversing the argument order).
   ⊖ E (≈-trans φ φ′) = let φ/E Δ E/φ = ⊖ E φ; φ′/E/φ Δ E/φ/φ′ = ⊖ E/φ φ′ in ≈-trans φ/E φ′/E/φ Δ E/φ/φ′
   ⊖ _ _ = {!!}
{-
   ⊖ (P │ᶜ F) (φ │₁ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in (φ │ ψ/F) Δ (ᴾ⁼.target φ │ᶜ F/ψ)
   ⊖ (_│•_ {y = y} E F) (φ │ ψ) = let φ/E Δ E/φ = ⊖ E φ; ψ/F Δ F/ψ = ⊖ F ψ in
      ((pop y *⁼) φ/E │ ψ/F) Δ (E/φ │• F/ψ)
   ⊖ (E │ᵥ F) (φ │ ψ) = let φ/E Δ E/φ = ⊖ E φ; ψ/F Δ F/ψ = ⊖ F ψ in ν (φ/E │ ψ/F) Δ (E/φ │ᵥ F/ψ)
-}
