module Braiding.Transition where

   open import ProofRelevantPiCommon

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Braiding.Proc as ᴾ⁼ using (_*⁼; _⋉_; ⋉-refl; ⋉-reflexive); open ᴾ⁼._⋉_
   open import Action.Ren
   open import Proc.Ren
   open import Ren as ᴿ using (suc; push; pop; swap; ᴺren; module Renameable); open Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; tgt); open ᵀ._—[_-_]→_
   open import Transition.Ren

   -- Type of symmetric residual (φ/E , E/φ) for a single transition.
   infixl 5 _Δ⁼_
   record _Δ⁼_ {ι Γ P P′} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (φ : P ⋉ P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         φ/E : R ⋉ R′
         E/φ : P′ —[ a - ι ]→ R′

   -- Symmetric residual. TODO: make infix.
   ⊖ : ∀ {ι Γ P P′} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) (φ : P ⋉ P′) → E Δ⁼ φ
   ⊖ (ν• (νᶜ E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P = ν ⋉-reflexive (sym (swap-involutive _)) Δ (νᵇ (ν• swap*E))
   ⊖ (νᵇ_ {a = • x} (ν• E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P = ⋉-refl Δ ν• (νᶜ swap*E)
   ⊖ (νᵇ_ {a = x •} (νᵇ E)) (νν-swapₗ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (tgt E)))
   ... | swap*E | νν rewrite swap-involutive P | swap∘suc-swap∘swap (tgt E) =
      νν Δ νᵇ (νᵇ swap*E)
   ⊖ (νᵇ_ {a = • x} (νᵇ E)) (νν-swapₗ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (tgt E)))
   ... | swap*E | νν rewrite swap-involutive P | swap∘suc-swap∘swap (tgt E) =
      νν Δ νᵇ (νᵇ swap*E)
   ⊖ (νᶜ_ {a = a} (νᶜ E)) (νν-swapₗ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap-involutive P | swap∘push∘push a = νν-swapᵣ _ Δ νᶜ (νᶜ swap*E)
   ⊖ (ν•_ {x = x} (νᶜ E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E = ν ⋉-reflexive (sym (swap-involutive _)) Δ νᵇ (ν• swap*E)
   ⊖ (νᵇ_ {a = • x} (ν• E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E = ⋉-refl Δ ν• (νᶜ swap*E)
   ⊖ (νᵇ_ {a = x •} (νᵇ E)) (νν-swapᵣ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (tgt E)))
   ... | swap*E | νν rewrite swap∘suc-swap∘swap (tgt E) = νν Δ νᵇ (νᵇ swap*E)
   ⊖ (νᵇ_ {a = • x} (νᵇ E)) (νν-swapᵣ P) with (swap *ᵇ) E | νν-swapᵣ ((suc swap *) ((swap *) (tgt E)))
   ... | swap*E | νν rewrite swap∘suc-swap∘swap (tgt E) = νν Δ νᵇ (νᵇ swap*E)
   ⊖ (νᶜ_ {a = a} (νᶜ E)) (νν-swapᵣ P) with (swap *ᶜ) E
   ... | swap*E rewrite swap∘push∘push a = νν-swapᵣ _ Δ νᶜ (νᶜ swap*E)
   ⊖ (x •∙ P) (.x •∙ refl) = ⋉-refl Δ (x •∙ P)
   ⊖ (• x 〈 y 〉∙ P) (• .x 〈 .y 〉∙ refl) = ⋉-refl Δ (• x 〈 y 〉∙ P)
   ⊖ (E ➕₁ Q) (φ ➕₁ refl) = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ (E/φ ➕₁ Q)
   ⊖ (E ➕₁ Q) (refl ➕₂ ψ) = ⋉-refl Δ (E ➕₁ ᴾ⁼.tgt ψ)
   ⊖ (E ᵇ│ Q) (φ │ ψ) = let φ/E Δ E/φ = ⊖ E φ in (φ/E │ (push *⁼) ψ) Δ (E/φ ᵇ│ ᴾ⁼.tgt ψ)
   ⊖ (E ᶜ│ Q) (φ │ ψ) = let φ/E Δ E/φ = ⊖ E φ in (φ/E │ ψ) Δ (E/φ ᶜ│ ᴾ⁼.tgt ψ)
   ⊖ (P │ᵇ F) (φ │ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in ((push *⁼) φ │ ψ/F) Δ (ᴾ⁼.tgt φ │ᵇ F/ψ)
   ⊖ (P │ᶜ F) (φ │ ψ) = let ψ/F Δ F/ψ = ⊖ F ψ in (φ │ ψ/F) Δ (ᴾ⁼.tgt φ │ᶜ F/ψ)
   ⊖ (_│•_ {y = y} E F) (φ │ ψ) = let φ/E Δ E/φ = ⊖ E φ; ψ/F Δ F/ψ = ⊖ F ψ in ((pop y *⁼) φ/E │ ψ/F) Δ (E/φ │• F/ψ)
   ⊖ (E │ᵥ F) (φ │ ψ) = let φ/E Δ E/φ = ⊖ E φ; ψ/F Δ F/ψ = ⊖ F ψ in (ν ((id *⁼) φ/E │ ψ/F)) Δ (E/φ │ᵥ F/ψ)
   ⊖ (ν• E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in φ/E Δ ν• E/φ
   ⊖ (νᵇ E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in ν (swap *⁼) φ/E Δ νᵇ E/φ
   ⊖ (νᶜ E) (ν φ) = let φ/E Δ E/φ = ⊖ E φ in ν φ/E Δ νᶜ E/φ
   ⊖ (! E) (! φ) = let φ/E Δ E/φ = ⊖ E (φ │ ! φ) in φ/E Δ ! E/φ
