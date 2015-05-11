-- Expand some equation-like rules into true equalities by pattern-matching. Agda mostly sucks at this.
module StructuralCong.Transition.Properties where

   open import SharedModules hiding (trans)

   open import Action as ᴬ using (Action); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Name as ᴺ using (Name; zero)
   open import StructuralCong.Proc as ᴾ⁼ using (_≅_); open ᴾ⁼._≅_
   open import StructuralCong.Transition using (⊖; _Δ_)
   open import Transition as ᵀ using (_—[_-_]→_); open ᵀ._—[_-_]→_

   ⊖-ν•-ν : ∀ {ι Γ P P′ R} {x : Name Γ} (E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - ι ]→ R) {φ : P ≅ P′} →
            ⊖ (ν• E) (ν φ) ≡ let φ/E Δ E/φ = ⊖ E φ in φ/E Δ ν• E/φ
   ⊖-ν•-ν (• ._ 〈 ._ 〉∙ _) = refl
   ⊖-ν•-ν (_ ➕₁ _) = refl
   ⊖-ν•-ν (_ ᶜ│ _) = refl
   ⊖-ν•-ν (_ │ᶜ _) = refl
   ⊖-ν•-ν (νᶜ _) = refl
   ⊖-ν•-ν (! _) = refl

   ⊖-trans : ∀ {ι Γ P P′ P″} {a : Action Γ} {R} (E : P —[ a - ι ]→ R) {φ : P ≅ P′} {φ′ : P′ ≅ P″} →
             ⊖ E (trans φ φ′) ≡ let φ/E Δ E/φ = ⊖ E φ; φ′/E/φ Δ E/φ/φ′ = ⊖ E/φ φ′ in (trans φ/E φ′/E/φ) Δ E/φ/φ′
   ⊖-trans (_ •∙ _) = refl
   ⊖-trans (• _ 〈 _ 〉∙ _) = refl
   ⊖-trans (_ ➕₁ _) = refl
   ⊖-trans (_ ᵇ│ _) = refl
   ⊖-trans (_ ᶜ│ _) = refl
   ⊖-trans (_ │ᵇ _) = refl
   ⊖-trans (_ │ᶜ _) = refl
   ⊖-trans (_ │• _) = refl
   ⊖-trans (_ •│ _) = refl
   ⊖-trans (_ │ᵥ _) = refl
   ⊖-trans (ν• (• ._ 〈 ._ 〉∙ _)) = refl
   ⊖-trans (ν• (_ ➕₁ _)) = refl
   ⊖-trans (ν• (_ ᶜ│ _)) = refl
   ⊖-trans (ν• (_ │ᶜ _)) = refl
   ⊖-trans (ν• (νᶜ _)) = refl
   ⊖-trans (ν• (! _)) = refl
   ⊖-trans (νᵇ_ {a = _ •} (._ •∙ _)) = refl
   ⊖-trans (νᵇ_ {a = _ •} (_ ➕₁ _)) = refl
   ⊖-trans (νᵇ_ {a = _ •} (_ ᵇ│ _)) = refl
   ⊖-trans (νᵇ_ {a = _ •} (_ │ᵇ _)) = refl
   ⊖-trans (νᵇ_ {a = _ •} (νᵇ _)) = refl
   ⊖-trans (νᵇ_ {a = _ •} (! _)) = refl
   ⊖-trans (νᵇ_ {a = • _} (_ ➕₁ _)) = refl
   ⊖-trans (νᵇ_ {a = • _} (_ ᵇ│ _)) = refl
   ⊖-trans (νᵇ_ {a = • _} (_ │ᵇ _)) = refl
   ⊖-trans (νᵇ_ {a = • _} (ν• _)) = refl
   ⊖-trans (νᵇ_ {a = • _} (νᵇ _)) = refl
   ⊖-trans (νᵇ_ {a = • _} (! _)) = refl
   ⊖-trans (νᶜ_ {a = • _ 〈 _ 〉} (• ._ 〈 ._ 〉∙ _)) = refl
   ⊖-trans (νᶜ_ {a = • _ 〈 _ 〉} (_ ➕₁ _)) = refl
   ⊖-trans (νᶜ_ {a = • _ 〈 _ 〉} (_ ᶜ│ _)) = refl
   ⊖-trans (νᶜ_ {a = • _ 〈 _ 〉} (_ │ᶜ _)) = refl
   ⊖-trans (νᶜ_ {a = • _ 〈 _ 〉} (νᶜ _)) = refl
   ⊖-trans (νᶜ_ {a = • _ 〈 _ 〉} (! _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (_ ➕₁ _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (_ ᶜ│ _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (_ │ᶜ _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (_ │• _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (_ •│ _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (_ │ᵥ _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (νᶜ _)) = refl
   ⊖-trans (νᶜ_ {a = τ} (! _)) = refl
   ⊖-trans (! _) = refl
