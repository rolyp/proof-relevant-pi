module Transition.Concur.Cofinal.Transition where

   open import SharedModules

   open import Action as ᴬ using (inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (Action₂)
   open import Action.Ren using (ren-preserves-inc-assoc)
   open import Name using (_+_; +-assoc)
   open import Ren as ᴿ using (_ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Proc using (Proc; Proc↱)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur.Cofinal using (⋈[_,_,_]; braid)
   open import Transition.Ren using (_*′)

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ} {ӓ : Action₂ Γ} {Γ′} {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {a R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : Proc _
         γ/E : ⋈[ Γ , ӓ , Γ′ + inc a ] (Proc↱ (+-assoc _ Γ′ (inc a)) R) R′
      σ = braid {Γ} ӓ
      field
         E/γ : P′ —[ ((σ ᴿ+ Γ′) *) a - ι ]→ Proc↱ (ren-preserves-inc-assoc σ Γ′ a) R′

   -- Hoped Agda would be able to infer ӓ and Γ′ from γ, but apparently not.
   ⊖′[_,_] : ∀ {ι Γ} (ӓ : Action₂ Γ) Γ′ {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {a R}
            (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) → _Δ′_ {ӓ = ӓ} {Γ′ = Γ′} E γ
   ⊖′[ ӓ , Γ′ ] {a = (_ •) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = (• _) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = • _ 〈 _ 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
