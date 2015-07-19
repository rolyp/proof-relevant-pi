module Transition.Concur.Cofinal.Transition where

   open import SharedModules

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖); open _ᴬ⌣_
   open import Action.Ren using (ren-preserves-inc-assoc)
   open import Braiding.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Name using (_+_; +-assoc)
   open import Ren as ᴿ using (swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Proc using (Proc; Proc↱)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur.Cofinal using (⋈[_,_,_])
   open import Transition.Ren using (_*′)

   blah : ∀ {Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) Δ′ → let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in
          (a† : Action (Γ′ + Δ′)) → Action (Γ′ + Δ′)
   blah ˣ∇ˣ _ a = a
   blah ᵇ∇ᵇ Γ′ a = ((swap ᴿ+ Γ′) *) a
   blah ᵇ∇ᶜ _ a = a
   blah ᶜ∇ᵇ _ a = a
   blah ᶜ∇ᶜ _ a = a
   blah ᵛ∇ᵛ _ a = a

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ} {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) {Γ′} {P P′ : Proc (Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) + Γ′)} {a R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , 𝑎 , Γ′ ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : Proc _
         γ/E : ⋈[ Γ , 𝑎 , Γ′ + inc a ] (Proc↱ (+-assoc _ Γ′ (inc a)) R) R′
         E/γ : P′ —[ blah 𝑎 Γ′ a - ι ]→ Proc↱ {!!} R′
{-
         E/γ : P′ —[ ((σ ᴿ+ Γ′) *) a - ι ]→ Proc↱ (ren-preserves-inc-assoc σ Γ′ a) R′

   -- Hoped Agda would be able to infer ӓ and Γ′ from γ, but apparently not.
   ⊖′[_,_] : ∀ {ι Γ} (ӓ : Action₂ Γ) Γ′ {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {a R}
            (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) → _Δ′_ {ӓ = ӓ} {Γ′ = Γ′} E γ
   ⊖′[ ӓ , Γ′ ] {a = (_ •) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = (• _) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = • _ 〈 _ 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , Γ′ ] {a = τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ Γ′) *′) E) γ in φ/E′ Δ E′/φ
-}
