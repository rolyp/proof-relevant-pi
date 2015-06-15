module Transition.Concur.Cofinal.Transition where

   open import Action as ᴬ using (inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Ren using (ren-preserves-inc-assoc)
   open import Name using (_+_; +-assoc)
   open import Ren as ᴿ using (_ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Proc using (Proc; Proc↱)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur using (Action₂; inc₂)
   open import Transition.Concur.Cofinal using (⋈[_,_,_]; braid)
   open import Transition.Ren using (_*′)

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ} {ӓ : Action₂ Γ} {m} {P P′ : Proc (Γ + inc₂ ӓ + m)} {a R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , ӓ , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E : ⋈[ Γ , ӓ , m + inc a ] (Proc↱ (+-assoc _ m (inc a)) R) R′
      σ = braid {Γ} ӓ
      field
         E/γ : P′ —[ ((σ ᴿ+ m) *) a - ι ]→ Proc↱ (ren-preserves-inc-assoc σ m a) R′

   ⊖′[_,_] : ∀ {ι Γ} (ӓ : Action₂ Γ) m {P P′ : Proc (Γ + inc₂ ӓ + m)} {a R}
            (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , ӓ , m ] P P′) → _Δ′_ {ӓ = ӓ} {m = m} E γ
   ⊖′[ ӓ , m ] {a = (_ •) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , m ] {a = (• _) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , m ] {a = • _ 〈 _ 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ ӓ , m ] {a = τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid ӓ ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
