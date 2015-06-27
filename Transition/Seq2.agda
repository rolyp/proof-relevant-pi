-- (Partial) monoid of traces.
module Transition.Seq2 where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action using (inc)
   open import Action.Concur using (Action₂)
   open import Action.Seq2 as ᴬ⋆ using (Action⋆; Action⋆↱; Action⋆↲; inc⋆); open ᴬ⋆.Action⋆
   open import Action.Seq2.Ren using (ren-preserves-inc⋆-assoc)
   open import Name using (_+_; +-assoc)
   open import Proc using (Proc; Proc↱)
   open import Ren as ᴿ using (_ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import Transition using (_—[_-_]→_)
   open import Transition.Concur.Cofinal using (braid; ⋈[_,_,_]; ⊖-✓)
   open import Transition.Concur.Cofinal.Transition using (⊖′[_,_]; _Δ_)

   -- Use APL's ⍮ for diagrammatic-order composition, since Unicode's only useful semicolon is already reserved.
   infixr 9 _⍮_

   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [_] : ∀ {a R} → P —[ a - _ ]→ R → P —[ [ a ] ]→⋆ R
      -- Monoid operations.
      [] : P —[ [] ]→⋆ P
      _⍮_ : ∀ {a⋆ R a′⋆ S} → P —[ a⋆ ]→⋆ R → R —[ a′⋆ ]→⋆ S →
            P —[ a⋆ ⍮ a′⋆ ]→⋆ subst Proc (+-assoc Γ (inc⋆ a⋆) (inc⋆ a′⋆)) S

   target⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc (Γ + inc⋆ a⋆)
   target⋆ {R = R} _ = R

   action⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Action⋆ Γ
   action⋆ {a⋆ = a⋆} _ = a⋆

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace. Cofinal by construction.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ} {ӓ : Action₂ Γ} {Γ′ a⋆} {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E⋆ : ⋈[ Γ , ӓ , Γ′ + inc⋆ a⋆ ] (Proc↱ (+-assoc _ _ (inc⋆ a⋆)) R) R′
         E⋆/γ : P′ —[ ((braid ӓ ᴿ+ Γ′) *) a⋆ ]→⋆ Proc↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) R′

   -- Mostly an exercise in heterogenous equality.
   ⊖⋆[_,_] : ∀ {Γ} (ӓ : Action₂ Γ) Γ′ {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {a⋆ R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) → _Δ⋆_ {ӓ = ӓ} {Γ′ = Γ′} E⋆ γ
   ⊖⋆[_,_] ӓ Γ′ [ E ] γ with ⊖′[ ӓ , Γ′ ] E γ
   ... | γ/E Δ E/γ = γ/E Δ [ E/γ ]
   ⊖⋆[_,_] _ _ [] γ = γ Δ []
   ⊖⋆[_,_] {Γ} ӓ Γ′ {a⋆ = a⋆ ⍮ a′⋆} (E⋆ ⍮ E′⋆) γ with ⊖⋆[ ӓ , Γ′ ] E⋆ γ
   ... | γ/E⋆ Δ E⋆/γ =
      let bib : Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′ + inc⋆ a⋆ ≡ Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + (Γ′ + inc⋆ a⋆)
          bib = +-assoc _ Γ′ (inc⋆ a⋆)
          a†⋆ : Action⋆ (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + (Γ′ + inc⋆ a⋆))
          a†⋆ = Action⋆↱ bib a′⋆
          nib : inc⋆ a′⋆ ≡ inc⋆ (Action⋆↱ bib a′⋆)
          nib = ≅-to-≡ (≅-cong✴ Action⋆ bib inc⋆ (≅-sym (Action⋆↲ bib a′⋆)))
          S : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + (Γ′ + inc⋆ a⋆) + inc⋆ a†⋆)
          S = Proc↱ (
             let open EqReasoning (setoid _) in
             begin
                Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′ + inc⋆ a⋆ + inc⋆ a′⋆
             ≡⟨ cong₂ _+_ bib nib ⟩
                Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + (Γ′ + inc⋆ a⋆) + inc⋆ (Action⋆↱ bib a′⋆)
             ∎) (target⋆ E′⋆)
          E†⋆ : Proc↱ (+-assoc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ)) Γ′ (inc⋆ a⋆)) (target⋆ E⋆) —[ a†⋆ ]→⋆ S
          E†⋆ = {!!}
      in {!!}
-- with ⊖⋆[ ӓ , Γ′ + inc⋆ (action⋆ E⋆) ] {!E′⋆!} {-E′⋆-} γ/E⋆
--   ... | _ = {!!} Δ {!!}
