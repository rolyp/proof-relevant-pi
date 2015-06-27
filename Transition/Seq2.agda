-- (Partial) monoid of traces.
module Transition.Seq2 where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action using (inc)
   open import Action.Concur using (Action₂)
   open import Action.Seq2 as ᴬ⋆ using (Action⋆; Action⋆↱; Action⋆↲; inc⋆); open ᴬ⋆.Action⋆
   open import Action.Seq2.Ren using (ren-preserves-inc⋆; ren-preserves-inc⋆-assoc)
   open import Name using (Cxt; _+_; +-assoc)
   open import Proc using (Proc; Proc↱; Proc↲)
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
            P —[ a⋆ ⍮ a′⋆ ]→⋆ Proc↱ (+-assoc Γ (inc⋆ a⋆) (inc⋆ a′⋆)) S

   source⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc Γ
   source⋆ {P = P} _ = P

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
         {R′} : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + (Γ′ + inc⋆ a⋆))
         γ/E⋆ : ⋈[ Γ , ӓ , Γ′ + inc⋆ a⋆ ] (Proc↱ (+-assoc _ _ (inc⋆ a⋆)) R) R′
         E⋆/γ : P′ —[ ((braid ӓ ᴿ+ Γ′) *) a⋆ ]→⋆ Proc↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) R′

   -- Mostly an exercise in heterogenous equality.
   {-# NO_TERMINATION_CHECK #-} -- might need size indices for this (residuation preserves size)
   ⊖⋆[_,_] : ∀ {Γ} (ӓ : Action₂ Γ) Γ′ {P P′ : Proc (Γ + inc (π₁ ӓ) + inc (π₂ ӓ) + Γ′)} {a⋆ R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , ӓ , Γ′ ] P P′) → _Δ⋆_ {ӓ = ӓ} {Γ′ = Γ′} E⋆ γ
   ⊖⋆[_,_] ӓ Γ′ [ E ] γ with ⊖′[ ӓ , Γ′ ] E γ
   ... | γ/E Δ E/γ = γ/E Δ [ E/γ ]
   ⊖⋆[_,_] _ _ [] γ = γ Δ []
   ⊖⋆[_,_] {Γ} ӓ Γ′ {a⋆ = a⋆ ⍮ a′⋆} (E⋆ ⍮ E′⋆) γ =
      let γ/E⋆ Δ E⋆/γ = ⊖⋆[ ӓ , Γ′ ] E⋆ γ
          Γ† = Γ + inc (π₁ ӓ) + inc (π₂ ӓ)
          bib : Γ† + Γ′ + inc⋆ a⋆ ≡ Γ† + (Γ′ + inc⋆ a⋆)
          bib = +-assoc Γ† Γ′ (inc⋆ a⋆)
          a†⋆ : Action⋆ (Γ† + (Γ′ + inc⋆ a⋆))
          a†⋆ = Action⋆↱ bib a′⋆
          nib : inc⋆ a′⋆ ≡ inc⋆ a†⋆
          nib = ≅-to-≡ (≅-cong✴ Action⋆ bib inc⋆ (≅-sym (Action⋆↲ bib a′⋆)))
          S : Proc (Γ† + (Γ′ + inc⋆ a⋆) + inc⋆ a†⋆)
          S = Proc↱ (cong₂ _+_ bib nib) (target⋆ E′⋆)
          E†⋆ : Proc↱ bib (target⋆ E⋆) —[ a†⋆ ]→⋆ S
          E†⋆ = ≅-subst✴₃ Proc _—[_]→⋆_ bib (≅-sym (Proc↲ bib (target⋆ E⋆))) (≅-sym (Action⋆↲ bib a′⋆))
                          (≅-sym (Proc↲ (cong₂ _+_ bib nib) (target⋆ E′⋆))) E′⋆
          _Δ_ {R′ = R′} γ/E⋆/E′⋆ E′⋆/γ/E⋆ = ⊖⋆[ ӓ , Γ′ + inc⋆ (action⋆ E⋆) ] E†⋆ γ/E⋆
          dib : ((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆ ≅
                Action⋆↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆)
          dib = ≅-sym (Action⋆↲ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆))
          gib : source⋆ (E⋆/γ) —[ ((braid ӓ ᴿ+ Γ′) *) (a⋆ ⍮ a′⋆) ]→⋆
                Proc↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ (a⋆ ⍮ a′⋆))
                      (Proc↱ (cong₂ _+_ refl (trans (cong₂ _+_ refl (sym nib)) (+-assoc Γ′ (inc⋆ a⋆) (inc⋆ a′⋆)))) R′)
          gib = {! !}
          fub : inc⋆ (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆) ≡
                inc⋆ (Action⋆↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆))
          fub = {!!}
          eab : Γ† + (Γ′ + inc⋆ a⋆) + inc⋆ (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆) ≡
                Γ† + Γ′ + inc⋆ (((braid ӓ ᴿ+ Γ′) *) a⋆) +
                inc⋆ (Action⋆↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆))
          eab =
             let open EqReasoning (setoid _) in
             begin
                Γ† + (Γ′ + inc⋆ a⋆) + inc⋆ (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆)
             ≡⟨ {!!} ⟩
                Γ† + Γ′ + inc⋆ (((braid ӓ ᴿ+ Γ′) *) a⋆) + inc⋆ (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆)
             ≡⟨ cong₂ _+_ refl fub ⟩
                Γ† + Γ′ + inc⋆ (((braid ӓ ᴿ+ Γ′) *) a⋆) +
                inc⋆ (Action⋆↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) (((braid ӓ ᴿ+ (Γ′ + inc⋆ a⋆)) *) a†⋆))
             ∎
          cib : source⋆ (E⋆/γ) —[ ((braid ӓ ᴿ+ Γ′) *) a⋆ ⍮ Action⋆↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) a†⋆ ]→⋆ {!
                !}
          cib = {!!}
-- _⍮_ {a′⋆ = Action⋆↱ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) (action⋆ E′⋆/γ/E⋆)}
--                    {S = Proc↱ eab (target⋆ E′⋆/γ/E⋆)} E⋆/γ
--                    (≅-subst✴₃ Proc _—[_]→⋆_ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆)
--                               (≅-sym (Proc↲ (ren-preserves-inc⋆-assoc (braid ӓ) Γ′ a⋆) _)) dib {!!} E′⋆/γ/E⋆)
          fib : Γ′ + inc⋆ a⋆ + inc⋆ a†⋆ ≡ Γ′ + (inc⋆ a⋆ + inc⋆ a′⋆)
          fib = trans (cong₂ _+_ refl (sym nib)) (+-assoc Γ′ (inc⋆ a⋆) (inc⋆ a′⋆))
          jib : R′ ≅ Proc↱ (cong₂ _+_ refl (trans (cong₂ _+_ refl (sym nib)) (+-assoc Γ′ (inc⋆ a⋆) (inc⋆ a′⋆)))) R′
          jib = ≅-sym (Proc↲ (cong₂ _+_ refl (trans (cong₂ _+_ refl (sym nib)) (+-assoc Γ′ (inc⋆ a⋆) (inc⋆ a′⋆)))) R′)
          twib : Proc↱ (+-assoc Γ† (Γ′ + inc⋆ a⋆) (inc⋆ a†⋆)) (Proc↱ (cong₂ _+_ bib nib) (target⋆ E′⋆)) ≅
                 Proc↱ (+-assoc Γ† Γ′ (inc⋆ a⋆ + inc⋆ a′⋆)) (Proc↱ (+-assoc (Γ† + Γ′) (inc⋆ a⋆) (inc⋆ a′⋆)) (target⋆ E′⋆))
          twib = let open ≅-Reasoning in
             begin
                Proc↱ (+-assoc Γ† (Γ′ + inc⋆ a⋆) (inc⋆ a†⋆)) (Proc↱ (cong₂ _+_ bib nib) (target⋆ E′⋆))
             ≅⟨ Proc↲ (+-assoc Γ† (Γ′ + inc⋆ a⋆) (inc⋆ a†⋆)) _ ⟩
                Proc↱ (cong₂ _+_ bib nib) (target⋆ E′⋆)
             ≅⟨ Proc↲ (cong₂ _+_ bib nib) _ ⟩
                target⋆ E′⋆
             ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ† + Γ′) (inc⋆ a⋆) (inc⋆ a′⋆)) _) ⟩
                Proc↱ (+-assoc (Γ† + Γ′) (inc⋆ a⋆) (inc⋆ a′⋆)) (target⋆ E′⋆)
             ≅⟨ ≅-sym (Proc↲ (+-assoc Γ† Γ′ (inc⋆ a⋆ + inc⋆ a′⋆)) _) ⟩
                Proc↱ (+-assoc Γ† Γ′ (inc⋆ a⋆ + inc⋆ a′⋆)) (Proc↱ (+-assoc (Γ† + Γ′) (inc⋆ a⋆) (inc⋆ a′⋆)) (target⋆ E′⋆))
             ∎
          pib : Γ† + (Γ′ + inc⋆ a⋆ + inc⋆ a†⋆) ≡ Γ† + (Γ′ + (inc⋆ a⋆ + inc⋆ a′⋆))
          pib = {!!}
          zib : ⋈[ Γ , ӓ , Γ′ + (inc⋆ a⋆ + inc⋆ a′⋆) ]
                (Proc↱ (+-assoc _ Γ′ (inc⋆ a⋆ + inc⋆ a′⋆)) (Proc↱ (+-assoc _ (inc⋆ a⋆) (inc⋆ a′⋆)) (target⋆ E′⋆)))
                (Proc↱ (cong₂ _+_ refl fib) R′)
          zib = {!!}
      in zib Δ gib
