module Transition.Concur2 where

   open import SharedModules hiding ([_])

   open import Ext

   open import Action as ᴬ
      using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc; _ᴬ⌣_; ᴬ⌣-sym; ᴬ⌣-sym-involutive);
      open ᴬ.Actionᵇ; open ᴬ.Actionᶜ; open ᴬ._ᴬ⌣_
   open import Action.Ren using (_*†)
   open import Name as ᴺ using (Name; Cxt; module Cxt; zero; _+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; ᴺren; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Second component here abstracts over the two action constructors.
   ᴬΔ : ∀ {Γ} {a a′ : Action Γ} → a ᴬ⌣ a′ → Σ[ A ∈ Set ] (A → Action (Γ + inc a))
   ᴬΔ {Γ} ᵛ∇ᵛ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᵇ∇ᵇ = Actionᵇ (Γ + 1) , _ᵇ
   ᴬΔ {Γ} ᵇ∇ᶜ = Actionᶜ (Γ + 1) , _ᶜ
   ᴬΔ {Γ} ᶜ∇ᵇ = Actionᵇ Γ , _ᵇ
   ᴬΔ {Γ} ᶜ∇ᶜ = Actionᶜ Γ , _ᶜ

   -- The residual a′/a. Note that ᵇ∇ᵇ may also relate two bound outputs, but only if they represent
   -- extrusions of distinct binders.
   ᴬ/ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → π₁ (ᴬΔ a⌣a′)
   ᴬ/ (ᵛ∇ᵛ {u = u}) = • ᴺ.suc u 〈 zero 〉
   ᴬ/ (ᵇ∇ᵇ {a′ = a′}) = (push *) a′
   ᴬ/ (ᵇ∇ᶜ {a′ = a′}) = (push *) a′
   ᴬ/ (ᶜ∇ᵇ {a′ = a′}) = a′
   ᴬ/ (ᶜ∇ᶜ {a′ = a′}) = a′

   -- Symmetrise.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Action (Γ + inc a) × Action (Γ + inc a′)
   ᴬ⊖ a⌣a′ = π₂ (ᴬΔ a⌣a′) (ᴬ/ a⌣a′) , π₂ (ᴬΔ (ᴬ⌣-sym a⌣a′)) (ᴬ/ (ᴬ⌣-sym a⌣a′))

   -- Cofinality of action residuals amounts to agreement on target context.
   ᴬ⊖-✓ : ∀ {Γ} {a a′ : Action Γ} (a⌣a′ : a ᴬ⌣ a′) → Γ + inc a + inc (π₁ (ᴬ⊖ a⌣a′)) ≡ Γ + inc a′ + inc (π₂ (ᴬ⊖ a⌣a′))
   ᴬ⊖-✓ ᵛ∇ᵛ = refl
   ᴬ⊖-✓ ᵇ∇ᵇ = refl
   ᴬ⊖-✓ ᵇ∇ᶜ = refl
   ᴬ⊖-✓ ᶜ∇ᵇ = refl
   ᴬ⊖-✓ ᶜ∇ᶜ = refl

   -- Whether two coinitial evaluation contexts are concurrent. Only give the left rules, then symmetrise.
   -- Convenient to have this indexed by the kind of action residual. TODO: cases for •│ and ᵥ│.
   syntax Concur₁ E E′ a′/a = E ⌣₁[ a′/a ] E′
   infix 4 Concur₁

   data Concur₁ {Γ} : ∀ {a : Action Γ} {a′ : Action Γ} {P R R′} →
                P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → a ᴬ⌣ a′ → Set where
      _ᵇ│ᵇ_ : ∀ {P Q R S} {a a′ : Actionᵇ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᵇ ] P │ᵇ F
      _ᵇ│ᶜ_ : ∀ {P Q R S} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F
      _ᶜ│ᵇ_ : ∀ {P Q R S} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᵇ ] P │ᵇ F
      _ᶜ│ᶜ_ : ∀ {P Q R S} {a a′ : Actionᶜ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F
      _│•ᵇ_ : ∀ {x y P R R′ S Q} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ ᵇ∇ᵇ ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ │• F
      _│•ᶜ_ : ∀ {x y P R R′ S Q} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᵇ ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ │• F
      _ᵇ│•_ : ∀ {x y P Q R S S′} {a : Actionᵇ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │• F′
      _ᶜ│•_ : ∀ {x y P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │• F′
      _│ᵥᵇ_ : ∀ {x P R R′ S Q} {a : Actionᵇ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ │ᵥ F
      _│ᵥᶜ_ : ∀ {x P R R′ S Q} {a : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᵇ ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F
      _ᵇ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᵇ Γ} {a⌣a′} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ a⌣a′ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] E │ᵥ F′
      _ᶜ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ ᶜ∇ᵇ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] E │ᵥ F′
      _➕₁_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a⌣a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
             E ⌣₁[ a⌣a′ ] E′ → (Q : Proc Γ) → E ➕₁ Q ⌣₁[ a⌣a′ ] E′ ➕₁ Q
      _│ᵇᵇ_ : ∀ {Q S S′} {a a′ : Actionᵇ Γ} {a⌣a′} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᵇ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ a⌣a′ ] F′ → P │ᵇ F ⌣₁[ a⌣a′ ] P │ᵇ F′
      _│ᵇᶜ_ : ∀ {Q S S′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᵇ∇ᶜ ] F′ → P │ᵇ F ⌣₁[ ᵇ∇ᶜ ] P │ᶜ F′
      _│ᶜᶜ_ : ∀ {Q S S′} {a a′ : Actionᶜ Γ} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ ᶜ∇ᶜ ] F′ → P │ᶜ F ⌣₁[ ᶜ∇ᶜ ] P │ᶜ F′
      _ᵇᵇ│_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {a⌣a′} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′} →
              E ⌣₁[ a⌣a′ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ a⌣a′ ] E′ ᵇ│ Q
      _ᵇᶜ│_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᵇ∇ᶜ ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ ᵇ∇ᶜ ] E′ ᶜ│ Q
      _ᶜᶜ│_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ ᶜ∇ᶜ ] E′ → (Q : Proc Γ) → E ᶜ│ Q ⌣₁[ ᶜ∇ᶜ ] E′ ᶜ│ Q
      _│•_ : ∀ {x y u z P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ • u 〈 z 〉 ᶜ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ᶜ∇ᶜ ] F′ → E │• F ⌣₁[ ᶜ∇ᶜ ] E′ │• F′
      _│•ᵥ_ : ∀ {x u y P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ ᶜ∇ᵇ ] F′ → E │• F ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F′
      _│ᵥ_ : ∀ {x u P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {•x⌣•u} {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁[ ᵇ∇ᵇ ] E′ → F ⌣₁[ •x⌣•u ] F′ → E │ᵥ F ⌣₁[ ᶜ∇ᶜ ] E′ │ᵥ F′
      ν•_ : ∀ {x u P R R′} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ • ᴺ.suc u 〈 zero 〉 ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵛ∇ᵛ ] ν• E′
      ν•ᵇ_ : ∀ {x P R R′} {a : Actionᵇ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᵇ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᵇ ] E′ → ν• E ⌣₁[ ᵇ∇ᵇ ] νᵇ E′
      ν•ᶜ_ : ∀ {x P R R′} {a : Actionᶜ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᶜ - _ ]→ R′} →
            E ⌣₁[ ᶜ∇ᶜ ] E′ → ν• E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᵇᵇ_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {a⌣a′} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᵇ - _ ]→ R′} →
          E ⌣₁[ (push *†) a⌣a′ ] E′ → νᵇ E ⌣₁[ a⌣a′ ] νᵇ E′
      νᵇᶜ_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣₁[ ᵇ∇ᶜ ] E′ → νᵇ E ⌣₁[ ᵇ∇ᶜ ] νᶜ E′
      νᶜᶜ_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ (push *) a ᶜ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣₁[ ᶜ∇ᶜ ] E′ → νᶜ E ⌣₁[ ᶜ∇ᶜ ] νᶜ E′
      !_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a⌣a′} {R R′} {E : P │ ! P —[ a - _ ]→ R} {E′ : P │ ! P —[ a′ - _ ]→ R′} →
           E ⌣₁[ a⌣a′ ] E′ → ! E ⌣₁[ a⌣a′ ] ! E′

   syntax Concur E E′ a⌣a′ = E ⌣[ a⌣a′ ] E′

   Concur : ∀ {Γ} {a a′ : Action Γ} {P R R′}
            (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → a ᴬ⌣ a′ → Set
   Concur E E′ a⌣a′ = E ⌣₁[ a⌣a′ ] E′ ⊎ E′ ⌣₁[ ᴬ⌣-sym a⌣a′ ] E

   ⌣-sym : ∀ {Γ} {P : Proc Γ} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} →
           Sym (λ (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → E ⌣[ a⌣a′ ] E′) (λ E E′ → E ⌣[ ᴬ⌣-sym a⌣a′ ] E′)
   ⌣-sym (inj₁ E⌣E′) = inj₂ (subst (Concur₁ _ _) (sym (ᴬ⌣-sym-involutive _)) E⌣E′)
   ⌣-sym (inj₂ E⌣E′) = inj₁ E⌣E′

   -- The type of the symmetric residual of concurrent transitions E and E′. Because cofinality of action
   -- residuals isn't baked in, need to coerce targets of E/E′ and E′/E to the same type.
   infixl 5 _∶_Δ_
   record _Δ_ {Γ P} {a a′ : Action Γ} {R R′} (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) : Set where
      constructor _∶_Δ_
      field
         a⌣a′ : a ᴬ⌣ a′
      a′/a = π₁ (ᴬ⊖ a⌣a′)
      a/a′ = π₂ (ᴬ⊖ a⌣a′)
      Γ′ = Γ + inc a + inc a′/a
      field
         {P₁ P₂} : Proc Γ′
         E′/E : R —[ a′/a - _ ]→ P₁
         E/E′ : R′ —[ a/a′ - _ ]→ subst Proc (ᴬ⊖-✓ a⌣a′) P₂

   open import Ren.Properties

   -- The symmetric residual  (E′/E , E/E′). The paper defines the residual using E and E′, with E ⌣ E′
   -- implicit, whereas we work directly with the proof of E ⌣ E′, with E and E′ implicit.
   ⊖₁ : ∀ {Γ P} {a a′ : Action Γ} {a⌣a′ : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
        E ⌣₁[ a⌣a′ ] E′ → E Δ E′
   ⊖₁ (E ᵇ│ᵇ F) = ᵇ∇ᵇ ∶ target E │ᵇ (push *ᵇ) F Δ (push *ᵇ) E ᵇ│ target F
   ⊖₁ (E ᵇ│ᶜ F) = ᵇ∇ᶜ ∶ target E │ᶜ (push *ᶜ) F Δ E ᵇ│ target F
   ⊖₁ (E ᶜ│ᵇ F) = ᶜ∇ᵇ ∶ target E │ᵇ F Δ (push *ᶜ) E ᶜ│ target F
   ⊖₁ (E ᶜ│ᶜ F) = ᶜ∇ᶜ ∶ target E │ᶜ F Δ E ᶜ│ target F
   ⊖₁ (_│•ᵇ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ with (pop y *ᵇ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a = ᵇ∇ᶜ ∶ (E′/E │• (push *ᶜ) F) Δ (pop-y*E/E′ ᵇ│ target F)
   ⊖₁ (_│•ᶜ_ {y = y} {a = a} E⌣E′ F) with ⊖₁ E⌣E′
   ... | ᶜ∇ᵇ ∶ E′/E Δ E/E′ with (pop y *ᶜ) E/E′
   ... | pop-y*E/E′ rewrite pop∘push y a = ᶜ∇ᶜ ∶ E′/E │• F Δ pop-y*E/E′ ᶜ│ target F
   ⊖₁ (_ᵇ│•_ {y = y} E F⌣F′) with ⊖₁ F⌣F′
   ... | ᵇ∇ᶜ ∶ F′/F Δ F/F′ = ᵇ∇ᶜ ∶ (push *ᵇ) E ᵀ.│• F′/F Δ (pop y *) (target E) │ᵇ F/F′
   ⊖₁ (_ᶜ│•_ {y = y} E F⌣F′) with ⊖₁ F⌣F′
   ... | ᶜ∇ᶜ ∶ F′/F Δ F/F′ = ᶜ∇ᶜ ∶ E │• F′/F Δ (pop y *) (target E) │ᶜ F/F′
   ⊖₁ (E⌣E′ │ᵥᵇ F) with ⊖₁ E⌣E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ = ᵇ∇ᶜ ∶ E′/E │ᵥ (push *ᵇ) F Δ νᵇ (E/E′ ᵇ│ target F)
   ⊖₁ (E⌣E′ │ᵥᶜ F) with ⊖₁ E⌣E′
   ... | ᶜ∇ᵇ ∶ E′/E Δ E/E′ = ᶜ∇ᶜ ∶ E′/E │ᵥ F Δ νᶜ (E/E′ ᶜ│ target F)
   ⊖₁ (_ᵇ│ᵥ_ {x} E F⌣F′) with ⊖₁ F⌣F′
   ... | ᵛ∇ᵛ ∶ F′/F Δ F/F′ with (push *ᵇ) E
   ... | push*E = ᵇ∇ᶜ ∶ push*E │• F′/F Δ ν• (target E │ᶜ F/F′)
   ⊖₁ (E ᵇ│ᵥ F⌣F′) | ᵇ∇ᵇ ∶ F′/F Δ F/F′ = ᵇ∇ᶜ ∶ (push *ᵇ) E │ᵥ F′/F Δ νᵇ (target E │ᵇ F/F′)
   ⊖₁ (E ᶜ│ᵥ F⌣F′) with ⊖₁ F⌣F′
   ... | ᶜ∇ᵇ ∶ F′/F Δ F/F′ = ᶜ∇ᶜ ∶ E │ᵥ F′/F Δ νᶜ (target E │ᶜ F/F′)
   ⊖₁ (P │ᵇᵇ F⌣F′) with ⊖₁ F⌣F′
   ... | ᵛ∇ᵛ ∶ F′/F Δ F/F′ = ᵛ∇ᵛ ∶ (push *) P │ᶜ F′/F Δ (push *) P │ᶜ F/F′
   ... | ᵇ∇ᵇ ∶ F′/F Δ F/F′ = ᵇ∇ᵇ ∶ (push *) P │ᵇ F′/F Δ (push *) P │ᵇ F/F′
   ⊖₁ (P │ᵇᶜ F⌣F′) with ⊖₁ F⌣F′
   ... | ᵇ∇ᶜ ∶ F′/F Δ F/F′ = ᵇ∇ᶜ ∶ (push *) P │ᶜ F′/F Δ P │ᵇ F/F′
   ⊖₁ (P │ᶜᶜ F⌣F′) with ⊖₁ F⌣F′
   ... | ᶜ∇ᶜ ∶ F′/F Δ F/F′ = ᶜ∇ᶜ ∶ P │ᶜ F′/F Δ P │ᶜ F/F′
   ⊖₁ (E⌣E′ ᵇᵇ│ Q) with ⊖₁ E⌣E′
   ... | ᵛ∇ᵛ ∶ E′/E Δ E/E′ = ᵛ∇ᵛ ∶ E′/E ᶜ│ (push *) Q Δ E/E′ ᶜ│ (push *) Q
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ = ᵇ∇ᵇ ∶ E′/E ᵇ│ (push *) Q Δ E/E′ ᵇ│ (push *) Q
   ⊖₁ (E⌣E′ ᵇᶜ│ Q) with ⊖₁ E⌣E′
   ... | ᵇ∇ᶜ ∶ E′/E Δ E/E′ = ᵇ∇ᶜ ∶ E′/E ᶜ│ (push *) Q Δ E/E′ ᵇ│ Q
   ⊖₁ (E⌣E′ ᶜᶜ│ Q) with ⊖₁ E⌣E′
   ... | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = ᶜ∇ᶜ ∶ E′/E ᶜ│ Q Δ E/E′ ᶜ│ Q
   ⊖₁ (E⌣E′ ➕₁ F) with ⊖₁ E⌣E′
   ... | ᵛ∇ᵛ ∶ E′/E Δ E/E′ = ᵛ∇ᵛ ∶ E′/E Δ E/E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ = ᵇ∇ᵇ ∶ E′/E Δ E/E′
   ... | ᵇ∇ᶜ ∶ E′/E Δ E/E′ = ᵇ∇ᶜ ∶ E′/E Δ E/E′
   ... | ᶜ∇ᵇ ∶ E′/E Δ E/E′ = ᶜ∇ᵇ ∶ E′/E Δ E/E′
   ... | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = ᶜ∇ᶜ ∶ E′/E Δ E/E′
   ⊖₁ (_│•_ {x = x} {y} {u} {z} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | ᶜ∇ᶜ ∶ F′/F Δ F/F′ with (pop y *ᵇ) E′/E | (pop z *ᵇ) E/E′
   ... | pop-y*E′/E | pop-z*E/E′ rewrite pop∘push u y | pop∘push x z = ᶜ∇ᶜ ∶ pop-y*E′/E │• F′/F Δ pop-z*E/E′ │• F/F′
   ⊖₁ (_│•ᵥ_ {u = u} {y} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | ᶜ∇ᵇ ∶ F′/F Δ F/F′ with (pop y *ᵇ) E′/E
   ... | pop-y*E′/E rewrite pop∘push u y = ᶜ∇ᶜ ∶ pop-y*E′/E │ᵥ F′/F Δ νᶜ (E/E′ │• F/F′)
   ⊖₁ (_│ᵥ_ {x = x} {u} E⌣E′ F⌣F′) with ⊖₁ E⌣E′ | ⊖₁ F⌣F′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | ᵛ∇ᵛ ∶ F′/F Δ F/F′ =
      ᶜ∇ᶜ ∶ νᶜ (E′/E │• F′/F) Δ νᶜ (E/E′ │• F/F′)
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ | ᵇ∇ᵇ ∶ F′/F Δ F/F′ = ᶜ∇ᶜ ∶ νᶜ (E′/E │ᵥ F′/F) Δ νᶜ (E/E′ │ᵥ F/F′)
   ⊖₁ (ν• E⌣E′) with ⊖₁ E⌣E′
   ... | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = ᵛ∇ᵛ ∶ E′/E Δ E/E′
   ⊖₁ (ν•ᵇ_ {x = x} {a = a} E⌣E′) with ⊖₁ E⌣E′
   ... | ᶜ∇ᵇ ∶ E′/E Δ E/E′ with (swap *ᶜ) E/E′
   ... | swap*E/E′ = ᵇ∇ᵇ ∶ E′/E Δ ν• swap*E/E′
   ⊖₁ (ν•ᶜ E⌣E′) with ⊖₁ E⌣E′
   ... | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = ᵇ∇ᶜ ∶ E′/E Δ ν• E/E′
   ⊖₁ (νᵇᵇ_ {a = x •} {a} E⌣E′) with ⊖₁ E⌣E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a = ᵇ∇ᵇ ∶ νᵇ swap*E′/E Δ νᵇ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {u •} E⌣E′) with ⊖₁ E⌣E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u = ᵇ∇ᵇ ∶ νᵇ swap*E′/E Δ νᵇ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {• u} E⌣E′) with ⊖₁ E⌣E′
   ... | ᵛ∇ᵛ ∶ E′/E Δ E/E′ with (swap *ᶜ) E/E′ | (swap *ᶜ) E′/E
   ... | swap*E/E′ | swap*E′/E {-rewrite ∘-*₁ x ᴿ.suc-push∘push | ∘-*₁ u ᴿ.suc-push∘push-} =
      ᵛ∇ᵛ ∶ νᶜ swap*E′/E Δ νᶜ swap*E/E′
   ⊖₁ (νᵇᵇ_ {a = • x} {• u} E⌣E′) | ᵇ∇ᵇ ∶ E′/E Δ E/E′ with (swap *ᵇ) E/E′ | (swap *ᵇ) E′/E
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push u =
      ᵇ∇ᵇ ∶ νᵇ swap*E′/E Δ νᵇ swap*E/E′
   ⊖₁ (νᵇᶜ_ {a′ = a′} E⌣E′) with ⊖₁ E⌣E′
   ... | ᵇ∇ᶜ ∶ E′/E Δ E/E′ with (swap *ᶜ) E′/E
   ... | swap*E′/E rewrite swap∘push∘push a′ = ᵇ∇ᶜ ∶ νᶜ swap*E′/E Δ νᵇ E/E′
   ⊖₁ (νᶜᶜ E⌣E′) with ⊖₁ E⌣E′
   ... | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = ᶜ∇ᶜ ∶ νᶜ E′/E Δ νᶜ E/E′
   ⊖₁ (! E⌣E′) with ⊖₁ E⌣E′
   ... | ᵛ∇ᵛ ∶ E′/E Δ E/E′ = ᵛ∇ᵛ ∶ E′/E Δ E/E′
   ... | ᵇ∇ᵇ ∶ E′/E Δ E/E′ = ᵇ∇ᵇ ∶ E′/E Δ E/E′
   ... | ᵇ∇ᶜ ∶ E′/E Δ E/E′ = ᵇ∇ᶜ ∶ E′/E Δ E/E′
   ... | ᶜ∇ᵇ ∶ E′/E Δ E/E′ = ᶜ∇ᵇ ∶ E′/E Δ E/E′
   ... | ᶜ∇ᶜ ∶ E′/E Δ E/E′ = ᶜ∇ᶜ ∶ E′/E Δ E/E′
