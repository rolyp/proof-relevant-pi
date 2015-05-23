module Transition.Concur2 where

   open import SharedModules hiding ([_])

   open import Ext

   open import Action as ᴬ using (Action; Actionᵇ; Actionᶜ; _ᵇ; _ᶜ; inc); open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   import Action.Ren
   open import Name as ᴺ using (Name; Cxt; module Cxt; zero; _+_; toℕ)
   open import Ren as ᴿ using (Ren; Renameable; ᴺren; suc; push; pop; swap); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Proc as ᴾ using (Proc); open ᴾ.Proc
   import Proc.Ren
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   _ᴬΔ_ : ∀ {Γ} (a a′ : Action Γ) → Set
   _ᴬΔ_ {Γ} a a′ = Action (Γ + inc a) × Action (Γ + inc a′)

   -- The 5 kinds of coinitial action residual. The ᵛ∇ᵛ case is what really makes this necessary.
   data coinitial {Γ} : (a a′ : Action Γ) → Set where
      ᵛ∇ᵛ : (x u : Name Γ) → coinitial ((• x) ᵇ) ((• u) ᵇ)
      ᵇ∇ᵇ : (a a′ : Actionᵇ Γ) → coinitial (a ᵇ) (a′ ᵇ)
      ᵇ∇ᶜ : (a : Actionᵇ Γ) (a′ : Actionᶜ Γ) → coinitial (a ᵇ) (a′ ᶜ)
      ᶜ∇ᵇ : (a : Actionᶜ Γ) (a′ : Actionᵇ Γ) → coinitial (a ᶜ) (a′ ᵇ)
      ᶜ∇ᶜ : (a a′ : Actionᶜ Γ) → coinitial (a ᶜ) (a′ ᶜ)

   -- The symmetric residual (a′/a, a/a′). Note that ᵇ∇ᵇ may also relate two bound outputs, but only if
   -- they represent extrusions of distinct binders.
   ᴬ⊖ : ∀ {Γ} {a a′ : Action Γ} → coinitial a a′ → a ᴬΔ a′
   ᴬ⊖ (ᵛ∇ᵛ x u) = • ᴺ.suc u 〈 zero 〉 ᶜ , • ᴺ.suc x 〈 zero 〉 ᶜ
   ᴬ⊖ (ᵇ∇ᵇ a a′) = (push *) a′ ᵇ , (push *) a ᵇ
   ᴬ⊖ (ᵇ∇ᶜ a a′) = (push *) a′ ᶜ , a ᵇ
   ᴬ⊖ (ᶜ∇ᵇ a a′) = a′ ᵇ , (push *) a ᶜ
   ᴬ⊖ (ᶜ∇ᶜ a a′) = a′ ᶜ , a ᶜ

   -- Action residuation is symmetric, so could have just defined this.
   ᴬ/ : ∀ {Γ} {a a′ : Action Γ} → coinitial a a′ → Action (Γ + inc a)
   ᴬ/ a⌣a′ = π₁ (ᴬ⊖ a⌣a′)

   -- Whether two coinitial evaluation contexts are concurrent. Only give the left rules, then symmetrise.
   -- Convenient to have this indexed by the residual actions. TODO: cases for •│ and ᵥ│.
   syntax Concur₁ E E′ a′/a = E ⌣₁[ a′/a ] E′
   infix 4 Concur₁

   data Concur₁ {Γ} : ∀ {a : Action Γ} {a′ : Action Γ} {P R R′} →
                P —[ a - _ ]→ R → P —[ a′ - _ ]→ R′ → Action (Γ + inc a) → Set where
      _ᵇ│ᵇ_ : ∀ {P Q R S} {a a′ : Actionᵇ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᴬ/ (ᵇ∇ᵇ a a′) ] P │ᵇ F
      _ᵇ│ᶜ_ : ∀ {P Q R S} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ}
             (E : P —[ a ᵇ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ ᴬ/ (ᵇ∇ᶜ a a′) ] P │ᶜ F
      _ᶜ│ᵇ_ : ∀ {P Q R S} {a : Actionᶜ Γ} {a′ : Actionᵇ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᴬ/ (ᶜ∇ᵇ a a′) ] P │ᵇ F
      _ᶜ│ᶜ_ : ∀ {P Q R S} {a a′ : Actionᶜ Γ}  →
             (E : P —[ a ᶜ - _ ]→ R) (F : Q —[ a′ ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ ᴬ/ (ᶜ∇ᶜ a a′) ] P │ᶜ F
      _│•ᵇ_ : ∀ {x y P R R′ S Q} {a : Actionᵇ Γ} {a′/a} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ a′/a ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᵇ│ Q ⌣₁[ a′/a ] E′ │• F
      _│•ᶜ_ : ∀ {x y P R R′ S Q} {a : Actionᶜ Γ} {a′/a} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ a′/a ] E′ → (F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S) → E ᶜ│ Q ⌣₁[ a′/a ] E′ │• F
      _ᵇ│•_ : ∀ {x y P Q R S S′} {a : Actionᵇ Γ} {a′/a} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ a′/a ] F′ → P │ᵇ F ⌣₁[ a′/a ] E │• F′
      _ᶜ│•_ : ∀ {x y P Q R S S′} {a : Actionᶜ Γ} {a′/a} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S′}
              (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ a′/a ] F′ → P │ᶜ F ⌣₁[ a′/a ] E │• F′
      _│ᵥᵇ_ : ∀ {x P R R′ S Q} {a : Actionᵇ Γ} {a′/a} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
             E ⌣₁[ a′/a ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᵇ│ Q ⌣₁[ a′/a ] E′ │ᵥ F
      _│ᵥᶜ_ : ∀ {x P R R′ S Q} {a : Actionᶜ Γ} {a′/a} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ x • ᵇ - _ ]→ R′} →
              E ⌣₁[ a′/a ] E′ → (F : Q —[ (• x) ᵇ - _ ]→ S) → E ᶜ│ Q ⌣₁[ a′/a ] E′ │ᵥ F
      _ᵇ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᵇ Γ} {a′/a} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ a′/a ] F′ → P │ᵇ F ⌣₁[ a′/a ] E │ᵥ F′
      _ᶜ│ᵥ_ : ∀ {x P Q R S S′} {a : Actionᶜ Γ} {a′/a} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ (• x) ᵇ - _ ]→ S′} →
             (E : P —[ x • ᵇ - _ ]→ R) → F ⌣₁[ a′/a ] F′ → P │ᶜ F ⌣₁[ a′/a ] E │ᵥ F′
      _➕₁_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {a′/a} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′} →
             E ⌣₁[ a′/a ] E′ → (Q : Proc Γ) → E ➕₁ Q ⌣₁[ a′/a ] E′ ➕₁ Q
      _│ᵇᵇ_ : ∀ {Q S S′} {a a′ : Actionᵇ Γ} {a′/a} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᵇ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ a′/a ] F′ → P │ᵇ F ⌣₁[ a′/a ] P │ᵇ F′
      _│ᵇᶜ_ : ∀ {Q S S′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {a′/a} {F : Q —[ a ᵇ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ a′/a ] F′ → P │ᵇ F ⌣₁[ a′/a ] P │ᶜ F′
      _│ᶜᶜ_ : ∀ {Q S S′} {a a′ : Actionᶜ Γ} {a′/a} {F : Q —[ a ᶜ - _ ]→ S} {F′ : Q —[ a′ ᶜ - _ ]→ S′} →
             (P : Proc Γ) → F ⌣₁[ a′/a ] F′ → P │ᶜ F ⌣₁[ a′/a ] P │ᶜ F′
      _ᵇᵇ│_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {a′/a} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᵇ - _ ]→ R′} →
              E ⌣₁[ a′/a ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ a′/a ] E′ ᵇ│ Q
      _ᵇᶜ│_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {a′/a} {E : P —[ a ᵇ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ a′/a ] E′ → (Q : Proc Γ) → E ᵇ│ Q ⌣₁[ a′/a ] E′ ᶜ│ Q
      _ᶜᶜ│_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {a′/a} {E : P —[ a ᶜ - _ ]→ R} {E′ : P —[ a′ ᶜ - _ ]→ R′} →
              E ⌣₁[ a′/a ] E′ → (Q : Proc Γ) → E ᶜ│ Q ⌣₁[ a′/a ] E′ ᶜ│ Q
{-
      _│•_ : ∀ {x y u z P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ • u 〈 z 〉 ᶜ - _ ]→ S′} →
             E ⌣₁ E′ → F ⌣₁ F′ → E │• F ⌣₁ E′ │• F′
      _│•ᵥ_ : ∀ {x u y P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ • x 〈 y 〉 ᶜ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁ E′ → F ⌣₁ F′ → E │• F ⌣₁ E′ │ᵥ F′
      _│ᵥ_ : ∀ {x u P Q R R′ S S′} {E : P —[ x • ᵇ - _ ]→ R} {E′ : P —[ u • ᵇ - _ ]→ R′}
             {F : Q —[ (• x) ᵇ - _ ]→ S} {F′ : Q —[ (• u) ᵇ - _ ]→ S′} →
             E ⌣₁ E′ → F ⌣₁ F′ → E │ᵥ F ⌣₁ E′ │ᵥ F′
      ν•_ : ∀ {x u P R R′} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ • ᴺ.suc u 〈 zero 〉 ᶜ - _ ]→ R′} →
            E ⌣₁ E′ → ν• E ⌣₁ ν• E′
      ν•ᵇ_ : ∀ {x P R R′} {a : Actionᵇ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᵇ - _ ]→ R′} →
            E ⌣₁ E′ → ν• E ⌣₁ νᵇ_ {a = a} E′
      ν•ᶜ_ : ∀ {x P R R′} {a : Actionᶜ Γ} {E : P —[ • ᴺ.suc x 〈 zero 〉 ᶜ - _ ]→ R} {E′ : P —[ (push *) a ᶜ - _ ]→ R′} →
            E ⌣₁ E′ → ν• E ⌣₁ νᶜ_ {a = a} E′
      νᵇᵇ_ : ∀ {P R R′} {a a′ : Actionᵇ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᵇ - _ ]→ R′} →
          E ⌣₁ E′ → νᵇ_ {a = a} E ⌣₁ νᵇ_ {a = a′} E′
      νᵇᶜ_ : ∀ {P R R′} {a : Actionᵇ Γ} {a′ : Actionᶜ Γ} {E : P —[ (push *) a ᵇ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣₁ E′ → νᵇ_ {a = a} E ⌣₁ νᶜ_ {a = a′} E′
      νᶜᶜ_ : ∀ {P R R′} {a a′ : Actionᶜ Γ} {E : P —[ (push *) a ᶜ - _ ]→ R} {E′ : P —[ (push *) a′ ᶜ - _ ]→ R′} →
          E ⌣₁ E′ → νᶜ_ {a = a} E ⌣₁ νᶜ_ {a = a′} E′
      !_ : ∀ {P} {a : Action Γ} {a′ : Action Γ} {R R′} {E : P │ ! P —[ a - _ ]→ R} {E′ : P │ ! P —[ a′ - _ ]→ R′} →
           E ⌣₁ E′ → ! E ⌣₁ ! E′
-}
   syntax Concur E E′ a′/a = E ⌣[ a′/a ] E′

   Concur : ∀ {Γ} {a : Action Γ} {a′ : Action Γ} {P R R′} (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) → a ᴬΔ a′ → Set
   Concur E E′ ( a′/a , a/a′ ) = E ⌣₁[ a′/a ] E′ ⊎ E′ ⌣₁[ a/a′ ] E
