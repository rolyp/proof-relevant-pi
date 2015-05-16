-- WIP: transition sequences and causal equivalence.
module Transition.Seq where

   open import SharedModules hiding (_⇒_; trans)
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; _ᵇ; _ᶜ; inc)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆; {-target⋆; -}[]; _∷_)
   open import Name as ᴺ using (Cxt; Name; _+_; +-assoc; zero; toℕ)
   open import Proc using (Proc)
   open import Ren as ᴿ using (Ren; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import StructuralCong.Proc using (_≅_; ≅-sym; ≅-refl)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_; target)
   open import Transition.Concur using (_⌣_; module _Δ_; ⊖; coinitial; ᴬ⊖; ᴬ⊖-✓)
   open import Transition.Ren using (_Δ_; _*′)

   braid : ∀ {Γ} (n : Name 3) → Ren (Γ + toℕ n) (Γ + toℕ n)
   braid zero = id
   braid (ᴺ.suc zero) = id
   braid (ᴺ.suc (ᴺ.suc zero)) = swap
   braid (ᴺ.suc (ᴺ.suc (ᴺ.suc ())))

   ⋈[_,_,_] : ∀ Γ (n : Name 3) (m : Cxt) → Proc (Γ + toℕ n + m) → Proc (Γ + toℕ n + m) → Set
   ⋈[_,_,_] Γ n m P₁ P₂ = ((braid n ᴿ+ m) *) P₁ ≅ P₂

   -- TODO: consolidate these a bit.
   target-+ : ∀ {Γ} (n : Name 3) m (a : Action (Γ + toℕ n + m)) → (Γ + toℕ n + m) + inc a ≡ Γ + toℕ n + (m + inc a)
   target-+ {Γ} n m a =
      let Γ′ = Γ + toℕ n in
      begin
         Γ′ + m + inc a
      ≡⟨ {!!} ⟩
         Γ′ + (m + inc a)
      ∎ where open EqReasoning (setoid _)

   bibble : ∀ {Γ} (n : Cxt) m m′ → ((Γ + n) + m) + m′ ≡ (Γ + n) + (m + m′)
   bibble {Γ} n m m′ = let blah = +-assoc (Γ + n) m m′ in {!!}

   target⋆-+ : ∀ {Γ} (n : Name 3) m (a⋆ : Action⋆ (Γ + toℕ n + m)) → (Γ + toℕ n + m) + inc⋆ a⋆ ≡ Γ + toℕ n + (m + inc⋆ a⋆)
   target⋆-+ = {!!}

   target-+′ : ∀ {Γ} m (n : Name 3) (a : Action (Γ + toℕ n + m)) →
              (Γ + toℕ n + m) + inc (((braid n ᴿ+ m) *) a) ≡ Γ + toℕ n + (m + inc a)
   target-+′ _ _ (_ ᵇ) = refl
   target-+′ _ _ (_ ᶜ) = refl

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ n m a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E : ⋈[ Γ , n , m + inc a ] (subst Proc (target-+ n m a) R) R′
         E/γ : P′ —[ ((braid n ᴿ+ m) *) a - ι ]→ subst Proc (sym (target-+′ m n a)) R′

   ⊖′[_,_] : ∀ {ι Γ} n m {a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
         (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ′_ {n = n} {m = m} E γ
   ⊖′[ n , m ] {(x ᴬ.•) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {(ᴬ.• x) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {ᴬ.• x 〈 y 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {ᴬ.τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ

   -- Traces are lists of composable transitions. Snoc lists would make more sense implementation-wise;
   -- composition is probably what we eventually want.
   infixr 5 _∷_
   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [] : P —[ [] ]→⋆ P
      _∷_ : ∀ {a R a⋆ S} (E : P —[ a - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) → P —[ a ∷ a⋆ ]→⋆
            let blah = +-assoc Γ (inc a) (inc⋆ a⋆) in subst Proc {!!} S

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ n m a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E⋆ : ⋈[ Γ , n , m + inc⋆ a⋆ ] (subst Proc (target⋆-+ n m a⋆) R) R′
--         E⋆/γ : P′ —[ ((braid n ᴿ+ m) *) a⋆ ]→⋆ subst Proc (sym (target-+′ m n a⋆)) R′

   ⊖⋆[_,_] : ∀ {Γ} n m {a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ⋆_ {n = n} {m = m} E⋆ γ
   ⊖⋆[ n , m ] [] γ = {!!}
   ⊖⋆[ n , m ] (E ∷ E⋆) γ = {!!}

   -- Causal equivalence. TODO: fix [_∶⇋∶_]∷_ rule; needs more general notion of cofinality.
   infix 4 _≃_
   infixr 9 _≃-∘_
   data _≃_ {Γ} {P : Proc Γ} : ∀ {a⋆ R a′⋆ R′} → P —[ a⋆ ]→⋆ R → P —[ a′⋆ ]→⋆ R′ → Set where
      --- Transposition rule.
      [_∶⇋∶_]∷_ : ∀ {a R a′ R′} (E : P —[ a - _ ]→ R) (E′ : P —[ a′ - _ ]→ R′) →
                  ⦃ E⌣E′ : E ⌣ E′ ⦄ → E ⌣ E′ → let open _Δ_ (⊖ E⌣E′); Q = target E′/E in
                  ∀ {a⋆ S a′⋆ S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                  E ∷ E′/E ∷ E⋆ ≃ E′ ∷ E/E′ ∷ []
      -- Close under trace constructors.
      [] : [] ≃ []
      _∷_ : ∀ {a R a⋆ S a′⋆ S′} (E : P —[ a - _ ]→ R) {E⋆ : R —[ a⋆ ]→⋆ S} {E′⋆ : R —[ a′⋆ ]→⋆ S′} →
            E⋆ ≃ E′⋆ → E ∷ E⋆ ≃ E ∷ E′⋆
      -- Transitivity and symmetry.
      _≃-∘_ : ∀ {a⋆ R a″⋆ S a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {F⋆ : P —[ a″⋆ ]→⋆ S} {E′⋆ : P —[ a′⋆ ]→⋆ R′} →
            F⋆ ≃ E′⋆ → E⋆ ≃ F⋆ → E⋆ ≃ E′⋆
      ≃-sym : ∀ {a⋆ R a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {E′⋆ : P —[ a′⋆ ]→⋆ R′} → E⋆ ≃ E′⋆ → E′⋆ ≃ E⋆

   -- TODO: IsEquivalence instance.
