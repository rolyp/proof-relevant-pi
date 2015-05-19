-- WIP: transition sequences and causal equivalence.
module Transition.Seq where

   open import SharedModules hiding (_⇒_; trans)
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; _ᵇ; _ᶜ; inc)
   open import Action.Ren using (ren-preserves-inc)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆; []; _ᵇ∷_)
   open import Action.Seq.Ren using (ren-preserves-inc⋆)
   open import Name as ᴺ using (Cxt; Name; _+_; +-assoc; zero; toℕ)
   open import Proc using (Proc)
   open import Ren as ᴿ using (Ren; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import StructuralCong.Proc using (_≅_; ≅-sym; ≅-refl)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_; source; target)
   open import Transition.Concur using (_⌣_; module _Δ_; ⊖; coinitial; ᴬ⊖; ᴬ⊖-✓)
   open import Transition.Ren using (_Δ_; _*′)

   braid : ∀ {Γ} (n : Name 3) → Ren (Γ + toℕ n) (Γ + toℕ n)
   braid zero = id
   braid (ᴺ.suc zero) = id
   braid (ᴺ.suc (ᴺ.suc zero)) = swap
   braid (ᴺ.suc (ᴺ.suc (ᴺ.suc ())))

   ⋈[_,_,_] : ∀ Γ (n : Name 3) (m : Cxt) → Proc (Γ + toℕ n + m) → Proc (Γ + toℕ n + m) → Set
   ⋈[_,_,_] Γ n m P₁ P₂ = ((braid n ᴿ+ m) *) P₁ ≅ P₂

   -- TODO: consolidate.
   braid-preserves-inc : ∀ {Γ} (n : Name 3) m (a : Action (Γ + toℕ n + m)) →
                         Γ + toℕ n + m + inc (((braid n ᴿ+ m) *) a) ≡ Γ + toℕ n + (m + inc a)
   braid-preserves-inc n m a rewrite sym (ren-preserves-inc (braid n ᴿ+ m) a) = +-assoc _ m (inc a)

   braid-preserves-inc⋆ : ∀ {Γ} (n : Name 3) m (a⋆ : Action⋆ (Γ + toℕ n + m)) →
                         Γ + toℕ n + m + inc⋆ (((braid n ᴿ+ m) *) a⋆) ≡ Γ + toℕ n + (m + inc⋆ a⋆)
   braid-preserves-inc⋆ n m a⋆ rewrite sym (ren-preserves-inc⋆ (braid n ᴿ+ m) a⋆) = +-assoc _ m (inc⋆ a⋆)

   -- The type of the symmetric residual (γ/E , E/γ) for a single transition.
   infixl 5 _Δ′_
   record _Δ′_ {ι Γ n m a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E : ⋈[ Γ , n , m + inc a ] (subst Proc (+-assoc _ m (inc a)) R) R′
         E/γ : P′ —[ ((braid n ᴿ+ m) *) a - ι ]→ subst Proc (sym (braid-preserves-inc n m a)) R′

   ⊖′[_,_] : ∀ {ι Γ} n m {a} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
         (E : P —[ a - ι ]→ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ′_ {n = n} {m = m} E γ
   ⊖′[ n , m ] {(x ᴬ.•) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {(ᴬ.• x) ᵇ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {ᴬ.• x 〈 y 〉 ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ
   ⊖′[ n , m ] {ᴬ.τ ᶜ} E γ = let φ/E′ Δ E′/φ = ⊖† (((braid n ᴿ+ m) *′) E) γ in φ/E′ Δ E′/φ

   -- Traces are lists of composable transitions. Snoc lists would make more sense implementation-wise;
   -- composition is probably what we eventually want.
   infixr 5 _ᵇ∷_
   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [] : P —[ [] ]→⋆ P
      _ᵇ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᵇ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
            P —[ a ᵇ∷ a⋆ ]→⋆ subst Proc (+-assoc _ _ (inc⋆ a⋆)) S

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace. Cofinal by construction.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ n m a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E⋆ : ⋈[ Γ , n , m + inc⋆ a⋆ ] (subst Proc (+-assoc _ _ (inc⋆ a⋆)) R) R′
         E⋆/γ : P′ —[ ((braid n ᴿ+ m) *) a⋆ ]→⋆ subst Proc (sym (braid-preserves-inc⋆ n m a⋆)) R′

   ⊖⋆[_,_] : ∀ {Γ} n m {a⋆} {P P′ : Proc ((Γ + toℕ n) + m)} {R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , n , m ] P P′) → _Δ⋆_ {n = n} {m = m} E⋆ γ
   ⊖⋆[ n , m ] [] γ = γ Δ []
   ⊖⋆[_,_] {Γ} n m {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ =
      let _Δ_ {R′} γ/E E/γ = ⊖′[ n , m ] E γ; _Δ_ {S′} γ/E/E⋆ E⋆/γ/E = ⊖⋆[ n , m + 1 ] E⋆ γ/E
          x : source E/γ —[ ((braid n ᴿ+ m) *) (a ᵇ∷ a⋆) ]→⋆
              subst Proc (sym (braid-preserves-inc⋆ n m (a ᵇ∷ a⋆)))
                    (subst Proc (cong (λ m → Γ + toℕ n + m) (+-assoc m 1 (inc⋆ a⋆))) S′)
          x = {!!}
          F : source E/γ —[ ((braid n ᴿ+ m) *) a ᵇ - _ ]→ subst Proc (sym (braid-preserves-inc n m (a ᵇ))) R′
          F = E/γ
          S† = subst Proc (sym (braid-preserves-inc⋆ n (m + 1) a⋆)) S′
          F⋆ : R′ —[ (ᴿ.suc (braid n ᴿ+ m) *) a⋆ ]→⋆ S†
          F⋆ = E⋆/γ/E
          b⋆ = (ᴿ.suc (braid n ᴿ+ m) *) a⋆
          F∷F⋆ : source E/γ —[ ((braid n ᴿ+ m) *) a ᵇ∷ b⋆ ]→⋆ subst Proc (+-assoc _ _ (inc⋆ b⋆)) S†
          F∷F⋆ = {!!}
          goal : source E/γ —[ ((braid n ᴿ+ m) *) (a ᵇ∷ a⋆) ]→⋆ subst Proc (sym (braid-preserves-inc⋆ n m (a ᵇ∷ a⋆))) _
          goal = {!!}
      in {! !} Δ {!!}

{-
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
-}
