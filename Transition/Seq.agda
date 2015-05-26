-- Traces and causal equivalence.
module Transition.Seq where

   open import SharedModules hiding (_⇒_)
   import Relation.Binary.EqReasoning as EqReasoning
   import Relation.Binary.HeterogeneousEquality

   open import Ext

   open import Action as ᴬ using (Action; _ᵇ; _ᶜ; inc; _ᴬ⌣_; module _ᴬ⌣_);
      open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ; open ᴬ._ᴬ⌣_
   open import Action.Ren using (ren-preserves-inc-assoc)
   open import Action.Seq as ᴬ⋆ using (Action⋆; inc⋆; []; _ᵇ∷_; _ᶜ∷_)
   open import Action.Seq.Ren using (ren-preserves-inc⋆-assoc)
   open import Name as ᴺ using (Cxt; Name; _+_; +-assoc; zero; toℕ; +-left-identity)
   open import Proc using (Proc)
   open import Ren as ᴿ using (Ren; push; swap; _ᴿ+_); open ᴿ.Renameable ⦃...⦄
   open import StructuralCong.Proc using (_≈_; ≈-sym; ≈-refl)
   open import StructuralCong.Transition using (_Δ_) renaming (⊖ to ⊖†)
   open import Transition using (_—[_-_]→_; source; target)
   open import Transition.Concur using (Concur; module Delta′; Delta; ⊖; ᴬ⊖; ᴬ⊖-✓; Action₂; inc₂)
   open import Transition.Concur.Properties using (braid; ⋈[_,_,_]; ⊖-✓)
   open import Transition.Ren using (_Δ_; _*′)

   Proc↱ = subst Proc
   Proc↲ = ≡-subst-removable Proc

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

   -- Traces are lists of composable transitions. Snoc lists would make more sense implementation-wise;
   -- composition is probably what we eventually want.
   infixr 5 _ᵇ∷_ _ᶜ∷_
   data _—[_]→⋆_ {Γ} (P : Proc Γ) : (a⋆ : Action⋆ Γ) → Proc (Γ + inc⋆ a⋆) → Set where
      [] : P —[ [] ]→⋆ P
      _ᵇ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᵇ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᵇ∷ a⋆ ]→⋆ Proc↱ (+-assoc _ _ (inc⋆ a⋆)) S
      _ᶜ∷_ : ∀ {a R a⋆ S} (E : P —[ a ᶜ - _ ]→ R) (E⋆ : R —[ a⋆ ]→⋆ S) →
             P —[ a ᶜ∷ a⋆ ]→⋆ Proc↱ (+-assoc _ _ (inc⋆ a⋆)) S

   target⋆ : ∀ {Γ} {P : Proc Γ} {a⋆ : Action⋆ Γ} {R} → P —[ a⋆ ]→⋆ R → Proc (Γ + inc⋆ a⋆)
   target⋆ {R = R} _ = R

   -- The type of the symmetric residual (γ/E⋆ , E⋆/γ) for a trace. Cofinal by construction.
   infixl 5 _Δ⋆_
   record _Δ⋆_ {Γ} {ӓ : Action₂ Γ} {m a⋆} {P P′ : Proc (Γ + inc₂ ӓ + m)} {R}
          (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , ӓ , m ] P P′) : Set where
      constructor _Δ_
      field
         {R′} : _
         γ/E⋆ : ⋈[ Γ , ӓ , m + inc⋆ a⋆ ] (Proc↱ (+-assoc _ _ (inc⋆ a⋆)) R) R′
         E⋆/γ : P′ —[ ((braid ӓ ᴿ+ m) *) a⋆ ]→⋆ Proc↱ (ren-preserves-inc⋆-assoc (braid ӓ) m a⋆) R′

   -- Hetereogeneously equate braidings up to associativity of + on contexts.
   braid-assoc : ∀ {Γ Γ′} (ρ : Ren Γ Γ′) Δ₁ Δ₂ Δ₃ S S′ →
                 (((ρ ᴿ+ (Δ₁ + Δ₂ + Δ₃))*)
                 (Proc↱ (+-assoc Γ (Δ₁ + Δ₂) Δ₃) (Proc↱ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S)) ≈ S′) ≅
                 (((ρ ᴿ+ (Δ₁ + (Δ₂ + Δ₃)))*)
                 (Proc↱ (+-assoc Γ Δ₁ (Δ₂ + Δ₃)) (Proc↱ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S)) ≈
                 Proc↱ (cong (_+_ Γ′) (+-assoc Δ₁ Δ₂ Δ₃)) S′)
   braid-assoc {Γ} {Γ′} ρ Δ₁ Δ₂ Δ₃ S S′ =
      ≅-cong₃ (λ Δ† P P′ → ((ρ ᴿ+ Δ†)*) P ≈ P′)
         (≡-to-≅ (+-assoc Δ₁ Δ₂ Δ₃))
         (
            let open ≅-Reasoning in
            begin
               Proc↱ (+-assoc Γ (Δ₁ + Δ₂) Δ₃) (Proc↱ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S)
            ≅⟨ Proc↲ (+-assoc Γ (Δ₁ + Δ₂) Δ₃) _ ⟩
               Proc↱ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S
            ≅⟨ Proc↲ (cong (flip _+_ Δ₃) (+-assoc Γ Δ₁ Δ₂)) S ⟩
               S
            ≅⟨ ≅-sym (Proc↲ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S) ⟩
               Proc↱ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S
            ≅⟨ ≅-sym (Proc↲ (+-assoc Γ Δ₁ (Δ₂ + Δ₃)) _) ⟩
               Proc↱ (+-assoc Γ Δ₁ (Δ₂ + Δ₃)) (Proc↱ (+-assoc (Γ + Δ₁) Δ₂ Δ₃) S)
            ∎
         )
         (≅-sym (Proc↲ (cong (_+_ Γ′) (+-assoc Δ₁ Δ₂ Δ₃)) S′))

   ⊖⋆[_,_] : ∀ {Γ} (ӓ : Action₂ Γ) m {P P′ : Proc (Γ + inc₂ ӓ + m)} {a⋆ R}
             (E⋆ : P —[ a⋆ ]→⋆ R) (γ : ⋈[ Γ , ӓ , m ] P P′) → _Δ⋆_ {ӓ = ӓ} {m = m} E⋆ γ
   ⊖⋆[ _ , _ ] [] γ = γ Δ []
   ⊖⋆[ ӓ , m ] {a⋆ = a ᵇ∷ a⋆} (E ᵇ∷ E⋆) γ with ⊖′[ ӓ , m ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ ӓ , m + 1 ] E⋆ γ/E | ren-preserves-inc-assoc (braid ӓ) m (a ᵇ)
   ... | _Δ_ {S′} γ/E/E⋆ E⋆/γ/E | refl rewrite ≅-to-≡ (braid-assoc (braid ӓ) m 1 (inc⋆ a⋆) (target⋆ E⋆) S′) =
      let σ = braid ӓ
          open ≅-Reasoning
          E/γ∷E⋆/γ/E =
             subst (λ P → source E/γ —[ ((σ ᴿ+ m) *) a ᵇ∷ ((σ ᴿ+ m ᴿ+ 1) *) a⋆ ]→⋆ P) (≅-to-≡ (
                begin
                   Proc↱ (+-assoc _ 1 (inc⋆ (((σ ᴿ+ m ᴿ+ 1) *) a⋆)))
                         (Proc↱ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′)
                ≅⟨ Proc↲ (+-assoc _ 1 (inc⋆ (((σ ᴿ+ m ᴿ+ 1) *) a⋆))) _ ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′
                ≅⟨ Proc↲ (ren-preserves-inc⋆-assoc σ (m + 1) a⋆) S′ ⟩
                   S′
                ≅⟨ ≅-sym (Proc↲ (cong (_+_ _) (+-assoc m 1 (inc⋆ a⋆))) S′) ⟩
                   Proc↱ (cong (_+_ _) (+-assoc m 1 (inc⋆ a⋆))) S′
                ≅⟨ ≅-sym (Proc↲ (ren-preserves-inc⋆-assoc σ m (a ᵇ∷ a⋆)) _) ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ m (a ᵇ∷ a⋆))
                         (Proc↱ (cong (_+_ _) (+-assoc m 1 (inc⋆ a⋆))) S′)
                ∎)
             ) (E/γ ᵇ∷ E⋆/γ/E)
      in γ/E/E⋆ Δ E/γ∷E⋆/γ/E
   ⊖⋆[ ӓ , m ] {a⋆ = a ᶜ∷ a⋆} (E ᶜ∷ E⋆) γ with ⊖′[ ӓ , m ] E γ
   ... | γ/E Δ E/γ with ⊖⋆[ ӓ , m ] E⋆ γ/E | ren-preserves-inc-assoc (braid ӓ) m (a ᶜ)
   ... | _Δ_ {S′} γ/E/E⋆ E⋆/γ/E | refl rewrite ≅-to-≡ (braid-assoc (braid ӓ) m 0 (inc⋆ a⋆) (target⋆ E⋆) S′) =
      let σ = braid ӓ
          open ≅-Reasoning
          E/γ∷E⋆/γ/E =
             subst (λ P → source E/γ —[ ((σ ᴿ+ m) *) a ᶜ∷ ((σ ᴿ+ m) *) a⋆ ]→⋆ P) (≅-to-≡ (
                begin
                   Proc↱ (+-assoc _ 0 (inc⋆ (((σ ᴿ+ m) *) a⋆)))
                         (Proc↱ (ren-preserves-inc⋆-assoc σ m a⋆) S′)
                ≅⟨ Proc↲ (+-assoc _ 0 (inc⋆ (((σ ᴿ+ m) *) a⋆))) _ ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ m a⋆) S′
                ≅⟨ Proc↲ (ren-preserves-inc⋆-assoc σ m a⋆) S′ ⟩
                   S′
                ≅⟨ ≅-sym (Proc↲ (cong (_+_ _) (+-assoc m 0 (inc⋆ a⋆))) S′) ⟩
                   Proc↱ (cong (_+_ _) (+-assoc m 0 (inc⋆ a⋆))) S′
                ≅⟨ ≅-sym (Proc↲ (ren-preserves-inc⋆-assoc σ m (a ᶜ∷ a⋆)) _) ⟩
                   Proc↱ (ren-preserves-inc⋆-assoc σ m (a ᶜ∷ a⋆))
                         (Proc↱ (cong (_+_ _) (+-assoc m 0 (inc⋆ a⋆))) S′)
                ∎)
             ) (E/γ ᶜ∷ E⋆/γ/E)
      in γ/E/E⋆ Δ E/γ∷E⋆/γ/E

   -- Causal equivalence.
   infix 4 _≃_
   data _≃_ {Γ} {P : Proc Γ} : ∀ {a⋆ a′⋆ R R′} → P —[ a⋆ ]→⋆ R → P —[ a′⋆ ]→⋆ R′ → Set where
      -- Transposition cases. Each specifies a way of extending an existing equivalence; would be
      -- cleaner to define these as axiomatic cases.
      [_ᶜ∶⇋∶ᶜ_] : ∀ {a a′} {R R′} (E : P —[ a ᶜ - _ ]→ R) (E′ : P —[ a′ ᶜ - _ ]→ R′) →
                 ⦃ E⌣E′ : E ⌣[ ᶜ∇ᶜ ] E′ ⦄ → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                 ∀ {a⋆ a′⋆ S S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                 let _ Δ E⋆/γ = ⊖⋆[ (a ᶜ , a′ ᶜ) , 0 ] E⋆ (⊖-✓ E⌣E′) in
                 E ᶜ∷ E′/E ᶜ∷ E⋆ ≃ E′ ᶜ∷ E/E′ ᶜ∷ E⋆/γ
      [_ᶜ∶⇋∶ᵇ_] : ∀ {a a′} {R R′} (E : P —[ a ᶜ - _ ]→ R) (E′ : P —[ a′ ᵇ - _ ]→ R′) →
                 ⦃ E⌣E′ : E ⌣[ ᶜ∇ᵇ ] E′ ⦄ → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                 ∀ {a⋆ a′⋆ S S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                 let _ Δ E⋆/γ = ⊖⋆[ (a ᶜ , a′ ᵇ) , 0 ] E⋆ (⊖-✓ E⌣E′) in
                 E ᶜ∷ E′/E ᵇ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᶜ∷ E⋆/γ
      [_ᵇ∶⇋∶ᵇ_] : ∀ {a a′} {R R′} (E : P —[ a ᵇ - _ ]→ R) (E′ : P —[ a′ ᵇ - _ ]→ R′) →
                 ⦃ E⌣E′ : E ⌣[ ᵇ∇ᵇ ] E′ ⦄ → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                 ∀ {a⋆ a′⋆ S S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                 let _ Δ E⋆/γ = ⊖⋆[ (a ᵇ , (push *) a′ ᵇ) , 0 ] E⋆ (⊖-✓ E⌣E′) in
                 E ᵇ∷ E′/E ᵇ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᵇ∷ E⋆/γ
      [_ᵛ∶⇋∶ᵛ_] : ∀ {x u} {R R′} (E : P —[ (• x) ᵇ - _ ]→ R) (E′ : P —[ (• u) ᵇ - _ ]→ R′) →
                 ⦃ E⌣E′ : E ⌣[ ᵛ∇ᵛ ] E′ ⦄ → let open Delta′ (⊖ E⌣E′); Q = target E′/E in
                 ∀ {a⋆ a′⋆ S S′} {E⋆ : Q —[ a⋆ ]→⋆ S} {E′⋆ : Q —[ a′⋆ ]→⋆ S′} → E⋆ ≃ E′⋆ →
                 let _ Δ E⋆/γ = ⊖⋆[ ((• x) ᵇ , • ᴺ.suc u 〈 zero 〉 ᶜ) , 0 ] E⋆ (⊖-✓ E⌣E′) in
                 E ᵇ∷ E′/E ᶜ∷ E⋆ ≃ E′ ᵇ∷ E/E′ ᶜ∷ E⋆/γ
      -- Close under trace constructors.
      [] : [] ≃ []
      _ᵇ∷_ : ∀ {a a⋆ a′⋆ R S S′} (E : P —[ a ᵇ - _ ]→ R) {E⋆ : R —[ a⋆ ]→⋆ S} {E′⋆ : R —[ a′⋆ ]→⋆ S′} →
             E⋆ ≃ E′⋆ → E ᵇ∷ E⋆ ≃ E ᵇ∷ E′⋆
      _ᶜ∷_ : ∀ {a a⋆ a′⋆ R S S′} (E : P —[ a ᶜ - _ ]→ R) {E⋆ : R —[ a⋆ ]→⋆ S} {E′⋆ : R —[ a′⋆ ]→⋆ S′} →
             E⋆ ≃ E′⋆ → E ᶜ∷ E⋆ ≃ E ᶜ∷ E′⋆
      -- Transitivity and symmetry.
      ≃-trans : ∀ {a⋆ R a″⋆ S a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {F⋆ : P —[ a″⋆ ]→⋆ S} {E′⋆ : P —[ a′⋆ ]→⋆ R′} →
                E⋆ ≃ F⋆ → F⋆ ≃ E′⋆ → E⋆ ≃ E′⋆
      ≃-sym : ∀ {a⋆ R a′⋆ R′} {E⋆ : P —[ a⋆ ]→⋆ R} {E′⋆ : P —[ a′⋆ ]→⋆ R′} → E⋆ ≃ E′⋆ → E′⋆ ≃ E⋆

   TraceFrom : ∀ {Γ} (P : Proc Γ) → Set
   TraceFrom P = Σ[ a⋆ ∈ Action⋆ _ ] Σ[ R ∈ Proc _ ] P —[ a⋆ ]→⋆ R

   ≃-isEquivalence : ∀ {Γ} {P : Proc Γ} → IsEquivalence (_≃_ {P = P})
   ≃-isEquivalence = record {
         refl = {!!};
         sym = {!!};
         trans = {!!}
      }
