module Transition.Concur.Cofinal where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬ⊖-✓; Action₂); open _ᴬ⌣_
   import Action.Ren
   open import Name as ᴺ using (Cxt; Name; toℕ; _+_; zero)
   open import Proc using (Proc); open Proc
   import Proc.Ren
   open import StructuralCong.Proc using (_≈_; module _≈_; ≈-refl; ≈-reflexive; ≈-sym; _*⁼; module ≈-Reasoning);
      open _≈_ renaming (trans to ≈-trans)
   open import Ren as ᴿ using (Ren; ᴺren; suc; _ᴿ+_; pop; push; swap; +-preserves-id); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; Delta; module Delta′; ⊖₁; ⊖); open Concur₁
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- related by an (optional) "bound" braid, or by a "free" braid.
   ⋈[_,_,_] : ∀ Γ (ӓ : Action₂ Γ) (Δ : Cxt) →
              let Γ′ = Γ + inc (π₁ ӓ) + inc (π₂ ӓ) in Proc (Γ′ + Δ) → Proc (Γ′ + Δ) → Set
   ⋈[_,_,_] _ (_ ᵇ , _ ᵇ) Δ P P′ = ((swap ᴿ+ Δ) *) P ≡ P′
   ⋈[_,_,_] _ (_ ᵇ , _ ᶜ) _ P P′ = P ≡ P′
   ⋈[_,_,_] _ (_ ᶜ , _ ᵇ) Δ P P′ = P ≈ P′
   ⋈[_,_,_] _ (_ ᶜ , _ ᶜ) Δ P P′ = P ≈ P′

   -- TODO: move to a more generic location.
   swap-swap : ∀ {Γ} {P P′ : Proc (Γ + 2)} → (swap *) P ≡ P′ → P ≡ (swap *) P′
   swap-swap {P = P} {P′} swap*P≡P′ =
      let open EqReasoning (setoid _) in
      begin
         P
      ≡⟨ sym (swap-involutive _) ⟩
         (swap *) ((swap *) P)
      ≡⟨ cong (swap *) swap*P≡P′ ⟩
         (swap *) P′
      ∎

   open Delta′

   -- Called 'cofin' in the paper. Use ≈-Reasoning for maximum clarity.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣₁[ 𝑎 ] E′) → ⋈[ Γ , (a , π₁ (ᴬ⊖ 𝑎)) , zero ] (S (⊖₁ 𝐸)) (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸)))
   ⊖₁-✓ (E ᵇ│ᵇ F) = sym (cong₂ _│_ (swap∘push (target E)) (swap∘suc-push (target F)))
   ⊖₁-✓ (E ᵇ│ᶜ F) = refl
   ⊖₁-✓ (E ᶜ│ᵇ F) = ≈-refl
   ⊖₁-✓ (E ᶜ│ᶜ F) = ≈-refl
   ⊖₁-✓ (_│•ᵇ_ {y = y} {a = a} 𝐸 F) with (pop y *ᵇ) (E/E′ (⊖₁ 𝐸))
   ... | _ rewrite pop∘push y a = cong₂ _│_ (
      let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      begin
         (pop (push y) *) S
      ≡⟨ cong (pop (push y) *) (swap-swap (⊖₁-✓ 𝐸)) ⟩
         (pop (push y) *) ((swap *) S′)
      ≡⟨ sym (pop∘swap y _) ⟩
         (suc (pop y) *) S′
      ∎) refl
   ⊖₁-✓ (_│•ᶜ_ {y = y} {a = a} 𝐸 F) with (pop y *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | _ rewrite pop∘push y a = (pop y *⁼) (⊖₁-✓ 𝐸) │₁ refl
   ⊖₁-✓ (_ᵇ│•_ {y = y} E 𝐹) = cong₂ _│_ (sym (pop∘suc-push y _)) (⊖₁-✓ 𝐹)
   ⊖₁-✓ (E ᶜ│• 𝐹) = refl │₂ ⊖₁-✓ 𝐹
   ⊖₁-✓ (𝐸 │ᵥᵇ F) = cong ν_ (cong₂ _│_ (swap-swap (⊖₁-✓ 𝐸)) (swap∘push _))
   ⊖₁-✓ (𝐸 │ᵥᶜ F) = ν (⊖₁-✓ 𝐸 │₁ refl)
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {𝑎 = ᵛ∇ᵛ} E 𝐹) = cong₂ _│_ (pop-zero∘suc-push _) (⊖₁-✓ 𝐹)
{-
   ⊖₁-✓ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) rewrite swap∘push (target E) = ν (refl │₂ ≈-reflexive (swap-swap (⊖₁-✓ 𝐹)))
   ⊖₁-✓ (E ᶜ│ᵥ 𝐹) = ν (refl │₂ ⊖₁-✓ 𝐹)
   ⊖₁-✓ (_│ᵇᵇ_ {𝑎 = ᵛ∇ᵛ} P 𝐹) = refl │₂ ⊖₁-✓ 𝐹
   ⊖₁-✓ (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) = cong₂ _│_ (swap∘push∘push P) (⊖₁-✓ 𝐹)
   ⊖₁-✓ (P │ᵇᶜ 𝐹) = refl │₂ ⊖₁-✓ 𝐹
   ⊖₁-✓ (P │ᶜᵇ 𝐹) = refl │₂ ⊖₁-✓ 𝐹
   ⊖₁-✓ (P │ᶜᶜ 𝐹) = refl │₂ ⊖₁-✓ 𝐹
   ⊖₁-✓ (_ᵇᵇ│_ {𝑎 = ᵛ∇ᵛ} 𝐸 _) = ⊖₁-✓ 𝐸 │₁ refl
   ⊖₁-✓ (_ᵇᵇ│_ {𝑎 = ᵇ∇ᵇ} 𝐸 Q) = cong₂ _│_ (⊖₁-✓ 𝐸) (swap∘push∘push Q)
   ⊖₁-✓ (𝐸 ᵇᶜ│ Q) = ⊖₁-✓ 𝐸 │₁ refl
   ⊖₁-✓ (𝐸 ᶜᵇ│ Q) = ⊖₁-✓ 𝐸 │₁ refl
   ⊖₁-✓ (𝐸 ᶜᶜ│ Q) = ⊖₁-✓ 𝐸 │₁ refl
   ⊖₁-✓ (𝐸 ➕₁ Q) = ⊖₁-✓ 𝐸
   ⊖₁-✓ (_│•_ {y = y} {z = z} 𝐸 𝐹) = (
      let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      begin
         (pop z *) ((suc (pop y) *) S)
      ≡⟨ sym (pop-pop-swap y z _) ⟩
         (pop y *) ((suc (pop z) *) ((swap *) S))
      ≡⟨ cong (pop y *) (cong (suc (pop z) *) (⊖₁-✓ 𝐸)) ⟩
         (pop y *) ((suc (pop z) *) S′)
      ∎) │₂ ⊖₁-✓ 𝐹
   ⊖₁-✓ (_│•ᵥ_ {y = y} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | _ = ν ((
      let open EqReasoning (setoid _); S₁ = S (⊖₁ 𝐸); S′₁ = S′ (⊖₁ 𝐸) in
      begin
         (suc (pop y) *) S₁
      ≡⟨ cong (suc (pop y) *) (sym (swap-involutive _ )) ⟩
         (suc (pop y) *) ((swap *) ((swap *) S₁))
      ≡⟨ cong (suc (pop y) *) (cong (swap *) (⊖₁-✓ 𝐸)) ⟩
         (suc (pop y) *) ((swap *) S′₁)
      ≡⟨ suc-pop∘swap y _ ⟩
         (pop ((push *) y) *) S′₁
      ∎) │₂ ⊖₁-✓ 𝐹)
   ⊖₁-✓ (_│ᵥ•_ {y = y} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | _ =
      let open EqReasoning (setoid _); S₁ = S (⊖₁ 𝐸); S′₁ = S′ (⊖₁ 𝐸) in
      ν ((
         begin
            (pop (push y) *) S₁
         ≡⟨ sym (suc-pop∘swap y _) ⟩
            (suc (pop y) *) ((swap *) S₁)
         ≡⟨ cong (suc (pop y) *) (⊖₁-✓ 𝐸) ⟩
            (suc (pop y) *) S′₁
         ∎) │₂ ⊖₁-✓ 𝐹)
   ⊖₁-✓ (_│ᵥ_ {•x⌣•u = ᵛ∇ᵛ} 𝐸 𝐹) =
      let open EqReasoning (setoid _); S₁ = S (⊖₁ 𝐸); S′₁ = S′ (⊖₁ 𝐸) in
      ν ((
         begin
            (pop zero *) S₁
         ≡⟨ sym (pop-swap _) ⟩
            (pop zero *) ((swap *) S₁)
         ≡⟨ cong (pop zero *) (⊖₁-✓ 𝐸) ⟩
            (pop zero *) S′₁
         ∎) │₂ ⊖₁-✓ 𝐹)
   ⊖₁-✓ (_│ᵥ_ {•x⌣•u = ᵇ∇ᵇ} 𝐸 𝐹) rewrite sym (⊖₁-✓ 𝐸) | sym (⊖₁-✓ 𝐹) = νν-swapᵣ _
   ⊖₁-✓ (ν• 𝐸) = ⊖₁-✓ 𝐸
   ⊖₁-✓ (ν•ᵇ 𝐸) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | _ = {!!}
-}
   ⊖₁-✓ _ = {!!}
{-
   ⊖₁-✓ (ν•ᵇ 𝐸) =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      begin
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ 𝐸) ⟩
         (swap *) S′
      ∎
   ⊖₁-✓ (ν•ᶜ 𝐸) = ⊖₁-✓ 𝐸
   ⊖₁-✓ (νᵇᵇ_ {a = x •} {a} 𝐸) with (swap *ᵇ) (E/E′ (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) (⊖₁-✓ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {u •} 𝐸) =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) (⊖₁-✓ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} 𝐸) =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≈⟨ (swap *⁼) ((suc swap *⁼) (⊖₁-✓ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵛᵛ 𝐸) =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ 𝐸) ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᵇᶜ_ {a′ = a′} 𝐸) with (swap *ᶜ) (E′/E (⊖₁ 𝐸))
   ... | _ rewrite swap∘push∘push a′ =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ 𝐸) ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᶜᵇ_ {a = a} 𝐸) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | _ rewrite swap∘push∘push a =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc id *) ((swap *) S)
      ≡⟨ +-id-elim 1 _ ⟩
         (swap *) S
      ≡⟨ cong (swap *) (sym (*-preserves-id _)) ⟩
         (swap *) ((id *) S)
      ≈⟨ (swap *⁼) (⊖₁-✓ 𝐸) ⟩
         (swap *) S′
      ∎)
   ⊖₁-✓ (νᶜᶜ 𝐸) =
      let S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      ν (begin
         (suc id *) S
      ≡⟨ *-preserves-≃ₑ (+-preserves-id 1) _ ⟩
         (id *) S
      ≈⟨ ⊖₁-✓ 𝐸 ⟩
         S′
      ∎)
   ⊖₁-✓ (! 𝐸) = ⊖₁-✓ 𝐸

   symmetrise : ∀ {Γ} {S S′ : Proc Γ} → (id *) S ≈ S′ → (id *) S′ ≈ S
   symmetrise {S = S} {S′} id*S≈S′ =
      begin
         (id *) S′
      ≡⟨ *-preserves-id _ ⟩
         S′
      ≈⟨ ≈-sym id*S≈S′ ⟩
         (id *) S
      ≡⟨ *-preserves-id _ ⟩
         S
      ∎

   -- Now symmetrise.
   ⊖-✓ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (𝐸 : E ⌣[ 𝑎 ] E′) →
         ⋈[ Γ , (a , π₁ (ᴬ⊖ 𝑎)) , zero ] (S (⊖ 𝐸)) (subst Proc (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖ 𝐸)))
   ⊖-✓ (inj₁ 𝐸) = ⊖₁-✓ 𝐸
   ⊖-✓ (inj₂ 𝐸′) with ⊖₁ 𝐸′ | ⊖₁-✓ 𝐸′
   ⊖-✓ {𝑎 = ᵛ∇ᵛ} (inj₂ 𝐸′) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
   ⊖-✓ {𝑎 = ᵇ∇ᵇ} (inj₂ 𝐸′) | E′/E ᵀΔ E/E′ | swap*S≈S′ =
      let S = target E′/E; S′ = target E/E′ in
      begin
         (swap *) S′
      ≈⟨ (swap *⁼) (≈-sym swap*S≈S′) ⟩
         (swap *) ((swap *) S)
      ≡⟨ swap-involutive _ ⟩
         S
      ∎
   ⊖-✓ {𝑎 = ᵇ∇ᶜ} (inj₂ 𝐸′) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
   ⊖-✓ {𝑎 = ᶜ∇ᵇ} (inj₂ 𝐸′) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
   ⊖-✓ {𝑎 = ᶜ∇ᶜ} (inj₂ 𝐸′) | _ ᵀΔ _ | id*S≈S′ = symmetrise id*S≈S′
-}
