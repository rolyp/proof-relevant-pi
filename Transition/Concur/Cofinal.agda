module Transition.Concur.Cofinal where

   open import SharedModules
   import Relation.Binary.EqReasoning as EqReasoning

   open import Action as ᴬ using (Action; inc); open ᴬ.Action; open ᴬ.Actionᵇ; open ᴬ.Actionᶜ
   open import Action.Concur using (_ᴬ⌣_; module _ᴬ⌣_; ᴬ⊖; ᴬ⊖-✓; Action₂); open _ᴬ⌣_
   import Action.Ren
   open import Braiding.Proc using (_≈_; module _≈_; ≈-sym; _*⁼); open _≈_
   open import Name as ᴺ using (Cxt; Name; toℕ; _+_; zero)
   open import Proc using (Proc); open Proc
   import Proc.Ren
   open import Ren as ᴿ using (Ren; ᴺren; suc; _ᴿ+_; pop; push; swap; +-preserves-id); open ᴿ.Renameable ⦃...⦄
   open import Ren.Properties
   open import Transition as ᵀ using (_—[_-_]→_; target); open ᵀ._—[_-_]→_
   open import Transition.Concur
      using (Concur₁; module Concur₁; Concur; Delta′; Delta; module Delta′; ⊖₁; ⊖); open Concur₁
   open import Transition.Ren using (_*ᵇ; _*ᶜ)

   -- Cofinality is generalised from the usual "on the nose" notion to means target states which are either
   -- related by a "bound" braid, by a "free" braid, or by identity.
   ⋈[_,_,_] : ∀ Γ {a a′ : Action Γ} (𝑎 : a ᴬ⌣ a′) (Δ : Cxt) →
               let Γ′ = Γ + inc a + inc (π₁ (ᴬ⊖ 𝑎)) in Proc (Γ′ + Δ) → Proc (Γ′ + Δ) → Set
   ⋈[ Γ , ˣ∇ˣ , Δ ] P P′ = P ≡ P′
   ⋈[ Γ , ᵇ∇ᵇ , Δ ] P P′ = ((swap ᴿ+ Δ) *) P ≡ P′ -- free braid
   ⋈[ Γ , ᵇ∇ᶜ , Δ ] P P′ = P ≡ P′
   ⋈[ Γ , ᶜ∇ᵇ , Δ ] P P′ = P ≡ P′
   ⋈[ Γ , ᶜ∇ᶜ , Δ ] P P′ = P ≡ P′
   ⋈[ Γ , ᵛ∇ᵛ , Δ ] P P′ = P ≈ P′ -- bound braid

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

   -- Called 'cofin' in the paper.
   ⊖₁-✓ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
          (𝐸 : E ⌣₁[ 𝑎 ] E′) → ⋈[ Γ , 𝑎 , zero ] (S (⊖₁ 𝐸)) (Proc↱ (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖₁ 𝐸)))
   ⊖₁-✓ (E ᵇ│ᵇ F) = sym (cong₂ _│_ (swap∘push (target E)) (swap∘suc-push (target F)))
   ⊖₁-✓ (E ᵇ│ᶜ F) = refl
   ⊖₁-✓ (E ᶜ│ᵇ F) = refl
   ⊖₁-✓ (E ᶜ│ᶜ F) = refl
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
   ... | _ rewrite pop∘push y a = cong₂ _│_ (cong (pop y *) (⊖₁-✓ 𝐸)) refl
   ⊖₁-✓ (_ᵇ│•_ {y = y} E 𝐹) = cong₂ _│_ (sym (pop∘suc-push y _)) (⊖₁-✓ 𝐹)
   ⊖₁-✓ (E ᶜ│• 𝐹) = cong₂ _│_ refl (⊖₁-✓ 𝐹)
   ⊖₁-✓ (𝐸 │ᵥᵇ F) = cong ν_ (cong₂ _│_ (swap-swap (⊖₁-✓ 𝐸)) (swap∘push _))
   ⊖₁-✓ (𝐸 │ᵥᶜ F) = cong ν_ (cong₂ _│_ (⊖₁-✓ 𝐸) refl)
   ⊖₁-✓ (_ᵇ│ᵥ_ {x = x} {𝑎 = ˣ∇ˣ} E 𝐹) = cong₂ _│_ (pop-zero∘suc-push _) (⊖₁-✓ 𝐹)
   ⊖₁-✓ (_ᵇ│ᵥ_ {𝑎 = ᵇ∇ᵇ} E 𝐹) rewrite swap∘push (target E) = cong ν_ (cong₂ _│_ refl (swap-swap (⊖₁-✓ 𝐹)))
   ⊖₁-✓ (E ᶜ│ᵥ 𝐹) = cong ν_ (cong₂ _│_ refl (⊖₁-✓ 𝐹))
   ⊖₁-✓ (_│ᵇᵇ_ {𝑎 = ˣ∇ˣ} P 𝐹) = cong₂ _│_ refl (⊖₁-✓ 𝐹)
   ⊖₁-✓ (_│ᵇᵇ_ {𝑎 = ᵇ∇ᵇ} P 𝐹) = cong₂ _│_ (swap∘push∘push P) (⊖₁-✓ 𝐹)
   ⊖₁-✓ (P │ᵇᶜ 𝐹) = cong₂ _│_ refl (⊖₁-✓ 𝐹)
   ⊖₁-✓ (P │ᶜᵇ 𝐹) = cong₂ _│_ refl (⊖₁-✓ 𝐹)
   ⊖₁-✓ (P │ᶜᶜ 𝐹) = cong₂ _│_ refl (⊖₁-✓ 𝐹)
   ⊖₁-✓ (P │ᵛᵛ 𝐹) = refl │₂ (⊖₁-✓ 𝐹)
   ⊖₁-✓ (_ᵇᵇ│_ {𝑎 = ˣ∇ˣ} 𝐸 _) = cong₂ _│_ (⊖₁-✓ 𝐸) refl
   ⊖₁-✓ (_ᵇᵇ│_ {𝑎 = ᵇ∇ᵇ} 𝐸 Q) = cong₂ _│_ (⊖₁-✓ 𝐸) (swap∘push∘push Q)
   ⊖₁-✓ (𝐸 ᵇᶜ│ Q) = cong₂ _│_ (⊖₁-✓ 𝐸) refl
   ⊖₁-✓ (𝐸 ᶜᵇ│ Q) = cong₂ _│_ (⊖₁-✓ 𝐸) refl
   ⊖₁-✓ (𝐸 ᶜᶜ│ Q) = cong₂ _│_ (⊖₁-✓ 𝐸) refl
   ⊖₁-✓ (𝐸 ᵛᵛ│ Q) = (⊖₁-✓ 𝐸) │₁ refl
   ⊖₁-✓ (𝐸 ➕₁ Q) = ⊖₁-✓ 𝐸
   ⊖₁-✓ (_│•_ {y = y} {z = z} 𝐸 𝐹) = cong₂ _│_ (
      let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      begin
         (pop z *) ((suc (pop y) *) S)
      ≡⟨ sym (pop-pop-swap y z _) ⟩
         (pop y *) ((suc (pop z) *) ((swap *) S))
      ≡⟨ cong (pop y *) (cong (suc (pop z) *) (⊖₁-✓ 𝐸)) ⟩
         (pop y *) ((suc (pop z) *) S′)
      ∎) (⊖₁-✓ 𝐹)
   ⊖₁-✓ (_│•ᵥ_ {y = y} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | _ = cong ν_ (cong₂ _│_ (
      let open EqReasoning (setoid _); S₁ = S (⊖₁ 𝐸); S′₁ = S′ (⊖₁ 𝐸) in
      begin
         (suc (pop y) *) S₁
      ≡⟨ cong (suc (pop y) *) (sym (swap-involutive _ )) ⟩
         (suc (pop y) *) ((swap *) ((swap *) S₁))
      ≡⟨ cong (suc (pop y) *) (cong (swap *) (⊖₁-✓ 𝐸)) ⟩
         (suc (pop y) *) ((swap *) S′₁)
      ≡⟨ suc-pop∘swap y _ ⟩
         (pop ((push *) y) *) S′₁
      ∎) (⊖₁-✓ 𝐹))
   ⊖₁-✓ (_│ᵥ•_ {y = y} 𝐸 𝐹) with (pop y *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | _ =
      let open EqReasoning (setoid _); S₁ = S (⊖₁ 𝐸); S′₁ = S′ (⊖₁ 𝐸) in
      cong ν_ (cong₂ _│_ (
         begin
            (pop (push y) *) S₁
         ≡⟨ sym (suc-pop∘swap y _) ⟩
            (suc (pop y) *) ((swap *) S₁)
         ≡⟨ cong (suc (pop y) *) (⊖₁-✓ 𝐸) ⟩
            (suc (pop y) *) S′₁
         ∎) (⊖₁-✓ 𝐹))
   ⊖₁-✓ (𝐸 │ᵥ 𝐹) =
      let open EqReasoning (setoid _); S₁ = S (⊖₁ 𝐸); S′₁ = S′ (⊖₁ 𝐸) in
      cong ν_ (cong₂ _│_ (
         begin
            (pop zero *) S₁
         ≡⟨ sym (pop-swap _) ⟩
            (pop zero *) ((swap *) S₁)
         ≡⟨ cong (pop zero *) (⊖₁-✓ 𝐸) ⟩
            (pop zero *) S′₁
         ∎) (⊖₁-✓ 𝐹))
   ⊖₁-✓ (𝐸 │ᵥ′ 𝐹) rewrite sym (⊖₁-✓ 𝐸) | sym (⊖₁-✓ 𝐹) = νν-swapᵣ _
   ⊖₁-✓ (ν• 𝐸) = ⊖₁-✓ 𝐸
   ⊖₁-✓ (ν•ᵇ 𝐸) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | _ = cong (swap *) (⊖₁-✓ 𝐸)
   ⊖₁-✓ (ν•ᶜ 𝐸) = ⊖₁-✓ 𝐸
   ⊖₁-✓ (νᵇᵇ_ {a = x •} {a} 𝐸) with (swap *ᵇ) (E/E′ (⊖₁ 𝐸)) | (swap *ᵇ) (E′/E (⊖₁ 𝐸))
   ... | swap*E/E′ | swap*E′/E rewrite swap∘push∘push x | swap∘push∘push a =
      cong ν_ (
         let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
         begin
            (suc swap *) ((swap *) ((suc swap *) S))
         ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
            (swap *) ((suc swap *) ((swap *) S))
         ≡⟨ cong (swap *) (cong (suc swap *) (⊖₁-✓ 𝐸)) ⟩
            (swap *) ((suc swap *) S′)
         ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {u •} 𝐸) = cong ν_ (
      let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≡⟨ cong (swap *) (cong (suc swap *) (⊖₁-✓ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νᵇᵇ_ {a = • x} {• u} 𝐸) = cong ν_ (
      let open EqReasoning (setoid _); S = S (⊖₁ 𝐸); S′ = S′ (⊖₁ 𝐸) in
      begin
         (suc swap *) ((swap *) ((suc swap *) S))
      ≡⟨ sym (swap∘suc-swap∘swap _) ⟩
         (swap *) ((suc swap *) ((swap *) S))
      ≡⟨ cong (swap *) (cong (suc swap *) (⊖₁-✓ 𝐸)) ⟩
         (swap *) ((suc swap *) S′)
      ∎)
   ⊖₁-✓ (νˣˣ 𝐸) = cong ν_ (cong (swap *) (⊖₁-✓ 𝐸))
   ⊖₁-✓ (νᵇᶜ_ {a′ = a′} 𝐸) with (swap *ᶜ) (E′/E (⊖₁ 𝐸))
   ... | _ rewrite swap∘push∘push a′ = cong ν_ (cong (swap *) (⊖₁-✓ 𝐸))
   ⊖₁-✓ (νᶜᵇ_ {a = a} 𝐸) with (swap *ᶜ) (E/E′ (⊖₁ 𝐸))
   ... | _ rewrite swap∘push∘push a = cong ν_ (cong (swap *) (⊖₁-✓ 𝐸))
   ⊖₁-✓ (νᶜᶜ 𝐸) = cong ν_ (⊖₁-✓ 𝐸)
   ⊖₁-✓ (νᵛᵛ 𝐸) = ν (⊖₁-✓ 𝐸)
   ⊖₁-✓ (! 𝐸) = ⊖₁-✓ 𝐸

   -- Now symmetrise.
   ⊖-✓ : ∀ {Γ P} {a a′ : Action Γ} {𝑎 : a ᴬ⌣ a′} {R R′} {E : P —[ a - _ ]→ R} {E′ : P —[ a′ - _ ]→ R′}
         (𝐸 : E ⌣[ 𝑎 ] E′) → ⋈[ Γ , 𝑎 , zero ] (S (⊖ 𝐸)) (subst Proc (sym (ᴬ⊖-✓ 𝑎)) (S′ (⊖ 𝐸)))
   ⊖-✓ (inj₁ 𝐸) = ⊖₁-✓ 𝐸
   ⊖-✓ (inj₂ 𝐸′) with ⊖₁ 𝐸′ | ⊖₁-✓ 𝐸′
   ⊖-✓ {𝑎 = ˣ∇ˣ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   ⊖-✓ {𝑎 = ᵇ∇ᵇ} (inj₂ 𝐸′) | E′/E ᵀΔ E/E′ | swap*S≡S′ =
      let open EqReasoning (setoid _); S = target E′/E; S′ = target E/E′ in
      begin
         (swap *) S′
      ≡⟨ cong (swap *) (sym swap*S≡S′) ⟩
         (swap *) ((swap *) S)
      ≡⟨ swap-involutive _ ⟩
         S
      ∎
   ⊖-✓ {𝑎 = ᵇ∇ᶜ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   ⊖-✓ {𝑎 = ᶜ∇ᵇ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   ⊖-✓ {𝑎 = ᶜ∇ᶜ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≡S′ = sym S≡S′
   ⊖-✓ {𝑎 = ᵛ∇ᵛ} (inj₂ 𝐸′) | _ ᵀΔ _ | S≈S′ = ≈-sym S≈S′
