/-
  B-eS de Sandqvist (2015) para IPL.
  LF: base = signatura, contexto = átomos del sitio, derivación = término.
-/

namespace BeS

abbrev Atom := Nat

-- ((P₁ ⇒ q₁), …, (Pₙ ⇒ qₙ)) ⇒ r
structure Rule where
  prems : List (List Atom × Atom)
  concl : Atom

abbrev Base := Rule → Prop

abbrev Ext (B C : Base) : Prop := ∀ r, B r → C r

theorem Ext.refl (B : Base) : Ext B B := fun _ h => h

theorem Ext.trans {B C D : Base} (h₁ : Ext B C) (h₂ : Ext C D) : Ext B D :=
  fun r h => h₂ r (h₁ r h)

/-! ## Derivabilidad atómica -/

inductive Deriv (B : Base) : List Atom → Atom → Prop where
  | ref {S : List Atom} {p : Atom} : p ∈ S → Deriv B S p                    -- (Ref)
  | app {S : List Atom} (r : Rule) : B r →
      (∀ pq, pq ∈ r.prems → Deriv B (pq.1 ++ S) pq.2) → Deriv B S r.concl  -- (App)

-- monotonía en la base
theorem Deriv.mono {B C : Base} (h : Ext B C) {S : List Atom} {p : Atom}
    (d : Deriv B S p) : Deriv C S p := by
  induction d with
  | @ref S p hp => exact Deriv.ref hp
  | @app S r hr _ ih => exact Deriv.app r (h r hr) ih

-- debilitamiento
theorem Deriv.weaken {B : Base} {S : List Atom} {p : Atom}
    (d : Deriv B S p) : ∀ {T : List Atom}, S ⊆ T → Deriv B T p := by
  induction d with
  | @ref S p hp => intro T hST; exact Deriv.ref (hST hp)
  | @app S r hr _ ih =>
    intro T hST
    refine Deriv.app r hr (fun pq hpq => ih pq hpq ?_)
    intro x hx
    cases List.mem_append.mp hx with
    | inl h => exact List.mem_append.mpr (Or.inl h)
    | inr h => exact List.mem_append.mpr (Or.inr (hST h))

/-! ## Soporte -/

inductive Form where
  | atom : Atom → Form
  | bot  : Form
  | and  : Form → Form → Form
  | or   : Form → Form → Form
  | imp  : Form → Form → Form

def supp : Base → Form → Prop
  | B, .atom p  => Deriv B [] p
  | B, .bot     => ∀ p, Deriv B [] p
  | B, .and φ ψ => supp B φ ∧ supp B ψ
  | B, .imp φ ψ => ∀ C, Ext B C → supp C φ → supp C ψ
  | B, .or φ ψ  => ∀ C, Ext B C → ∀ p : Atom,          -- Church / CPS sobre átomos
      (∀ D, Ext C D → supp D φ → Deriv D [] p) →
      (∀ D, Ext C D → supp D ψ → Deriv D [] p) → Deriv C [] p

-- monotonía (Sandqvist, Lema 2)
theorem supp_mono (φ : Form) : ∀ {B C : Base}, Ext B C → supp B φ → supp C φ := by
  induction φ with
  | atom p =>
    intro B C h hs; simp only [supp] at hs ⊢; exact Deriv.mono h hs
  | bot =>
    intro B C h hs; simp only [supp] at hs ⊢; exact fun q => Deriv.mono h (hs q)
  | and φ ψ ih₁ ih₂ =>
    intro B C h hs; simp only [supp] at hs ⊢; exact ⟨ih₁ h hs.1, ih₂ h hs.2⟩
  | imp φ ψ _ _ =>
    intro B C h hs; simp only [supp] at hs ⊢
    exact fun D hCD => hs D (Ext.trans h hCD)
  | or φ ψ _ _ =>
    intro B C h hs; simp only [supp] at hs ⊢
    exact fun D hCD => hs D (Ext.trans h hCD)

/-! ## Eliminaciones generalizadas -/

-- ex falso: ⊥ ⊩ χ
theorem bot_elim (χ : Form) : ∀ {B : Base}, supp B .bot → supp B χ := by
  induction χ with
  | atom p => intro B hb; simp only [supp] at hb ⊢; exact hb p
  | bot => intro B hb; exact hb
  | and χ₁ χ₂ ih₁ ih₂ =>
    intro B hb; simp only [supp]; exact ⟨ih₁ hb, ih₂ hb⟩
  | imp χ₁ χ₂ _ ih₂ =>
    intro B hb; simp only [supp]
    intro C hBC _
    exact ih₂ (supp_mono .bot hBC hb)
  | or χ₁ χ₂ _ _ =>
    intro B hb; simp only [supp]
    intro C hBC p _ _
    have hC := supp_mono .bot hBC hb
    simp only [supp] at hC
    exact hC p

-- ∨E para χ arbitraria (Sandqvist, Lema 3)
theorem or_elim (φ ψ χ : Form) : ∀ {B : Base},
    supp B (.or φ ψ) →
    (∀ C, Ext B C → supp C φ → supp C χ) →
    (∀ C, Ext B C → supp C ψ → supp C χ) →
    supp B χ := by
  induction χ with
  | atom p =>
    intro B hor h₁ h₂
    simp only [supp] at hor h₁ h₂ ⊢
    exact hor B (Ext.refl B) p h₁ h₂
  | bot =>
    intro B hor h₁ h₂
    simp only [supp] at hor h₁ h₂ ⊢
    intro q
    exact hor B (Ext.refl B) q
      (fun D hD hφ => h₁ D hD hφ q) (fun D hD hψ => h₂ D hD hψ q)
  | and χ₁ χ₂ ih₁ ih₂ =>
    intro B hor h₁ h₂
    simp only [supp] at h₁ h₂ ⊢
    exact ⟨ih₁ hor (fun C hC hφ => (h₁ C hC hφ).1) (fun C hC hψ => (h₂ C hC hψ).1),
           ih₂ hor (fun C hC hφ => (h₁ C hC hφ).2) (fun C hC hψ => (h₂ C hC hψ).2)⟩
  | imp χ₁ χ₂ _ ih₂ =>
    intro B hor h₁ h₂
    simp only [supp] at h₁ h₂ ⊢
    intro C hBC hχ₁
    apply ih₂ (supp_mono (.or φ ψ) hBC hor)
    · intro D hCD hφ
      exact h₁ D (Ext.trans hBC hCD) hφ D (Ext.refl D) (supp_mono χ₁ hCD hχ₁)
    · intro D hCD hψ
      exact h₂ D (Ext.trans hBC hCD) hψ D (Ext.refl D) (supp_mono χ₁ hCD hχ₁)
  | or χ₁ χ₂ _ _ =>
    intro B hor h₁ h₂
    simp only [supp] at hor h₁ h₂ ⊢
    intro C hBC p k₁ k₂
    apply hor C hBC p
    · intro D hCD hφ
      exact h₁ D (Ext.trans hBC hCD) hφ D (Ext.refl D) p
        (fun E hDE => k₁ E (Ext.trans hCD hDE)) (fun E hDE => k₂ E (Ext.trans hCD hDE))
    · intro D hCD hψ
      exact h₂ D (Ext.trans hBC hCD) hψ D (Ext.refl D) p
        (fun E hDE => k₁ E (Ext.trans hCD hDE)) (fun E hDE => k₂ E (Ext.trans hCD hDE))

/-! ## NJ y validez -/

inductive NJ : List Form → Form → Prop where
  | hyp   {Γ φ}     : φ ∈ Γ → NJ Γ φ
  | andI  {Γ φ ψ}   : NJ Γ φ → NJ Γ ψ → NJ Γ (.and φ ψ)
  | andE₁ {Γ φ ψ}   : NJ Γ (.and φ ψ) → NJ Γ φ
  | andE₂ {Γ φ ψ}   : NJ Γ (.and φ ψ) → NJ Γ ψ
  | impI  {Γ φ ψ}   : NJ (φ :: Γ) ψ → NJ Γ (.imp φ ψ)
  | impE  {Γ φ ψ}   : NJ Γ (.imp φ ψ) → NJ Γ φ → NJ Γ ψ
  | orI₁  {Γ φ ψ}   : NJ Γ φ → NJ Γ (.or φ ψ)
  | orI₂  {Γ φ ψ}   : NJ Γ ψ → NJ Γ (.or φ ψ)
  | orE   {Γ φ ψ χ} : NJ Γ (.or φ ψ) → NJ (φ :: Γ) χ → NJ (ψ :: Γ) χ → NJ Γ χ
  | botE  {Γ φ}     : NJ Γ .bot → NJ Γ φ

-- Γ ⊩ φ; equivalente a Sandqvist por monotonía
abbrev valid (Γ : List Form) (φ : Form) : Prop :=
  ∀ B, (∀ θ, θ ∈ Γ → supp B θ) → supp B φ

/-! ## Corrección -/

theorem soundness {Γ : List Form} {φ : Form} (d : NJ Γ φ) : valid Γ φ := by
  induction d with
  | @hyp Γ φ h => intro B hΓ; exact hΓ φ h
  | @andI Γ φ ψ _ _ ih₁ ih₂ =>
    intro B hΓ; simp only [supp]; exact ⟨ih₁ B hΓ, ih₂ B hΓ⟩
  | @andE₁ Γ φ ψ _ ih =>
    intro B hΓ; have h := ih B hΓ; simp only [supp] at h; exact h.1
  | @andE₂ Γ φ ψ _ ih =>
    intro B hΓ; have h := ih B hΓ; simp only [supp] at h; exact h.2
  | @impI Γ φ ψ _ ih =>
    intro B hΓ; simp only [supp]
    intro C hBC hφ
    apply ih C
    intro θ hθ
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact hφ
    | inr h => exact supp_mono θ hBC (hΓ θ h)
  | @impE Γ φ ψ _ _ ih₁ ih₂ =>
    intro B hΓ; have h := ih₁ B hΓ; simp only [supp] at h
    exact h B (Ext.refl B) (ih₂ B hΓ)
  | @orI₁ Γ φ ψ _ ih =>
    intro B hΓ; simp only [supp]
    intro C hBC p k₁ _
    exact k₁ C (Ext.refl C) (supp_mono φ hBC (ih B hΓ))
  | @orI₂ Γ φ ψ _ ih =>
    intro B hΓ; simp only [supp]
    intro C hBC p _ k₂
    exact k₂ C (Ext.refl C) (supp_mono ψ hBC (ih B hΓ))
  | @orE Γ φ ψ χ _ _ _ ih₀ ih₁ ih₂ =>
    intro B hΓ
    apply or_elim φ ψ χ (ih₀ B hΓ)
    · intro C hBC hφ
      apply ih₁ C
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hφ
      | inr h => exact supp_mono θ hBC (hΓ θ h)
    · intro C hBC hψ
      apply ih₂ C
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hψ
      | inr h => exact supp_mono θ hBC (hΓ θ h)
  | @botE Γ φ _ ih =>
    intro B hΓ; exact bot_elim φ (ih B hΓ)

/-! ## Completitud -/

-- plan: aplanamiento φ ↦ φ♭, base 𝒩, lemas puente
theorem completeness {Γ : List Form} {φ : Form} : valid Γ φ → NJ Γ φ := by
  sorry

end BeS
