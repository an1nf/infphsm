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

/-! ## Bases compuestas -/

abbrev bunion (B C : Base) : Base := fun r => B r ∨ C r

-- átomos como hechos
abbrev facts (T : List Atom) : Base := fun r => r.prems = [] ∧ r.concl ∈ T

abbrev ofList (L : List Rule) : Base := fun r => r ∈ L

-- hechos → contexto
theorem Deriv.facts_to_ctx {B : Base} {T : List Atom} {Γ : List Atom} {q : Atom}
    (d : Deriv (bunion B (facts T)) Γ q) : Deriv B (Γ ++ T) q := by
  induction d with
  | @ref Γ p hp => exact Deriv.ref (List.mem_append.mpr (Or.inl hp))
  | @app Γ r hr _ ih =>
    cases hr with
    | inl hB =>
      refine Deriv.app r hB (fun pq hpq => ?_)
      have h := ih pq hpq
      rw [List.append_assoc] at h
      exact h
    | inr hA => exact Deriv.ref (List.mem_append.mpr (Or.inr hA.2))

-- contexto → hechos
theorem Deriv.ctx_to_facts {C : Base} {Γ Δ : List Atom} {q : Atom}
    (d : Deriv C Δ q) : ∀ {P : List Atom}, (∀ t, t ∈ Δ → t ∈ P ∨ t ∈ Γ) →
      Deriv (bunion C (facts Γ)) P q := by
  induction d with
  | @ref Δ p hp =>
    intro P hP
    cases hP p hp with
    | inl h => exact Deriv.ref h
    | inr h => exact Deriv.app ⟨[], p⟩ (Or.inr ⟨rfl, h⟩) (by intro _ h'; cases h')
  | @app Δ r hr _ ih =>
    intro P hP
    refine Deriv.app r (Or.inl hr) (fun pq hpq => ih pq hpq ?_)
    intro t ht
    cases List.mem_append.mp ht with
    | inl h => exact Or.inl (List.mem_append.mpr (Or.inl h))
    | inr h =>
      cases hP t h with
      | inl h' => exact Or.inl (List.mem_append.mpr (Or.inr h'))
      | inr h' => exact Or.inr h'

-- corte sobre átomos
theorem Deriv.cut_atoms {B C : Base} (hBC : Ext B C) {Γ : List Atom} {q : Atom}
    (d : Deriv B Γ q) : ∀ {S : List Atom}, (∀ t, t ∈ Γ → t ∈ S ∨ Deriv C [] t) →
      Deriv C S q := by
  induction d with
  | @ref Γ p hp =>
    intro S hS
    cases hS p hp with
    | inl h => exact Deriv.ref h
    | inr h => exact Deriv.weaken h (fun _ hx => by cases hx)
  | @app Γ r hr _ ih =>
    intro S hS
    refine Deriv.app r (hBC r hr) (fun pq hpq => ih pq hpq ?_)
    intro t ht
    cases List.mem_append.mp ht with
    | inl h => exact Or.inl (List.mem_append.mpr (Or.inl h))
    | inr h =>
      cases hS t h with
      | inl h' => exact Or.inl (List.mem_append.mpr (Or.inr h'))
      | inr h' => exact Or.inr h'

-- adecuación atómica (Sandqvist, Lema 2.2)
theorem atomic_adequacy {B : Base} {T : List Atom} {u : Atom} :
    Deriv B T u ↔ ∀ C, Ext B C → (∀ t, t ∈ T → Deriv C [] t) → Deriv C [] u := by
  constructor
  · intro d C hBC hT
    exact Deriv.cut_atoms hBC d (fun t ht => Or.inr (hT t ht))
  · intro h
    have hC := h (bunion B (facts T)) (fun _ hr => Or.inl hr)
      (fun t ht => Deriv.app ⟨[], t⟩ (Or.inr ⟨rfl, ht⟩) (by intro _ h'; cases h'))
    exact Deriv.facts_to_ctx hC

/-! ## Reglas como fórmulas -/

-- φ₁ → … → φₙ → ψ
def impF : List Form → Form → Form
  | [],     ψ => ψ
  | φ :: L, ψ => .imp φ (impF L ψ)

theorem supp_impF (L : List Form) (ψ : Form) : ∀ {B : Base},
    supp B (impF L ψ) ↔ ∀ C, Ext B C → (∀ φ, φ ∈ L → supp C φ) → supp C ψ := by
  induction L with
  | nil =>
    intro B
    simp only [impF]
    constructor
    · intro h C hBC _; exact supp_mono ψ hBC h
    · intro h; exact h B (Ext.refl B) (fun _ hφ => by cases hφ)
  | cons φ L ih =>
    intro B
    simp only [impF, supp]
    constructor
    · intro h C hBC hL
      have h1 := h C hBC (hL φ (List.mem_cons.mpr (Or.inl rfl)))
      exact (ih.mp h1) C (Ext.refl C) (fun θ hθ => hL θ (List.mem_cons.mpr (Or.inr hθ)))
    · intro h C hBC hφ
      apply ih.mpr
      intro D hCD hL
      apply h D (Ext.trans hBC hCD)
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact supp_mono _ hCD hφ
      | inr h' => exact hL θ h'

-- (P ⇒ q) ↦ p₁ → … → q
def premForm (pq : List Atom × Atom) : Form := impF (pq.1.map Form.atom) (.atom pq.2)

theorem supp_prem (pq : List Atom × Atom) {C : Base} :
    supp C (premForm pq) ↔ Deriv C pq.1 pq.2 := by
  unfold premForm
  rw [supp_impF, atomic_adequacy]
  constructor
  · intro h D hCD hT
    have := h D hCD (fun φ hφ => by
      cases List.mem_map.mp hφ with
      | intro t ht =>
        cases ht with
        | intro htm e => subst e; simp only [supp]; exact hT t htm)
    simp only [supp] at this
    exact this
  · intro h D hCD hL
    simp only [supp]
    exact h D hCD (fun t ht => by
      have := hL (.atom t) (List.mem_map.mpr ⟨t, ht, rfl⟩)
      simp only [supp] at this
      exact this)

-- regla ↦ fórmula
def ruleForm (r : Rule) : Form := impF (r.prems.map premForm) (.atom r.concl)

-- admisible en toda extensión
def Adm (C : Base) (r : Rule) : Prop :=
  ∀ D, Ext C D → (∀ pq, pq ∈ r.prems → Deriv D pq.1 pq.2) → Deriv D [] r.concl

theorem supp_rule (r : Rule) {C : Base} : supp C (ruleForm r) ↔ Adm C r := by
  unfold ruleForm Adm
  rw [supp_impF]
  constructor
  · intro h D hCD hP
    have := h D hCD (fun φ hφ => by
      cases List.mem_map.mp hφ with
      | intro pq hpq =>
        cases hpq with
        | intro hm e => subst e; exact (supp_prem pq).mpr (hP pq hm))
    simp only [supp] at this
    exact this
  · intro h D hCD hL
    simp only [supp]
    exact h D hCD (fun pq hm => (supp_prem pq).mp (hL _ (List.mem_map.mpr ⟨pq, hm, rfl⟩)))

-- eliminación de reglas admisibles
theorem Deriv.elim_adm {B C : Base} {Sig : List Rule} (hBC : Ext B C)
    (hA : ∀ r, r ∈ Sig → Adm C r) {Γ : List Atom} {q : Atom}
    (d : Deriv (bunion B (ofList Sig)) Γ q) : Deriv C Γ q := by
  induction d with
  | @ref Γ p hp => exact Deriv.ref hp
  | @app Γ r hr _ ih =>
    cases hr with
    | inl hB => exact Deriv.app r (hBC r hB) ih
    | inr hS =>
      have hD : Deriv (bunion C (facts Γ)) [] r.concl :=
        hA r hS (bunion C (facts Γ)) (fun _ h => Or.inl h)
          (fun pq hpq => Deriv.ctx_to_facts (ih pq hpq) (fun t ht => List.mem_append.mp ht))
      exact Deriv.facts_to_ctx hD

/-! ## Exportación (conclusión atómica) -/

-- ⊢_{B ∪ Σ} p ⟺ ⊩_B Σ* → p
theorem export_atom (B : Base) (Sig : List Rule) (p : Atom) :
    Deriv (bunion B (ofList Sig)) [] p ↔ supp B (impF (Sig.map ruleForm) (.atom p)) := by
  rw [supp_impF]
  constructor
  · intro d C hBC hS
    simp only [supp]
    refine Deriv.elim_adm hBC ?_ d
    intro r hr
    exact (supp_rule r).mp (hS _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  · intro h
    have := h (bunion B (ofList Sig)) (fun _ hr => Or.inl hr) (fun φ hφ => by
      cases List.mem_map.mp hφ with
      | intro r hr =>
        cases hr with
        | intro hm e =>
          subst e
          apply (supp_rule r).mpr
          intro D hD hP
          exact Deriv.app r (hD r (Or.inr hm)) (fun pq hpq => by
            rw [List.append_nil]; exact hP pq hpq))
    simp only [supp] at this
    exact this

/-! ## Exportación general (Σ finito) -/

theorem Adm.mono {C D : Base} (h : Ext C D) {r : Rule} (ha : Adm C r) : Adm D r :=
  fun E hDE hP => ha E (Ext.trans h hDE) hP

theorem Ext.union {C D S : Base} (h : Ext C D) : Ext (bunion C S) (bunion D S) :=
  fun r hr => Or.elim hr (fun h' => Or.inl (h r h')) Or.inr

-- Σ admisible en C ⟹ (⊩_{C ∪ Σ} ψ → ⊩_C ψ)
theorem supp_elim_adm {Sig : List Rule} (ψ : Form) : ∀ {C : Base},
    (∀ r, r ∈ Sig → Adm C r) → supp (bunion C (ofList Sig)) ψ → supp C ψ := by
  induction ψ with
  | atom p =>
    intro C hA h
    simp only [supp] at h ⊢
    exact Deriv.elim_adm (Ext.refl C) hA h
  | bot =>
    intro C hA h
    simp only [supp] at h ⊢
    exact fun q => Deriv.elim_adm (Ext.refl C) hA (h q)
  | and φ ψ ih₁ ih₂ =>
    intro C hA h
    simp only [supp] at h ⊢
    exact ⟨ih₁ hA h.1, ih₂ hA h.2⟩
  | imp φ ψ _ ih₂ =>
    intro C hA h
    simp only [supp] at h ⊢
    intro D hCD hφ
    have hA' : ∀ r, r ∈ Sig → Adm D r := fun r hr => Adm.mono hCD (hA r hr)
    exact ih₂ hA' (h (bunion D (ofList Sig)) (Ext.union hCD)
      (supp_mono φ (fun _ h' => Or.inl h') hφ))
  | or φ ψ _ _ =>
    intro C hA h
    simp only [supp] at h ⊢
    intro D hCD p k₁ k₂
    have hA' : ∀ r, r ∈ Sig → Adm D r := fun r hr => Adm.mono hCD (hA r hr)
    have hp := h (bunion D (ofList Sig)) (Ext.union hCD) p
      (fun E hE hφ => k₁ E (Ext.trans (fun _ h' => Or.inl h') hE) hφ)
      (fun E hE hψ => k₂ E (Ext.trans (fun _ h' => Or.inl h') hE) hψ)
    exact Deriv.elim_adm (Ext.refl D) hA' hp

-- ⊩_{B ∪ Σ} χ ⟺ ⊩_B Σ* → χ, para toda χ
theorem export_all (B : Base) (Sig : List Rule) (χ : Form) :
    supp (bunion B (ofList Sig)) χ ↔ supp B (impF (Sig.map ruleForm) χ) := by
  rw [supp_impF]
  constructor
  · intro h C hBC hS
    have hA : ∀ r, r ∈ Sig → Adm C r :=
      fun r hr => (supp_rule r).mp (hS _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    exact supp_elim_adm χ hA (supp_mono χ (Ext.union hBC) h)
  · intro h
    exact h (bunion B (ofList Sig)) (fun _ hr => Or.inl hr) (fun φ hφ => by
      cases List.mem_map.mp hφ with
      | intro r hr =>
        cases hr with
        | intro hm e =>
          subst e
          apply (supp_rule r).mpr
          intro D hD hP
          exact Deriv.app r (hD r (Or.inr hm)) (fun pq hpq => by
            rw [List.append_nil]; exact hP pq hpq))

abbrev emptyB : Base := fun _ => False

/-! ## Inferones -/

-- ⟨⟨P, 𝒫, b⟩⟩; polaridad codificada en el átomo
structure Inferon where
  a   : Atom
  loc : List Rule

-- (At), Collinson–Eckhardt–Pym
def suppInf (B : Base) (ι : Inferon) : Prop := Deriv (bunion B (ofList ι.loc)) [] ι.a

-- 𝒫* → ⟨P, b⟩
def Inferon.form (ι : Inferon) : Form := impF (ι.loc.map ruleForm) (.atom ι.a)

-- inferón = fórmula de IPL
theorem inferon_definable (B : Base) (ι : Inferon) : suppInf B ι ↔ supp B ι.form :=
  export_atom B ι.loc ι.a

/-! ## Completitud -/

-- plan: aplanamiento φ ↦ φ♭, base 𝒩, lemas puente
theorem completeness {Γ : List Form} {φ : Form} : valid Γ φ → NJ Γ φ := by
  sorry

/-! ## Bases finitas -/

-- Σ finito: ⊩_Σ χ ⟺ ⊢_NJ Σ* → χ  (condicional: completeness)
theorem finite_base_export (Sig : List Rule) (χ : Form) :
    supp (bunion emptyB (ofList Sig)) χ ↔ NJ [] (impF (Sig.map ruleForm) χ) := by
  rw [export_all]
  constructor
  · intro h
    exact completeness (fun B _ => supp_mono _ (fun _ hr => False.elim hr) h)
  · intro d
    exact soundness d emptyB (fun _ hθ => by cases hθ)

end BeS
