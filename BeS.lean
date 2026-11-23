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
  deriving DecidableEq

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

/-! ## Completitud: subfórmulas -/

def subs : Form → List Form
  | .atom p  => [.atom p]
  | .bot     => [.bot]
  | .and a b => .and a b :: (subs a ++ subs b)
  | .or a b  => .or a b :: (subs a ++ subs b)
  | .imp a b => .imp a b :: (subs a ++ subs b)

theorem mem0 {α : Type} {x : α} {l : List α} : x ∈ x :: l := List.mem_cons.mpr (Or.inl rfl)
theorem mem1 {α : Type} {x y : α} {l : List α} : y ∈ x :: y :: l := List.mem_cons.mpr (Or.inr mem0)
theorem mem2 {α : Type} {x y z : α} {l : List α} : z ∈ x :: y :: z :: l :=
  List.mem_cons.mpr (Or.inr mem1)

theorem self_mem_subs (χ : Form) : χ ∈ subs χ := by
  cases χ <;> exact mem0

theorem sub_l {χ a b : Form} (h : subs χ = χ :: (subs a ++ subs b)) : a ∈ subs χ := by
  rw [h]; exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (self_mem_subs a))))

theorem sub_r {χ a b : Form} (h : subs χ = χ :: (subs a ++ subs b)) : b ∈ subs χ := by
  rw [h]; exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (self_mem_subs b))))

theorem subs_trans_bin {χ a b θ ζ : Form} (hs : subs χ = χ :: (subs a ++ subs b))
    (iha : ∀ θ, θ ∈ subs a → ∀ ζ, ζ ∈ subs θ → ζ ∈ subs a)
    (ihb : ∀ θ, θ ∈ subs b → ∀ ζ, ζ ∈ subs θ → ζ ∈ subs b)
    (hθ : θ ∈ subs χ) (hζ : ζ ∈ subs θ) : ζ ∈ subs χ := by
  rw [hs] at hθ ⊢
  cases List.mem_cons.mp hθ with
  | inl e => subst e; rw [hs] at hζ; exact hζ
  | inr h =>
    cases List.mem_append.mp h with
    | inl h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (iha θ h' ζ hζ))))
    | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (ihb θ h' ζ hζ))))

-- transitividad de subfórmula
theorem subs_trans (χ : Form) : ∀ θ, θ ∈ subs χ → ∀ ζ, ζ ∈ subs θ → ζ ∈ subs χ := by
  induction χ with
  | atom p =>
    intro θ hθ ζ hζ
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact hζ
    | inr h => cases h
  | bot =>
    intro θ hθ ζ hζ
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact hζ
    | inr h => cases h
  | and a b iha ihb => intro θ hθ ζ hζ; exact subs_trans_bin rfl iha ihb hθ hζ
  | or a b iha ihb => intro θ hθ ζ hζ; exact subs_trans_bin rfl iha ihb hθ hζ
  | imp a b iha ihb => intro θ hθ ζ hζ; exact subs_trans_bin rfl iha ihb hθ hζ

def subsL : List Form → List Form
  | []     => []
  | θ :: L => subs θ ++ subsL L

abbrev Closed (Ξ : List Form) : Prop := ∀ χ, χ ∈ Ξ → ∀ ζ, ζ ∈ subs χ → ζ ∈ Ξ

theorem mem_subsL_of {θ : Form} (L : List Form) (h : θ ∈ L) : θ ∈ subsL L := by
  induction L with
  | nil => cases h
  | cons y L ih =>
    cases List.mem_cons.mp h with
    | inl e => subst e; exact List.mem_append.mpr (Or.inl (self_mem_subs _))
    | inr h' => exact List.mem_append.mpr (Or.inr (ih h'))

theorem subsL_closed (L : List Form) : Closed (subsL L) := by
  induction L with
  | nil => intro χ h; cases h
  | cons y L ih =>
    intro χ hχ ζ hζ
    cases List.mem_append.mp hχ with
    | inl h => exact List.mem_append.mpr (Or.inl (subs_trans y χ h ζ hζ))
    | inr h => exact List.mem_append.mpr (Or.inr (ih χ h ζ hζ))

/-! ## Completitud: aplanamiento -/

-- cota de átomos
def sumAt : Form → Nat
  | .atom p  => p
  | .bot     => 0
  | .and a b => sumAt a + sumAt b
  | .or a b  => sumAt a + sumAt b
  | .imp a b => sumAt a + sumAt b

def sumAtL : List Form → Nat
  | []     => 0
  | θ :: L => sumAt θ + sumAtL L

theorem le_bin {p : Atom} {χ a b : Form} (hs : subs χ = χ :: (subs a ++ subs b))
    (hn : sumAt χ = sumAt a + sumAt b)
    (iha : Form.atom p ∈ subs a → p ≤ sumAt a) (ihb : Form.atom p ∈ subs b → p ≤ sumAt b)
    (hne : Form.atom p ≠ χ) : Form.atom p ∈ subs χ → p ≤ sumAt χ := by
  intro h
  rw [hs] at h
  rw [hn]
  cases List.mem_cons.mp h with
  | inl e => exact absurd e hne
  | inr h' =>
    cases List.mem_append.mp h' with
    | inl h'' => exact Nat.le_trans (iha h'') (Nat.le_add_right _ _)
    | inr h'' => exact Nat.le_trans (ihb h'') (Nat.le_add_left _ _)

theorem atom_le_sumAt (p : Atom) (χ : Form) : Form.atom p ∈ subs χ → p ≤ sumAt χ := by
  induction χ with
  | atom q =>
    intro h
    cases List.mem_cons.mp h with
    | inl e => cases e; exact Nat.le_refl _
    | inr h' => cases h'
  | bot =>
    intro h
    cases List.mem_cons.mp h with
    | inl e => cases e
    | inr h' => cases h'
  | and a b iha ihb => exact le_bin rfl rfl iha ihb (by intro e; cases e)
  | or a b iha ihb => exact le_bin rfl rfl iha ihb (by intro e; cases e)
  | imp a b iha ihb => exact le_bin rfl rfl iha ihb (by intro e; cases e)

theorem atom_le_sumAtL (p : Atom) (L : List Form) (h : Form.atom p ∈ subsL L) :
    p ≤ sumAtL L := by
  induction L with
  | nil => cases h
  | cons θ L ih =>
    cases List.mem_append.mp h with
    | inl h' => exact Nat.le_trans (atom_le_sumAt p θ h') (Nat.le_add_right _ _)
    | inr h' => exact Nat.le_trans (ih h') (Nat.le_add_left _ _)

def idx : List Form → Form → Nat
  | [],     _ => 0
  | θ :: L, χ => if θ = χ then 0 else idx L χ + 1

def nth : List Form → Nat → Option Form
  | [],     _     => none
  | θ :: _, 0     => some θ
  | _ :: L, n + 1 => nth L n

theorem nth_idx (χ : Form) (L : List Form) (h : χ ∈ L) : nth L (idx L χ) = some χ := by
  induction L with
  | nil => cases h
  | cons θ L ih =>
    by_cases e : θ = χ
    · rw [idx, ite_eq_left e, nth, e]
    · rw [idx, ite_eq_right e, nth]
      cases List.mem_cons.mp h with
      | inl h' => exact absurd h'.symm e
      | inr h' => exact ih h'

-- φ♭: identidad en átomos, fresco en compuestas
def flat (M : Nat) (Ξ : List Form) : Form → Atom
  | .atom p => p
  | χ       => M + 1 + idx Ξ χ

-- p♮
def unflat (M : Nat) (Ξ : List Form) (a : Atom) : Form :=
  if M < a then (nth Ξ (a - M - 1)).getD (.atom a) else .atom a

theorem unflat_cx {M : Nat} {Ξ : List Form} {χ : Form} (hχ : χ ∈ Ξ) :
    unflat M Ξ (M + 1 + idx Ξ χ) = χ := by
  have h : M < M + 1 + idx Ξ χ := by omega
  have e : M + 1 + idx Ξ χ - M - 1 = idx Ξ χ := by omega
  unfold unflat
  rw [ite_eq_left h, e, nth_idx χ Ξ hχ, Option.getD_some]

-- (φ♭)♮ = φ
theorem unflat_flat {M : Nat} {Ξ : List Form} (hM : ∀ p, Form.atom p ∈ Ξ → p ≤ M)
    (χ : Form) (hχ : χ ∈ Ξ) : unflat M Ξ (flat M Ξ χ) = χ := by
  cases χ with
  | atom p =>
    have hp := hM p hχ
    have h : ¬ M < p := Nat.not_lt.mpr hp
    show unflat M Ξ p = Form.atom p
    unfold unflat
    rw [ite_eq_right h]
  | bot => exact unflat_cx hχ
  | and a b => exact unflat_cx hχ
  | or a b => exact unflat_cx hχ
  | imp a b => exact unflat_cx hχ

/-! ## Completitud: base 𝒩 -/

-- reglas de 𝒩 para χ
def nRule (fl : Form → Atom) : Form → Rule → Prop
  | .atom _,  _ => False
  | .bot,     r => ∃ p, r = ⟨[([], fl .bot)], p⟩
  | .and a b, r => r = ⟨[([], fl a), ([], fl b)], fl (.and a b)⟩ ∨
                   r = ⟨[([], fl (.and a b))], fl a⟩ ∨
                   r = ⟨[([], fl (.and a b))], fl b⟩
  | .imp a b, r => r = ⟨[([fl a], fl b)], fl (.imp a b)⟩ ∨
                   r = ⟨[([], fl (.imp a b)), ([], fl a)], fl b⟩
  | .or a b,  r => r = ⟨[([], fl a)], fl (.or a b)⟩ ∨
                   r = ⟨[([], fl b)], fl (.or a b)⟩ ∨
                   ∃ p, r = ⟨[([], fl (.or a b)), ([fl a], p), ([fl b], p)], p⟩

abbrev NBase (fl : Form → Atom) (Ξ : List Form) : Base :=
  fun r => ∃ χ, χ ∈ Ξ ∧ nRule fl χ r

theorem Deriv.app1 {B : Base} {S P₁ : List Atom} {q₁ r : Atom}
    (hr : B ⟨[(P₁, q₁)], r⟩) (h₁ : Deriv B (P₁ ++ S) q₁) : Deriv B S r :=
  Deriv.app ⟨[(P₁, q₁)], r⟩ hr (fun pq hpq => by
    cases hpq with
    | head => exact h₁
    | tail _ h => cases h)

theorem Deriv.app2 {B : Base} {S P₁ P₂ : List Atom} {q₁ q₂ r : Atom}
    (hr : B ⟨[(P₁, q₁), (P₂, q₂)], r⟩) (h₁ : Deriv B (P₁ ++ S) q₁)
    (h₂ : Deriv B (P₂ ++ S) q₂) : Deriv B S r :=
  Deriv.app ⟨[(P₁, q₁), (P₂, q₂)], r⟩ hr (fun pq hpq => by
    cases hpq with
    | head => exact h₁
    | tail _ h =>
      cases h with
      | head => exact h₂
      | tail _ h' => cases h')

theorem Deriv.app3 {B : Base} {S P₁ P₂ P₃ : List Atom} {q₁ q₂ q₃ r : Atom}
    (hr : B ⟨[(P₁, q₁), (P₂, q₂), (P₃, q₃)], r⟩) (h₁ : Deriv B (P₁ ++ S) q₁)
    (h₂ : Deriv B (P₂ ++ S) q₂) (h₃ : Deriv B (P₃ ++ S) q₃) : Deriv B S r :=
  Deriv.app ⟨[(P₁, q₁), (P₂, q₂), (P₃, q₃)], r⟩ hr (fun pq hpq => by
    cases hpq with
    | head => exact h₁
    | tail _ h =>
      cases h with
      | head => exact h₂
      | tail _ h' =>
        cases h' with
        | head => exact h₃
        | tail _ h'' => cases h'')

/-! ## Completitud: (†) -/

-- ⊩_C χ ⟺ ⊢_C χ♭, para C ⊇ 𝒩
theorem dagger {fl : Form → Atom} (hfl : ∀ p, fl (.atom p) = p) {Ξ : List Form}
    (hcl : Closed Ξ) (χ : Form) : χ ∈ Ξ → ∀ {C : Base}, Ext (NBase fl Ξ) C →
      (supp C χ ↔ Deriv C [] (fl χ)) := by
  induction χ with
  | atom p =>
    intro _ C _
    simp only [supp, hfl]
  | bot =>
    intro hχ C hNC
    simp only [supp]
    constructor
    · intro h; exact h _
    · intro h p; exact Deriv.app1 (hNC _ ⟨.bot, hχ, ⟨p, rfl⟩⟩) h
  | and a b iha ihb =>
    intro hχ C hNC
    have ha := hcl _ hχ a (sub_l rfl)
    have hb := hcl _ hχ b (sub_r rfl)
    simp only [supp]
    constructor
    · intro h
      exact Deriv.app2 (hNC _ ⟨.and a b, hχ, Or.inl rfl⟩)
        ((iha ha hNC).mp h.1) ((ihb hb hNC).mp h.2)
    · intro h
      exact ⟨(iha ha hNC).mpr (Deriv.app1 (hNC _ ⟨.and a b, hχ, Or.inr (Or.inl rfl)⟩) h),
             (ihb hb hNC).mpr (Deriv.app1 (hNC _ ⟨.and a b, hχ, Or.inr (Or.inr rfl)⟩) h)⟩
  | imp a b iha ihb =>
    intro hχ C hNC
    have ha := hcl _ hχ a (sub_l rfl)
    have hb := hcl _ hχ b (sub_r rfl)
    simp only [supp]
    constructor
    · intro h
      refine Deriv.app1 (hNC _ ⟨.imp a b, hχ, Or.inl rfl⟩) ?_
      show Deriv C [fl a] (fl b)
      rw [atomic_adequacy]
      intro D hCD hT
      have hND := Ext.trans hNC hCD
      exact (ihb hb hND).mp (h D hCD ((iha ha hND).mpr (hT _ mem0)))
    · intro h D hCD hDa
      have hND := Ext.trans hNC hCD
      exact (ihb hb hND).mpr (Deriv.app2 (hND _ ⟨.imp a b, hχ, Or.inr rfl⟩)
        (Deriv.mono hCD h) ((iha ha hND).mp hDa))
  | or a b iha ihb =>
    intro hχ C hNC
    have ha := hcl _ hχ a (sub_l rfl)
    have hb := hcl _ hχ b (sub_r rfl)
    simp only [supp]
    constructor
    · intro h
      exact h C (Ext.refl C) (fl (.or a b))
        (fun E hCE hEa => Deriv.app1 (Ext.trans hNC hCE _ ⟨.or a b, hχ, Or.inl rfl⟩)
          ((iha ha (Ext.trans hNC hCE)).mp hEa))
        (fun E hCE hEb => Deriv.app1 (Ext.trans hNC hCE _ ⟨.or a b, hχ, Or.inr (Or.inl rfl)⟩)
          ((ihb hb (Ext.trans hNC hCE)).mp hEb))
    · intro h D hCD p k₁ k₂
      have hND := Ext.trans hNC hCD
      refine Deriv.app3 (hND _ ⟨.or a b, hχ, Or.inr (Or.inr ⟨p, rfl⟩)⟩) (Deriv.mono hCD h) ?_ ?_
      · show Deriv D [fl a] p
        rw [atomic_adequacy]
        intro E hDE hT
        exact k₁ E hDE ((iha ha (Ext.trans hND hDE)).mpr (hT _ mem0))
      · show Deriv D [fl b] p
        rw [atomic_adequacy]
        intro E hDE hT
        exact k₂ E hDE ((ihb hb (Ext.trans hND hDE)).mpr (hT _ mem0))

/-! ## Completitud: (††) -/

-- ⊢_𝒩 ⟹ ⊢_NJ, vía ♮
theorem simulation {fl : Form → Atom} {un : Atom → Form} {Ξ : List Form}
    (hcl : Closed Ξ) (hun : ∀ χ, χ ∈ Ξ → un (fl χ) = χ) {S : List Atom} {q : Atom}
    (d : Deriv (NBase fl Ξ) S q) : NJ (S.map un) (un q) := by
  induction d with
  | @ref S p hp => exact NJ.hyp (List.mem_map.mpr ⟨p, hp, rfl⟩)
  | @app S r hr _ ih =>
    cases hr with
    | intro χ hχr =>
      cases hχr with
      | intro hχ hrule =>
        cases χ with
        | atom p => exact False.elim hrule
        | bot =>
          cases hrule with
          | intro p e =>
            subst e
            have h₀ : NJ (S.map un) (un (fl .bot)) := ih _ mem0
            rw [hun _ hχ] at h₀
            exact NJ.botE h₀
        | and a b =>
          have ha := hcl _ hχ a (sub_l rfl)
          have hb := hcl _ hχ b (sub_r rfl)
          cases hrule with
          | inl e =>
            subst e
            have h₁ : NJ (S.map un) (un (fl a)) := ih _ mem0
            have h₂ : NJ (S.map un) (un (fl b)) := ih _ mem1
            rw [hun _ ha] at h₁
            rw [hun _ hb] at h₂
            show NJ (S.map un) (un (fl (.and a b)))
            rw [hun _ hχ]
            exact NJ.andI h₁ h₂
          | inr e' =>
            cases e' with
            | inl e =>
              subst e
              have h₀ : NJ (S.map un) (un (fl (.and a b))) := ih _ mem0
              rw [hun _ hχ] at h₀
              show NJ (S.map un) (un (fl a))
              rw [hun _ ha]
              exact NJ.andE₁ h₀
            | inr e =>
              subst e
              have h₀ : NJ (S.map un) (un (fl (.and a b))) := ih _ mem0
              rw [hun _ hχ] at h₀
              show NJ (S.map un) (un (fl b))
              rw [hun _ hb]
              exact NJ.andE₂ h₀
        | imp a b =>
          have ha := hcl _ hχ a (sub_l rfl)
          have hb := hcl _ hχ b (sub_r rfl)
          cases hrule with
          | inl e =>
            subst e
            have h₁ : NJ (un (fl a) :: S.map un) (un (fl b)) := ih _ mem0
            rw [hun _ ha, hun _ hb] at h₁
            show NJ (S.map un) (un (fl (.imp a b)))
            rw [hun _ hχ]
            exact NJ.impI h₁
          | inr e =>
            subst e
            have h₀ : NJ (S.map un) (un (fl (.imp a b))) := ih _ mem0
            have h₁ : NJ (S.map un) (un (fl a)) := ih _ mem1
            rw [hun _ hχ] at h₀
            rw [hun _ ha] at h₁
            show NJ (S.map un) (un (fl b))
            rw [hun _ hb]
            exact NJ.impE h₀ h₁
        | or a b =>
          have ha := hcl _ hχ a (sub_l rfl)
          have hb := hcl _ hχ b (sub_r rfl)
          cases hrule with
          | inl e =>
            subst e
            have h₁ : NJ (S.map un) (un (fl a)) := ih _ mem0
            rw [hun _ ha] at h₁
            show NJ (S.map un) (un (fl (.or a b)))
            rw [hun _ hχ]
            exact NJ.orI₁ h₁
          | inr e' =>
            cases e' with
            | inl e =>
              subst e
              have h₁ : NJ (S.map un) (un (fl b)) := ih _ mem0
              rw [hun _ hb] at h₁
              show NJ (S.map un) (un (fl (.or a b)))
              rw [hun _ hχ]
              exact NJ.orI₂ h₁
            | inr e =>
              cases e with
              | intro p e =>
                subst e
                have h₀ : NJ (S.map un) (un (fl (.or a b))) := ih _ mem0
                have h₁ : NJ (un (fl a) :: S.map un) (un p) := ih _ mem1
                have h₂ : NJ (un (fl b) :: S.map un) (un p) := ih _ mem2
                rw [hun _ hχ] at h₀
                rw [hun _ ha] at h₁
                rw [hun _ hb] at h₂
                exact NJ.orE h₀ h₁ h₂

/-! ## Completitud -/

def Xi (Γ : List Form) (φ : Form) : List Form := subsL (φ :: Γ)

def bnd (Γ : List Form) (φ : Form) : Nat := sumAtL (φ :: Γ)

theorem map_inv {fl : Form → Atom} {un : Atom → Form} (L : List Form)
    (h : ∀ x, x ∈ L → un (fl x) = x) : (L.map fl).map un = L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map]
    rw [h x mem0, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

-- Sandqvist 2015, Teorema 1 (⇐)
theorem completeness {Γ : List Form} {φ : Form} : valid Γ φ → NJ Γ φ := by
  intro hv
  have hcl : Closed (Xi Γ φ) := subsL_closed _
  have hM : ∀ p, Form.atom p ∈ Xi Γ φ → p ≤ bnd Γ φ := fun p h => atom_le_sumAtL p _ h
  have hun : ∀ χ, χ ∈ Xi Γ φ →
      unflat (bnd Γ φ) (Xi Γ φ) (flat (bnd Γ φ) (Xi Γ φ) χ) = χ := unflat_flat hM
  have hφ : φ ∈ Xi Γ φ := mem_subsL_of _ mem0
  have hΓ : ∀ θ, θ ∈ Γ → θ ∈ Xi Γ φ :=
    fun θ h => mem_subsL_of _ (List.mem_cons.mpr (Or.inr h))
  -- Γ♭ ⊢_𝒩 φ♭
  have hd : Deriv (NBase (flat (bnd Γ φ) (Xi Γ φ)) (Xi Γ φ))
      (Γ.map (flat (bnd Γ φ) (Xi Γ φ))) (flat (bnd Γ φ) (Xi Γ φ) φ) := by
    rw [atomic_adequacy]
    intro C hNC hT
    apply (dagger (fl := flat (bnd Γ φ) (Xi Γ φ)) (fun _ => rfl) hcl φ hφ hNC).mp
    apply hv C
    intro θ hθ
    exact (dagger (fl := flat (bnd Γ φ) (Xi Γ φ)) (fun _ => rfl) hcl θ (hΓ θ hθ) hNC).mpr
      (hT _ (List.mem_map.mpr ⟨θ, hθ, rfl⟩))
  have hs := simulation hcl hun hd
  rw [map_inv Γ (fun θ h => hun θ (hΓ θ h)), hun φ hφ] at hs
  exact hs

/-! ## Bases finitas -/

-- Σ finito: ⊩_Σ χ ⟺ ⊢_NJ Σ* → χ
theorem finite_base_export (Sig : List Rule) (χ : Form) :
    supp (bunion emptyB (ofList Sig)) χ ↔ NJ [] (impF (Sig.map ruleForm) χ) := by
  rw [export_all]
  constructor
  · intro h
    exact completeness (fun B _ => supp_mono _ (fun _ hr => False.elim hr) h)
  · intro d
    exact soundness d emptyB (fun _ hθ => by cases hθ)

/-! ## Lógica de inferones (Collinson–Eckhardt–Pym, Fig. 6) -/

inductive IForm where
  | inf : Inferon → IForm
  | bot : IForm
  | and : IForm → IForm → IForm
  | or  : IForm → IForm → IForm
  | imp : IForm → IForm → IForm

-- (∨) y (⊥) cuantifican sobre inferones
def isupp : Base → IForm → Prop
  | B, .inf ι   => suppInf B ι
  | B, .bot     => ∀ ι, suppInf B ι
  | B, .and φ ψ => isupp B φ ∧ isupp B ψ
  | B, .imp φ ψ => ∀ C, Ext B C → isupp C φ → isupp C ψ
  | B, .or φ ψ  => ∀ C, Ext B C → ∀ ι : Inferon,
      (∀ D, Ext C D → isupp D φ → suppInf D ι) →
      (∀ D, Ext C D → isupp D ψ → suppInf D ι) → suppInf C ι

-- inferón ↦ 𝒫* → ⟨P, b⟩
def tr : IForm → Form
  | .inf ι   => ι.form
  | .bot     => .bot
  | .and φ ψ => .and (tr φ) (tr ψ)
  | .or φ ψ  => .or (tr φ) (tr ψ)
  | .imp φ ψ => .imp (tr φ) (tr ψ)

-- base local vacía = átomo
theorem suppInf_nil {B : Base} {p : Atom} : suppInf B ⟨p, []⟩ ↔ Deriv B [] p := by
  constructor
  · intro h
    have h' : Deriv (bunion B (ofList [])) [] p := h
    exact Deriv.elim_adm (Sig := []) (Ext.refl B) (fun _ hr => by cases hr) h'
  · intro h
    show Deriv (bunion B (ofList [])) [] p
    exact Deriv.mono (fun _ h' => Or.inl h') h

-- ⊩_B φ ⟺ ⊩_B tr φ; incluye: ∨ sobre inferones = ∨ sobre átomos
theorem isupp_tr (φ : IForm) : ∀ {B : Base}, isupp B φ ↔ supp B (tr φ) := by
  induction φ with
  | inf ι => intro B; exact inferon_definable B ι
  | bot =>
    intro B
    simp only [isupp, tr, supp]
    constructor
    · intro h p; exact suppInf_nil.mp (h ⟨p, []⟩)
    · intro h ι; exact Deriv.mono (fun _ h' => Or.inl h') (h ι.a)
  | and φ ψ ih₁ ih₂ =>
    intro B
    simp only [isupp, tr, supp]
    exact ⟨fun h => ⟨ih₁.mp h.1, ih₂.mp h.2⟩, fun h => ⟨ih₁.mpr h.1, ih₂.mpr h.2⟩⟩
  | imp φ ψ ih₁ ih₂ =>
    intro B
    simp only [isupp, tr, supp]
    constructor
    · intro h C hBC hφ; exact ih₂.mp (h C hBC (ih₁.mpr hφ))
    · intro h C hBC hφ; exact ih₂.mpr (h C hBC (ih₁.mp hφ))
  | or φ ψ ih₁ ih₂ =>
    intro B
    simp only [isupp, tr, supp]
    constructor
    · intro h C hBC p k₁ k₂
      exact suppInf_nil.mp (h C hBC ⟨p, []⟩
        (fun D hCD hφ => suppInf_nil.mpr (k₁ D hCD (ih₁.mp hφ)))
        (fun D hCD hψ => suppInf_nil.mpr (k₂ D hCD (ih₂.mp hψ))))
    · intro h C hBC ι k₁ k₂
      have hC' : Ext C (bunion C (ofList ι.loc)) := fun _ h' => Or.inl h'
      have hsub : ∀ D, Ext (bunion C (ofList ι.loc)) D → Ext (bunion D (ofList ι.loc)) D :=
        fun D hD r hr => Or.elim hr id (fun h' => hD r (Or.inr h'))
      exact h (bunion C (ofList ι.loc)) (Ext.trans hBC hC') ι.a
        (fun D hD hφ => Deriv.mono (hsub D hD) (k₁ D (Ext.trans hC' hD) (ih₁.mpr hφ)))
        (fun D hD hψ => Deriv.mono (hsub D hD) (k₂ D (Ext.trans hC' hD) (ih₂.mpr hψ)))

-- Γ ⊩ φ (inferones)
abbrev ivalid (Γ : List IForm) (φ : IForm) : Prop :=
  ∀ B, (∀ θ, θ ∈ Γ → isupp B θ) → isupp B φ

theorem ivalid_iff (Γ : List IForm) (φ : IForm) :
    ivalid Γ φ ↔ valid (Γ.map tr) (tr φ) := by
  constructor
  · intro h B hΓ
    exact (isupp_tr φ).mp
      (h B (fun θ hθ => (isupp_tr θ).mpr (hΓ _ (List.mem_map.mpr ⟨θ, hθ, rfl⟩))))
  · intro h B hΓ
    apply (isupp_tr φ).mpr
    apply h B
    intro θ' hθ'
    cases List.mem_map.mp hθ' with
    | intro θ hθ =>
      cases hθ with
      | intro hm e => subst e; exact (isupp_tr θ).mp (hΓ θ hm)

-- Teoremas 11 y 12, con NJ sintáctico
theorem inferon_sound_complete (Γ : List IForm) (φ : IForm) :
    ivalid Γ φ ↔ NJ (Γ.map tr) (tr φ) :=
  (ivalid_iff Γ φ).trans ⟨completeness, soundness⟩

-- (Inferon) sintáctico: Γ ⊩ ⟨⟨P, 𝒫, b⟩⟩ ⟺ tr Γ ⊢_NJ 𝒫* → ⟨P, b⟩
theorem inferon_axiom (Γ : List IForm) (ι : Inferon) :
    ivalid Γ (.inf ι) ↔ NJ (Γ.map tr) (impF (ι.loc.map ruleForm) (.atom ι.a)) :=
  inferon_sound_complete Γ (.inf ι)

end BeS
