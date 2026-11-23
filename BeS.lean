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

/-! ## B-eS restringida: bases y extensiones finitas de reglas concretas -/

def suppF : List Rule → Form → Prop
  | L, .atom p  => Deriv (ofList L) [] p
  | L, .bot     => ∀ p, Deriv (ofList L) [] p
  | L, .and φ ψ => suppF L φ ∧ suppF L ψ
  | L, .imp φ ψ => ∀ L', Ext (ofList L) (ofList L') → suppF L' φ → suppF L' ψ
  | L, .or φ ψ  => ∀ L', Ext (ofList L) (ofList L') → ∀ p : Atom,
      (∀ L'', Ext (ofList L') (ofList L'') → suppF L'' φ → Deriv (ofList L'') [] p) →
      (∀ L'', Ext (ofList L') (ofList L'') → suppF L'' ψ → Deriv (ofList L'') [] p) →
      Deriv (ofList L') [] p

theorem suppF_mono (φ : Form) : ∀ {L L' : List Rule},
    Ext (ofList L) (ofList L') → suppF L φ → suppF L' φ := by
  induction φ with
  | atom p => intro L L' h hs; simp only [suppF] at hs ⊢; exact Deriv.mono h hs
  | bot => intro L L' h hs; simp only [suppF] at hs ⊢; exact fun q => Deriv.mono h (hs q)
  | and φ ψ ih₁ ih₂ =>
    intro L L' h hs; simp only [suppF] at hs ⊢; exact ⟨ih₁ h hs.1, ih₂ h hs.2⟩
  | imp φ ψ _ _ =>
    intro L L' h hs; simp only [suppF] at hs ⊢
    exact fun D hCD => hs D (Ext.trans h hCD)
  | or φ ψ _ _ =>
    intro L L' h hs; simp only [suppF] at hs ⊢
    exact fun D hCD => hs D (Ext.trans h hCD)

theorem bot_elimF (χ : Form) : ∀ {L : List Rule}, suppF L .bot → suppF L χ := by
  induction χ with
  | atom p => intro L hb; simp only [suppF] at hb ⊢; exact hb p
  | bot => intro L hb; exact hb
  | and χ₁ χ₂ ih₁ ih₂ =>
    intro L hb; simp only [suppF]; exact ⟨ih₁ hb, ih₂ hb⟩
  | imp χ₁ χ₂ _ ih₂ =>
    intro L hb; simp only [suppF]
    intro C hBC _
    exact ih₂ (suppF_mono .bot hBC hb)
  | or χ₁ χ₂ _ _ =>
    intro L hb; simp only [suppF]
    intro C hBC p _ _
    have hC := suppF_mono .bot hBC hb
    simp only [suppF] at hC
    exact hC p

theorem or_elimF (φ ψ χ : Form) : ∀ {L : List Rule},
    suppF L (.or φ ψ) →
    (∀ C, Ext (ofList L) (ofList C) → suppF C φ → suppF C χ) →
    (∀ C, Ext (ofList L) (ofList C) → suppF C ψ → suppF C χ) →
    suppF L χ := by
  induction χ with
  | atom p =>
    intro L hor h₁ h₂
    simp only [suppF] at hor h₁ h₂ ⊢
    exact hor L (Ext.refl _) p h₁ h₂
  | bot =>
    intro L hor h₁ h₂
    simp only [suppF] at hor h₁ h₂ ⊢
    intro q
    exact hor L (Ext.refl _) q
      (fun D hD hφ => h₁ D hD hφ q) (fun D hD hψ => h₂ D hD hψ q)
  | and χ₁ χ₂ ih₁ ih₂ =>
    intro L hor h₁ h₂
    simp only [suppF] at h₁ h₂ ⊢
    exact ⟨ih₁ hor (fun C hC hφ => (h₁ C hC hφ).1) (fun C hC hψ => (h₂ C hC hψ).1),
           ih₂ hor (fun C hC hφ => (h₁ C hC hφ).2) (fun C hC hψ => (h₂ C hC hψ).2)⟩
  | imp χ₁ χ₂ _ ih₂ =>
    intro L hor h₁ h₂
    simp only [suppF] at h₁ h₂ ⊢
    intro C hBC hχ₁
    apply ih₂ (suppF_mono (.or φ ψ) hBC hor)
    · intro D hCD hφ
      exact h₁ D (Ext.trans hBC hCD) hφ D (Ext.refl _) (suppF_mono χ₁ hCD hχ₁)
    · intro D hCD hψ
      exact h₂ D (Ext.trans hBC hCD) hψ D (Ext.refl _) (suppF_mono χ₁ hCD hχ₁)
  | or χ₁ χ₂ _ _ =>
    intro L hor h₁ h₂
    simp only [suppF] at hor h₁ h₂ ⊢
    intro C hBC p k₁ k₂
    apply hor C hBC p
    · intro D hCD hφ
      exact h₁ D (Ext.trans hBC hCD) hφ D (Ext.refl _) p
        (fun E hDE => k₁ E (Ext.trans hCD hDE)) (fun E hDE => k₂ E (Ext.trans hCD hDE))
    · intro D hCD hψ
      exact h₂ D (Ext.trans hBC hCD) hψ D (Ext.refl _) p
        (fun E hDE => k₁ E (Ext.trans hCD hDE)) (fun E hDE => k₂ E (Ext.trans hCD hDE))

abbrev validF (Γ : List Form) (φ : Form) : Prop :=
  ∀ L : List Rule, (∀ θ, θ ∈ Γ → suppF L θ) → suppF L φ

-- corrección en la clase finita
theorem soundnessF {Γ : List Form} {φ : Form} (d : NJ Γ φ) : validF Γ φ := by
  induction d with
  | @hyp Γ φ h => intro L hΓ; exact hΓ φ h
  | @andI Γ φ ψ _ _ ih₁ ih₂ =>
    intro L hΓ; simp only [suppF]; exact ⟨ih₁ L hΓ, ih₂ L hΓ⟩
  | @andE₁ Γ φ ψ _ ih =>
    intro L hΓ; have h := ih L hΓ; simp only [suppF] at h; exact h.1
  | @andE₂ Γ φ ψ _ ih =>
    intro L hΓ; have h := ih L hΓ; simp only [suppF] at h; exact h.2
  | @impI Γ φ ψ _ ih =>
    intro L hΓ; simp only [suppF]
    intro C hBC hφ
    apply ih C
    intro θ hθ
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact hφ
    | inr h => exact suppF_mono θ hBC (hΓ θ h)
  | @impE Γ φ ψ _ _ ih₁ ih₂ =>
    intro L hΓ; have h := ih₁ L hΓ; simp only [suppF] at h
    exact h L (Ext.refl _) (ih₂ L hΓ)
  | @orI₁ Γ φ ψ _ ih =>
    intro L hΓ; simp only [suppF]
    intro C hBC p k₁ _
    exact k₁ C (Ext.refl _) (suppF_mono φ hBC (ih L hΓ))
  | @orI₂ Γ φ ψ _ ih =>
    intro L hΓ; simp only [suppF]
    intro C hBC p _ k₂
    exact k₂ C (Ext.refl _) (suppF_mono ψ hBC (ih L hΓ))
  | @orE Γ φ ψ χ _ _ _ ih₀ ih₁ ih₂ =>
    intro L hΓ
    apply or_elimF φ ψ χ (ih₀ L hΓ)
    · intro C hBC hφ
      apply ih₁ C
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hφ
      | inr h => exact suppF_mono θ hBC (hΓ θ h)
    · intro C hBC hψ
      apply ih₂ C
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hψ
      | inr h => exact suppF_mono θ hBC (hΓ θ h)
  | @botE Γ φ _ ih =>
    intro L hΓ; exact bot_elimF φ (ih L hΓ)

theorem suppF_impF (Ls : List Form) (ψ : Form) : ∀ {L : List Rule},
    suppF L (impF Ls ψ) ↔
      ∀ L', Ext (ofList L) (ofList L') → (∀ φ, φ ∈ Ls → suppF L' φ) → suppF L' ψ := by
  induction Ls with
  | nil =>
    intro L
    simp only [impF]
    constructor
    · intro h C hBC _; exact suppF_mono ψ hBC h
    · intro h; exact h L (Ext.refl _) (fun _ hφ => by cases hφ)
  | cons φ Ls ih =>
    intro L
    simp only [impF, suppF]
    constructor
    · intro h C hBC hL
      have h1 := h C hBC (hL φ (List.mem_cons.mpr (Or.inl rfl)))
      exact (ih.mp h1) C (Ext.refl _) (fun θ hθ => hL θ (List.mem_cons.mpr (Or.inr hθ)))
    · intro h C hBC hφ
      apply ih.mpr
      intro D hCD hL
      apply h D (Ext.trans hBC hCD)
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact suppF_mono _ hCD hφ
      | inr h' => exact hL θ h'

/-! ### Hechos como lista finita -/

abbrev factsL (T : List Atom) : List Rule := T.map (fun t => ⟨[], t⟩)

theorem ext_factsL₁ (L : List Rule) (T : List Atom) :
    Ext (ofList (L ++ factsL T)) (bunion (ofList L) (facts T)) := by
  intro r hr
  cases List.mem_append.mp hr with
  | inl h => exact Or.inl h
  | inr h =>
    cases List.mem_map.mp h with
    | intro t ht =>
      cases ht with
      | intro htm e => subst e; exact Or.inr ⟨rfl, htm⟩

theorem ext_factsL₂ (L : List Rule) (T : List Atom) :
    Ext (bunion (ofList L) (facts T)) (ofList (L ++ factsL T)) := by
  intro r hr
  cases hr with
  | inl h => exact List.mem_append.mpr (Or.inl h)
  | inr h =>
    cases r with
    | mk ps c =>
      have hp : ps = [] := h.1
      subst hp
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c, h.2, rfl⟩))

theorem atomic_adequacyF {L : List Rule} {T : List Atom} {u : Atom} :
    Deriv (ofList L) T u ↔ ∀ L', Ext (ofList L) (ofList L') →
      (∀ t, t ∈ T → Deriv (ofList L') [] t) → Deriv (ofList L') [] u := by
  constructor
  · intro d L' hL hT
    exact Deriv.cut_atoms hL d (fun t ht => Or.inr (hT t ht))
  · intro h
    have hC := h (L ++ factsL T) (fun _ hr => List.mem_append.mpr (Or.inl hr))
      (fun t ht => Deriv.app ⟨[], t⟩
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨t, ht, rfl⟩)))
        (by intro _ h'; cases h'))
    exact Deriv.facts_to_ctx (Deriv.mono (ext_factsL₁ L T) hC)

theorem supp_premF (pq : List Atom × Atom) {L : List Rule} :
    suppF L (premForm pq) ↔ Deriv (ofList L) pq.1 pq.2 := by
  unfold premForm
  rw [suppF_impF, atomic_adequacyF]
  constructor
  · intro h D hCD hT
    have := h D hCD (fun φ hφ => by
      cases List.mem_map.mp hφ with
      | intro t ht =>
        cases ht with
        | intro htm e => subst e; simp only [suppF]; exact hT t htm)
    simp only [suppF] at this
    exact this
  · intro h D hCD hL
    simp only [suppF]
    exact h D hCD (fun t ht => by
      have := hL (.atom t) (List.mem_map.mpr ⟨t, ht, rfl⟩)
      simp only [suppF] at this
      exact this)

-- admisible en toda extensión finita
def AdmF (L : List Rule) (r : Rule) : Prop :=
  ∀ L', Ext (ofList L) (ofList L') →
    (∀ pq, pq ∈ r.prems → Deriv (ofList L') pq.1 pq.2) → Deriv (ofList L') [] r.concl

theorem supp_ruleF (r : Rule) {L : List Rule} : suppF L (ruleForm r) ↔ AdmF L r := by
  unfold ruleForm AdmF
  rw [suppF_impF]
  constructor
  · intro h D hCD hP
    have := h D hCD (fun φ hφ => by
      cases List.mem_map.mp hφ with
      | intro pq hpq =>
        cases hpq with
        | intro hm e => subst e; exact (supp_premF pq).mpr (hP pq hm))
    simp only [suppF] at this
    exact this
  · intro h D hCD hL
    simp only [suppF]
    exact h D hCD (fun pq hm => (supp_premF pq).mp (hL _ (List.mem_map.mpr ⟨pq, hm, rfl⟩)))

theorem AdmF.mono {L L' : List Rule} (h : Ext (ofList L) (ofList L')) {r : Rule}
    (ha : AdmF L r) : AdmF L' r :=
  fun E hE hP => ha E (Ext.trans h hE) hP

-- eliminación de reglas admisibles, en la clase finita
theorem Deriv.elim_admF {L Sig : List Rule} (hA : ∀ r, r ∈ Sig → AdmF L r)
    {Γ : List Atom} {q : Atom} (d : Deriv (ofList (L ++ Sig)) Γ q) : Deriv (ofList L) Γ q := by
  induction d with
  | @ref Γ p hp => exact Deriv.ref hp
  | @app Γ r hr _ ih =>
    cases List.mem_append.mp hr with
    | inl hB => exact Deriv.app r hB ih
    | inr hS =>
      have hD : Deriv (ofList (L ++ factsL Γ)) [] r.concl :=
        hA r hS (L ++ factsL Γ) (fun _ h => List.mem_append.mpr (Or.inl h))
          (fun pq hpq => Deriv.mono (ext_factsL₂ L Γ)
            (Deriv.ctx_to_facts (ih pq hpq) (fun t ht => List.mem_append.mp ht)))
      exact Deriv.facts_to_ctx (Deriv.mono (ext_factsL₁ L Γ) hD)

theorem extApp {L D Sig : List Rule} (h : Ext (ofList L) (ofList D)) :
    Ext (ofList (L ++ Sig)) (ofList (D ++ Sig)) := fun r hr =>
  (List.mem_append.mp hr).elim (fun h' => List.mem_append.mpr (Or.inl (h r h')))
    (fun h' => List.mem_append.mpr (Or.inr h'))

-- Σ admisible en L ⟹ (⊩_{L ∪ Σ} ψ → ⊩_L ψ)
theorem suppF_elim_adm {Sig : List Rule} (ψ : Form) : ∀ {L : List Rule},
    (∀ r, r ∈ Sig → AdmF L r) → suppF (L ++ Sig) ψ → suppF L ψ := by
  induction ψ with
  | atom p =>
    intro L hA h
    simp only [suppF] at h ⊢
    exact Deriv.elim_admF hA h
  | bot =>
    intro L hA h
    simp only [suppF] at h ⊢
    exact fun q => Deriv.elim_admF hA (h q)
  | and φ ψ ih₁ ih₂ =>
    intro L hA h
    simp only [suppF] at h ⊢
    exact ⟨ih₁ hA h.1, ih₂ hA h.2⟩
  | imp φ ψ _ ih₂ =>
    intro L hA h
    simp only [suppF] at h ⊢
    intro D hCD hφ
    have hA' : ∀ r, r ∈ Sig → AdmF D r := fun r hr => AdmF.mono hCD (hA r hr)
    exact ih₂ hA' (h (D ++ Sig) (extApp hCD)
      (suppF_mono φ (fun _ h' => List.mem_append.mpr (Or.inl h')) hφ))
  | or φ ψ _ _ =>
    intro L hA h
    simp only [suppF] at h ⊢
    intro D hCD p k₁ k₂
    have hA' : ∀ r, r ∈ Sig → AdmF D r := fun r hr => AdmF.mono hCD (hA r hr)
    have hp := h (D ++ Sig) (extApp hCD) p
      (fun E hE hφ => k₁ E (Ext.trans (fun _ h' => List.mem_append.mpr (Or.inl h')) hE) hφ)
      (fun E hE hψ => k₂ E (Ext.trans (fun _ h' => List.mem_append.mpr (Or.inl h')) hE) hψ)
    exact Deriv.elim_admF hA' hp

/-! ## NJ: debilitamiento y sustitución -/

theorem consSub {Γ Δ : List Form} {φ : Form} (h : ∀ θ, θ ∈ Γ → θ ∈ Δ) :
    ∀ θ, θ ∈ φ :: Γ → θ ∈ φ :: Δ := fun θ hθ =>
  (List.mem_cons.mp hθ).elim (fun e => List.mem_cons.mpr (Or.inl e))
    (fun h' => List.mem_cons.mpr (Or.inr (h θ h')))

theorem NJ.weaken {Γ : List Form} {φ : Form} (d : NJ Γ φ) :
    ∀ {Δ : List Form}, (∀ θ, θ ∈ Γ → θ ∈ Δ) → NJ Δ φ := by
  induction d with
  | hyp h => intro Δ hΔ; exact NJ.hyp (hΔ _ h)
  | andI _ _ ih₁ ih₂ => intro Δ hΔ; exact NJ.andI (ih₁ hΔ) (ih₂ hΔ)
  | andE₁ _ ih => intro Δ hΔ; exact NJ.andE₁ (ih hΔ)
  | andE₂ _ ih => intro Δ hΔ; exact NJ.andE₂ (ih hΔ)
  | impI _ ih => intro Δ hΔ; exact NJ.impI (ih (consSub hΔ))
  | impE _ _ ih₁ ih₂ => intro Δ hΔ; exact NJ.impE (ih₁ hΔ) (ih₂ hΔ)
  | orI₁ _ ih => intro Δ hΔ; exact NJ.orI₁ (ih hΔ)
  | orI₂ _ ih => intro Δ hΔ; exact NJ.orI₂ (ih hΔ)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
    intro Δ hΔ; exact NJ.orE (ih₀ hΔ) (ih₁ (consSub hΔ)) (ih₂ (consSub hΔ))
  | botE _ ih => intro Δ hΔ; exact NJ.botE (ih hΔ)

theorem substCons {Δ Γ : List Form} {φ : Form} (h : ∀ δ, δ ∈ Δ → NJ Γ δ) :
    ∀ δ, δ ∈ φ :: Δ → NJ (φ :: Γ) δ := fun δ hδ =>
  (List.mem_cons.mp hδ).elim (fun e => NJ.hyp (List.mem_cons.mpr (Or.inl e)))
    (fun h' => NJ.weaken (h δ h') (fun _ hθ => List.mem_cons.mpr (Or.inr hθ)))

theorem NJ.subst {Δ : List Form} {φ : Form} (d : NJ Δ φ) :
    ∀ {Γ : List Form}, (∀ δ, δ ∈ Δ → NJ Γ δ) → NJ Γ φ := by
  induction d with
  | hyp h => intro Γ hΓ; exact hΓ _ h
  | andI _ _ ih₁ ih₂ => intro Γ hΓ; exact NJ.andI (ih₁ hΓ) (ih₂ hΓ)
  | andE₁ _ ih => intro Γ hΓ; exact NJ.andE₁ (ih hΓ)
  | andE₂ _ ih => intro Γ hΓ; exact NJ.andE₂ (ih hΓ)
  | impI _ ih => intro Γ hΓ; exact NJ.impI (ih (substCons hΓ))
  | impE _ _ ih₁ ih₂ => intro Γ hΓ; exact NJ.impE (ih₁ hΓ) (ih₂ hΓ)
  | orI₁ _ ih => intro Γ hΓ; exact NJ.orI₁ (ih hΓ)
  | orI₂ _ ih => intro Γ hΓ; exact NJ.orI₂ (ih hΓ)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
    intro Γ hΓ; exact NJ.orE (ih₀ hΓ) (ih₁ (substCons hΓ)) (ih₂ (substCons hΓ))
  | botE _ ih => intro Γ hΓ; exact NJ.botE (ih hΓ)

/-! ## Slash de Aczel: propiedad de disyunción para contextos de Harrop -/

def slash (Γ : List Form) : Form → Prop
  | .atom p  => NJ Γ (.atom p)
  | .bot     => NJ Γ .bot
  | .and φ ψ => slash Γ φ ∧ slash Γ ψ
  | .or φ ψ  => slash Γ φ ∨ slash Γ ψ
  | .imp φ ψ => NJ Γ (.imp φ ψ) ∧ (slash Γ φ → slash Γ ψ)

theorem slash_nj {Γ : List Form} : ∀ (φ : Form), slash Γ φ → NJ Γ φ
  | .atom _, h => h
  | .bot, h => h
  | .and φ ψ, h => NJ.andI (slash_nj φ (And.left h)) (slash_nj ψ (And.right h))
  | .or φ ψ, h =>
    Or.elim h (fun h' => NJ.orI₁ (slash_nj φ h')) (fun h' => NJ.orI₂ (slash_nj ψ h'))
  | .imp _ _, h => And.left h

theorem slash_bot {Γ : List Form} (hb : NJ Γ .bot) : ∀ (φ : Form), slash Γ φ
  | .atom _ => NJ.botE hb
  | .bot => hb
  | .and φ ψ => And.intro (slash_bot hb φ) (slash_bot hb ψ)
  | .or φ _ => Or.inl (slash_bot hb φ)
  | .imp _ ψ => And.intro (NJ.botE hb) (fun _ => slash_bot hb ψ)

theorem consSlash {Δ Γ : List Form} {φ : Form} (h : ∀ δ, δ ∈ Δ → slash Γ δ)
    (hφ : slash Γ φ) : ∀ δ, δ ∈ φ :: Δ → slash Γ δ := fun δ hδ =>
  (List.mem_cons.mp hδ).elim (fun e => by subst e; exact hφ) (fun h' => h δ h')

-- Δ ⊢ φ y Γ | Δ ⟹ Γ | φ
theorem slash_sound {Δ : List Form} {φ : Form} (d : NJ Δ φ) :
    ∀ {Γ : List Form}, (∀ δ, δ ∈ Δ → slash Γ δ) → slash Γ φ := by
  induction d with
  | hyp h => intro Γ hΓ; exact hΓ _ h
  | andI _ _ ih₁ ih₂ => intro Γ hΓ; exact And.intro (ih₁ hΓ) (ih₂ hΓ)
  | andE₁ _ ih => intro Γ hΓ; exact And.left (ih hΓ)
  | andE₂ _ ih => intro Γ hΓ; exact And.right (ih hΓ)
  | @impI Δ φ ψ d' ih =>
    intro Γ hΓ
    exact And.intro (NJ.subst (NJ.impI d') (fun δ hδ => slash_nj δ (hΓ δ hδ)))
      (fun hφ => ih (consSlash hΓ hφ))
  | impE _ _ ih₁ ih₂ => intro Γ hΓ; exact (And.right (ih₁ hΓ)) (ih₂ hΓ)
  | orI₁ _ ih => intro Γ hΓ; exact Or.inl (ih hΓ)
  | orI₂ _ ih => intro Γ hΓ; exact Or.inr (ih hΓ)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
    intro Γ hΓ
    exact Or.elim (ih₀ hΓ) (fun h => ih₁ (consSlash hΓ h)) (fun h => ih₂ (consSlash hΓ h))
  | @botE Δ φ _ ih => intro Γ hΓ; exact slash_bot (ih hΓ) φ

-- fórmulas de Harrop: sin ∨ estrictamente positiva
def harrop : Form → Prop
  | .atom _  => True
  | .bot     => True
  | .and φ ψ => harrop φ ∧ harrop ψ
  | .or _ _  => False
  | .imp _ ψ => harrop ψ

theorem harrop_slash {Γ : List Form} : ∀ (H : Form), harrop H → NJ Γ H → slash Γ H
  | .atom _, _, d => d
  | .bot, _, d => d
  | .and φ ψ, hh, d =>
    And.intro (harrop_slash φ (And.left hh) (NJ.andE₁ d))
      (harrop_slash ψ (And.right hh) (NJ.andE₂ d))
  | .or _ _, hh, _ => False.elim hh
  | .imp φ ψ, hh, d =>
    And.intro d (fun hφ => harrop_slash ψ hh (NJ.impE d (slash_nj φ hφ)))

-- propiedad de disyunción para contextos de Harrop
theorem harrop_dp {Γ : List Form} (hΓ : ∀ θ, θ ∈ Γ → harrop θ) {φ ψ : Form}
    (d : NJ Γ (.or φ ψ)) : NJ Γ φ ∨ NJ Γ ψ := by
  have hs : slash Γ (.or φ ψ) :=
    slash_sound d (fun δ hδ => harrop_slash δ (hΓ δ hδ) (NJ.hyp hδ))
  exact Or.elim hs (fun h => Or.inl (slash_nj φ h)) (fun h => Or.inr (slash_nj ψ h))

theorem harrop_impF (Ls : List Form) (ψ : Form) (h : harrop ψ) : harrop (impF Ls ψ) := by
  induction Ls with
  | nil => exact h
  | cons _ Ls ih => exact ih

theorem harrop_rule (r : Rule) : harrop (ruleForm r) :=
  harrop_impF (r.prems.map premForm) (.atom r.concl) trivial

/-! ## Contramodelo de Kripke para la regla de Harrop -/

structure Kripke where
  le    : Nat → Nat → Prop
  val   : Nat → Atom → Prop
  refl  : ∀ w, le w w
  trans : ∀ u v w, le u v → le v w → le u w
  mono  : ∀ v w p, le v w → val v p → val w p

def forces (M : Kripke) : Nat → Form → Prop
  | w, .atom p  => M.val w p
  | _, .bot     => False
  | w, .and φ ψ => forces M w φ ∧ forces M w ψ
  | w, .or φ ψ  => forces M w φ ∨ forces M w ψ
  | w, .imp φ ψ => ∀ v, M.le w v → forces M v φ → forces M v ψ

theorem forces_mono (M : Kripke) (φ : Form) :
    ∀ {v w : Nat}, M.le v w → forces M v φ → forces M w φ := by
  induction φ with
  | atom p => intro v w h hf; exact M.mono v w p h hf
  | bot => intro v w _ hf; exact hf
  | and φ ψ ih₁ ih₂ =>
    intro v w h hf; exact And.intro (ih₁ h (And.left hf)) (ih₂ h (And.right hf))
  | or φ ψ ih₁ ih₂ =>
    intro v w h hf
    exact Or.elim hf (fun h' => Or.inl (ih₁ h h')) (fun h' => Or.inr (ih₂ h h'))
  | imp φ ψ _ _ => intro v w h hf; exact fun u hwu => hf u (M.trans v w u h hwu)

theorem kripke_sound (M : Kripke) {Γ : List Form} {φ : Form} (d : NJ Γ φ) :
    ∀ w, (∀ θ, θ ∈ Γ → forces M w θ) → forces M w φ := by
  induction d with
  | hyp h => intro w hw; exact hw _ h
  | andI _ _ ih₁ ih₂ => intro w hw; exact And.intro (ih₁ w hw) (ih₂ w hw)
  | andE₁ _ ih => intro w hw; exact And.left (ih w hw)
  | andE₂ _ ih => intro w hw; exact And.right (ih w hw)
  | impI _ ih =>
    intro w hw v hwv hφ
    exact ih v (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hφ
      | inr h => exact forces_mono M θ hwv (hw θ h))
  | impE _ _ ih₁ ih₂ => intro w hw; exact ih₁ w hw w (M.refl w) (ih₂ w hw)
  | orI₁ _ ih => intro w hw; exact Or.inl (ih w hw)
  | orI₂ _ ih => intro w hw; exact Or.inr (ih w hw)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
    intro w hw
    exact Or.elim (ih₀ w hw)
      (fun h => ih₁ w (fun θ hθ => by
        cases List.mem_cons.mp hθ with
        | inl e => subst e; exact h
        | inr h' => exact hw θ h'))
      (fun h => ih₂ w (fun θ hθ => by
        cases List.mem_cons.mp hθ with
        | inl e => subst e; exact h
        | inr h' => exact hw θ h'))
  | botE _ ih => intro w hw; exact False.elim (ih w hw)

-- mundos: 0 raíz; 1 ⊩ r; 2 ⊩ q; ≥ 3 ⊩ p.  Átomos: p = 0, q = 1, r = 2
def hmod : Kripke where
  le v w := v = w ∨ v = 0
  val w x := (3 ≤ w ∧ x = 0) ∨ (w = 2 ∧ x = 1) ∨ (w = 1 ∧ x = 2)
  refl _ := Or.inl rfl
  trans u v w h₁ h₂ := by
    cases h₁ with
    | inl e => subst e; exact h₂
    | inr e => exact Or.inr e
  mono v w x h hv := by
    cases h with
    | inl e => subst e; exact hv
    | inr e =>
      subst e
      cases hv with
      | inl h' => exact absurd h'.1 (by decide)
      | inr h' =>
        cases h' with
        | inl h'' => exact absurd h''.1 (by decide)
        | inr h'' => exact absurd h''.1 (by decide)

abbrev negF (φ : Form) : Form := .imp φ .bot

-- ¬p → q ∨ r  y  (¬p → q) ∨ (¬p → r)
def harropH : Form := .imp (negF (.atom 0)) (.or (.atom 1) (.atom 2))
def harropC : Form := .or (.imp (negF (.atom 0)) (.atom 1)) (.imp (negF (.atom 0)) (.atom 2))

theorem hmod_neg {v : Nat} (h : forces hmod v (negF (.atom 0))) : v = 1 ∨ v = 2 := by
  have h0 : v ≠ 0 := fun e => h 3 (Or.inr e) (Or.inl ⟨by decide, rfl⟩)
  have h3 : ¬ 3 ≤ v := fun hv => h v (Or.inl rfl) (Or.inl ⟨hv, rfl⟩)
  omega

theorem hmod_negp1 : forces hmod 1 (negF (.atom 0)) := by
  intro u hu hp
  cases hu with
  | inl e =>
    subst e
    cases hp with
    | inl h => exact absurd h.1 (by decide)
    | inr h =>
      cases h with
      | inl h' => exact absurd h'.1 (by decide)
      | inr h' => exact absurd h'.2 (by decide)
  | inr e => exact absurd e (by decide)

theorem hmod_negp2 : forces hmod 2 (negF (.atom 0)) := by
  intro u hu hp
  cases hu with
  | inl e =>
    subst e
    cases hp with
    | inl h => exact absurd h.1 (by decide)
    | inr h =>
      cases h with
      | inl h' => exact absurd h'.2 (by decide)
      | inr h' => exact absurd h'.1 (by decide)
  | inr e => exact absurd e (by decide)

theorem hmod_H : forces hmod 0 harropH := by
  intro v _ hv
  cases hmod_neg hv with
  | inl e => subst e; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  | inr e => subst e; exact Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩))

theorem hmod_C : ¬ forces hmod 0 harropC := by
  intro h
  cases h with
  | inl h₁ =>
    have hq := h₁ 1 (Or.inr rfl) hmod_negp1
    cases hq with
    | inl h => exact absurd h.1 (by decide)
    | inr h =>
      cases h with
      | inl h' => exact absurd h'.1 (by decide)
      | inr h' => exact absurd h'.2 (by decide)
  | inr h₂ =>
    have hr := h₂ 2 (Or.inr rfl) hmod_negp2
    cases hr with
    | inl h => exact absurd h.1 (by decide)
    | inr h =>
      cases h with
      | inl h' => exact absurd h'.2 (by decide)
      | inr h' => exact absurd h'.1 (by decide)

-- la regla de Harrop no es derivable
theorem harrop_rule_not_derivable : ¬ NJ [harropH] harropC := fun d =>
  hmod_C (kripke_sound hmod d 0 (fun θ hθ => by
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact hmod_H
    | inr h => cases h))

/-! ## Incompletitud de la B-eS en bases finitas concretas -/

-- Si fuera completa: ⊩_L H ⟹ L* ⊢ H ⟹ (Harrop, DP) L* ⊢ C ⟹ ⊩_L C;
-- luego H ⊩ C, luego H ⊢ C: contradicción.
theorem finite_incomplete : ¬ (∀ (Γ : List Form) (φ : Form), validF Γ φ → NJ Γ φ) := by
  intro hc
  apply harrop_rule_not_derivable
  apply hc
  intro L hL
  have hH : suppF L harropH := hL _ mem0
  -- L* ⊩ H (exportación en la clase finita)
  have v1 : validF (L.map ruleForm) harropH := by
    intro L' hL'
    have hA : ∀ r, r ∈ L → AdmF L' r :=
      fun r hr => (supp_ruleF r).mp (hL' _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    exact suppF_elim_adm harropH hA
      (suppF_mono harropH (fun _ h => List.mem_append.mpr (Or.inr h)) hH)
  have d1 := hc _ _ v1
  -- ¬p, L* ⊢ q ∨ r
  have d2 : NJ (negF (.atom 0) :: L.map ruleForm) (.or (.atom 1) (.atom 2)) :=
    NJ.impE (NJ.weaken d1 (fun θ hθ => List.mem_cons.mpr (Or.inr hθ))) (NJ.hyp mem0)
  have hΓ : ∀ θ, θ ∈ negF (.atom 0) :: L.map ruleForm → harrop θ := fun θ hθ => by
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact trivial
    | inr h =>
      cases List.mem_map.mp h with
      | intro r hr =>
        cases hr with
        | intro _ e => subst e; exact harrop_rule r
  have d3 : NJ (L.map ruleForm) harropC := by
    cases harrop_dp hΓ d2 with
    | inl h => exact NJ.orI₁ (NJ.impI h)
    | inr h => exact NJ.orI₂ (NJ.impI h)
  -- L* ⊢ C ⟹ ⊩_L C (corrección; las reglas de L son admisibles en L)
  exact soundnessF d3 L (fun θ hθ => by
    cases List.mem_map.mp hθ with
    | intro r hr =>
      cases hr with
      | intro hm e =>
        subst e
        exact (supp_ruleF r).mpr (fun L' hL' hP => Deriv.app r (hL' r hm) (fun pq hpq => by
          rw [List.append_nil]; exact hP pq hpq)))

end BeS
