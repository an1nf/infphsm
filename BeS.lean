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

/-! ## ⊥ en la clase finita
  Infinitos átomos, bases finitas: ⊥ nunca se soporta. Entonces ¬φ es rígida, ¬¬p es válida
  y la regla de Harrop vale trivialmente. Sin ⊥, la división p → q ∨ r separa la clase de NJ. -/

-- suma de conclusiones
def cbound : List Rule → Nat
  | []     => 0
  | r :: L => r.concl + cbound L

theorem concl_le {r : Rule} (L : List Rule) (h : r ∈ L) : r.concl ≤ cbound L := by
  induction L with
  | nil => cases h
  | cons s L ih =>
    show r.concl ≤ s.concl + cbound L
    cases List.mem_cons.mp h with
    | inl e => rw [e]; exact Nat.le_add_right _ _
    | inr h' => exact Nat.le_trans (ih h') (Nat.le_add_left _ _)

-- sin hipótesis solo salen conclusiones de L
theorem deriv_concl {L : List Rule} {p : Atom} (d : Deriv (ofList L) [] p) : p ≤ cbound L := by
  cases d with
  | ref h => cases h
  | app r hr _ => exact concl_le L hr

theorem finite_bot (L : List Rule) : ¬ suppF L .bot := fun h =>
  Nat.not_succ_le_self (cbound L) (deriv_concl (h (cbound L + 1)))

-- ¬p nunca: basta añadir el hecho p
theorem finite_neg (L : List Rule) (p : Atom) : ¬ suppF L (negF (.atom p)) := fun h =>
  finite_bot (⟨[], p⟩ :: L)
    (h (⟨[], p⟩ :: L) (fun _ hr => List.mem_cons.mpr (Or.inr hr))
      (Deriv.app ⟨[], p⟩ mem0 (fun _ hpq => by cases hpq)))

-- ¬φ no depende de la base
theorem finite_neg_rigid (φ : Form) {L : List Rule} (h : suppF L (negF φ)) (L' : List Rule) :
    suppF L' (negF φ) := fun L2 _ h2 =>
  absurd (h (L2 ++ L) (fun _ hr => List.mem_append.mpr (Or.inr hr))
    (suppF_mono φ (fun _ hr => List.mem_append.mpr (Or.inl hr)) h2)) (finite_bot _)

-- ¬¬p válida en la clase finita
theorem finite_dn (p : Atom) : validF [] (negF (negF (.atom p))) :=
  fun _ _ L' _ h => absurd h (finite_neg L' p)

-- un mundo, ningún átomo
def kmod1 : Kripke where
  le v w := v = w
  val _ _ := False
  refl _ := rfl
  trans _ _ _ h₁ h₂ := h₁.trans h₂
  mono _ _ _ _ hv := hv

theorem dn_not_nj (p : Atom) : ¬ NJ [] (negF (negF (.atom p))) := fun d =>
  kripke_sound kmod1 d 0 (fun _ hθ => by cases hθ) 0 rfl (fun _ _ hp => hp)

-- incompletitud inmediata
theorem finite_incomplete_dn : ¬ (∀ (Γ : List Form) (φ : Form), validF Γ φ → NJ Γ φ) :=
  fun hc => dn_not_nj 0 (hc [] _ (finite_dn 0))

-- regla de Harrop válida en la clase finita (¬φ rígida)
theorem finite_harrop (φ ψ χ : Form) :
    validF [.imp (negF φ) (.or ψ χ)] (.or (.imp (negF φ) ψ) (.imp (negF φ) χ)) := by
  intro L hL
  have hH : suppF L (.imp (negF φ) (.or ψ χ)) := hL _ mem0
  cases Classical.em (suppF L (negF φ)) with
  | inl hn =>
    have hor : suppF L (.or ψ χ) := hH L (fun _ h => h) hn
    have d : NJ [.or ψ χ] (.or (.imp (negF φ) ψ) (.imp (negF φ) χ)) :=
      NJ.orE (NJ.hyp mem0)
        (NJ.orI₁ (NJ.impI (NJ.hyp (List.mem_cons.mpr (Or.inr mem0)))))
        (NJ.orI₂ (NJ.impI (NJ.hyp (List.mem_cons.mpr (Or.inr mem0)))))
    exact soundnessF d L (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hor
      | inr h => cases h)
  | inr hn =>
    have hi : suppF L (.imp (negF φ) ψ) := fun _ _ h => absurd (finite_neg_rigid φ h L) hn
    have d : NJ [.imp (negF φ) ψ] (.or (.imp (negF φ) ψ) (.imp (negF φ) χ)) :=
      NJ.orI₁ (NJ.hyp mem0)
    exact soundnessF d L (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hi
      | inr h => cases h)

-- sin ⊥: p → q ∨ r  y  (p → q) ∨ (p → r)
def splitH : Form := .imp (.atom 0) (.or (.atom 1) (.atom 2))
def splitC : Form := .or (.imp (.atom 0) (.atom 1)) (.imp (.atom 0) (.atom 2))

-- mundos: 0 raíz; 1 ⊩ p, q; 2 ⊩ p, r
def smod : Kripke where
  le v w := v = w ∨ v = 0
  val w x := (w = 1 ∧ (x = 0 ∨ x = 1)) ∨ (w = 2 ∧ (x = 0 ∨ x = 2))
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
      | inr h' => exact absurd h'.1 (by decide)

theorem smod_H : forces smod 0 splitH := by
  intro v _ hv
  cases hv with
  | inl h =>
    have e := h.1
    subst e
    exact Or.inl (Or.inl ⟨rfl, Or.inr rfl⟩)
  | inr h =>
    have e := h.1
    subst e
    exact Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)

theorem smod_C : ¬ forces smod 0 splitC := by
  intro h
  cases h with
  | inl h₁ =>
    have hq := h₁ 2 (Or.inr rfl) (Or.inr ⟨rfl, Or.inl rfl⟩)
    cases hq with
    | inl h => exact absurd h.1 (by decide)
    | inr h =>
      cases h.2 with
      | inl e => exact absurd e (by decide)
      | inr e => exact absurd e (by decide)
  | inr h₂ =>
    have hr := h₂ 1 (Or.inr rfl) (Or.inl ⟨rfl, Or.inl rfl⟩)
    cases hr with
    | inl h =>
      cases h.2 with
      | inl e => exact absurd e (by decide)
      | inr e => exact absurd e (by decide)
    | inr h => exact absurd h.1 (by decide)

theorem split_not_derivable : ¬ NJ [splitH] splitC := fun d =>
  smod_C (kripke_sound smod d 0 (fun θ hθ => by
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact smod_H
    | inr h => cases h))

-- incompletitud sin ⊥: el esquema de finite_incomplete con p en lugar de ¬p
theorem finite_incomplete_pos : ¬ (∀ (Γ : List Form) (φ : Form), validF Γ φ → NJ Γ φ) := by
  intro hc
  apply split_not_derivable
  apply hc
  intro L hL
  have hH : suppF L splitH := hL _ mem0
  have v1 : validF (L.map ruleForm) splitH := by
    intro L' hL'
    have hA : ∀ r, r ∈ L → AdmF L' r :=
      fun r hr => (supp_ruleF r).mp (hL' _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    exact suppF_elim_adm splitH hA
      (suppF_mono splitH (fun _ h => List.mem_append.mpr (Or.inr h)) hH)
  have d1 := hc _ _ v1
  have d2 : NJ (.atom 0 :: L.map ruleForm) (.or (.atom 1) (.atom 2)) :=
    NJ.impE (NJ.weaken d1 (fun θ hθ => List.mem_cons.mpr (Or.inr hθ))) (NJ.hyp mem0)
  have hΓ : ∀ θ, θ ∈ .atom 0 :: L.map ruleForm → harrop θ := fun θ hθ => by
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact trivial
    | inr h =>
      cases List.mem_map.mp h with
      | intro r hr =>
        cases hr with
        | intro _ e => subst e; exact harrop_rule r
  have d3 : NJ (L.map ruleForm) splitC := by
    cases harrop_dp hΓ d2 with
    | inl h => exact NJ.orI₁ (NJ.impI h)
    | inr h => exact NJ.orI₂ (NJ.impI h)
  exact soundnessF d3 L (fun θ hθ => by
    cases List.mem_map.mp hθ with
    | intro r hr =>
      cases hr with
      | intro hm e =>
        subst e
        exact (supp_ruleF r).mpr (fun L' hL' hP => Deriv.app r (hL' r hm) (fun pq hpq => by
          rw [List.append_nil]; exact hP pq hpq)))

/-! ## ∨ de Sandqvist en la clase finita: el átomo fresco
  Una base finita concreta deja átomos frescos. Con uno fresco r, las reglas b ⇒ r y c ⇒ r
  no derivan r salvo que se derive b o c: la ∨ de Sandqvist tiene la propiedad de disyunción
  en átomos, y la división vale (PCS 2015, prueba 2). -/

def sumN : List Nat → Nat
  | []     => 0
  | x :: l => x + sumN l

theorem le_sumN {a : Nat} (l : List Nat) (h : a ∈ l) : a ≤ sumN l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    show a ≤ x + sumN l
    cases List.mem_cons.mp h with
    | inl e => rw [e]; exact Nat.le_add_right _ _
    | inr h' => exact Nat.le_trans (ih h') (Nat.le_add_left _ _)

def pbound : List (List Atom × Atom) → Nat
  | []      => 0
  | pq :: l => pq.2 + sumN pq.1 + pbound l

theorem le_pbound {pq : List Atom × Atom} (l : List (List Atom × Atom)) (h : pq ∈ l) :
    pq.2 + sumN pq.1 ≤ pbound l := by
  induction l with
  | nil => cases h
  | cons x l ih =>
    show pq.2 + sumN pq.1 ≤ x.2 + sumN x.1 + pbound l
    cases List.mem_cons.mp h with
    | inl e => rw [e]; exact Nat.le_add_right _ _
    | inr h' => exact Nat.le_trans (ih h') (Nat.le_add_left _ _)

-- cota de los átomos de una regla y de una lista de reglas
def rbound (x : Rule) : Nat := x.concl + pbound x.prems

def lbound : List Rule → Nat
  | []     => 0
  | x :: L => rbound x + lbound L

theorem le_lbound {x : Rule} (L : List Rule) (h : x ∈ L) : rbound x ≤ lbound L := by
  induction L with
  | nil => cases h
  | cons y L ih =>
    show rbound x ≤ rbound y + lbound L
    cases List.mem_cons.mp h with
    | inl e => rw [e]; exact Nat.le_add_right _ _
    | inr h' => exact Nat.le_trans (ih h') (Nat.le_add_left _ _)

-- r > lbound L no aparece en L
theorem fresh_of_gt {L : List Rule} {r : Atom} (hr : lbound L < r) :
    ∀ x, x ∈ L → x.concl ≠ r ∧ ∀ pq, pq ∈ x.prems → pq.2 ≠ r ∧ r ∉ pq.1 := by
  intro x hx
  have hx' : rbound x ≤ lbound L := le_lbound L hx
  constructor
  · intro e
    have h1 : x.concl ≤ rbound x := Nat.le_add_right _ _
    rw [e] at h1
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h1 hx') hr)
  · intro pq hpq
    have hp : pq.2 + sumN pq.1 ≤ rbound x :=
      Nat.le_trans (le_pbound x.prems hpq) (Nat.le_add_left _ _)
    constructor
    · intro e
      have h1 : pq.2 ≤ rbound x := Nat.le_trans (Nat.le_add_right _ _) hp
      rw [e] at h1
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h1 hx') hr)
    · intro hm
      have h1 : r ≤ rbound x :=
        Nat.le_trans (le_sumN pq.1 hm) (Nat.le_trans (Nat.le_add_left _ _) hp)
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans h1 hx') hr)

-- reglas nuevas con conclusión fresca: fuera de r nada cambia
theorem deriv_fresh {L E : List Rule} {r : Atom}
    (hL : ∀ x, x ∈ L → x.concl ≠ r ∧ ∀ pq, pq ∈ x.prems → pq.2 ≠ r ∧ r ∉ pq.1)
    (hE : ∀ e, e ∈ E → e.concl = r) {S : List Atom} {q : Atom}
    (d : Deriv (ofList (L ++ E)) S q) : r ∉ S → q ≠ r → Deriv (ofList L) S q := by
  induction d with
  | ref h => intro _ _; exact Deriv.ref h
  | app x hx _ ih =>
    intro hS hq
    cases List.mem_append.mp hx with
    | inr he => exact absurd (hE x he) hq
    | inl hl =>
      exact Deriv.app x hl (fun pq hpq => ih pq hpq
        (fun hm => by
          cases List.mem_append.mp hm with
          | inl h1 => exact ((hL x hl).2 pq hpq).2 h1
          | inr h2 => exact hS h2)
        ((hL x hl).2 pq hpq).1)

-- el último paso hacia r usa una regla nueva
theorem last_fresh {L E : List Rule} {r : Atom}
    (hL : ∀ x, x ∈ L → x.concl ≠ r ∧ ∀ pq, pq ∈ x.prems → pq.2 ≠ r ∧ r ∉ pq.1)
    {S : List Atom} {q : Atom} (d : Deriv (ofList (L ++ E)) S q) (hS : r ∉ S) (hq : q = r) :
    ∃ e, e ∈ E ∧ ∀ pq, pq ∈ e.prems → Deriv (ofList (L ++ E)) (pq.1 ++ S) pq.2 := by
  cases d with
  | ref h => subst hq; exact absurd h hS
  | app x hx hp =>
    cases List.mem_append.mp hx with
    | inl hl => exact absurd hq ((hL x hl).1)
    | inr he => exact ⟨x, he, hp⟩

theorem dp_of_fresh {L : List Rule} {b c r : Atom}
    (hfr : ∀ x, x ∈ L → x.concl ≠ r ∧ ∀ pq, pq ∈ x.prems → pq.2 ≠ r ∧ r ∉ pq.1)
    (hb : b ≠ r) (hc : c ≠ r) (h : suppF L (.or (.atom b) (.atom c))) :
    Deriv (ofList L) [] b ∨ Deriv (ofList L) [] c := by
  have hE : ∀ e, e ∈ [(⟨[([], b)], r⟩ : Rule), ⟨[([], c)], r⟩] → e.concl = r := by
    intro e he
    cases List.mem_cons.mp he with
    | inl e1 => subst e1; rfl
    | inr he' =>
      cases List.mem_cons.mp he' with
      | inl e2 => subst e2; rfl
      | inr he'' => cases he''
  have hext : Ext (ofList L) (ofList (L ++ [(⟨[([], b)], r⟩ : Rule), ⟨[([], c)], r⟩])) :=
    fun _ hx => List.mem_append.mpr (Or.inl hx)
  have d := h _ hext r
    (fun _ hL'' hb'' => Deriv.app ⟨[([], b)], r⟩
      (hL'' _ (List.mem_append.mpr (Or.inr mem0)))
      (fun pq hpq => by
        cases List.mem_cons.mp hpq with
        | inl e => subst e; exact hb''
        | inr h' => cases h'))
    (fun _ hL'' hc'' => Deriv.app ⟨[([], c)], r⟩
      (hL'' _ (List.mem_append.mpr (Or.inr mem1)))
      (fun pq hpq => by
        cases List.mem_cons.mp hpq with
        | inl e => subst e; exact hc''
        | inr h' => cases h'))
  cases last_fresh hfr d (fun h' => by cases h') rfl with
  | intro e he =>
    cases List.mem_cons.mp he.1 with
    | inl e1 =>
      subst e1
      have d1 : Deriv (ofList (L ++ [(⟨[([], b)], r⟩ : Rule), ⟨[([], c)], r⟩])) [] b :=
        he.2 ([], b) mem0
      exact Or.inl (deriv_fresh hfr hE d1 (fun h' => by cases h') hb)
    | inr he' =>
      cases List.mem_cons.mp he' with
      | inl e2 =>
        subst e2
        have d2 : Deriv (ofList (L ++ [(⟨[([], b)], r⟩ : Rule), ⟨[([], c)], r⟩])) [] c :=
          he.2 ([], c) mem0
        exact Or.inr (deriv_fresh hfr hE d2 (fun h' => by cases h') hc)
      | inr he'' => cases he''

-- propiedad de disyunción en átomos para la clase finita
theorem finite_dp_atom (L : List Rule) (b c : Atom) (h : suppF L (.or (.atom b) (.atom c))) :
    Deriv (ofList L) [] b ∨ Deriv (ofList L) [] c :=
  dp_of_fresh (r := lbound L + b + c + 1)
    (fresh_of_gt (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ b) (Nat.le_add_right _ c))))
    (Nat.ne_of_lt (Nat.lt_succ_of_le
      (Nat.le_trans (Nat.le_add_left b (lbound L)) (Nat.le_add_right _ c))))
    (Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_add_left c (lbound L + b))))
    h

-- cortar un hecho añadido
theorem cut_fact {L L' : List Rule} {a : Atom} (hL : Ext (ofList L) (ofList L'))
    (ha : Deriv (ofList L') [] a) {S : List Atom} {q : Atom}
    (d : Deriv (ofList (⟨[], a⟩ :: L)) S q) : Deriv (ofList L') S q := by
  induction d with
  | ref h => exact Deriv.ref h
  | app x hx _ ih =>
    cases List.mem_cons.mp hx with
    | inl e => subst e; exact Deriv.weaken ha (fun _ hx => by cases hx)
    | inr hl => exact Deriv.app x (hL x hl) ih

-- la división es válida en la clase finita
theorem finite_split : validF [splitH] splitC := by
  intro L hL
  have hH : suppF L (.imp (.atom 0) (.or (.atom 1) (.atom 2))) := hL _ mem0
  have hp : suppF (⟨[], 0⟩ :: L) (.atom 0) := Deriv.app ⟨[], 0⟩ mem0 (fun _ h => by cases h)
  have hor := hH (⟨[], 0⟩ :: L) (fun _ hr => List.mem_cons.mpr (Or.inr hr)) hp
  cases finite_dp_atom _ 1 2 hor with
  | inl hq =>
    have hi : suppF L (.imp (.atom 0) (.atom 1)) := fun _ hL' hp' => cut_fact hL' hp' hq
    have d : NJ [.imp (.atom 0) (.atom 1)] splitC := NJ.orI₁ (NJ.hyp mem0)
    exact soundnessF d L (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hi
      | inr h => cases h)
  | inr hr =>
    have hi : suppF L (.imp (.atom 0) (.atom 2)) := fun _ hL' hp' => cut_fact hL' hp' hr
    have d : NJ [.imp (.atom 0) (.atom 2)] splitC := NJ.orI₂ (NJ.hyp mem0)
    exact soundnessF d L (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hi
      | inr h => cases h)

-- incompletitud directa, sin ⊥ ni completitud supuesta
theorem finite_incomplete_split : ¬ (∀ (Γ : List Form) (φ : Form), validF Γ φ → NJ Γ φ) :=
  fun hc => split_not_derivable (hc _ _ finite_split)

/-! ## Validez esquemática: ¬φ ∨ ¬¬φ (Kremer, en Goldfarb 2016)
  Por la rigidez de ¬, el esquema vale para toda φ: la clase finita tampoco es
  completa para la validez esquemática, a diferencia de la noción revisada de Goldfarb. -/

theorem finite_kremer (φ : Form) : validF [] (.or (negF φ) (negF (negF φ))) := by
  intro L _
  cases Classical.em (∃ L₀, suppF L₀ (negF φ)) with
  | inl h =>
    cases h with
    | intro L₀ h₀ =>
      have d : NJ [negF φ] (.or (negF φ) (negF (negF φ))) := NJ.orI₁ (NJ.hyp mem0)
      exact soundnessF d L (fun θ hθ => by
        cases List.mem_cons.mp hθ with
        | inl e => subst e; exact finite_neg_rigid φ h₀ L
        | inr h' => cases h')
  | inr h =>
    have hn : suppF L (negF (negF φ)) := fun L' _ h' => False.elim (h ⟨L', h'⟩)
    have d : NJ [negF (negF φ)] (.or (negF φ) (negF (negF φ))) := NJ.orI₂ (NJ.hyp mem0)
    exact soundnessF d L (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hn
      | inr h' => cases h')

-- mundos: 0 raíz; 1 ⊩ p; los demás, nada
def kmodK : Kripke where
  le v w := v = w ∨ v = 0
  val w x := w = 1 ∧ x = 0
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
      | intro h1 _ => exact absurd h1 (by decide)

theorem kremer_not_nj : ¬ NJ [] (.or (negF (.atom 0)) (negF (negF (.atom 0)))) := fun d => by
  have h := kripke_sound kmodK d 0 (fun _ hθ => by cases hθ)
  cases h with
  | inl h₁ => exact h₁ 1 (Or.inr rfl) ⟨rfl, rfl⟩
  | inr h₂ =>
    apply h₂ 2 (Or.inr rfl)
    intro u hu hv
    cases hu with
    | inl e =>
      subst e
      cases hv with
      | intro h1 _ => exact absurd h1 (by decide)
    | inr e => exact absurd e (by decide)

theorem finite_schematic_incomplete :
    ¬ (∀ (Γ : List Form) (φ : Form), validF Γ φ → NJ Γ φ) :=
  fun hc => kremer_not_nj (hc [] _ (finite_kremer (.atom 0)))

/-! ## Conjetura inquisitiva, I: 𝒩 finita y simulación semántica
  Sin ∨ ni ⊥, la base 𝒩 de Sandqvist es finita: (†) vale en la clase finita y el
  fragmento es completo. Una derivación en L ∪ 𝒩 se traduce en soporte sobre las
  extensiones de L (simulación semántica); no hace falta renombrar átomos. -/

theorem mem_nil_false {α : Type} {x : α} (h : x ∈ ([] : List α)) : False := by cases h

-- sin ∨ ni ⊥
def nvb : Form → Prop
  | .atom _  => True
  | .bot     => False
  | .and a b => nvb a ∧ nvb b
  | .or _ _  => False
  | .imp a b => nvb a ∧ nvb b

theorem nvb_subs (χ : Form) : nvb χ → ∀ ζ, ζ ∈ subs χ → nvb ζ := by
  induction χ with
  | atom _ =>
    intro _ ζ hζ
    cases List.mem_cons.mp hζ with
    | inl e => subst e; exact True.intro
    | inr h => exact (mem_nil_false h).elim
  | bot => intro h; exact False.elim h
  | or _ _ _ _ => intro h; exact False.elim h
  | and _ _ iha ihb =>
    intro h ζ hζ
    cases List.mem_cons.mp hζ with
    | inl e => subst e; exact h
    | inr h' =>
      cases List.mem_append.mp h' with
      | inl ha => exact iha (And.left h) ζ ha
      | inr hb => exact ihb (And.right h) ζ hb
  | imp _ _ iha ihb =>
    intro h ζ hζ
    cases List.mem_cons.mp hζ with
    | inl e => subst e; exact h
    | inr h' =>
      cases List.mem_append.mp h' with
      | inl ha => exact iha (And.left h) ζ ha
      | inr hb => exact ihb (And.right h) ζ hb

theorem nvb_subsL (L : List Form) (h : ∀ θ, θ ∈ L → nvb θ) : ∀ χ, χ ∈ subsL L → nvb χ := by
  induction L with
  | nil => intro χ hχ; exact (mem_nil_false hχ).elim
  | cons θ L ih =>
    intro χ hχ
    cases List.mem_append.mp hχ with
    | inl h1 => exact nvb_subs θ (h θ mem0) χ h1
    | inr h2 => exact ih (fun θ' hθ' => h θ' (List.mem_cons.mpr (Or.inr hθ'))) χ h2

-- reglas de 𝒩 como lista (vacía en átomos, ⊥ y ∨)
def nRuleL (fl : Form → Atom) : Form → List Rule
  | .atom _  => []
  | .bot     => []
  | .or _ _  => []
  | .and a b => [⟨[([], fl a), ([], fl b)], fl (.and a b)⟩,
                 ⟨[([], fl (.and a b))], fl a⟩,
                 ⟨[([], fl (.and a b))], fl b⟩]
  | .imp a b => [⟨[([fl a], fl b)], fl (.imp a b)⟩,
                 ⟨[([], fl (.imp a b)), ([], fl a)], fl b⟩]

def nL (fl : Form → Atom) : List Form → List Rule
  | []     => []
  | χ :: Ξ => nRuleL fl χ ++ nL fl Ξ

theorem mem_nL {fl : Form → Atom} {Ξ : List Form} {χ : Form} (hχ : χ ∈ Ξ) {x : Rule}
    (hx : x ∈ nRuleL fl χ) : x ∈ nL fl Ξ := by
  induction Ξ with
  | nil => exact (mem_nil_false hχ).elim
  | cons θ Ξ ih =>
    cases List.mem_cons.mp hχ with
    | inl e => subst e; exact List.mem_append.mpr (Or.inl hx)
    | inr h => exact List.mem_append.mpr (Or.inr (ih h))

theorem nL_inv {fl : Form → Atom} {Ξ : List Form} {x : Rule} (h : x ∈ nL fl Ξ) :
    ∃ χ, χ ∈ Ξ ∧ x ∈ nRuleL fl χ := by
  induction Ξ with
  | nil => exact (mem_nil_false h).elim
  | cons θ Ξ ih =>
    cases List.mem_append.mp h with
    | inl h1 => exact ⟨θ, mem0, h1⟩
    | inr h2 =>
      cases ih h2 with
      | intro χ hχ => exact ⟨χ, List.mem_cons.mpr (Or.inr hχ.1), hχ.2⟩

theorem nRuleL_sub {fl : Form → Atom} {χ : Form} {x : Rule} (hx : x ∈ nRuleL fl χ) :
    nRule fl χ x := by
  cases χ with
  | atom _ => exact (mem_nil_false hx).elim
  | bot => exact (mem_nil_false hx).elim
  | or _ _ => exact (mem_nil_false hx).elim
  | and _ _ =>
    cases List.mem_cons.mp hx with
    | inl e => exact Or.inl e
    | inr h =>
      cases List.mem_cons.mp h with
      | inl e => exact Or.inr (Or.inl e)
      | inr h' =>
        cases List.mem_cons.mp h' with
        | inl e => exact Or.inr (Or.inr e)
        | inr h'' => exact (mem_nil_false h'').elim
  | imp _ _ =>
    cases List.mem_cons.mp hx with
    | inl e => exact Or.inl e
    | inr h =>
      cases List.mem_cons.mp h with
      | inl e => exact Or.inr e
      | inr h' => exact (mem_nil_false h').elim

theorem nL_sub_NBase {fl : Form → Atom} {Ξ : List Form} :
    Ext (ofList (nL fl Ξ)) (NBase fl Ξ) := by
  intro x hx
  cases nL_inv hx with
  | intro χ hχ => exact ⟨χ, hχ.1, nRuleL_sub hχ.2⟩

-- (†) en la clase finita
theorem daggerF {fl : Form → Atom} (hfl : ∀ p, fl (.atom p) = p) {Ξ : List Form}
    (hcl : Closed Ξ) (hnv : ∀ χ, χ ∈ Ξ → nvb χ) (χ : Form) : χ ∈ Ξ →
      ∀ {L : List Rule}, Ext (ofList (nL fl Ξ)) (ofList L) →
        (suppF L χ ↔ Deriv (ofList L) [] (fl χ)) := by
  induction χ with
  | atom _ =>
    intro _ L _
    simp only [suppF, hfl]
  | bot => intro hχ; exact False.elim (hnv _ hχ)
  | or _ _ _ _ => intro hχ; exact False.elim (hnv _ hχ)
  | and a b iha ihb =>
    intro hχ L hNL
    have ha := hcl _ hχ a (sub_l rfl)
    have hb := hcl _ hχ b (sub_r rfl)
    simp only [suppF]
    constructor
    · intro h
      exact Deriv.app2 (hNL ⟨[([], fl a), ([], fl b)], fl (.and a b)⟩ (mem_nL hχ mem0))
        ((iha ha hNL).mp h.1) ((ihb hb hNL).mp h.2)
    · intro h
      exact ⟨(iha ha hNL).mpr
              (Deriv.app1 (hNL ⟨[([], fl (.and a b))], fl a⟩ (mem_nL hχ mem1)) h),
             (ihb hb hNL).mpr
              (Deriv.app1 (hNL ⟨[([], fl (.and a b))], fl b⟩ (mem_nL hχ mem2)) h)⟩
  | imp a b iha ihb =>
    intro hχ L hNL
    have ha := hcl _ hχ a (sub_l rfl)
    have hb := hcl _ hχ b (sub_r rfl)
    simp only [suppF]
    constructor
    · intro h
      refine Deriv.app1 (hNL ⟨[([fl a], fl b)], fl (.imp a b)⟩ (mem_nL hχ mem0)) ?_
      show Deriv (ofList L) [fl a] (fl b)
      rw [atomic_adequacyF]
      intro D hCD hT
      have hND := Ext.trans hNL hCD
      exact (ihb hb hND).mp (h D hCD ((iha ha hND).mpr (hT _ mem0)))
    · intro h D hCD hDa
      have hND := Ext.trans hNL hCD
      exact (ihb hb hND).mpr (Deriv.app2
        (hND ⟨[([], fl (.imp a b)), ([], fl a)], fl b⟩ (mem_nL hχ mem1))
        (Deriv.mono hCD h) ((iha ha hND).mp hDa))

-- fragmento sin ∨ ni ⊥: la clase finita es completa
theorem finite_complete_nvb {Γ : List Form} {φ : Form} (hΓ : ∀ θ, θ ∈ Γ → nvb θ)
    (hφ : nvb φ) (hv : validF Γ φ) : NJ Γ φ := by
  have hcl : Closed (Xi Γ φ) := subsL_closed _
  have hnv : ∀ χ, χ ∈ Xi Γ φ → nvb χ := nvb_subsL (φ :: Γ) (fun θ hθ => by
    cases List.mem_cons.mp hθ with
    | inl e => rw [e]; exact hφ
    | inr h => exact hΓ θ h)
  have hM : ∀ p, Form.atom p ∈ Xi Γ φ → p ≤ bnd Γ φ := fun p h => atom_le_sumAtL p _ h
  have hun : ∀ χ, χ ∈ Xi Γ φ →
      unflat (bnd Γ φ) (Xi Γ φ) (flat (bnd Γ φ) (Xi Γ φ) χ) = χ := unflat_flat hM
  have hφX : φ ∈ Xi Γ φ := mem_subsL_of _ mem0
  have hΓX : ∀ θ, θ ∈ Γ → θ ∈ Xi Γ φ :=
    fun θ h => mem_subsL_of _ (List.mem_cons.mpr (Or.inr h))
  -- Γ♭ ⊢_𝒩 φ♭, con 𝒩 finita
  have hd : Deriv (ofList (nL (flat (bnd Γ φ) (Xi Γ φ)) (Xi Γ φ)))
      (Γ.map (flat (bnd Γ φ) (Xi Γ φ))) (flat (bnd Γ φ) (Xi Γ φ) φ) := by
    rw [atomic_adequacyF]
    intro L' hNL hT
    apply (daggerF (fl := flat (bnd Γ φ) (Xi Γ φ)) (fun _ => rfl) hcl hnv φ hφX hNL).mp
    apply hv L'
    intro θ hθ
    exact (daggerF (fl := flat (bnd Γ φ) (Xi Γ φ)) (fun _ => rfl) hcl hnv θ (hΓX θ hθ) hNL).mpr
      (hT _ (List.mem_map.mpr ⟨θ, hθ, rfl⟩))
  have hs := simulation hcl hun
    (Deriv.mono (nL_sub_NBase (fl := flat (bnd Γ φ) (Xi Γ φ))) hd)
  rw [map_inv Γ (fun θ h => hun θ (hΓX θ h)), hun φ hφX] at hs
  exact hs

theorem finite_nvb_iff {Γ : List Form} {φ : Form} (hΓ : ∀ θ, θ ∈ Γ → nvb θ) (hφ : nvb φ) :
    validF Γ φ ↔ NJ Γ φ :=
  ⟨finite_complete_nvb hΓ hφ, soundnessF⟩

-- simulación semántica: L ∪ 𝒩 ⊢_S q ⟹ (⊩ S♮ ⟹ ⊩ q♮) en toda extensión de L
theorem ssim {fl : Form → Atom} {un : Atom → Form} {Ξ : List Form} (hcl : Closed Ξ)
    (hun : ∀ χ, χ ∈ Ξ → un (fl χ) = χ) {L : List Rule}
    (hL : ∀ x, x ∈ L → un x.concl = .atom x.concl ∧
      ∀ pq, pq ∈ x.prems → un pq.2 = .atom pq.2 ∧ ∀ t, t ∈ pq.1 → un t = .atom t)
    {S : List Atom} {q : Atom} (d : Deriv (ofList (L ++ nL fl Ξ)) S q) :
    ∀ L', Ext (ofList L) (ofList L') → (∀ s, s ∈ S → suppF L' (un s)) → suppF L' (un q) := by
  induction d with
  | ref h => intro L' _ hS; exact hS _ h
  | app x hx _ ih =>
    intro L' hLL' hS
    cases List.mem_append.mp hx with
    | inl hl =>
      -- regla de L
      have hx' := hL x hl
      rw [hx'.1]
      show Deriv (ofList L') [] x.concl
      refine Deriv.app x (hLL' x hl) (fun pq hpq => ?_)
      rw [atomic_adequacyF]
      intro L'' hL'' hT
      have h : suppF L'' (un pq.2) := ih pq hpq L'' (Ext.trans hLL' hL'') (fun s hs => by
        cases List.mem_append.mp hs with
        | inl h1 =>
          rw [(hx'.2 pq hpq).2 s h1]
          exact hT s (List.mem_append.mpr (Or.inl h1))
        | inr h2 => exact suppF_mono _ hL'' (hS s h2))
      rw [(hx'.2 pq hpq).1] at h
      exact h
    | inr hn =>
      -- regla de 𝒩
      cases nL_inv hn with
      | intro χ hχ =>
        cases χ with
        | atom _ => exact (mem_nil_false hχ.2).elim
        | bot => exact (mem_nil_false hχ.2).elim
        | or _ _ => exact (mem_nil_false hχ.2).elim
        | and a b =>
          have ha : a ∈ Ξ := hcl _ hχ.1 a (sub_l rfl)
          have hb : b ∈ Ξ := hcl _ hχ.1 b (sub_r rfl)
          have hab : un (fl (.and a b)) = .and a b := hun _ hχ.1
          cases List.mem_cons.mp hχ.2 with
          | inl e =>
            subst e
            have h1 : suppF L' (un (fl a)) := ih ([], fl a) mem0 L' hLL' (fun s hs => hS s hs)
            have h2 : suppF L' (un (fl b)) := ih ([], fl b) mem1 L' hLL' (fun s hs => hS s hs)
            rw [hun a ha] at h1
            rw [hun b hb] at h2
            show suppF L' (un (fl (.and a b)))
            rw [hab]
            exact ⟨h1, h2⟩
          | inr h' =>
            cases List.mem_cons.mp h' with
            | inl e =>
              subst e
              have h : suppF L' (un (fl (.and a b))) :=
                ih ([], fl (.and a b)) mem0 L' hLL' (fun s hs => hS s hs)
              rw [hab] at h
              show suppF L' (un (fl a))
              rw [hun a ha]
              exact And.left h
            | inr h'' =>
              cases List.mem_cons.mp h'' with
              | inl e =>
                subst e
                have h : suppF L' (un (fl (.and a b))) :=
                  ih ([], fl (.and a b)) mem0 L' hLL' (fun s hs => hS s hs)
                rw [hab] at h
                show suppF L' (un (fl b))
                rw [hun b hb]
                exact And.right h
              | inr h3 => exact (mem_nil_false h3).elim
        | imp a b =>
          have ha : a ∈ Ξ := hcl _ hχ.1 a (sub_l rfl)
          have hb : b ∈ Ξ := hcl _ hχ.1 b (sub_r rfl)
          have hab : un (fl (.imp a b)) = .imp a b := hun _ hχ.1
          cases List.mem_cons.mp hχ.2 with
          | inl e =>
            subst e
            show suppF L' (un (fl (.imp a b)))
            rw [hab]
            intro L'' hL'' haL
            have h : suppF L'' (un (fl b)) :=
              ih ([fl a], fl b) mem0 L'' (Ext.trans hLL' hL'') (fun s hs => by
                cases List.mem_cons.mp hs with
                | inl e' => subst e'; rw [hun a ha]; exact haL
                | inr h' => exact suppF_mono _ hL'' (hS s h'))
            rw [hun b hb] at h
            exact h
          | inr h' =>
            cases List.mem_cons.mp h' with
            | inl e =>
              subst e
              have h1 : suppF L' (un (fl (.imp a b))) :=
                ih ([], fl (.imp a b)) mem0 L' hLL' (fun s hs => hS s hs)
              have h2 : suppF L' (un (fl a)) := ih ([], fl a) mem1 L' hLL' (fun s hs => hS s hs)
              rw [hab] at h1
              rw [hun a ha] at h2
              show suppF L' (un (fl b))
              rw [hun b hb]
              exact h1 L' (Ext.refl _) h2
            | inr h'' => exact (mem_nil_false h'').elim

-- L ∪ 𝒩 ⊢ χ♭ ⟹ L ⊩ χ
theorem ssim_nil {fl : Form → Atom} {un : Atom → Form} {Ξ : List Form} (hcl : Closed Ξ)
    (hun : ∀ χ, χ ∈ Ξ → un (fl χ) = χ) {L : List Rule}
    (hL : ∀ x, x ∈ L → un x.concl = .atom x.concl ∧
      ∀ pq, pq ∈ x.prems → un pq.2 = .atom pq.2 ∧ ∀ t, t ∈ pq.1 → un t = .atom t)
    {χ : Form} (hχ : χ ∈ Ξ) (d : Deriv (ofList (L ++ nL fl Ξ)) [] (fl χ)) : suppF L χ := by
  have h := ssim hcl hun hL d L (Ext.refl _) (fun s hs => (mem_nil_false hs).elim)
  rw [hun χ hχ] at h
  exact h

-- L ∪ 𝒩, α♭ ⊢ β♭ ⟹ L ⊩ α → β
theorem ssim_imp {fl : Form → Atom} {un : Atom → Form} {Ξ : List Form} (hcl : Closed Ξ)
    (hun : ∀ χ, χ ∈ Ξ → un (fl χ) = χ) {L : List Rule}
    (hL : ∀ x, x ∈ L → un x.concl = .atom x.concl ∧
      ∀ pq, pq ∈ x.prems → un pq.2 = .atom pq.2 ∧ ∀ t, t ∈ pq.1 → un t = .atom t)
    {α β : Form} (hα : α ∈ Ξ) (hβ : β ∈ Ξ)
    (d : Deriv (ofList (L ++ nL fl Ξ)) [fl α] (fl β)) : suppF L (.imp α β) := by
  intro L' hLL' hαL
  have h := ssim hcl hun hL d L' hLL' (fun s hs => by
    cases List.mem_cons.mp hs with
    | inl e => rw [e, hun α hα]; exact hαL
    | inr h' => exact (mem_nil_false h').elim)
  rw [hun β hβ] at h
  exact h

/-! ## Conjetura inquisitiva, II: forma normal semántica
  Toda φ soporta, base a base, lo mismo que alguna αᵢ de una lista sin ∨ ni ⊥.
  ∨: átomo fresco sobre los nombres αᵢ♭. →: ssim_imp con el hecho α♭.
  Consecuencias: propiedad de disyunción en cada base, H para Harrop, y la validez
  reducida a NJ sobre fórmulas sin ∨ ni ⊥. -/

-- cotas de átomos
theorem idx_le (Ξ : List Form) (χ : Form) : idx Ξ χ ≤ Ξ.length := by
  induction Ξ with
  | nil => exact Nat.le_refl 0
  | cons θ Ξ ih =>
    by_cases e : θ = χ
    · rw [idx, ite_eq_left e]; exact Nat.zero_le _
    · rw [idx, ite_eq_right e]; exact Nat.succ_le_succ ih

theorem flat_le {M : Nat} {Ξ : List Form} (hM : ∀ p, Form.atom p ∈ Ξ → p ≤ M) (χ : Form)
    (hχ : χ ∈ Ξ) : flat M Ξ χ ≤ M + 1 + Ξ.length := by
  cases χ with
  | atom p =>
    exact Nat.le_trans (hM p hχ) (Nat.le_trans (Nat.le_add_right M 1) (Nat.le_add_right _ _))
  | bot => exact Nat.add_le_add_left (idx_le Ξ _) _
  | and a b => exact Nat.add_le_add_left (idx_le Ξ _) _
  | or a b => exact Nat.add_le_add_left (idx_le Ξ _) _
  | imp a b => exact Nat.add_le_add_left (idx_le Ξ _) _

theorem unflat_le {M : Nat} {Ξ : List Form} {a : Atom} (h : a ≤ M) :
    unflat M Ξ a = .atom a := by
  unfold unflat
  rw [ite_eq_right (Nat.not_lt.mpr h)]

theorem atoms_le_lbound {L : List Rule} {x : Rule} (hx : x ∈ L) :
    x.concl ≤ lbound L ∧
      ∀ pq, pq ∈ x.prems → pq.2 ≤ lbound L ∧ ∀ t, t ∈ pq.1 → t ≤ lbound L := by
  have hx' : rbound x ≤ lbound L := le_lbound L hx
  have hc : x.concl ≤ rbound x := Nat.le_add_right _ _
  refine ⟨Nat.le_trans hc hx', fun pq hpq => ?_⟩
  have hp : pq.2 + sumN pq.1 ≤ rbound x :=
    Nat.le_trans (le_pbound x.prems hpq) (Nat.le_add_left _ _)
  have h1 : pq.2 ≤ rbound x := Nat.le_trans (Nat.le_add_right _ _) hp
  refine ⟨Nat.le_trans h1 hx', fun t ht => ?_⟩
  have h2 : t ≤ rbound x :=
    Nat.le_trans (le_sumN pq.1 ht) (Nat.le_trans (Nat.le_add_left _ _) hp)
  exact Nat.le_trans h2 hx'

-- los átomos de L quedan fijos bajo ♮
theorem unflat_rules {L : List Rule} {M : Nat} {Ξ : List Form} (hM : lbound L ≤ M) :
    ∀ x, x ∈ L → unflat M Ξ x.concl = .atom x.concl ∧
      ∀ pq, pq ∈ x.prems → unflat M Ξ pq.2 = .atom pq.2 ∧
        ∀ t, t ∈ pq.1 → unflat M Ξ t = .atom t := by
  intro x hx
  have h := atoms_le_lbound hx
  exact ⟨unflat_le (Nat.le_trans h.1 hM), fun pq hpq =>
    ⟨unflat_le (Nat.le_trans (h.2 pq hpq).1 hM),
     fun t ht => unflat_le (Nat.le_trans ((h.2 pq hpq).2 t ht) hM)⟩⟩

-- disyunción de nombres: alguna se soporta (átomo fresco r, reglas α♭ ⇒ r)
theorem fresh_choice_aux {fl : Form → Atom} {un : Atom → Form} {Ξ : List Form}
    (hfl : ∀ p, fl (.atom p) = p) (hcl : Closed Ξ) (hnv : ∀ χ, χ ∈ Ξ → nvb χ)
    (hun : ∀ χ, χ ∈ Ξ → un (fl χ) = χ) {L : List Rule}
    (hL : ∀ x, x ∈ L → un x.concl = .atom x.concl ∧
      ∀ pq, pq ∈ x.prems → un pq.2 = .atom pq.2 ∧ ∀ t, t ∈ pq.1 → un t = .atom t)
    {A : List Form} (hAΞ : ∀ α, α ∈ A → α ∈ Ξ) {r : Atom}
    (hfr : ∀ x, x ∈ L ++ nL fl Ξ → x.concl ≠ r ∧ ∀ pq, pq ∈ x.prems → pq.2 ≠ r ∧ r ∉ pq.1)
    (hrA : ∀ α, α ∈ A → fl α ≠ r)
    (h : ∀ L', Ext (ofList L) (ofList L') → ∀ p : Atom,
      (∀ L'', Ext (ofList L') (ofList L'') → (∃ α, α ∈ A ∧ suppF L'' α) →
        Deriv (ofList L'') [] p) → Deriv (ofList L') [] p) :
    ∃ α, α ∈ A ∧ suppF L α := by
  have hE : ∀ e, e ∈ A.map (fun α => (⟨[([], fl α)], r⟩ : Rule)) → e.concl = r := by
    intro e he
    cases List.mem_map.mp he with
    | intro α hα =>
      cases hα with
      | intro _ e' => subst e'; rfl
  have hext : Ext (ofList L)
      (ofList ((L ++ nL fl Ξ) ++ A.map (fun α => (⟨[([], fl α)], r⟩ : Rule)))) :=
    fun _ hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
  have d := h _ hext r (fun L'' hL'' hex => by
    cases hex with
    | intro α hα =>
      have hNL : Ext (ofList (nL fl Ξ)) (ofList L'') := fun x hx =>
        hL'' x (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
      have hd := (daggerF hfl hcl hnv α (hAΞ α hα.1) hNL).mp hα.2
      exact Deriv.app1 (hL'' ⟨[([], fl α)], r⟩
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨α, hα.1, rfl⟩)))) hd)
  cases last_fresh hfr d (fun h' => mem_nil_false h') rfl with
  | intro e he =>
    cases List.mem_map.mp he.1 with
    | intro α hα =>
      cases hα with
      | intro hαA e' =>
        subst e'
        have d1 : Deriv (ofList ((L ++ nL fl Ξ) ++ A.map (fun α => (⟨[([], fl α)], r⟩ : Rule))))
            [] (fl α) := he.2 ([], fl α) mem0
        exact ⟨α, hαA, ssim_nil hcl hun hL (hAΞ α hαA)
          (deriv_fresh hfr hE d1 (fun h' => mem_nil_false h') (hrA α hαA))⟩

theorem fresh_choice {L : List Rule} {A : List Form} (hA : ∀ α, α ∈ A → nvb α)
    (h : ∀ L', Ext (ofList L) (ofList L') → ∀ p : Atom,
      (∀ L'', Ext (ofList L') (ofList L'') → (∃ α, α ∈ A ∧ suppF L'' α) →
        Deriv (ofList L'') [] p) → Deriv (ofList L') [] p) :
    ∃ α, α ∈ A ∧ suppF L α := by
  have hMΞ : ∀ p, Form.atom p ∈ subsL A → p ≤ lbound L + sumAtL A :=
    fun p hp => Nat.le_trans (atom_le_sumAtL p A hp) (Nat.le_add_left _ _)
  have hfr := fresh_of_gt (L := L ++ nL (flat (lbound L + sumAtL A) (subsL A)) (subsL A))
    (r := lbound (L ++ nL (flat (lbound L + sumAtL A) (subsL A)) (subsL A)) +
      (lbound L + sumAtL A + 1 + (subsL A).length) + 1)
    (Nat.lt_succ_of_le (Nat.le_add_right _ _))
  exact fresh_choice_aux (fl := flat (lbound L + sumAtL A) (subsL A)) (Ξ := subsL A) (L := L)
    (fun _ => rfl) (subsL_closed A) (nvb_subsL A hA) (unflat_flat hMΞ)
    (unflat_rules (Nat.le_add_right _ _)) (fun α hα => mem_subsL_of A hα) hfr
    (fun α hα => Nat.ne_of_lt (Nat.lt_succ_of_le
      (Nat.le_trans (flat_le hMΞ α (mem_subsL_of A hα)) (Nat.le_add_left _ _))))
    h

-- α → ⋁B: algún β con ⊩ α → β (hecho α♭ y ssim_imp)
theorem imp_choice_aux {fl : Form → Atom} {un : Atom → Form} {Ξ : List Form}
    (hfl : ∀ p, fl (.atom p) = p) (hcl : Closed Ξ) (hnv : ∀ χ, χ ∈ Ξ → nvb χ)
    (hun : ∀ χ, χ ∈ Ξ → un (fl χ) = χ) {L : List Rule}
    (hL : ∀ x, x ∈ L → un x.concl = .atom x.concl ∧
      ∀ pq, pq ∈ x.prems → un pq.2 = .atom pq.2 ∧ ∀ t, t ∈ pq.1 → un t = .atom t)
    {α : Form} {B : List Form} (hαΞ : α ∈ Ξ) (hBΞ : ∀ β, β ∈ B → β ∈ Ξ)
    (h : ∀ L', Ext (ofList L) (ofList L') → suppF L' α → ∃ β, β ∈ B ∧ suppF L' β) :
    ∃ β, β ∈ B ∧ suppF L (.imp α β) := by
  have hext : Ext (ofList L) (ofList ((L ++ nL fl Ξ) ++ factsL [fl α])) :=
    fun _ hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx)))
  have hNL : Ext (ofList (nL fl Ξ)) (ofList ((L ++ nL fl Ξ) ++ factsL [fl α])) :=
    fun _ hx => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx)))
  have hα1 : suppF ((L ++ nL fl Ξ) ++ factsL [fl α]) α :=
    (daggerF hfl hcl hnv α hαΞ hNL).mpr
      (Deriv.app ⟨[], fl α⟩ (List.mem_append.mpr (Or.inr mem0))
        (fun _ h' => (mem_nil_false h').elim))
  cases h _ hext hα1 with
  | intro β hβ =>
    have d : Deriv (ofList ((L ++ nL fl Ξ) ++ factsL [fl α])) [] (fl β) :=
      (daggerF hfl hcl hnv β (hBΞ β hβ.1) hNL).mp hβ.2
    have d' : Deriv (ofList (L ++ nL fl Ξ)) [fl α] (fl β) :=
      Deriv.facts_to_ctx (Deriv.mono (ext_factsL₁ (L ++ nL fl Ξ) [fl α]) d)
    exact ⟨β, hβ.1, ssim_imp hcl hun hL hαΞ (hBΞ β hβ.1) d'⟩

theorem imp_choice {L : List Rule} {α : Form} {B : List Form} (hα : nvb α)
    (hB : ∀ β, β ∈ B → nvb β)
    (h : ∀ L', Ext (ofList L) (ofList L') → suppF L' α → ∃ β, β ∈ B ∧ suppF L' β) :
    ∃ β, β ∈ B ∧ suppF L (.imp α β) := by
  have hall : ∀ θ, θ ∈ α :: B → nvb θ := fun θ hθ => by
    cases List.mem_cons.mp hθ with
    | inl e => rw [e]; exact hα
    | inr h' => exact hB θ h'
  have hMΞ : ∀ p, Form.atom p ∈ subsL (α :: B) → p ≤ lbound L + sumAtL (α :: B) :=
    fun p hp => Nat.le_trans (atom_le_sumAtL p _ hp) (Nat.le_add_left _ _)
  exact imp_choice_aux (fl := flat (lbound L + sumAtL (α :: B)) (subsL (α :: B)))
    (Ξ := subsL (α :: B)) (L := L)
    (fun _ => rfl) (subsL_closed _) (nvb_subsL _ hall) (unflat_flat hMΞ)
    (unflat_rules (Nat.le_add_right _ _)) (mem_subsL_of _ mem0)
    (fun β hβ => mem_subsL_of _ (List.mem_cons.mpr (Or.inr hβ))) h

-- combinadores de listas
def topF : Form := .imp (.atom 0) (.atom 0)

theorem supp_top (L : List Rule) : suppF L topF := fun _ _ h => h

theorem nvb_top : nvb topF := ⟨True.intro, True.intro⟩

def andL : List Form → List Form → List Form
  | [],     _ => []
  | x :: X, Y => Y.map (fun y => .and x y) ++ andL X Y

theorem andL_nvb {X Y : List Form} (hX : ∀ x, x ∈ X → nvb x) (hY : ∀ y, y ∈ Y → nvb y) :
    ∀ γ, γ ∈ andL X Y → nvb γ := by
  induction X with
  | nil => intro γ h; exact (mem_nil_false h).elim
  | cons x X ih =>
    intro γ h
    cases List.mem_append.mp h with
    | inl h1 =>
      cases List.mem_map.mp h1 with
      | intro y hy =>
        cases hy with
        | intro hyY e => subst e; exact ⟨hX x mem0, hY y hyY⟩
    | inr h2 => exact ih (fun x' hx' => hX x' (List.mem_cons.mpr (Or.inr hx'))) γ h2

theorem andL_supp {L : List Rule} (X Y : List Form) :
    (∃ γ, γ ∈ andL X Y ∧ suppF L γ) ↔
      (∃ x, x ∈ X ∧ suppF L x) ∧ (∃ y, y ∈ Y ∧ suppF L y) := by
  induction X with
  | nil =>
    constructor
    · intro h
      cases h with
      | intro γ hγ => exact (mem_nil_false hγ.1).elim
    · intro h
      cases h.1 with
      | intro x hx => exact (mem_nil_false hx.1).elim
  | cons x X ih =>
    constructor
    · intro h
      cases h with
      | intro γ hγ =>
        cases List.mem_append.mp hγ.1 with
        | inl h1 =>
          cases List.mem_map.mp h1 with
          | intro y hy =>
            cases hy with
            | intro hyY e =>
              subst e
              have hs : suppF L (.and x y) := hγ.2
              exact ⟨⟨x, mem0, And.left hs⟩, ⟨y, hyY, And.right hs⟩⟩
        | inr h2 =>
          cases ih.mp ⟨γ, h2, hγ.2⟩ with
          | intro hx hy =>
            cases hx with
            | intro x' hx' => exact ⟨⟨x', List.mem_cons.mpr (Or.inr hx'.1), hx'.2⟩, hy⟩
    · intro h
      cases h with
      | intro hx hy =>
        cases hx with
        | intro x' hx' =>
          cases hy with
          | intro y hy' =>
            cases List.mem_cons.mp hx'.1 with
            | inl e =>
              have hsx : suppF L x := by rw [← e]; exact hx'.2
              have hs : suppF L (.and x y) := ⟨hsx, hy'.2⟩
              exact ⟨.and x y, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨y, hy'.1, rfl⟩)), hs⟩
            | inr h' =>
              cases ih.mpr ⟨⟨x', h', hx'.2⟩, ⟨y, hy'.1, hy'.2⟩⟩ with
              | intro γ hγ => exact ⟨γ, List.mem_append.mpr (Or.inr hγ.1), hγ.2⟩

theorem andL_len {X Y : List Form} (hX : X.length ≤ 1) (hY : Y.length ≤ 1) :
    (andL X Y).length ≤ 1 := by
  cases X with
  | nil => exact Nat.zero_le _
  | cons x X' =>
    cases X' with
    | nil =>
      show (Y.map (fun y => Form.and x y) ++ []).length ≤ 1
      rw [List.append_nil, List.length_map]
      exact hY
    | cons _ X'' => exact absurd (Nat.le_of_succ_le_succ hX) (Nat.not_succ_le_zero _)

-- ⋀ᵢ (aᵢ → b_{f i}), f elección
def impNF (B : List Form) : List Form → List Form
  | []     => [topF]
  | a :: A => andL (B.map (fun b => .imp a b)) (impNF B A)

theorem impNF_nvb {A B : List Form} (hA : ∀ a, a ∈ A → nvb a) (hB : ∀ b, b ∈ B → nvb b) :
    ∀ γ, γ ∈ impNF B A → nvb γ := by
  induction A with
  | nil =>
    intro γ h
    cases List.mem_cons.mp h with
    | inl e => rw [e]; exact nvb_top
    | inr h' => exact (mem_nil_false h').elim
  | cons a A ih =>
    intro γ h
    exact andL_nvb (fun x hx => by
        cases List.mem_map.mp hx with
        | intro b hb =>
          cases hb with
          | intro hbB e => subst e; exact ⟨hA a mem0, hB b hbB⟩)
      (ih (fun a' ha' => hA a' (List.mem_cons.mpr (Or.inr ha')))) γ h

theorem impNF_supp {L : List Rule} (B A : List Form) :
    (∃ γ, γ ∈ impNF B A ∧ suppF L γ) ↔ ∀ a, a ∈ A → ∃ b, b ∈ B ∧ suppF L (.imp a b) := by
  induction A with
  | nil =>
    constructor
    · intro _ a ha; exact (mem_nil_false ha).elim
    · intro _; exact ⟨topF, mem0, supp_top L⟩
  | cons a A ih =>
    show (∃ γ, γ ∈ andL (B.map (fun b => .imp a b)) (impNF B A) ∧ suppF L γ) ↔ _
    rw [andL_supp]
    constructor
    · intro h a' ha'
      cases List.mem_cons.mp ha' with
      | inl e =>
        rw [e]
        cases h.1 with
        | intro x hx =>
          cases List.mem_map.mp hx.1 with
          | intro b hb =>
            cases hb with
            | intro hbB e' => subst e'; exact ⟨b, hbB, hx.2⟩
      | inr h' => exact (ih.mp h.2) a' h'
    · intro h
      constructor
      · cases h a mem0 with
        | intro b hb => exact ⟨.imp a b, List.mem_map.mpr ⟨b, hb.1, rfl⟩, hb.2⟩
      · exact ih.mpr (fun a' ha' => h a' (List.mem_cons.mpr (Or.inr ha')))

theorem impNF_len {B : List Form} (hB : B.length ≤ 1) (A : List Form) :
    (impNF B A).length ≤ 1 := by
  induction A with
  | nil => exact Nat.le_refl _
  | cons a A ih =>
    exact andL_len (by rw [List.length_map]; exact hB) ih

-- ∨I en la clase finita
theorem or_introF₁ {L : List Rule} {φ : Form} (ψ : Form) (h : suppF L φ) :
    suppF L (.or φ ψ) :=
  fun L' hLL' _ k₁ _ => k₁ L' (Ext.refl _) (suppF_mono φ hLL' h)

theorem or_introF₂ {L : List Rule} (φ : Form) {ψ : Form} (h : suppF L ψ) :
    suppF L (.or φ ψ) :=
  fun L' hLL' _ _ k₂ => k₂ L' (Ext.refl _) (suppF_mono ψ hLL' h)

-- paso de ∨
theorem or_choice {L : List Rule} {φ ψ : Form} {Aφ Aψ : List Form}
    (hnφ : ∀ α, α ∈ Aφ → nvb α) (hnψ : ∀ α, α ∈ Aψ → nvb α)
    (hφ : ∀ L₀, suppF L₀ φ ↔ ∃ α, α ∈ Aφ ∧ suppF L₀ α)
    (hψ : ∀ L₀, suppF L₀ ψ ↔ ∃ α, α ∈ Aψ ∧ suppF L₀ α)
    (h : suppF L (.or φ ψ)) : ∃ α, α ∈ Aφ ++ Aψ ∧ suppF L α := by
  refine fresh_choice (A := Aφ ++ Aψ)
    (fun α hα => (List.mem_append.mp hα).elim (hnφ α) (hnψ α)) ?_
  intro L' hLL' p k
  exact h L' hLL' p
    (fun L'' hL'' hφ'' => k L'' hL'' (by
      cases (hφ L'').mp hφ'' with
      | intro α hα => exact ⟨α, List.mem_append.mpr (Or.inl hα.1), hα.2⟩))
    (fun L'' hL'' hψ'' => k L'' hL'' (by
      cases (hψ L'').mp hψ'' with
      | intro α hα => exact ⟨α, List.mem_append.mpr (Or.inr hα.1), hα.2⟩))

-- forma normal: lista de fórmulas sin ∨ ni ⊥
def nfL : Form → List Form
  | .atom p  => [.atom p]
  | .bot     => []
  | .and φ ψ => andL (nfL φ) (nfL ψ)
  | .or φ ψ  => nfL φ ++ nfL ψ
  | .imp φ ψ => impNF (nfL ψ) (nfL φ)

-- forma normal semántica
theorem nfL_spec (φ : Form) : (∀ α, α ∈ nfL φ → nvb α) ∧
    (harrop φ → (nfL φ).length ≤ 1) ∧ ∀ L, suppF L φ ↔ ∃ α, α ∈ nfL φ ∧ suppF L α := by
  induction φ with
  | atom p =>
    refine ⟨fun α hα => ?_, fun _ => Nat.le_refl _,
      fun L => ⟨fun h => ⟨.atom p, mem0, h⟩, fun h => ?_⟩⟩
    · cases List.mem_cons.mp hα with
      | inl e => rw [e]; exact True.intro
      | inr h' => exact (mem_nil_false h').elim
    · cases h with
      | intro α hα =>
        cases List.mem_cons.mp hα.1 with
        | inl e => rw [e] at hα; exact hα.2
        | inr h' => exact (mem_nil_false h').elim
  | bot =>
    refine ⟨fun α hα => (mem_nil_false hα).elim, fun _ => Nat.zero_le _,
      fun L => ⟨fun h => (finite_bot L h).elim, fun h => ?_⟩⟩
    cases h with
    | intro α hα => exact (mem_nil_false hα.1).elim
  | and φ ψ ihφ ihψ =>
    refine ⟨andL_nvb ihφ.1 ihψ.1,
      fun h => andL_len (ihφ.2.1 (And.left h)) (ihψ.2.1 (And.right h)), fun L => ?_⟩
    show suppF L (.and φ ψ) ↔ ∃ α, α ∈ andL (nfL φ) (nfL ψ) ∧ suppF L α
    rw [andL_supp]
    show suppF L φ ∧ suppF L ψ ↔ _
    rw [ihφ.2.2 L, ihψ.2.2 L]
  | or φ ψ ihφ ihψ =>
    refine ⟨fun α hα => (List.mem_append.mp hα).elim (ihφ.1 α) (ihψ.1 α),
      fun h => False.elim h,
      fun L => ⟨fun h => or_choice ihφ.1 ihψ.1 ihφ.2.2 ihψ.2.2 h, fun h => ?_⟩⟩
    cases h with
    | intro α hα =>
      cases List.mem_append.mp hα.1 with
      | inl h1 => exact or_introF₁ ψ ((ihφ.2.2 L).mpr ⟨α, h1, hα.2⟩)
      | inr h2 => exact or_introF₂ φ ((ihψ.2.2 L).mpr ⟨α, h2, hα.2⟩)
  | imp φ ψ ihφ ihψ =>
    refine ⟨impNF_nvb ihφ.1 ihψ.1, fun h => impNF_len (ihψ.2.1 h) (nfL φ), fun L => ?_⟩
    show suppF L (.imp φ ψ) ↔ ∃ α, α ∈ impNF (nfL ψ) (nfL φ) ∧ suppF L α
    rw [impNF_supp]
    constructor
    · intro h a ha
      apply imp_choice (ihφ.1 a ha) ihψ.1
      intro L' hLL' haL
      apply (ihψ.2.2 L').mp
      exact h L' hLL' ((ihφ.2.2 L').mpr ⟨a, ha, haL⟩)
    · intro h L' hLL' hφL
      cases (ihφ.2.2 L').mp hφL with
      | intro a ha =>
        cases h a ha.1 with
        | intro b hb => exact (ihψ.2.2 L').mpr ⟨b, hb.1, hb.2 L' hLL' ha.2⟩

theorem nf_exists (φ : Form) : ∃ A : List Form, (∀ α, α ∈ A → nvb α) ∧
    (harrop φ → A.length ≤ 1) ∧ ∀ L, suppF L φ ↔ ∃ α, α ∈ A ∧ suppF L α :=
  ⟨nfL φ, nfL_spec φ⟩

-- propiedad de disyunción en cada base finita (GDP)
theorem finite_gdp {L : List Rule} {φ ψ : Form} (h : suppF L (.or φ ψ)) :
    suppF L φ ∨ suppF L ψ := by
  cases nf_exists φ with
  | intro Aφ hAφ =>
    cases nf_exists ψ with
    | intro Aψ hAψ =>
      cases or_choice hAφ.1 hAψ.1 hAφ.2.2 hAψ.2.2 h with
      | intro α hα =>
        cases List.mem_append.mp hα.1 with
        | inl h1 => exact Or.inl ((hAφ.2.2 L).mpr ⟨α, h1, hα.2⟩)
        | inr h2 => exact Or.inr ((hAψ.2.2 L).mpr ⟨α, h2, hα.2⟩)

theorem valid_of_nil {φ : Form} (h : suppF [] φ) : validF [] φ :=
  fun _ _ => suppF_mono φ (fun _ hx => (mem_nil_false hx).elim) h

-- propiedad de disyunción de la lógica
theorem finite_dp {φ ψ : Form} (h : validF [] (.or φ ψ)) : validF [] φ ∨ validF [] ψ :=
  (finite_gdp (h [] (fun _ hθ => (mem_nil_false hθ).elim))).elim
    (fun h1 => Or.inl (valid_of_nil h1)) (fun h2 => Or.inr (valid_of_nil h2))

-- H: (α → φ ∨ ψ) → (α → φ) ∨ (α → ψ), α de Harrop
theorem finite_H (α φ ψ : Form) (hα : harrop α) :
    validF [] (.imp (.imp α (.or φ ψ)) (.or (.imp α φ) (.imp α ψ))) := by
  intro L _ L' _ h
  cases nf_exists α with
  | intro Aα hAα =>
    cases nf_exists φ with
    | intro Aφ hAφ =>
      cases nf_exists ψ with
      | intro Aψ hAψ =>
        have hlen := hAα.2.1 hα
        cases Aα with
        | nil =>
          -- α no se soporta nunca
          apply or_introF₁
          intro L'' _ hαL
          cases (hAα.2.2 L'').mp hαL with
          | intro a ha => exact (mem_nil_false ha.1).elim
        | cons a rest =>
          cases rest with
          | cons _ _ => exact absurd (Nat.le_of_succ_le_succ hlen) (Nat.not_succ_le_zero _)
          | nil =>
            have hk : ∃ β, β ∈ Aφ ++ Aψ ∧ suppF L' (.imp a β) := by
              apply imp_choice (hAα.1 a mem0)
                (fun β hβ => (List.mem_append.mp hβ).elim (hAφ.1 β) (hAψ.1 β))
              intro L'' hL'' haL
              have hαL : suppF L'' α := (hAα.2.2 L'').mpr ⟨a, mem0, haL⟩
              exact or_choice hAφ.1 hAψ.1 hAφ.2.2 hAψ.2.2 (h L'' hL'' hαL)
            cases hk with
            | intro β hβ =>
              cases List.mem_append.mp hβ.1 with
              | inl h1 =>
                apply or_introF₁
                intro L'' hL'' hαL
                cases (hAα.2.2 L'').mp hαL with
                | intro a' ha' =>
                  cases List.mem_cons.mp ha'.1 with
                  | inl e =>
                    rw [e] at ha'
                    exact (hAφ.2.2 L'').mpr ⟨β, h1, hβ.2 L'' hL'' ha'.2⟩
                  | inr h' => exact (mem_nil_false h').elim
              | inr h2 =>
                apply or_introF₂
                intro L'' hL'' hαL
                cases (hAα.2.2 L'').mp hαL with
                | intro a' ha' =>
                  cases List.mem_cons.mp ha'.1 with
                  | inl e =>
                    rw [e] at ha'
                    exact (hAψ.2.2 L'').mpr ⟨β, h2, hβ.2 L'' hL'' ha'.2⟩
                  | inr h' => exact (mem_nil_false h').elim

-- validez en la clase finita = algún disyunto normal es teorema de NJ
theorem finite_valid_nf (φ : Form) : ∃ A : List Form, (∀ α, α ∈ A → nvb α) ∧
    (validF [] φ ↔ ∃ α, α ∈ A ∧ NJ [] α) := by
  cases nf_exists φ with
  | intro A hA =>
    refine ⟨A, hA.1, ⟨fun hv => ?_, fun h => ?_⟩⟩
    · cases (hA.2.2 []).mp (hv [] (fun _ h => (mem_nil_false h).elim)) with
      | intro α hα =>
        exact ⟨α, hα.1, finite_complete_nvb (fun _ h => (mem_nil_false h).elim)
          (hA.1 α hα.1) (valid_of_nil hα.2)⟩
    · cases h with
      | intro α hα =>
        exact valid_of_nil ((hA.2.2 []).mpr
          ⟨α, hα.1, soundnessF hα.2 [] (fun _ h => (mem_nil_false h).elim)⟩)

/-! ## Conjetura inquisitiva, III: IL + H y el ensamblaje
  NJA Ax = NJ con axiomas Ax. En NJA, cada b ∈ nfL ψ implica ψ (ISyn) y α → ψ se
  divide en los α → b (SSyn), por inducción conjunta; para ⊥ basta ¬¬p atómico.
  Sin ⊥: válida en la clase finita ⟺ teorema de IL + H, la lógica inquisitiva
  general, GKPL (Punčochář 2016, Cor. 5; Stafford–Piecha–Schroeder-Heister 2026, Def. 3.9).
  Con ⊥: GKPL + ¬¬p. -/

-- H
def Hf (α φ ψ : Form) : Form := .imp (.imp α (.or φ ψ)) (.or (.imp α φ) (.imp α ψ))

inductive NJA (Ax : Form → Prop) : List Form → Form → Prop where
  | hyp   {Γ φ}     : φ ∈ Γ → NJA Ax Γ φ
  | andI  {Γ φ ψ}   : NJA Ax Γ φ → NJA Ax Γ ψ → NJA Ax Γ (.and φ ψ)
  | andE₁ {Γ φ ψ}   : NJA Ax Γ (.and φ ψ) → NJA Ax Γ φ
  | andE₂ {Γ φ ψ}   : NJA Ax Γ (.and φ ψ) → NJA Ax Γ ψ
  | impI  {Γ φ ψ}   : NJA Ax (φ :: Γ) ψ → NJA Ax Γ (.imp φ ψ)
  | impE  {Γ φ ψ}   : NJA Ax Γ (.imp φ ψ) → NJA Ax Γ φ → NJA Ax Γ ψ
  | orI₁  {Γ φ ψ}   : NJA Ax Γ φ → NJA Ax Γ (.or φ ψ)
  | orI₂  {Γ φ ψ}   : NJA Ax Γ ψ → NJA Ax Γ (.or φ ψ)
  | orE   {Γ φ ψ χ} : NJA Ax Γ (.or φ ψ) → NJA Ax (φ :: Γ) χ → NJA Ax (ψ :: Γ) χ → NJA Ax Γ χ
  | botE  {Γ φ}     : NJA Ax Γ .bot → NJA Ax Γ φ
  | ax    {Γ φ}     : Ax φ → NJA Ax Γ φ

theorem NJA.weaken {Ax : Form → Prop} {Γ : List Form} {φ : Form} (d : NJA Ax Γ φ) :
    ∀ {Δ : List Form}, (∀ θ, θ ∈ Γ → θ ∈ Δ) → NJA Ax Δ φ := by
  induction d with
  | hyp h => intro Δ hΔ; exact NJA.hyp (hΔ _ h)
  | andI _ _ ih₁ ih₂ => intro Δ hΔ; exact NJA.andI (ih₁ hΔ) (ih₂ hΔ)
  | andE₁ _ ih => intro Δ hΔ; exact NJA.andE₁ (ih hΔ)
  | andE₂ _ ih => intro Δ hΔ; exact NJA.andE₂ (ih hΔ)
  | impI _ ih => intro Δ hΔ; exact NJA.impI (ih (consSub hΔ))
  | impE _ _ ih₁ ih₂ => intro Δ hΔ; exact NJA.impE (ih₁ hΔ) (ih₂ hΔ)
  | orI₁ _ ih => intro Δ hΔ; exact NJA.orI₁ (ih hΔ)
  | orI₂ _ ih => intro Δ hΔ; exact NJA.orI₂ (ih hΔ)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
    intro Δ hΔ; exact NJA.orE (ih₀ hΔ) (ih₁ (consSub hΔ)) (ih₂ (consSub hΔ))
  | botE _ ih => intro Δ hΔ; exact NJA.botE (ih hΔ)
  | ax h => intro Δ _; exact NJA.ax h

theorem NJA.ofNJ {Ax : Form → Prop} {Γ : List Form} {φ : Form} (d : NJ Γ φ) : NJA Ax Γ φ := by
  induction d with
  | hyp h => exact NJA.hyp h
  | andI _ _ ih₁ ih₂ => exact NJA.andI ih₁ ih₂
  | andE₁ _ ih => exact NJA.andE₁ ih
  | andE₂ _ ih => exact NJA.andE₂ ih
  | impI _ ih => exact NJA.impI ih
  | impE _ _ ih₁ ih₂ => exact NJA.impE ih₁ ih₂
  | orI₁ _ ih => exact NJA.orI₁ ih
  | orI₂ _ ih => exact NJA.orI₂ ih
  | orE _ _ _ ih₀ ih₁ ih₂ => exact NJA.orE ih₀ ih₁ ih₂
  | botE _ ih => exact NJA.botE ih

-- axiomas válidos ⟹ NJA correcto en la clase finita
theorem soundnessA {Ax : Form → Prop} (hAx : ∀ φ, Ax φ → validF [] φ) {Γ : List Form}
    {φ : Form} (d : NJA Ax Γ φ) : validF Γ φ := by
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
  | @ax Γ φ h =>
    intro L _; exact hAx φ h L (fun _ h' => (mem_nil_false h').elim)

theorem subTl {x : Form} {Γ : List Form} : ∀ θ, θ ∈ Γ → θ ∈ x :: Γ :=
  fun _ h => List.mem_cons.mpr (Or.inr h)

theorem mem3 {α : Type} {x y z w : α} {l : List α} : w ∈ x :: y :: z :: w :: l :=
  List.mem_cons.mpr (Or.inr mem2)

theorem NJA.cut {Ax : Form → Prop} {Γ : List Form} {a χ : Form} (d₁ : NJA Ax Γ a)
    (d₂ : NJA Ax (a :: Γ) χ) : NJA Ax Γ χ :=
  NJA.impE (NJA.impI d₂) d₁

theorem NJA.wk1 {Ax : Form → Prop} {Γ : List Form} {x φ : Form} (d : NJA Ax Γ φ) :
    NJA Ax (x :: Γ) φ :=
  NJA.weaken d subTl

theorem NJA.top {Ax : Form → Prop} {Γ : List Form} : NJA Ax Γ topF := NJA.impI (NJA.hyp mem0)

-- sin ⊥
def nb : Form → Prop
  | .atom _  => True
  | .bot     => False
  | .and a b => nb a ∧ nb b
  | .or a b  => nb a ∧ nb b
  | .imp a b => nb a ∧ nb b

-- sin ∨ (⊥ permitido): antecedentes de GKP
def orFree : Form → Prop
  | .atom _  => True
  | .bot     => True
  | .and a b => orFree a ∧ orFree b
  | .or _ _  => False
  | .imp a b => orFree a ∧ orFree b

theorem orFree_harrop (a : Form) : orFree a → harrop a := by
  induction a with
  | atom _ => intro _; exact True.intro
  | bot => intro _; exact True.intro
  | or _ _ _ _ => intro h; exact False.elim h
  | and _ _ iha ihb => intro h; exact ⟨iha (And.left h), ihb (And.right h)⟩
  | imp _ _ _ ihb => intro h; exact ihb (And.right h)

theorem nvb_orFree (a : Form) : nvb a → orFree a := by
  induction a with
  | atom _ => intro _; exact True.intro
  | bot => intro h; exact False.elim h
  | or _ _ _ _ => intro h; exact False.elim h
  | and _ _ iha ihb => intro h; exact ⟨iha (And.left h), ihb (And.right h)⟩
  | imp _ _ iha ihb => intro h; exact ⟨iha (And.left h), ihb (And.right h)⟩

theorem mem_andL {x y : Form} {X Y : List Form} (hx : x ∈ X) (hy : y ∈ Y) :
    Form.and x y ∈ andL X Y := by
  induction X with
  | nil => exact (mem_nil_false hx).elim
  | cons x' X ih =>
    cases List.mem_cons.mp hx with
    | inl e =>
      rw [e]
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨y, hy, rfl⟩))
    | inr h => exact List.mem_append.mpr (Or.inr (ih h))

theorem mem_andL_inv {γ : Form} {X Y : List Form} (h : γ ∈ andL X Y) :
    ∃ x y, x ∈ X ∧ y ∈ Y ∧ γ = Form.and x y := by
  induction X with
  | nil => exact (mem_nil_false h).elim
  | cons x' X ih =>
    cases List.mem_append.mp h with
    | inl h1 =>
      cases List.mem_map.mp h1 with
      | intro y hy => exact ⟨x', y, mem0, hy.1, hy.2.symm⟩
    | inr h2 =>
      cases ih h2 with
      | intro x hx =>
        cases hx with
        | intro y hy => exact ⟨x, y, List.mem_cons.mpr (Or.inr hy.1), hy.2.1, hy.2.2⟩

-- cada conjunto de impNF da c → d para cada c
theorem impNF_proj {Ax : Form → Prop} {B A : List Form} {γ c : Form} (hγ : γ ∈ impNF B A)
    (hc : c ∈ A) : ∃ d, d ∈ B ∧ ∀ Γ, NJA Ax (γ :: Γ) (.imp c d) := by
  induction A generalizing γ with
  | nil => exact (mem_nil_false hc).elim
  | cons a A ih =>
    cases mem_andL_inv hγ with
    | intro x hx =>
      cases hx with
      | intro y hy =>
        cases List.mem_map.mp hy.1 with
        | intro d₀ hd₀ =>
          cases List.mem_cons.mp hc with
          | inl e =>
            refine ⟨d₀, hd₀.1, fun Γ => ?_⟩
            have hx' : x = .imp a d₀ := hd₀.2.symm
            rw [hy.2.2, e, hx']
            exact NJA.andE₁ (NJA.hyp mem0)
          | inr h =>
            cases ih (γ := y) hy.2.1 h with
            | intro d hd =>
              refine ⟨d, hd.1, fun Γ => ?_⟩
              rw [hy.2.2]
              exact NJA.cut (NJA.andE₂ (NJA.hyp mem0)) (NJA.weaken (hd.2 Γ) (consSub subTl))

-- ¬¬α para α sin ∨ ni ⊥, desde ¬¬p atómico
theorem dnA {Ax : Form → Prop} (hD : ∀ p, Ax (negF (negF (.atom p)))) (a : Form) :
    nvb a → ∀ Γ, NJA Ax Γ (negF (negF a)) := by
  induction a with
  | atom p => intro _ Γ; exact NJA.ax (hD p)
  | bot => intro h; exact False.elim h
  | or _ _ _ _ => intro h; exact False.elim h
  | and _ _ iha ihb =>
    intro h Γ
    exact NJA.impI (NJA.impE (iha (And.left h) _) (NJA.impI (NJA.impE (ihb (And.right h) _)
      (NJA.impI (NJA.impE (NJA.hyp mem2) (NJA.andI (NJA.hyp mem1) (NJA.hyp mem0)))))))
  | imp _ _ _ ihb =>
    intro h Γ
    exact NJA.impI (NJA.impE (ihb (And.right h) _)
      (NJA.impI (NJA.impE (NJA.hyp mem1) (NJA.impI (NJA.hyp mem1)))))

-- introducción y división de la forma normal en NJA
def ISyn (Ax : Form → Prop) (ψ : Form) : Prop := ∀ b, b ∈ nfL ψ → ∀ Γ, NJA Ax (b :: Γ) ψ

def SSyn (Ax : Form → Prop) (ψ : Form) : Prop := ∀ a, nvb a → ∀ Γ χ, NJA Ax Γ (.imp a ψ) →
  (∀ b, b ∈ nfL ψ → NJA Ax ((.imp a b) :: Γ) χ) → NJA Ax Γ χ

theorem nf_elim_of {Ax : Form → Prop} {ψ : Form} (hS : SSyn Ax ψ) {Γ : List Form} {χ : Form}
    (h : ∀ b, b ∈ nfL ψ → NJA Ax (b :: Γ) χ) : NJA Ax (ψ :: Γ) χ :=
  hS topF nvb_top (ψ :: Γ) χ (NJA.impI (NJA.hyp mem1)) (fun b hb =>
    NJA.cut (NJA.impE (NJA.hyp mem0) NJA.top)
      (NJA.weaken (h b hb) (consSub (fun θ hθ => subTl θ (subTl θ hθ)))))

-- paso → de la división, por la recursión de impNF
theorem impS {Ax : Form → Prop} {a ψ : Form} {B : List Form} (ha : nvb a)
    (hS2 : ∀ a', nvb a' → ∀ Γ χ, NJA Ax Γ (.imp a' ψ) →
      (∀ d, d ∈ B → NJA Ax ((.imp a' d) :: Γ) χ) → NJA Ax Γ χ)
    (A : List Form) (hA : ∀ c, c ∈ A → nvb c) : ∀ Γ χ,
    (∀ c, c ∈ A → NJA Ax Γ (.imp (.and a c) ψ)) →
    (∀ γ, γ ∈ impNF B A → NJA Ax ((.imp a γ) :: Γ) χ) → NJA Ax Γ χ := by
  induction A with
  | nil =>
    intro Γ χ _ k
    exact NJA.cut (NJA.impI NJA.top) (k topF mem0)
  | cons c A ih =>
    intro Γ χ hp k
    apply hS2 (.and a c) ⟨ha, hA c mem0⟩ Γ χ (hp c mem0)
    intro d hd
    apply ih (fun c' hc' => hA c' (subTl c' hc')) ((.imp (.and a c) d) :: Γ) χ
      (fun c' hc' => NJA.wk1 (hp c' (subTl c' hc')))
    intro γ' hγ'
    have hm : Form.and (.imp c d) γ' ∈ impNF B (c :: A) :=
      mem_andL (List.mem_map.mpr ⟨d, hd, rfl⟩) hγ'
    have hk := k _ hm
    -- a → (c → d) ∧ γ', desde a → γ' y a ∧ c → d
    have hder : NJA Ax ((.imp a γ') :: (.imp (.and a c) d) :: Γ)
        (.imp a (.and (.imp c d) γ')) :=
      NJA.impI (NJA.andI
        (NJA.impI (NJA.impE (NJA.hyp mem3) (NJA.andI (NJA.hyp mem1) (NJA.hyp mem0))))
        (NJA.impE (NJA.hyp mem1) (NJA.hyp mem0)))
    exact NJA.cut hder (NJA.weaken hk (consSub (fun θ hθ => subTl θ (subTl θ hθ))))

-- H en Ax; ⊥ excluido o ¬¬p atómico en Ax
theorem nf_syn {Ax : Form → Prop} (hH : ∀ {α φ ψ : Form}, nvb α → Ax (Hf α φ ψ))
    (ψ : Form) : nb ψ ∨ (∀ p, Ax (negF (negF (.atom p)))) → ISyn Ax ψ ∧ SSyn Ax ψ := by
  induction ψ with
  | atom p =>
    intro _
    constructor
    · intro b hb Γ
      cases List.mem_cons.mp hb with
      | inl e => rw [e]; exact NJA.hyp mem0
      | inr h => exact (mem_nil_false h).elim
    · intro a _ Γ χ h k
      exact NJA.cut h (k (.atom p) mem0)
  | bot =>
    intro hb
    constructor
    · intro b hb' _
      exact (mem_nil_false hb').elim
    · intro a ha Γ χ h _
      cases hb with
      | inl h0 => exact False.elim h0
      | inr hD => exact NJA.botE (NJA.impE (dnA hD a ha Γ) h)
  | and φ ψ ihφ ihψ =>
    intro hb
    have hb₁ : nb φ ∨ (∀ p, Ax (negF (negF (.atom p)))) :=
      hb.elim (fun h => Or.inl (And.left h)) Or.inr
    have hb₂ : nb ψ ∨ (∀ p, Ax (negF (negF (.atom p)))) :=
      hb.elim (fun h => Or.inl (And.right h)) Or.inr
    have Iφ := (ihφ hb₁).1
    have Sφ := (ihφ hb₁).2
    have Iψ := (ihψ hb₂).1
    have Sψ := (ihψ hb₂).2
    constructor
    · intro b hb' Γ
      cases mem_andL_inv hb' with
      | intro x hx =>
        cases hx with
        | intro y hy =>
          rw [hy.2.2]
          exact NJA.andI (NJA.cut (NJA.andE₁ (NJA.hyp mem0)) (Iφ x hy.1 _))
            (NJA.cut (NJA.andE₂ (NJA.hyp mem0)) (Iψ y hy.2.1 _))
    · intro a ha Γ χ h k
      have hφa : NJA Ax Γ (.imp a φ) :=
        NJA.impI (NJA.andE₁ (NJA.impE (NJA.wk1 h) (NJA.hyp mem0)))
      have hψa : NJA Ax Γ (.imp a ψ) :=
        NJA.impI (NJA.andE₂ (NJA.impE (NJA.wk1 h) (NJA.hyp mem0)))
      apply Sφ a ha Γ χ hφa
      intro x hx
      apply Sψ a ha ((.imp a x) :: Γ) χ (NJA.wk1 hψa)
      intro y hy
      have hk := k (.and x y) (mem_andL hx hy)
      have hder : NJA Ax ((.imp a y) :: (.imp a x) :: Γ) (.imp a (.and x y)) :=
        NJA.impI (NJA.andI (NJA.impE (NJA.hyp mem2) (NJA.hyp mem0))
          (NJA.impE (NJA.hyp mem1) (NJA.hyp mem0)))
      exact NJA.cut hder (NJA.weaken hk (consSub (fun θ hθ => subTl θ (subTl θ hθ))))
  | or φ ψ ihφ ihψ =>
    intro hb
    have hb₁ : nb φ ∨ (∀ p, Ax (negF (negF (.atom p)))) :=
      hb.elim (fun h => Or.inl (And.left h)) Or.inr
    have hb₂ : nb ψ ∨ (∀ p, Ax (negF (negF (.atom p)))) :=
      hb.elim (fun h => Or.inl (And.right h)) Or.inr
    have Iφ := (ihφ hb₁).1
    have Sφ := (ihφ hb₁).2
    have Iψ := (ihψ hb₂).1
    have Sψ := (ihψ hb₂).2
    constructor
    · intro b hb' Γ
      cases List.mem_append.mp hb' with
      | inl h1 => exact NJA.orI₁ (Iφ b h1 Γ)
      | inr h2 => exact NJA.orI₂ (Iψ b h2 Γ)
    · intro a ha Γ χ h k
      have hH' : NJA Ax Γ (.or (.imp a φ) (.imp a ψ)) :=
        NJA.impE (NJA.ax (hH ha)) h
      exact NJA.orE hH'
        (Sφ a ha _ χ (NJA.hyp mem0) (fun b hb' =>
          NJA.weaken (k b (List.mem_append.mpr (Or.inl hb'))) (consSub subTl)))
        (Sψ a ha _ χ (NJA.hyp mem0) (fun b hb' =>
          NJA.weaken (k b (List.mem_append.mpr (Or.inr hb'))) (consSub subTl)))
  | imp φ ψ ihφ ihψ =>
    intro hb
    have hb₁ : nb φ ∨ (∀ p, Ax (negF (negF (.atom p)))) :=
      hb.elim (fun h => Or.inl (And.left h)) Or.inr
    have hb₂ : nb ψ ∨ (∀ p, Ax (negF (negF (.atom p)))) :=
      hb.elim (fun h => Or.inl (And.right h)) Or.inr
    have Iφ := (ihφ hb₁).1
    have Sφ := (ihφ hb₁).2
    have Iψ := (ihψ hb₂).1
    have Sψ := (ihψ hb₂).2
    constructor
    · intro γ hγ Γ
      apply NJA.impI
      apply nf_elim_of Sφ
      intro c hc
      cases impNF_proj (Ax := Ax) hγ hc with
      | intro d hd =>
        exact NJA.cut (NJA.impE (NJA.weaken (hd.2 Γ) subTl) (NJA.hyp mem0)) (Iψ d hd.1 _)
    · intro a ha Γ χ h k
      refine impS ha Sψ (nfL φ) (nfL_spec φ).1 Γ χ ?_ k
      intro c hc
      exact NJA.impI (NJA.impE (NJA.impE (NJA.wk1 h) (NJA.andE₁ (NJA.hyp mem0)))
        (NJA.cut (NJA.andE₂ (NJA.hyp mem0)) (Iφ c hc _)))

-- GKPL = IPC + GKP (antecedente sin ∨); GKPL + ¬¬p
def AxG (φ : Form) : Prop := ∃ α ψ₁ ψ₂, orFree α ∧ φ = Hf α ψ₁ ψ₂

def AxGD (φ : Form) : Prop := AxG φ ∨ ∃ p, φ = negF (negF (.atom p))

theorem hH_AxG {α φ ψ : Form} (h : nvb α) : AxG (Hf α φ ψ) := ⟨α, φ, ψ, nvb_orFree α h, rfl⟩

theorem hH_AxGD {α φ ψ : Form} (h : nvb α) : AxGD (Hf α φ ψ) := Or.inl (hH_AxG h)

theorem hD_AxGD (p : Atom) : AxGD (negF (negF (.atom p))) := Or.inr ⟨p, rfl⟩

theorem axG_valid (φ : Form) (h : AxG φ) : validF [] φ := by
  cases h with
  | intro α h =>
    cases h with
    | intro ψ₁ h =>
      cases h with
      | intro ψ₂ h => rw [h.2]; exact finite_H α ψ₁ ψ₂ (orFree_harrop α h.1)

theorem axGD_valid (φ : Form) (h : AxGD φ) : validF [] φ := by
  cases h with
  | inl h1 => exact axG_valid φ h1
  | inr h2 =>
    cases h2 with
    | intro p e => rw [e]; exact finite_dn p

-- válida ⟹ algún disyunto normal es teorema de NJ ⟹ φ en NJA
theorem nf_complete {Ax : Form → Prop} (hH : ∀ {α φ ψ : Form}, nvb α → Ax (Hf α φ ψ))
    {φ : Form} (hb : nb φ ∨ (∀ p, Ax (negF (negF (.atom p))))) (hv : validF [] φ) :
    NJA Ax [] φ := by
  cases ((nfL_spec φ).2.2 []).mp (hv [] (fun _ h => (mem_nil_false h).elim)) with
  | intro b hb' =>
    have hnj : NJ [] b := finite_complete_nvb (fun _ h => (mem_nil_false h).elim)
      ((nfL_spec φ).1 b hb'.1) (valid_of_nil hb'.2)
    exact NJA.cut (NJA.ofNJ hnj) ((nf_syn hH φ hb).1 b hb'.1 [])

-- sin ⊥: válida en la clase finita ⟺ teorema de GKPL (lógica inquisitiva general)
theorem finite_inquisitive (φ : Form) (hb : nb φ) : validF [] φ ↔ NJA AxG [] φ :=
  ⟨nf_complete (Ax := AxG) hH_AxG (Or.inl hb), soundnessA axG_valid⟩

-- con ⊥: válida en la clase finita ⟺ teorema de GKPL + ¬¬p
theorem finite_logic (φ : Form) : validF [] φ ↔ NJA AxGD [] φ :=
  ⟨nf_complete (Ax := AxGD) hH_AxGD (Or.inr hD_AxGD), soundnessA axGD_valid⟩

/-! ## E e I coinciden en bases finitas
  Semántica I (Stafford–Piecha–Schroeder-Heister 2026): ∨ por introducción. En bases
  finitas, finite_gdp hace que la ∨ de eliminación sea la de introducción. -/

def suppI : List Rule → Form → Prop
  | L, .atom p  => Deriv (ofList L) [] p
  | L, .bot     => ∀ p, Deriv (ofList L) [] p
  | L, .and φ ψ => suppI L φ ∧ suppI L ψ
  | L, .or φ ψ  => suppI L φ ∨ suppI L ψ
  | L, .imp φ ψ => ∀ L', Ext (ofList L) (ofList L') → suppI L' φ → suppI L' ψ

theorem suppI_iff (φ : Form) : ∀ L, suppI L φ ↔ suppF L φ := by
  induction φ with
  | atom _ => intro L; exact Iff.rfl
  | bot => intro L; exact Iff.rfl
  | and φ ψ ih₁ ih₂ =>
    intro L
    show (suppI L φ ∧ suppI L ψ) ↔ (suppF L φ ∧ suppF L ψ)
    rw [ih₁ L, ih₂ L]
  | or φ ψ ih₁ ih₂ =>
    intro L
    show (suppI L φ ∨ suppI L ψ) ↔ suppF L (.or φ ψ)
    rw [ih₁ L, ih₂ L]
    exact ⟨fun h => h.elim (or_introF₁ ψ) (or_introF₂ φ), finite_gdp⟩
  | imp φ ψ ih₁ ih₂ =>
    intro L
    show (∀ L', Ext (ofList L) (ofList L') → suppI L' φ → suppI L' ψ) ↔
      (∀ L', Ext (ofList L) (ofList L') → suppF L' φ → suppF L' ψ)
    exact ⟨fun h L' hL h' => (ih₂ L').mp (h L' hL ((ih₁ L').mpr h')),
      fun h L' hL h' => (ih₂ L').mpr (h L' hL ((ih₁ L').mp h'))⟩

-- E2 finita = I2 finita
theorem finite_E_I (φ : Form) : validF [] φ ↔ ∀ L, suppI L φ :=
  ⟨fun h L => (suppI_iff φ L).mpr (h L (fun _ h' => (mem_nil_false h').elim)),
   fun h L _ => (suppI_iff φ L).mp (h L)⟩

/-! ## Complementos
  E2: en cada base finita, Export y la propiedad de disyunción (Harrop).
  Clase finita: ¬φ o ¬¬φ; sustitución: KC esquemática, sin propiedad de disyunción. -/

-- de contexto a implicaciones
theorem NJ.impF_intro : ∀ (Ls : List Form) {Δ : List Form} {ψ : Form},
    NJ (Ls ++ Δ) ψ → NJ Δ (impF Ls ψ)
  | [], _, _, d => d
  | φ :: Ls, Δ, ψ, d => by
    show NJ Δ (.imp φ (impF Ls ψ))
    apply NJ.impI
    apply NJ.impF_intro Ls
    apply NJ.weaken d
    intro θ hθ
    cases List.mem_append.mp hθ with
    | inl h1 =>
      cases List.mem_cons.mp h1 with
      | inl e => exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
      | inr h2 => exact List.mem_append.mpr (Or.inl h2)
    | inr h1 => exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h1)))

-- E2, base finita Σ: ⊩_Σ φ ∨ ψ ⟹ ⊩_Σ φ o ⊩_Σ ψ
theorem e2_finite_dp (Sig : List Rule) {φ ψ : Form}
    (h : supp (bunion emptyB (ofList Sig)) (.or φ ψ)) :
    supp (bunion emptyB (ofList Sig)) φ ∨ supp (bunion emptyB (ofList Sig)) ψ := by
  have d0 : NJ [] (impF (Sig.map ruleForm) (.or φ ψ)) := (finite_base_export Sig _).mp h
  have hv : valid (Sig.map ruleForm) (.or φ ψ) := fun B hB =>
    (supp_impF (Sig.map ruleForm) (.or φ ψ)).mp
      (soundness d0 B (fun _ hθ => by cases hθ)) B (Ext.refl B) hB
  have hH : ∀ θ, θ ∈ Sig.map ruleForm → harrop θ := fun θ hθ => by
    cases List.mem_map.mp hθ with
    | intro r hr =>
      cases hr with
      | intro _ e => subst e; exact harrop_rule r
  have back : ∀ {χ : Form}, NJ (Sig.map ruleForm) χ → supp (bunion emptyB (ofList Sig)) χ :=
    fun d => (finite_base_export Sig _).mpr
      (NJ.impF_intro (Sig.map ruleForm)
        (NJ.weaken d (fun _ hθ => List.mem_append.mpr (Or.inl hθ))))
  cases harrop_dp hH (completeness hv) with
  | inl d => exact Or.inl (back d)
  | inr d => exact Or.inr (back d)

-- ¬¬⊥ no es válida
theorem finite_nnbot : ¬ validF [] (negF (negF .bot)) := fun h =>
  finite_bot [] (h [] (fun _ hθ => by cases hθ) [] (Ext.refl _) (fun _ _ hb => hb))

-- exactamente una de ¬φ, ¬¬φ es válida
theorem finite_neg_dec (φ : Form) :
    (validF [] (negF φ) ∨ validF [] (negF (negF φ))) ∧
    ¬ (validF [] (negF φ) ∧ validF [] (negF (negF φ))) := by
  constructor
  · exact finite_dp (finite_kremer φ)
  · intro h
    exact finite_bot []
      (And.right h [] (fun _ hθ => by cases hθ) [] (Ext.refl _)
        (And.left h [] (fun _ hθ => by cases hθ)))

-- lo mismo en GKPL + ¬¬p
theorem finite_logic_neg_dec (φ : Form) :
    (NJA AxGD [] (negF φ) ∨ NJA AxGD [] (negF (negF φ))) ∧
    ¬ (NJA AxGD [] (negF φ) ∧ NJA AxGD [] (negF (negF φ))) := by
  have h := finite_neg_dec φ
  constructor
  · cases And.left h with
    | inl a => exact Or.inl ((finite_logic _).mp a)
    | inr a => exact Or.inr ((finite_logic _).mp a)
  · intro hb
    exact And.right h
      (And.intro ((finite_logic _).mpr (And.left hb)) ((finite_logic _).mpr (And.right hb)))

-- sustitución de átomos
def substF (σ : Atom → Form) : Form → Form
  | .atom p  => σ p
  | .bot     => .bot
  | .and a b => .and (substF σ a) (substF σ b)
  | .or a b  => .or (substF σ a) (substF σ b)
  | .imp a b => .imp (substF σ a) (substF σ b)

-- todas las instancias válidas
abbrev validS (φ : Form) : Prop := ∀ σ : Atom → Form, validF [] (substF σ φ)

-- KC esquemática
theorem finite_kc_schematic : validS (.or (negF (.atom 0)) (negF (negF (.atom 0)))) :=
  fun σ => finite_kremer (σ 0)

-- la parte cerrada bajo sustitución no tiene la propiedad de disyunción
theorem finite_s_no_dp :
    validS (.or (negF (.atom 0)) (negF (negF (.atom 0)))) ∧
    ¬ validS (negF (.atom 0)) ∧ ¬ validS (negF (negF (.atom 0))) := by
  refine And.intro finite_kc_schematic (And.intro ?_ ?_)
  · intro h
    exact finite_neg [] 0 (h Form.atom [] (fun _ hθ => by cases hθ))
  · intro h
    exact finite_nnbot (h (fun _ => .bot))

/-! ## ρ: eliminación de ⊥ (Prop. 6.4)
  Soporte en una clase K de bases finitas (todas, o las de nivel 1).
  En ambas, ⊩_B φ ⟺ ⊩_B ρφ; e IPC + ¬¬p ⊢ φ ↔ ρφ. -/

-- filtro por un predicado cualquiera
theorem exists_sub {α : Type} (P : α → Prop) (S : List α) :
    ∃ T : List α, ∀ a, a ∈ T ↔ a ∈ S ∧ P a := by
  induction S with
  | nil => exact ⟨[], fun _ => ⟨fun h => (mem_nil_false h).elim, fun h => (mem_nil_false h.1).elim⟩⟩
  | cons x S ih =>
    cases ih with
    | intro T hT =>
      cases Classical.em (P x) with
      | inl hx =>
        refine ⟨x :: T, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
        · cases List.mem_cons.mp h with
          | inl e => rw [e]; exact ⟨mem0, hx⟩
          | inr h' => exact ⟨List.mem_cons.mpr (Or.inr ((hT a).mp h').1), ((hT a).mp h').2⟩
        · cases List.mem_cons.mp h.1 with
          | inl e => rw [e]; exact mem0
          | inr h' => exact List.mem_cons.mpr (Or.inr ((hT a).mpr ⟨h', h.2⟩))
      | inr hx =>
        refine ⟨T, fun a => ⟨fun h => ⟨List.mem_cons.mpr (Or.inr ((hT a).mp h).1), ((hT a).mp h).2⟩,
          fun h => ?_⟩⟩
        cases List.mem_cons.mp h.1 with
        | inl e => rw [e] at h; exact absurd h.2 hx
        | inr h' => exact (hT a).mpr ⟨h', h.2⟩

-- constructores que simplifican ⊥
def rAnd (x y : Form) : Form := if x = .bot then .bot else if y = .bot then .bot else .and x y
def rOr (x y : Form) : Form := if x = .bot then y else if y = .bot then x else .or x y
def rImp (x y : Form) : Form := if x = .bot then topF else if y = .bot then .bot else .imp x y

def rho : Form → Form
  | .atom p  => .atom p
  | .bot     => .bot
  | .and a b => rAnd (rho a) (rho b)
  | .or a b  => rOr (rho a) (rho b)
  | .imp a b => rImp (rho a) (rho b)

-- ρφ es ⊥ o no contiene ⊥
theorem rho_nb (φ : Form) : rho φ = .bot ∨ nb (rho φ) := by
  induction φ with
  | atom _ => exact Or.inr True.intro
  | bot => exact Or.inl rfl
  | and a b iha ihb =>
    show rAnd (rho a) (rho b) = .bot ∨ nb (rAnd (rho a) (rho b))
    unfold rAnd
    by_cases ha : rho a = .bot
    · rw [ite_eq_left ha]; exact Or.inl rfl
    · rw [ite_eq_right ha]
      by_cases hb : rho b = .bot
      · rw [ite_eq_left hb]; exact Or.inl rfl
      · rw [ite_eq_right hb]
        exact Or.inr ⟨iha.resolve_left ha, ihb.resolve_left hb⟩
  | or a b iha ihb =>
    show rOr (rho a) (rho b) = .bot ∨ nb (rOr (rho a) (rho b))
    unfold rOr
    by_cases ha : rho a = .bot
    · rw [ite_eq_left ha]; exact ihb
    · rw [ite_eq_right ha]
      by_cases hb : rho b = .bot
      · rw [ite_eq_left hb]; exact iha
      · rw [ite_eq_right hb]
        exact Or.inr ⟨iha.resolve_left ha, ihb.resolve_left hb⟩
  | imp a b iha ihb =>
    show rImp (rho a) (rho b) = .bot ∨ nb (rImp (rho a) (rho b))
    unfold rImp
    by_cases ha : rho a = .bot
    · rw [ite_eq_left ha]; exact Or.inr ⟨True.intro, True.intro⟩
    · rw [ite_eq_right ha]
      by_cases hb : rho b = .bot
      · rw [ite_eq_left hb]; exact Or.inl rfl
      · rw [ite_eq_right hb]
        exact Or.inr ⟨iha.resolve_left ha, ihb.resolve_left hb⟩

def atomsF : Form → List Atom
  | .atom p  => [p]
  | .bot     => []
  | .and a b => atomsF a ++ atomsF b
  | .or a b  => atomsF a ++ atomsF b
  | .imp a b => atomsF a ++ atomsF b

-- soporte en la clase K
def suppK (K : List Rule → Prop) : List Rule → Form → Prop
  | L, .atom p  => Deriv (ofList L) [] p
  | L, .bot     => ∀ p, Deriv (ofList L) [] p
  | L, .and φ ψ => suppK K L φ ∧ suppK K L ψ
  | L, .imp φ ψ => ∀ L', K L' → Ext (ofList L) (ofList L') → suppK K L' φ → suppK K L' ψ
  | L, .or φ ψ  => ∀ L', K L' → Ext (ofList L) (ofList L') → ∀ p : Atom,
      (∀ L'', K L'' → Ext (ofList L') (ofList L'') → suppK K L'' φ → Deriv (ofList L'') [] p) →
      (∀ L'', K L'' → Ext (ofList L') (ofList L'') → suppK K L'' ψ → Deriv (ofList L'') [] p) →
      Deriv (ofList L') [] p

theorem suppK_mono {K : List Rule → Prop} (φ : Form) : ∀ {L L' : List Rule},
    Ext (ofList L) (ofList L') → suppK K L φ → suppK K L' φ := by
  induction φ with
  | atom p => intro L L' h hs; simp only [suppK] at hs ⊢; exact Deriv.mono h hs
  | bot => intro L L' h hs; simp only [suppK] at hs ⊢; exact fun q => Deriv.mono h (hs q)
  | and φ ψ ih₁ ih₂ =>
    intro L L' h hs; simp only [suppK] at hs ⊢; exact ⟨ih₁ h hs.1, ih₂ h hs.2⟩
  | imp φ ψ _ _ =>
    intro L L' h hs; simp only [suppK] at hs ⊢
    exact fun D hD hCD => hs D hD (Ext.trans h hCD)
  | or φ ψ _ _ =>
    intro L L' h hs; simp only [suppK] at hs ⊢
    exact fun D hD hCD => hs D hD (Ext.trans h hCD)

theorem bot_elimK {K : List Rule → Prop} (χ : Form) : ∀ {L : List Rule},
    suppK K L .bot → suppK K L χ := by
  induction χ with
  | atom p => intro L hb; simp only [suppK] at hb ⊢; exact hb p
  | bot => intro L hb; exact hb
  | and χ₁ χ₂ ih₁ ih₂ => intro L hb; simp only [suppK]; exact ⟨ih₁ hb, ih₂ hb⟩
  | imp χ₁ χ₂ _ ih₂ =>
    intro L hb; simp only [suppK]
    intro C _ hBC _
    exact ih₂ (suppK_mono .bot hBC hb)
  | or χ₁ χ₂ _ _ =>
    intro L hb; simp only [suppK]
    intro C _ hBC p _ _
    have hC := suppK_mono (K := K) .bot hBC hb
    simp only [suppK] at hC
    exact hC p

theorem or_elimK {K : List Rule → Prop} (φ ψ χ : Form) : ∀ {L : List Rule}, K L →
    suppK K L (.or φ ψ) →
    (∀ C, K C → Ext (ofList L) (ofList C) → suppK K C φ → suppK K C χ) →
    (∀ C, K C → Ext (ofList L) (ofList C) → suppK K C ψ → suppK K C χ) →
    suppK K L χ := by
  induction χ with
  | atom p =>
    intro L hK hor h₁ h₂
    simp only [suppK] at hor h₁ h₂ ⊢
    exact hor L hK (Ext.refl _) p h₁ h₂
  | bot =>
    intro L hK hor h₁ h₂
    simp only [suppK] at hor h₁ h₂ ⊢
    intro q
    exact hor L hK (Ext.refl _) q
      (fun D hD hLD hφ => h₁ D hD hLD hφ q) (fun D hD hLD hψ => h₂ D hD hLD hψ q)
  | and χ₁ χ₂ ih₁ ih₂ =>
    intro L hK hor h₁ h₂
    simp only [suppK] at h₁ h₂ ⊢
    exact ⟨ih₁ hK hor (fun C hC hLC hφ => (h₁ C hC hLC hφ).1) (fun C hC hLC hψ => (h₂ C hC hLC hψ).1),
           ih₂ hK hor (fun C hC hLC hφ => (h₁ C hC hLC hφ).2) (fun C hC hLC hψ => (h₂ C hC hLC hψ).2)⟩
  | imp χ₁ χ₂ _ ih₂ =>
    intro L hK hor h₁ h₂
    simp only [suppK] at h₁ h₂ ⊢
    intro C hC hBC hχ₁
    apply ih₂ hC (suppK_mono (.or φ ψ) hBC hor)
    · intro D hD hCD hφ
      exact h₁ D hD (Ext.trans hBC hCD) hφ D hD (Ext.refl _) (suppK_mono χ₁ hCD hχ₁)
    · intro D hD hCD hψ
      exact h₂ D hD (Ext.trans hBC hCD) hψ D hD (Ext.refl _) (suppK_mono χ₁ hCD hχ₁)
  | or χ₁ χ₂ _ _ =>
    intro L hK hor h₁ h₂
    simp only [suppK] at hor h₁ h₂ ⊢
    intro C hC hBC p k₁ k₂
    apply hor C hC hBC p
    · intro D hD hCD hφ
      exact h₁ D hD (Ext.trans hBC hCD) hφ D hD (Ext.refl _) p
        (fun E hE hDE => k₁ E hE (Ext.trans hCD hDE)) (fun E hE hDE => k₂ E hE (Ext.trans hCD hDE))
    · intro D hD hCD hψ
      exact h₂ D hD (Ext.trans hBC hCD) hψ D hD (Ext.refl _) p
        (fun E hE hDE => k₁ E hE (Ext.trans hCD hDE)) (fun E hE hDE => k₂ E hE (Ext.trans hCD hDE))

abbrev validK (K : List Rule → Prop) (Γ : List Form) (φ : Form) : Prop :=
  ∀ L, K L → (∀ θ, θ ∈ Γ → suppK K L θ) → suppK K L φ

-- NJA correcto en la clase K
theorem soundnessK {K : List Rule → Prop} {Ax : Form → Prop} (hAx : ∀ φ, Ax φ → validK K [] φ)
    {Γ : List Form} {φ : Form} (d : NJA Ax Γ φ) : validK K Γ φ := by
  induction d with
  | @hyp Γ φ h => intro L _ hΓ; exact hΓ φ h
  | @andI Γ φ ψ _ _ ih₁ ih₂ =>
    intro L hK hΓ; simp only [suppK]; exact ⟨ih₁ L hK hΓ, ih₂ L hK hΓ⟩
  | @andE₁ Γ φ ψ _ ih =>
    intro L hK hΓ; have h := ih L hK hΓ; simp only [suppK] at h; exact h.1
  | @andE₂ Γ φ ψ _ ih =>
    intro L hK hΓ; have h := ih L hK hΓ; simp only [suppK] at h; exact h.2
  | @impI Γ φ ψ _ ih =>
    intro L _ hΓ; simp only [suppK]
    intro C hC hBC hφ
    apply ih C hC
    intro θ hθ
    cases List.mem_cons.mp hθ with
    | inl e => subst e; exact hφ
    | inr h => exact suppK_mono θ hBC (hΓ θ h)
  | @impE Γ φ ψ _ _ ih₁ ih₂ =>
    intro L hK hΓ; have h := ih₁ L hK hΓ; simp only [suppK] at h
    exact h L hK (Ext.refl _) (ih₂ L hK hΓ)
  | @orI₁ Γ φ ψ _ ih =>
    intro L hK hΓ; simp only [suppK]
    intro C hC hBC p k₁ _
    exact k₁ C hC (Ext.refl _) (suppK_mono φ hBC (ih L hK hΓ))
  | @orI₂ Γ φ ψ _ ih =>
    intro L hK hΓ; simp only [suppK]
    intro C hC hBC p _ k₂
    exact k₂ C hC (Ext.refl _) (suppK_mono ψ hBC (ih L hK hΓ))
  | @orE Γ φ ψ χ _ _ _ ih₀ ih₁ ih₂ =>
    intro L hK hΓ
    apply or_elimK φ ψ χ hK (ih₀ L hK hΓ)
    · intro C hC hBC hφ
      apply ih₁ C hC
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hφ
      | inr h => exact suppK_mono θ hBC (hΓ θ h)
    · intro C hC hBC hψ
      apply ih₂ C hC
      intro θ hθ
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hψ
      | inr h => exact suppK_mono θ hBC (hΓ θ h)
  | @botE Γ φ _ ih => intro L hK hΓ; exact bot_elimK φ (ih L hK hΓ)
  | @ax Γ φ h => intro L hK _; exact hAx φ h L hK (fun _ h' => (mem_nil_false h').elim)

-- K = todas: es suppF
theorem suppK_true (φ : Form) : ∀ L, suppK (fun _ => True) L φ ↔ suppF L φ := by
  induction φ with
  | atom _ => intro L; exact Iff.rfl
  | bot => intro L; exact Iff.rfl
  | and φ ψ ih₁ ih₂ =>
    intro L
    show (suppK (fun _ => True) L φ ∧ suppK (fun _ => True) L ψ) ↔ (suppF L φ ∧ suppF L ψ)
    rw [ih₁ L, ih₂ L]
  | imp φ ψ ih₁ ih₂ =>
    intro L
    show (∀ L', True → Ext (ofList L) (ofList L') → suppK (fun _ => True) L' φ →
        suppK (fun _ => True) L' ψ) ↔
      (∀ L', Ext (ofList L) (ofList L') → suppF L' φ → suppF L' ψ)
    exact ⟨fun h L' hL h' => (ih₂ L').mp (h L' True.intro hL ((ih₁ L').mpr h')),
      fun h L' _ hL h' => (ih₂ L').mpr (h L' hL ((ih₁ L').mp h'))⟩
  | or φ ψ ih₁ ih₂ =>
    intro L
    show (∀ L', True → Ext (ofList L) (ofList L') → ∀ p : Atom,
      (∀ L'', True → Ext (ofList L') (ofList L'') → suppK (fun _ => True) L'' φ →
        Deriv (ofList L'') [] p) →
      (∀ L'', True → Ext (ofList L') (ofList L'') → suppK (fun _ => True) L'' ψ →
        Deriv (ofList L'') [] p) →
      Deriv (ofList L') [] p) ↔ suppF L (.or φ ψ)
    constructor
    · intro h L' hL p k₁ k₂
      exact h L' True.intro hL p (fun L'' _ hL'' h'' => k₁ L'' hL'' ((ih₁ L'').mp h''))
        (fun L'' _ hL'' h'' => k₂ L'' hL'' ((ih₂ L'').mp h''))
    · intro h L' _ hL p k₁ k₂
      exact h L' hL p (fun L'' hL'' h'' => k₁ L'' True.intro hL'' ((ih₁ L'').mpr h''))
        (fun L'' hL'' h'' => k₂ L'' True.intro hL'' ((ih₂ L'').mpr h''))

theorem botK {K : List Rule → Prop} (L : List Rule) : ¬ suppK K L .bot := fun h =>
  Nat.not_succ_le_self (cbound L) (deriv_concl (h (cbound L + 1)))

theorem or_introK₁ {K : List Rule → Prop} {L : List Rule} {φ : Form} (ψ : Form)
    (h : suppK K L φ) : suppK K L (.or φ ψ) :=
  fun L' hK hLL' _ k₁ _ => k₁ L' hK (Ext.refl _) (suppK_mono φ hLL' h)

theorem or_introK₂ {K : List Rule → Prop} {L : List Rule} (φ : Form) {ψ : Form}
    (h : suppK K L ψ) : suppK K L (.or φ ψ) :=
  fun L' hK hLL' _ _ k₂ => k₂ L' hK (Ext.refl _) (suppK_mono ψ hLL' h)

theorem or_congrK {K : List Rule → Prop} {a b x y : Form}
    (ha : ∀ L, K L → (suppK K L a ↔ suppK K L x)) (hb : ∀ L, K L → (suppK K L b ↔ suppK K L y))
    (L : List Rule) : suppK K L (.or a b) ↔ suppK K L (.or x y) :=
  ⟨fun h L' hK hLL' p k₁ k₂ => h L' hK hLL' p
      (fun L'' hK'' hL'' h'' => k₁ L'' hK'' hL'' ((ha L'' hK'').mp h''))
      (fun L'' hK'' hL'' h'' => k₂ L'' hK'' hL'' ((hb L'' hK'').mp h'')),
   fun h L' hK hLL' p k₁ k₂ => h L' hK hLL' p
      (fun L'' hK'' hL'' h'' => k₁ L'' hK'' hL'' ((ha L'' hK'').mpr h''))
      (fun L'' hK'' hL'' h'' => k₂ L'' hK'' hL'' ((hb L'' hK'').mpr h''))⟩

theorem deriv_factsL (L : List Rule) {T : List Atom} {p : Atom} (h : p ∈ T) :
    Deriv (ofList (L ++ factsL T)) [] p :=
  Deriv.app ⟨[], p⟩ (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, h, rfl⟩)))
    (fun _ h' => (mem_nil_false h').elim)

-- sin ⊥ y con todos sus átomos derivables: soportada
theorem suppK_atoms {K : List Rule → Prop} (χ : Form) : nb χ → ∀ {L : List Rule},
    (∀ p, p ∈ atomsF χ → Deriv (ofList L) [] p) → suppK K L χ := by
  induction χ with
  | atom p => intro _ L h; exact h p mem0
  | bot => intro h; exact False.elim h
  | and a b iha ihb =>
    intro h L hL
    exact ⟨iha (And.left h) (fun p hp => hL p (List.mem_append.mpr (Or.inl hp))),
      ihb (And.right h) (fun p hp => hL p (List.mem_append.mpr (Or.inr hp)))⟩
  | or a b iha _ =>
    intro h L hL
    have ha := iha (And.left h) (fun p hp => hL p (List.mem_append.mpr (Or.inl hp)))
    exact fun L' hK hLL' _ k₁ _ => k₁ L' hK (Ext.refl _) (suppK_mono a hLL' ha)
  | imp a b _ ihb =>
    intro h L hL
    exact fun L' _ hLL' _ => ihb (And.right h)
      (fun p hp => Deriv.mono hLL' (hL p (List.mem_append.mpr (Or.inr hp))))

-- ¬p nunca, si K admite añadir hechos
theorem negK_atom {K : List Rule → Prop} (hKf : ∀ L, K L → ∀ T, K (L ++ factsL T))
    {L : List Rule} (hL : K L) (p : Atom) : ¬ suppK K L (negF (.atom p)) := fun h =>
  botK _ (h (L ++ factsL [p]) (hKf L hL [p]) (fun _ hr => List.mem_append.mpr (Or.inl hr))
    (deriv_factsL L mem0))

theorem rAnd_K {K : List Rule → Prop} {a b x y : Form}
    (ha : ∀ L, K L → (suppK K L a ↔ suppK K L x)) (hb : ∀ L, K L → (suppK K L b ↔ suppK K L y)) :
    ∀ L, K L → (suppK K L (.and a b) ↔ suppK K L (rAnd x y)) := by
  intro L hL
  unfold rAnd
  by_cases ex : x = .bot
  · rw [ite_eq_left ex]
    constructor
    · intro h; have h1 := (ha L hL).mp (And.left h); rw [ex] at h1; exact h1
    · intro h; exact absurd h (botK L)
  · rw [ite_eq_right ex]
    by_cases ey : y = .bot
    · rw [ite_eq_left ey]
      constructor
      · intro h; have h1 := (hb L hL).mp (And.right h); rw [ey] at h1; exact h1
      · intro h; exact absurd h (botK L)
    · rw [ite_eq_right ey]
      exact ⟨fun h => ⟨(ha L hL).mp (And.left h), (hb L hL).mp (And.right h)⟩,
        fun h => ⟨(ha L hL).mpr (And.left h), (hb L hL).mpr (And.right h)⟩⟩

theorem rOr_K {K : List Rule → Prop} {a b x y : Form}
    (ha : ∀ L, K L → (suppK K L a ↔ suppK K L x)) (hb : ∀ L, K L → (suppK K L b ↔ suppK K L y)) :
    ∀ L, K L → (suppK K L (.or a b) ↔ suppK K L (rOr x y)) := by
  intro L hL
  unfold rOr
  by_cases ex : x = .bot
  · rw [ite_eq_left ex]
    have na : ∀ C, K C → ¬ suppK K C a := fun C hC h => by
      have h1 := (ha C hC).mp h; rw [ex] at h1; exact botK C h1
    constructor
    · intro h
      exact (hb L hL).mp (or_elimK a b b hL h (fun C hC _ h' => absurd h' (na C hC))
        (fun _ _ _ h' => h'))
    · intro h; exact or_introK₂ a ((hb L hL).mpr h)
  · rw [ite_eq_right ex]
    by_cases ey : y = .bot
    · rw [ite_eq_left ey]
      have nb' : ∀ C, K C → ¬ suppK K C b := fun C hC h => by
        have h1 := (hb C hC).mp h; rw [ey] at h1; exact botK C h1
      constructor
      · intro h
        exact (ha L hL).mp (or_elimK a b a hL h (fun _ _ _ h' => h')
          (fun C hC _ h' => absurd h' (nb' C hC)))
      · intro h; exact or_introK₁ b ((ha L hL).mpr h)
    · rw [ite_eq_right ey]
      exact or_congrK ha hb L

theorem rImp_K {K : List Rule → Prop} (hKf : ∀ L, K L → ∀ T, K (L ++ factsL T)) {a b x y : Form}
    (hxn : x = .bot ∨ nb x)
    (ha : ∀ L, K L → (suppK K L a ↔ suppK K L x)) (hb : ∀ L, K L → (suppK K L b ↔ suppK K L y)) :
    ∀ L, K L → (suppK K L (.imp a b) ↔ suppK K L (rImp x y)) := by
  intro L hL
  unfold rImp
  by_cases ex : x = .bot
  · rw [ite_eq_left ex]
    constructor
    · intro _; exact fun _ _ _ h => h
    · intro _ L' hK _ h
      have h1 := (ha L' hK).mp h; rw [ex] at h1; exact absurd h1 (botK L')
  · rw [ite_eq_right ex]
    by_cases ey : y = .bot
    · rw [ite_eq_left ey]
      constructor
      · intro h
        have hnx : nb x := hxn.resolve_left ex
        have hK' := hKf L hL (atomsF x)
        have hext : Ext (ofList L) (ofList (L ++ factsL (atomsF x))) :=
          fun _ hr => List.mem_append.mpr (Or.inl hr)
        have hx' : suppK K (L ++ factsL (atomsF x)) x :=
          suppK_atoms x hnx (fun p hp => deriv_factsL L hp)
        have h2 := (hb _ hK').mp (h _ hK' hext ((ha _ hK').mpr hx'))
        rw [ey] at h2
        exact absurd h2 (botK _)
      · intro h; exact absurd h (botK L)
    · rw [ite_eq_right ey]
      exact ⟨fun h L' hK hLL' h' => (hb L' hK).mp (h L' hK hLL' ((ha L' hK).mpr h')),
        fun h L' hK hLL' h' => (hb L' hK).mpr (h L' hK hLL' ((ha L' hK).mp h'))⟩

-- ⊩_B φ ⟺ ⊩_B ρφ
theorem rho_suppK {K : List Rule → Prop} (hKf : ∀ L, K L → ∀ T, K (L ++ factsL T)) (φ : Form) :
    ∀ L, K L → (suppK K L φ ↔ suppK K L (rho φ)) := by
  induction φ with
  | atom _ => intro L _; exact Iff.rfl
  | bot => intro L _; exact Iff.rfl
  | and a b iha ihb => exact rAnd_K iha ihb
  | or a b iha ihb => exact rOr_K iha ihb
  | imp a b iha ihb => exact rImp_K hKf (rho_nb a) iha ihb

-- nivel 2
theorem rho_suppF (φ : Form) (L : List Rule) : suppF L φ ↔ suppF L (rho φ) :=
  (suppK_true φ L).symm.trans
    ((rho_suppK (K := fun _ => True) (fun _ _ _ => True.intro) φ L True.intro).trans
      (suppK_true (rho φ) L))

theorem finite_valid_rho (φ : Form) : validF [] φ ↔ (rho φ ≠ .bot ∧ validF [] (rho φ)) := by
  constructor
  · intro h
    have h0 : suppF [] (rho φ) := (rho_suppF φ []).mp (h [] (fun _ h' => (mem_nil_false h').elim))
    refine ⟨fun e => ?_, valid_of_nil h0⟩
    rw [e] at h0
    exact finite_bot [] h0
  · intro h L _
    exact (rho_suppF φ L).mpr (h.2 L (fun _ h' => (mem_nil_false h').elim))

-- otra vía a finite_logic: ρφ ≠ ⊥ y ρφ ∈ GKPL
theorem finite_logic_rho (φ : Form) : validF [] φ ↔ (rho φ ≠ .bot ∧ NJA AxG [] (rho φ)) :=
  (finite_valid_rho φ).trans
    ⟨fun h => ⟨h.1, (finite_inquisitive _ ((rho_nb φ).resolve_left h.1)).mp h.2⟩,
     fun h => ⟨h.1, (finite_inquisitive _ ((rho_nb φ).resolve_left h.1)).mpr h.2⟩⟩

-- ¬¬χ para χ sin ⊥, desde ¬¬p atómico
theorem dnB {Ax : Form → Prop} (hD : ∀ p, Ax (negF (negF (.atom p)))) (a : Form) :
    nb a → ∀ Γ, NJA Ax Γ (negF (negF a)) := by
  induction a with
  | atom p => intro _ Γ; exact NJA.ax (hD p)
  | bot => intro h; exact False.elim h
  | and _ _ iha ihb =>
    intro h Γ
    exact NJA.impI (NJA.impE (iha (And.left h) _) (NJA.impI (NJA.impE (ihb (And.right h) _)
      (NJA.impI (NJA.impE (NJA.hyp mem2) (NJA.andI (NJA.hyp mem1) (NJA.hyp mem0)))))))
  | or _ _ iha _ =>
    intro h Γ
    exact NJA.impI (NJA.impE (iha (And.left h) _)
      (NJA.impI (NJA.impE (NJA.hyp mem1) (NJA.orI₁ (NJA.hyp mem0)))))
  | imp _ _ _ ihb =>
    intro h Γ
    exact NJA.impI (NJA.impE (ihb (And.right h) _)
      (NJA.impI (NJA.impE (NJA.hyp mem1) (NJA.impI (NJA.hyp mem1)))))

theorem rAnd_syn {Ax : Form → Prop} {a b x y : Form}
    (ha : ∀ Γ, NJA Ax (a :: Γ) x ∧ NJA Ax (x :: Γ) a)
    (hb : ∀ Γ, NJA Ax (b :: Γ) y ∧ NJA Ax (y :: Γ) b) :
    ∀ Γ, NJA Ax (.and a b :: Γ) (rAnd x y) ∧ NJA Ax (rAnd x y :: Γ) (.and a b) := by
  intro Γ
  have pa : NJA Ax (.and a b :: Γ) x :=
    NJA.cut (NJA.andE₁ (NJA.hyp mem0)) (NJA.weaken ((ha Γ).1) (consSub subTl))
  have pb : NJA Ax (.and a b :: Γ) y :=
    NJA.cut (NJA.andE₂ (NJA.hyp mem0)) (NJA.weaken ((hb Γ).1) (consSub subTl))
  unfold rAnd
  by_cases ex : x = .bot
  · rw [ite_eq_left ex]
    rw [ex] at pa
    exact ⟨pa, NJA.botE (NJA.hyp mem0)⟩
  · rw [ite_eq_right ex]
    by_cases ey : y = .bot
    · rw [ite_eq_left ey]
      rw [ey] at pb
      exact ⟨pb, NJA.botE (NJA.hyp mem0)⟩
    · rw [ite_eq_right ey]
      exact ⟨NJA.andI pa pb,
        NJA.andI (NJA.cut (NJA.andE₁ (NJA.hyp mem0)) (NJA.weaken ((ha Γ).2) (consSub subTl)))
          (NJA.cut (NJA.andE₂ (NJA.hyp mem0)) (NJA.weaken ((hb Γ).2) (consSub subTl)))⟩

theorem rOr_syn {Ax : Form → Prop} {a b x y : Form}
    (ha : ∀ Γ, NJA Ax (a :: Γ) x ∧ NJA Ax (x :: Γ) a)
    (hb : ∀ Γ, NJA Ax (b :: Γ) y ∧ NJA Ax (y :: Γ) b) :
    ∀ Γ, NJA Ax (.or a b :: Γ) (rOr x y) ∧ NJA Ax (rOr x y :: Γ) (.or a b) := by
  intro Γ
  have pa : NJA Ax (a :: Form.or a b :: Γ) x := NJA.weaken ((ha Γ).1) (consSub subTl)
  have pb : NJA Ax (b :: Form.or a b :: Γ) y := NJA.weaken ((hb Γ).1) (consSub subTl)
  unfold rOr
  by_cases ex : x = .bot
  · rw [ite_eq_left ex]
    rw [ex] at pa
    exact ⟨NJA.orE (NJA.hyp mem0) (NJA.botE pa) pb, NJA.orI₂ ((hb Γ).2)⟩
  · rw [ite_eq_right ex]
    by_cases ey : y = .bot
    · rw [ite_eq_left ey]
      rw [ey] at pb
      exact ⟨NJA.orE (NJA.hyp mem0) pa (NJA.botE pb), NJA.orI₁ ((ha Γ).2)⟩
    · rw [ite_eq_right ey]
      exact ⟨NJA.orE (NJA.hyp mem0) (NJA.orI₁ pa) (NJA.orI₂ pb),
        NJA.orE (NJA.hyp mem0) (NJA.orI₁ (NJA.weaken ((ha Γ).2) (consSub subTl)))
          (NJA.orI₂ (NJA.weaken ((hb Γ).2) (consSub subTl)))⟩

theorem rImp_syn {Ax : Form → Prop} (hD : ∀ p, Ax (negF (negF (.atom p)))) {a b x y : Form}
    (hxn : x = .bot ∨ nb x)
    (ha : ∀ Γ, NJA Ax (a :: Γ) x ∧ NJA Ax (x :: Γ) a)
    (hb : ∀ Γ, NJA Ax (b :: Γ) y ∧ NJA Ax (y :: Γ) b) :
    ∀ Γ, NJA Ax (.imp a b :: Γ) (rImp x y) ∧ NJA Ax (rImp x y :: Γ) (.imp a b) := by
  intro Γ
  unfold rImp
  by_cases ex : x = .bot
  · rw [ite_eq_left ex]
    have hax := (ha (topF :: Γ)).1
    rw [ex] at hax
    exact ⟨NJA.top, NJA.impI (NJA.botE hax)⟩
  · rw [ite_eq_right ex]
    by_cases ey : y = .bot
    · rw [ite_eq_left ey]
      have hby := (hb (x :: Form.imp a b :: Γ)).1
      rw [ey] at hby
      have hx : NJA Ax (x :: Form.imp a b :: Γ) .bot :=
        NJA.cut (NJA.impE (NJA.hyp mem1) ((ha (Form.imp a b :: Γ)).2)) hby
      exact ⟨NJA.impE (dnB hD x (hxn.resolve_left ex) _) (NJA.impI hx), NJA.botE (NJA.hyp mem0)⟩
    · rw [ite_eq_right ey]
      exact ⟨NJA.impI (NJA.cut (NJA.impE (NJA.hyp mem1) ((ha (Form.imp a b :: Γ)).2))
               ((hb (x :: Form.imp a b :: Γ)).1)),
             NJA.impI (NJA.cut (NJA.impE (NJA.hyp mem1) ((ha (Form.imp x y :: Γ)).1))
               ((hb (a :: Form.imp x y :: Γ)).2))⟩

-- φ ⊣⊢ ρφ en IPC + ¬¬p
theorem rho_syn {Ax : Form → Prop} (hD : ∀ p, Ax (negF (negF (.atom p)))) (φ : Form) :
    ∀ Γ, NJA Ax (φ :: Γ) (rho φ) ∧ NJA Ax (rho φ :: Γ) φ := by
  induction φ with
  | atom _ => intro Γ; exact ⟨NJA.hyp mem0, NJA.hyp mem0⟩
  | bot => intro Γ; exact ⟨NJA.hyp mem0, NJA.hyp mem0⟩
  | and a b iha ihb => exact rAnd_syn iha ihb
  | or a b iha ihb => exact rOr_syn iha ihb
  | imp a b iha ihb => exact rImp_syn hD (rho_nb a) iha ihb

theorem rho_equiv {Ax : Form → Prop} (hD : ∀ p, Ax (negF (negF (.atom p)))) (φ : Form) :
    NJA Ax [] (.and (.imp φ (rho φ)) (.imp (rho φ) φ)) :=
  NJA.andI (NJA.impI ((rho_syn hD φ []).1)) (NJA.impI ((rho_syn hD φ []).2))

/-! ## Bases finitas de nivel 1 (§8)
  Modelo de L: conjunto de átomos cerrado bajo sus reglas. Sin ⊥, L ⊩ φ ⟺ φ es
  verdadera en todo modelo de L (Teorema 8.1). E1fin: sin ⊥, CPC; en general,
  IPC + ¬¬p + A ∨ (A → B) (Kalmár); su parte cerrada bajo sustitución, G3. -/

abbrev lvl1 (L : List Rule) : Prop := ∀ r, r ∈ L → ∀ pq, pq ∈ r.prems → pq.1 = []

abbrev supp1 := suppK lvl1

abbrev valid1 (φ : Form) : Prop := ∀ L, lvl1 L → supp1 L φ

theorem lvl1_nil : lvl1 [] := fun _ h => (mem_nil_false h).elim

theorem lvl1_app {L M : List Rule} (hL : lvl1 L) (hM : lvl1 M) : lvl1 (L ++ M) := fun r hr =>
  (List.mem_append.mp hr).elim (hL r) (hM r)

theorem lvl1_facts (T : List Atom) : lvl1 (factsL T) := fun r hr pq hpq => by
  cases List.mem_map.mp hr with
  | intro t ht =>
    cases ht with
    | intro _ e => subst e; exact (mem_nil_false hpq).elim

theorem lvl1_closed : ∀ L, lvl1 L → ∀ T, lvl1 (L ++ factsL T) :=
  fun _ hL T => lvl1_app hL (lvl1_facts T)

theorem lvl1_one {a b : Atom} : ∀ pq, pq ∈ (⟨[([], a)], b⟩ : Rule).prems → pq.1 = [] :=
  fun pq hpq => by
    cases List.mem_cons.mp hpq with
    | inl e => subst e; rfl
    | inr h => exact (mem_nil_false h).elim

-- reglas a ⇒ b, a ∈ U, b ∈ S
def abRs (S : List Atom) : List Atom → List Rule
  | []     => []
  | a :: U => S.map (fun b => (⟨[([], a)], b⟩ : Rule)) ++ abRs S U

theorem mem_abRs {S U : List Atom} {r : Rule} (h : r ∈ abRs S U) :
    ∃ a b, a ∈ U ∧ b ∈ S ∧ r = ⟨[([], a)], b⟩ := by
  induction U with
  | nil => exact (mem_nil_false h).elim
  | cons a U ih =>
    cases List.mem_append.mp h with
    | inl h1 =>
      cases List.mem_map.mp h1 with
      | intro b hb => exact ⟨a, b, mem0, hb.1, hb.2.symm⟩
    | inr h2 =>
      cases ih h2 with
      | intro a' h' =>
        cases h' with
        | intro b h'' => exact ⟨a', b, List.mem_cons.mpr (Or.inr h''.1), h''.2.1, h''.2.2⟩

theorem mem_abRs' {S U : List Atom} {a b : Atom} (ha : a ∈ U) (hb : b ∈ S) :
    (⟨[([], a)], b⟩ : Rule) ∈ abRs S U := by
  induction U with
  | nil => exact (mem_nil_false ha).elim
  | cons a' U ih =>
    cases List.mem_cons.mp ha with
    | inl e => subst e; exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨b, hb, rfl⟩))
    | inr h => exact List.mem_append.mpr (Or.inr (ih h))

theorem lvl1_abRs (S U : List Atom) : lvl1 (abRs S U) := fun r hr pq hpq => by
  cases mem_abRs hr with
  | intro a h =>
    cases h with
    | intro b h' =>
      rw [h'.2.2] at hpq
      exact lvl1_one pq hpq

abbrev model (L : List Rule) (v : Atom → Prop) : Prop :=
  ∀ r, r ∈ L → (∀ pq, pq ∈ r.prems → v pq.2) → v r.concl

-- verdad clásica
def tv (v : Atom → Prop) : Form → Prop
  | .atom p  => v p
  | .bot     => False
  | .and a b => tv v a ∧ tv v b
  | .or a b  => tv v a ∨ tv v b
  | .imp a b => tv v a → tv v b

theorem tv_agree {v w : Atom → Prop} (φ : Form) :
    (∀ p, p ∈ atomsF φ → (v p ↔ w p)) → (tv v φ ↔ tv w φ) := by
  induction φ with
  | atom p => intro h; exact h p mem0
  | bot => intro _; exact Iff.rfl
  | and a b iha ihb =>
    intro h
    have ea := iha (fun p hp => h p (List.mem_append.mpr (Or.inl hp)))
    have eb := ihb (fun p hp => h p (List.mem_append.mpr (Or.inr hp)))
    show (tv v a ∧ tv v b) ↔ (tv w a ∧ tv w b)
    rw [ea, eb]
  | or a b iha ihb =>
    intro h
    have ea := iha (fun p hp => h p (List.mem_append.mpr (Or.inl hp)))
    have eb := ihb (fun p hp => h p (List.mem_append.mpr (Or.inr hp)))
    show (tv v a ∨ tv v b) ↔ (tv w a ∨ tv w b)
    rw [ea, eb]
  | imp a b iha ihb =>
    intro h
    have ea := iha (fun p hp => h p (List.mem_append.mpr (Or.inl hp)))
    have eb := ihb (fun p hp => h p (List.mem_append.mpr (Or.inr hp)))
    show (tv v a → tv v b) ↔ (tv w a → tv w b)
    rw [ea, eb]

-- sin ⊥: verdadera si lo son todos sus átomos
theorem tv_full {w : Atom → Prop} (φ : Form) : nb φ → (∀ p, p ∈ atomsF φ → w p) → tv w φ := by
  induction φ with
  | atom p => intro _ h; exact h p mem0
  | bot => intro h; exact False.elim h
  | and a b iha ihb =>
    intro h hw
    exact ⟨iha (And.left h) (fun p hp => hw p (List.mem_append.mpr (Or.inl hp))),
      ihb (And.right h) (fun p hp => hw p (List.mem_append.mpr (Or.inr hp)))⟩
  | or a b iha _ =>
    intro h hw
    exact Or.inl (iha (And.left h) (fun p hp => hw p (List.mem_append.mpr (Or.inl hp))))
  | imp a b _ ihb =>
    intro h hw
    exact fun _ => ihb (And.right h) (fun p hp => hw p (List.mem_append.mpr (Or.inr hp)))

-- lo derivable está en todo modelo
theorem deriv_model {L : List Rule} (hL : lvl1 L) {v : Atom → Prop} (hv : model L v)
    {S : List Atom} {q : Atom} (d : Deriv (ofList L) S q) : (∀ s, s ∈ S → v s) → v q := by
  induction d with
  | ref h => intro hS; exact hS _ h
  | app r hr _ ih =>
    intro hS
    exact hv r hr (fun pq hpq => ih pq hpq (fun s hs => by
      rw [hL r hr pq hpq, List.nil_append] at hs
      exact hS s hs))

-- modelo mínimo
theorem lm_model {L : List Rule} (hL : lvl1 L) : model L (fun q => Deriv (ofList L) [] q) :=
  fun r hr hp => Deriv.app r hr (fun pq hpq => by
    rw [hL r hr pq hpq, List.nil_append]
    exact hp pq hpq)

-- C^S_v: hechos de v ∩ S y reglas a ⇒ b (a ∈ S ∖ v, b ∈ S)
theorem cSv_exists {C : List Rule} (hC : lvl1 C) {v : Atom → Prop} (hv : model C v)
    (S : List Atom) :
    ∃ C' : List Rule, lvl1 C' ∧ Ext (ofList C) (ofList C') ∧ model C' v ∧
      ∀ w, model C' w → model C w ∧ ((∀ a, a ∈ S → (w a ↔ v a)) ∨ (∀ a, a ∈ S → w a)) := by
  cases exists_sub v S with
  | intro T hT =>
    cases exists_sub (fun x => ¬ v x) S with
    | intro U hU =>
      refine ⟨C ++ factsL T ++ abRs S U, lvl1_app (lvl1_app hC (lvl1_facts T)) (lvl1_abRs S U),
        fun _ hr => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr))), ?_, ?_⟩
      · intro r hr hp
        cases List.mem_append.mp hr with
        | inl h1 =>
          cases List.mem_append.mp h1 with
          | inl h2 => exact hv r h2 hp
          | inr h2 =>
            cases List.mem_map.mp h2 with
            | intro a ha =>
              cases ha with
              | intro haT e => subst e; exact ((hT a).mp haT).2
        | inr h1 =>
          cases mem_abRs h1 with
          | intro a h =>
            cases h with
            | intro b h' =>
              rw [h'.2.2] at hp
              exact absurd (hp ([], a) mem0) ((hU a).mp h'.1).2
      · intro w hw
        refine ⟨fun r hr => hw r (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr)))), ?_⟩
        cases Classical.em (∃ a, a ∈ S ∧ ¬ v a ∧ w a) with
        | inl h =>
          cases h with
          | intro a ha =>
            refine Or.inr (fun b hb => ?_)
            exact hw ⟨[([], a)], b⟩
              (List.mem_append.mpr (Or.inr (mem_abRs' ((hU a).mpr ⟨ha.1, ha.2.1⟩) hb)))
              (fun pq hpq => by
                cases List.mem_cons.mp hpq with
                | inl e => rw [e]; exact ha.2.2
                | inr h' => exact (mem_nil_false h').elim)
        | inr h =>
          refine Or.inl (fun a haS => ⟨fun hwa => ?_, fun hva => ?_⟩)
          · apply Classical.byContradiction
            intro hna
            exact h ⟨a, haS, hna, hwa⟩
          · exact hw ⟨[], a⟩ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
              (List.mem_map.mpr ⟨a, (hT a).mpr ⟨haS, hva⟩, rfl⟩)))))
              (fun pq hpq => (mem_nil_false hpq).elim)

-- φ ⊩_C d ⟺ d en todo modelo de C donde φ es verdadera
theorem force_models {c : Form} (hc : nb c)
    (ihc : ∀ C, lvl1 C → (supp1 C c ↔ ∀ v, model C v → tv v c))
    {C : List Rule} (hC : lvl1 C) (d : Atom) :
    (∀ L'', lvl1 L'' → Ext (ofList C) (ofList L'') → supp1 L'' c → Deriv (ofList L'') [] d) ↔
      ∀ w, model C w → tv w c → w d := by
  constructor
  · intro hf w hw hwc
    cases cSv_exists hC hw (atomsF c) with
    | intro D hD =>
      have hDc : supp1 D c := (ihc D hD.1).mpr (fun u hu => by
        cases (hD.2.2.2 u hu).2 with
        | inl hag => exact (tv_agree c hag).mpr hwc
        | inr hfull => exact tv_full c hc hfull)
      exact deriv_model hD.1 hD.2.2.1 (hf D hD.1 hD.2.1 hDc) (fun _ hs => (mem_nil_false hs).elim)
  · intro hm L'' hL'' hCL hc''
    exact hm (fun q => Deriv (ofList L'') [] q) (fun r hr => lm_model hL'' r (hCL r hr))
      ((ihc L'' hL'').mp hc'' _ (lm_model hL''))

-- Teorema 8.1
theorem level1_models (φ : Form) : nb φ → ∀ B : List Rule, lvl1 B →
    (supp1 B φ ↔ ∀ v, model B v → tv v φ) := by
  induction φ with
  | atom p =>
    intro _ B hB
    constructor
    · intro h v hv; exact deriv_model hB hv h (fun _ hs => (mem_nil_false hs).elim)
    · intro h; exact h _ (lm_model hB)
  | bot => intro h; exact False.elim h
  | and a b iha ihb =>
    intro h B hB
    have ea := iha (And.left h) B hB
    have eb := ihb (And.right h) B hB
    constructor
    · intro hs v hv; exact ⟨ea.mp (And.left hs) v hv, eb.mp (And.right hs) v hv⟩
    · intro hm
      exact ⟨ea.mpr (fun v hv => And.left (hm v hv)), eb.mpr (fun v hv => And.right (hm v hv))⟩
  | imp a b iha ihb =>
    intro h B hB
    constructor
    · intro hs v hv hva
      cases cSv_exists hB hv (atomsF a ++ atomsF b) with
      | intro C hC =>
        have hCa : supp1 C a := (iha (And.left h) C hC.1).mpr (fun w hw => by
          cases (hC.2.2.2 w hw).2 with
          | inl hag =>
            exact (tv_agree a (fun p hp => hag p (List.mem_append.mpr (Or.inl hp)))).mpr hva
          | inr hfull =>
            exact tv_full a (And.left h) (fun p hp => hfull p (List.mem_append.mpr (Or.inl hp))))
        have hCb : supp1 C b := hs C hC.1 hC.2.1 hCa
        exact (ihb (And.right h) C hC.1).mp hCb v hC.2.2.1
    · intro hm L hL hBL hLa
      apply (ihb (And.right h) L hL).mpr
      intro w hw
      exact hm w (fun r hr => hw r (hBL r hr)) ((iha (And.left h) L hL).mp hLa w hw)
  | or a b iha ihb =>
    intro h B hB
    have ka := fun (C : List Rule) (hC : lvl1 C) (d : Atom) =>
      force_models (And.left h) (iha (And.left h)) hC d
    have kb := fun (C : List Rule) (hC : lvl1 C) (d : Atom) =>
      force_models (And.right h) (ihb (And.right h)) hC d
    constructor
    · intro hs v hv
      cases Classical.em (tv v a ∨ tv v b) with
      | inl h' => exact h'
      | inr hn =>
        exfalso
        have hfr : ∃ d : Atom, (∀ s, s ∈ atomsF a ++ atomsF b → s ≠ d) ∧
            (∀ r, r ∈ B → r.concl ≠ d) :=
          ⟨lbound B + sumN (atomsF a ++ atomsF b) + 1,
           fun s hs e => Nat.ne_of_lt (Nat.lt_of_le_of_lt (le_sumN _ hs)
             (Nat.lt_succ_of_le (Nat.le_add_left (sumN (atomsF a ++ atomsF b)) (lbound B)))) e,
           fun r hr e => Nat.ne_of_lt (Nat.lt_succ_of_le (Nat.le_trans (atoms_le_lbound hr).1
             (Nat.le_add_right (lbound B) (sumN (atomsF a ++ atomsF b))))) e⟩
        cases exists_sub v (atomsF a ++ atomsF b) with
        | intro T hT =>
          cases exists_sub (fun x => ¬ v x) (atomsF a ++ atomsF b) with
          | intro U hU =>
            cases hfr with
            | intro d hd =>
              have hC : lvl1 (B ++ factsL T ++ abRs [d] U) :=
                lvl1_app (lvl1_app hB (lvl1_facts T)) (lvl1_abRs [d] U)
              have hBC : Ext (ofList B) (ofList (B ++ factsL T ++ abRs [d] U)) :=
                fun _ hr => List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr)))
              -- todo modelo de C donde c es verdadera contiene d
              have forc : ∀ c, (∀ p, p ∈ atomsF c → p ∈ atomsF a ++ atomsF b) → ¬ tv v c →
                  ∀ w, model (B ++ factsL T ++ abRs [d] U) w → tv w c → w d := by
                intro c hcS hnc w hw hwc
                apply Classical.byContradiction
                intro h1
                apply hnc
                refine (tv_agree (v := w) (w := v) c (fun p hp => ⟨fun hwp => ?_, fun hvp => ?_⟩)).mp hwc
                · apply Classical.byContradiction
                  intro hnp
                  exact h1 (hw ⟨[([], p)], d⟩
                    (List.mem_append.mpr (Or.inr (mem_abRs' ((hU p).mpr ⟨hcS p hp, hnp⟩) mem0)))
                    (fun pq hpq => by
                      cases List.mem_cons.mp hpq with
                      | inl e => rw [e]; exact hwp
                      | inr h' => exact (mem_nil_false h').elim))
                · exact hw ⟨[], p⟩ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
                    (List.mem_map.mpr ⟨p, (hT p).mpr ⟨hcS p hp, hvp⟩, rfl⟩)))))
                    (fun pq hpq => (mem_nil_false hpq).elim)
              have ka' := (ka _ hC d).mpr (forc a (fun p hp => List.mem_append.mpr (Or.inl hp))
                (fun h' => hn (Or.inl h')))
              have kb' := (kb _ hC d).mpr (forc b (fun p hp => List.mem_append.mpr (Or.inr hp))
                (fun h' => hn (Or.inr h')))
              have hdC := hs _ hC hBC d ka' kb'
              -- v sin d es modelo de C
              have hv' : model (B ++ factsL T ++ abRs [d] U) (fun q => v q ∧ q ≠ d) := by
                intro r hr hp
                cases List.mem_append.mp hr with
                | inl h1 =>
                  cases List.mem_append.mp h1 with
                  | inl h2 => exact ⟨hv r h2 (fun pq hpq => (hp pq hpq).1), hd.2 r h2⟩
                  | inr h2 =>
                    cases List.mem_map.mp h2 with
                    | intro x hx =>
                      cases hx with
                      | intro hxT e =>
                        subst e
                        exact ⟨((hT x).mp hxT).2, hd.1 x ((hT x).mp hxT).1⟩
                | inr h1 =>
                  cases mem_abRs h1 with
                  | intro x h' =>
                    cases h' with
                    | intro y h'' =>
                      rw [h''.2.2] at hp
                      exact False.elim (((hU x).mp h''.1).2 (hp ([], x) mem0).1)
              exact (deriv_model hC hv' hdC (fun _ hs' => (mem_nil_false hs').elim)).2 rfl
    · intro hm L' hL' hBL' d k₁ k₂
      have hv0 := lm_model hL'
      cases hm (fun q => Deriv (ofList L') [] q) (fun r hr => hv0 r (hBL' r hr)) with
      | inl hta => exact (ka L' hL' d).mp k₁ _ hv0 hta
      | inr htb => exact (kb L' hL' d).mp k₂ _ hv0 htb

theorem valid1_of_nil {φ : Form} (h : supp1 [] φ) : valid1 φ :=
  fun _ _ => suppK_mono φ (fun _ hx => (mem_nil_false hx).elim) h

-- Cor. 8.2(a): sin ⊥, E1fin = CPC
theorem level1_taut (φ : Form) (hb : nb φ) : valid1 φ ↔ ∀ v, tv v φ := by
  constructor
  · intro h v
    exact (level1_models φ hb [] lvl1_nil).mp (h [] lvl1_nil) v (fun _ h' => (mem_nil_false h').elim)
  · intro h
    exact valid1_of_nil ((level1_models φ hb [] lvl1_nil).mpr (fun v _ => h v))

-- (p → q) ∨ (q → p)
def dummF : Form := .or (.imp (.atom 0) (.atom 1)) (.imp (.atom 1) (.atom 0))

-- Cor. 8.2(c): sin propiedad de disyunción
theorem level1_dummett :
    valid1 dummF ∧ ¬ valid1 (.imp (.atom 0) (.atom 1)) ∧ ¬ valid1 (.imp (.atom 1) (.atom 0)) := by
  refine ⟨(level1_taut dummF ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩).mpr
    (fun v => ?_), fun h => ?_, fun h => ?_⟩
  · cases Classical.em (v 1) with
    | inl h1 => exact Or.inl (fun _ => h1)
    | inr h1 => exact Or.inr (fun h' => absurd h' h1)
  · have h0 := (level1_taut (.imp (.atom 0) (.atom 1)) ⟨True.intro, True.intro⟩).mp h (fun x => x = 0)
    exact Nat.one_ne_zero (h0 rfl)
  · have h0 := (level1_taut (.imp (.atom 1) (.atom 0)) ⟨True.intro, True.intro⟩).mp h (fun x => x = 1)
    exact Nat.zero_ne_one (h0 rfl)

-- cláusula de introducción
def suppIK (K : List Rule → Prop) : List Rule → Form → Prop
  | L, .atom p  => Deriv (ofList L) [] p
  | L, .bot     => ∀ p, Deriv (ofList L) [] p
  | L, .and φ ψ => suppIK K L φ ∧ suppIK K L ψ
  | L, .or φ ψ  => suppIK K L φ ∨ suppIK K L ψ
  | L, .imp φ ψ => ∀ L', K L' → Ext (ofList L) (ofList L') → suppIK K L' φ → suppIK K L' ψ

theorem deriv_concl_mem {L : List Rule} {p : Atom} (d : Deriv (ofList L) [] p) :
    ∃ r, r ∈ L ∧ r.concl = p := by
  cases d with
  | ref h => exact (mem_nil_false h).elim
  | app r hr _ => exact ⟨r, hr, rfl⟩

theorem facts_concl {T : List Atom} {p : Atom} (d : Deriv (ofList (factsL T)) [] p) : p ∈ T := by
  cases deriv_concl_mem d with
  | intro r hr =>
    cases List.mem_map.mp hr.1 with
    | intro t ht =>
      rw [← hr.2, ← ht.2]
      exact ht.1

-- en nivel 1, E ≠ I en la base vacía
theorem level1_E_ne_I : supp1 [] dummF ∧ ¬ suppIK lvl1 [] dummF := by
  refine ⟨level1_dummett.1 [] lvl1_nil, fun h => ?_⟩
  have h' : suppIK lvl1 [] (.imp (.atom 0) (.atom 1)) ∨ suppIK lvl1 [] (.imp (.atom 1) (.atom 0)) := h
  cases h' with
  | inl h1 =>
    have d : Deriv (ofList (factsL [0])) [] 1 :=
      h1 (factsL [0]) (lvl1_facts [0]) (fun _ hx => (mem_nil_false hx).elim)
        (Deriv.app ⟨[], 0⟩ (List.mem_map.mpr ⟨0, mem0, rfl⟩) (fun _ h'' => (mem_nil_false h'').elim))
    cases List.mem_cons.mp (facts_concl d) with
    | inl e => exact Nat.one_ne_zero e
    | inr h'' => exact (mem_nil_false h'').elim
  | inr h2 =>
    have d : Deriv (ofList (factsL [1])) [] 0 :=
      h2 (factsL [1]) (lvl1_facts [1]) (fun _ hx => (mem_nil_false hx).elim)
        (Deriv.app ⟨[], 1⟩ (List.mem_map.mpr ⟨1, mem0, rfl⟩) (fun _ h'' => (mem_nil_false h'').elim))
    cases List.mem_cons.mp (facts_concl d) with
    | inl e => exact Nat.zero_ne_one e
    | inr h'' => exact (mem_nil_false h'').elim

theorem valid1_rho (φ : Form) : valid1 φ ↔ (rho φ ≠ .bot ∧ valid1 (rho φ)) :=
  ⟨fun h => ⟨fun e => by
      have h0 := (rho_suppK lvl1_closed φ [] lvl1_nil).mp (h [] lvl1_nil)
      rw [e] at h0
      exact botK [] h0,
    fun L hL => (rho_suppK lvl1_closed φ L hL).mp (h L hL)⟩,
   fun h L hL => (rho_suppK lvl1_closed φ L hL).mpr (h.2 L hL)⟩

/-! ### Kalmár -/

-- IPC + ¬¬p + A ∨ (A → B), A y B sin ⊥
def AxL1 (φ : Form) : Prop :=
  (∃ p, φ = negF (negF (.atom p))) ∨ ∃ A B, nb A ∧ nb B ∧ φ = .or A (.imp A B)

theorem axL1_valid (φ : Form) (h : AxL1 φ) : valid1 φ := by
  cases h with
  | inl h1 =>
    cases h1 with
    | intro p e =>
      rw [e]
      intro L _ L' hL' _ h'
      exact absurd h' (negK_atom lvl1_closed hL' p)
  | inr h2 =>
    cases h2 with
    | intro A h =>
      cases h with
      | intro B h =>
        rw [h.2.2]
        apply (level1_taut (.or A (.imp A B)) ⟨h.1, h.1, h.2.1⟩).mpr
        intro v
        cases Classical.em (tv v A) with
        | inl hA => exact Or.inl hA
        | inr hA => exact Or.inr (fun hA' => absurd hA' hA)

-- con Γ ⊢ p o Γ ⊢ p → χ según v: ψ ∨ χ si ψ es verdadera, ψ → χ si no
theorem kalmar {Ax : Form → Prop} (hAx : ∀ A B, nb A → nb B → Ax (.or A (.imp A B)))
    {χ : Form} {Γ : List Form} {v : Atom → Prop}
    (hv : ∀ p, p ∈ atomsF χ → (v p → NJA Ax Γ (.atom p)) ∧ (¬ v p → NJA Ax Γ (.imp (.atom p) χ)))
    (ψ : Form) : nb ψ → (∀ p, p ∈ atomsF ψ → p ∈ atomsF χ) →
      (tv v ψ → NJA Ax Γ (.or ψ χ)) ∧ (¬ tv v ψ → NJA Ax Γ (.imp ψ χ)) := by
  induction ψ with
  | atom p =>
    intro _ hp
    exact ⟨fun h => NJA.orI₁ ((hv p (hp p mem0)).1 h), fun h => (hv p (hp p mem0)).2 h⟩
  | bot => intro h; exact False.elim h
  | and a b iha ihb =>
    intro hn hS
    have ka := iha (And.left hn) (fun p hp => hS p (List.mem_append.mpr (Or.inl hp)))
    have kb := ihb (And.right hn) (fun p hp => hS p (List.mem_append.mpr (Or.inr hp)))
    constructor
    · intro h
      exact NJA.orE (ka.1 (And.left h))
        (NJA.orE (NJA.wk1 (kb.1 (And.right h)))
          (NJA.orI₁ (NJA.andI (NJA.hyp mem1) (NJA.hyp mem0)))
          (NJA.orI₂ (NJA.hyp mem0)))
        (NJA.orI₂ (NJA.hyp mem0))
    · intro h
      cases Classical.em (tv v a) with
      | inl ha =>
        have hb : ¬ tv v b := fun hb => h ⟨ha, hb⟩
        exact NJA.impI (NJA.impE (NJA.wk1 (kb.2 hb)) (NJA.andE₂ (NJA.hyp mem0)))
      | inr ha =>
        exact NJA.impI (NJA.impE (NJA.wk1 (ka.2 ha)) (NJA.andE₁ (NJA.hyp mem0)))
  | or a b iha ihb =>
    intro hn hS
    have ka := iha (And.left hn) (fun p hp => hS p (List.mem_append.mpr (Or.inl hp)))
    have kb := ihb (And.right hn) (fun p hp => hS p (List.mem_append.mpr (Or.inr hp)))
    constructor
    · intro h
      have h' : tv v a ∨ tv v b := h
      cases h' with
      | inl ha =>
        exact NJA.orE (ka.1 ha) (NJA.orI₁ (NJA.orI₁ (NJA.hyp mem0))) (NJA.orI₂ (NJA.hyp mem0))
      | inr hb =>
        exact NJA.orE (kb.1 hb) (NJA.orI₁ (NJA.orI₂ (NJA.hyp mem0))) (NJA.orI₂ (NJA.hyp mem0))
    · intro h
      have ha : ¬ tv v a := fun ha => h (Or.inl ha)
      have hb : ¬ tv v b := fun hb => h (Or.inr hb)
      exact NJA.impI (NJA.orE (NJA.hyp mem0)
        (NJA.impE (NJA.wk1 (NJA.wk1 (ka.2 ha))) (NJA.hyp mem0))
        (NJA.impE (NJA.wk1 (NJA.wk1 (kb.2 hb))) (NJA.hyp mem0)))
  | imp a b iha ihb =>
    intro hn hS
    have ka := iha (And.left hn) (fun p hp => hS p (List.mem_append.mpr (Or.inl hp)))
    have kb := ihb (And.right hn) (fun p hp => hS p (List.mem_append.mpr (Or.inr hp)))
    constructor
    · intro h
      cases Classical.em (tv v b) with
      | inl hb =>
        exact NJA.orE (kb.1 hb) (NJA.orI₁ (NJA.impI (NJA.hyp mem1))) (NJA.orI₂ (NJA.hyp mem0))
      | inr hb =>
        have ha : ¬ tv v a := fun ha => hb (h ha)
        exact NJA.orE (NJA.ax (hAx a b (And.left hn) (And.right hn)))
          (NJA.orI₂ (NJA.impE (NJA.wk1 (ka.2 ha)) (NJA.hyp mem0)))
          (NJA.orI₁ (NJA.hyp mem0))
    · intro h
      have ha : tv v a := Classical.byContradiction (fun hna => h (fun ha => absurd ha hna))
      have hb : ¬ tv v b := fun hb => h (fun _ => hb)
      exact NJA.impI (NJA.orE (NJA.wk1 (ka.1 ha))
        (NJA.impE (NJA.wk1 (NJA.wk1 (kb.2 hb))) (NJA.impE (NJA.hyp mem1) (NJA.hyp mem0)))
        (NJA.hyp mem0))

-- eliminar las hipótesis con p ∨ (p → χ)
theorem kal_elim {Ax : Form → Prop} (hAx : ∀ A B, nb A → nb B → Ax (.or A (.imp A B)))
    {χ : Form} (hχ : nb χ) (Q : List Atom) : ∀ Γ : List Form,
    (∀ Δ : List Form, (∀ θ, θ ∈ Γ → θ ∈ Δ) →
      (∀ p, p ∈ Q → NJA Ax Δ (.atom p) ∨ NJA Ax Δ (.imp (.atom p) χ)) → NJA Ax Δ χ) →
    NJA Ax Γ χ := by
  induction Q with
  | nil => intro Γ h; exact h Γ (fun _ h' => h') (fun _ hp => (mem_nil_false hp).elim)
  | cons q Q ih =>
    intro Γ h
    apply NJA.orE (NJA.ax (hAx (.atom q) χ True.intro hχ))
    · apply ih (.atom q :: Γ)
      intro Δ hΔ hQ
      apply h Δ (fun θ hθ => hΔ θ (subTl θ hθ))
      intro p hp
      cases List.mem_cons.mp hp with
      | inl e => rw [e]; exact Or.inl (NJA.hyp (hΔ _ mem0))
      | inr h' => exact hQ p h'
    · apply ih (.imp (.atom q) χ :: Γ)
      intro Δ hΔ hQ
      apply h Δ (fun θ hθ => hΔ θ (subTl θ hθ))
      intro p hp
      cases List.mem_cons.mp hp with
      | inl e => rw [e]; exact Or.inr (NJA.hyp (hΔ _ mem0))
      | inr h' => exact hQ p h'

theorem kalmar_taut {Ax : Form → Prop} (hAx : ∀ A B, nb A → nb B → Ax (.or A (.imp A B)))
    {χ : Form} (hχ : nb χ) (ht : ∀ v, tv v χ) : NJA Ax [] χ := by
  apply kal_elim hAx hχ (atomsF χ) []
  intro Δ _ hQ
  have k := kalmar hAx (v := fun p => NJA Ax Δ (.atom p)) (Γ := Δ)
    (fun p hp => ⟨fun h => h, fun h => (hQ p hp).resolve_left h⟩) χ hχ (fun _ h => h)
  exact NJA.orE (k.1 (ht _)) (NJA.hyp mem0) (NJA.hyp mem0)

-- Cor. 8.2(b): E1fin = IPC + ¬¬p + A ∨ (A → B)
theorem level1_logic (φ : Form) : valid1 φ ↔ NJA AxL1 [] φ := by
  constructor
  · intro h
    have hr := (valid1_rho φ).mp h
    have hnb : nb (rho φ) := (rho_nb φ).resolve_left hr.1
    have ht := (level1_taut (rho φ) hnb).mp hr.2
    have hk : NJA AxL1 [] (rho φ) :=
      kalmar_taut (fun A B hA hB => Or.inr ⟨A, B, hA, hB, rfl⟩) hnb ht
    exact NJA.cut hk ((rho_syn (fun p => Or.inl ⟨p, rfl⟩) φ []).2)
  · intro d
    exact fun L hL => soundnessK (K := lvl1) (Ax := AxL1)
      (fun ψ hψ L' hL' _ => axL1_valid ψ hψ L' hL') d L hL
      (fun _ h' => (mem_nil_false h').elim)

/-! ### G3: 0 < ½ < 1 como 0 < 1 < 2 -/

def gmin (x y : Nat) : Nat := if x ≤ y then x else y
def gmax (x y : Nat) : Nat := if x ≤ y then y else x
def gimp (x y : Nat) : Nat := if x ≤ y then 2 else y

def g3 (e : Atom → Nat) : Form → Nat
  | .atom p  => e p
  | .bot     => 0
  | .and a b => gmin (g3 e a) (g3 e b)
  | .or a b  => gmax (g3 e a) (g3 e b)
  | .imp a b => gimp (g3 e a) (g3 e b)

theorem gmin_zl (y : Nat) : gmin 0 y = 0 := by unfold gmin; rw [ite_eq_left (Nat.zero_le y)]

theorem gmin_zr (x : Nat) : gmin x 0 = 0 := by
  unfold gmin
  by_cases h : x ≤ 0
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]

theorem gmax_zl (y : Nat) : gmax 0 y = y := by unfold gmax; rw [ite_eq_left (Nat.zero_le y)]

theorem gmax_zr (x : Nat) : gmax x 0 = x := by
  unfold gmax
  by_cases h : x ≤ 0
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]

theorem gimp_zl (y : Nat) : gimp 0 y = 2 := by unfold gimp; rw [ite_eq_left (Nat.zero_le y)]

theorem gimp_zr {x : Nat} (h : 1 ≤ x) : gimp x 0 = 0 := by
  unfold gimp; rw [ite_eq_right (show ¬ x ≤ 0 by omega)]

theorem gimp_refl (x : Nat) : gimp x x = 2 := by unfold gimp; rw [ite_eq_left (Nat.le_refl x)]

-- sin ⊥ y átomos en {1, 2}: valor en {1, 2}, y 2 ⟺ verdad clásica
theorem g3_nb {e : Atom → Nat} (he : ∀ p, e p = 1 ∨ e p = 2) (χ : Form) : nb χ →
    (g3 e χ = 1 ∨ g3 e χ = 2) ∧ (g3 e χ = 2 ↔ tv (fun p => e p = 2) χ) := by
  induction χ with
  | atom p => intro _; exact ⟨he p, Iff.rfl⟩
  | bot => intro h; exact False.elim h
  | and a b iha ihb =>
    intro hn
    have ka := iha (And.left hn)
    have kb := ihb (And.right hn)
    have h1 := ka.1
    have h2 := kb.1
    show (gmin (g3 e a) (g3 e b) = 1 ∨ gmin (g3 e a) (g3 e b) = 2) ∧
      (gmin (g3 e a) (g3 e b) = 2 ↔ (tv (fun p => e p = 2) a ∧ tv (fun p => e p = 2) b))
    rw [← ka.2, ← kb.2]
    unfold gmin
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]
      exact ⟨h1, fun h3 => ⟨h3, by omega⟩, fun h3 => h3.1⟩
    · rw [ite_eq_right h]
      exact ⟨h2, fun h3 => ⟨by omega, h3⟩, fun h3 => h3.2⟩
  | or a b iha ihb =>
    intro hn
    have ka := iha (And.left hn)
    have kb := ihb (And.right hn)
    have h1 := ka.1
    have h2 := kb.1
    show (gmax (g3 e a) (g3 e b) = 1 ∨ gmax (g3 e a) (g3 e b) = 2) ∧
      (gmax (g3 e a) (g3 e b) = 2 ↔ (tv (fun p => e p = 2) a ∨ tv (fun p => e p = 2) b))
    rw [← ka.2, ← kb.2]
    unfold gmax
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]
      exact ⟨h2, fun h3 => Or.inr h3, fun h3 => h3.elim (fun h4 => by omega) id⟩
    · rw [ite_eq_right h]
      exact ⟨h1, fun h3 => Or.inl h3, fun h3 => h3.elim id (fun h4 => by omega)⟩
  | imp a b iha ihb =>
    intro hn
    have ka := iha (And.left hn)
    have kb := ihb (And.right hn)
    have h1 := ka.1
    have h2 := kb.1
    show (gimp (g3 e a) (g3 e b) = 1 ∨ gimp (g3 e a) (g3 e b) = 2) ∧
      (gimp (g3 e a) (g3 e b) = 2 ↔ (tv (fun p => e p = 2) a → tv (fun p => e p = 2) b))
    rw [← ka.2, ← kb.2]
    unfold gimp
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]
      exact ⟨Or.inr rfl, fun _ h4 => by omega, fun _ => rfl⟩
    · rw [ite_eq_right h]
      exact ⟨h2, fun h3 _ => h3, fun h3 => h3 (by omega)⟩

theorem g3_pos {e : Atom → Nat} (he : ∀ p, 1 ≤ e p) (χ : Form) : nb χ → 1 ≤ g3 e χ := by
  induction χ with
  | atom p => intro _; exact he p
  | bot => intro h; exact False.elim h
  | and a b iha ihb =>
    intro hn
    have h1 := iha (And.left hn)
    have h2 := ihb (And.right hn)
    show 1 ≤ gmin (g3 e a) (g3 e b)
    unfold gmin
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]; exact h1
    · rw [ite_eq_right h]; exact h2
  | or a b iha ihb =>
    intro hn
    have h1 := iha (And.left hn)
    have h2 := ihb (And.right hn)
    show 1 ≤ gmax (g3 e a) (g3 e b)
    unfold gmax
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]; exact h2
    · rw [ite_eq_right h]; exact h1
  | imp a b _ ihb =>
    intro hn
    have h2 := ihb (And.right hn)
    show 1 ≤ gimp (g3 e a) (g3 e b)
    unfold gimp
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]; omega
    · rw [ite_eq_right h]; exact h2

-- las simplificaciones de ρ son las operaciones de G3
theorem g3_rho {e : Atom → Nat} (he : ∀ p, 1 ≤ e p) (φ : Form) : g3 e φ = g3 e (rho φ) := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | and a b iha ihb =>
    show gmin (g3 e a) (g3 e b) = g3 e (rAnd (rho a) (rho b))
    rw [iha, ihb]
    unfold rAnd
    by_cases ex : rho a = .bot
    · rw [ite_eq_left ex, ex]; exact gmin_zl _
    · rw [ite_eq_right ex]
      by_cases ey : rho b = .bot
      · rw [ite_eq_left ey, ey]; exact gmin_zr _
      · rw [ite_eq_right ey]; rfl
  | or a b iha ihb =>
    show gmax (g3 e a) (g3 e b) = g3 e (rOr (rho a) (rho b))
    rw [iha, ihb]
    unfold rOr
    by_cases ex : rho a = .bot
    · rw [ite_eq_left ex, ex]; exact gmax_zl _
    · rw [ite_eq_right ex]
      by_cases ey : rho b = .bot
      · rw [ite_eq_left ey, ey]; exact gmax_zr _
      · rw [ite_eq_right ey]; rfl
  | imp a b iha ihb =>
    show gimp (g3 e a) (g3 e b) = g3 e (rImp (rho a) (rho b))
    rw [iha, ihb]
    unfold rImp
    by_cases ex : rho a = .bot
    · rw [ite_eq_left ex, ex]; exact (gimp_zl _).trans (gimp_refl (e 0)).symm
    · rw [ite_eq_right ex]
      by_cases ey : rho b = .bot
      · rw [ite_eq_left ey, ey]
        exact gimp_zr (g3_pos he (rho a) ((rho_nb a).resolve_left ex))
      · rw [ite_eq_right ey]; rfl

-- valuación clásica como valuación en {1, 2}
noncomputable def ev (v : Atom → Prop) (p : Atom) : Nat :=
  @ite Nat (v p) (Classical.propDecidable (v p)) 2 1

theorem ev_pos {v : Atom → Prop} {p : Atom} (h : v p) : ev v p = 2 := by
  unfold ev
  split
  · rfl
  · contradiction

theorem ev_neg {v : Atom → Prop} {p : Atom} (h : ¬ v p) : ev v p = 1 := by
  unfold ev
  split
  · contradiction
  · rfl

-- Cor. 8.2(d): φ ∈ E1fin ⟺ valor 2 con átomos en {1, 2}
theorem level1_g3 (φ : Form) :
    valid1 φ ↔ ∀ e : Atom → Nat, (∀ p, e p = 1 ∨ e p = 2) → g3 e φ = 2 := by
  have he1 : ∀ e : Atom → Nat, (∀ p, e p = 1 ∨ e p = 2) → ∀ p, 1 ≤ e p :=
    fun e he p => (he p).elim (fun _ => by omega) (fun _ => by omega)
  constructor
  · intro h e he
    have hr := (valid1_rho φ).mp h
    have hnb := (rho_nb φ).resolve_left hr.1
    rw [g3_rho (he1 e he) φ]
    exact ((g3_nb he (rho φ) hnb).2).mpr ((level1_taut _ hnb).mp hr.2 _)
  · intro h
    have hne : rho φ ≠ .bot := fun e => by
      have h2 := h (fun _ => 2) (fun _ => Or.inr rfl)
      rw [g3_rho (e := fun _ => 2) (fun _ => (by decide : (1 : Nat) ≤ 2)) φ, e] at h2
      exact absurd h2 (by decide)
    have hnb := (rho_nb φ).resolve_left hne
    apply (valid1_rho φ).mpr
    refine ⟨hne, (level1_taut _ hnb).mpr (fun v => ?_)⟩
    have hev : ∀ p, ev v p = 1 ∨ ev v p = 2 := fun p =>
      (Classical.em (v p)).elim (fun hp => Or.inr (ev_pos hp)) (fun hp => Or.inl (ev_neg hp))
    have h2 := h (ev v) hev
    rw [g3_rho (he1 _ hev) φ] at h2
    have ht := ((g3_nb hev (rho φ) hnb).2).mp h2
    exact (tv_agree (v := fun p => ev v p = 2) (w := v) (rho φ) (fun p _ => ⟨fun hp => (Classical.em (v p)).elim id (fun hn => by
        have h3 : ev v p = 2 := hp
        rw [ev_neg hn] at h3
        exact absurd h3 (by decide)), fun hp => ev_pos hp⟩)).mp ht

theorem g3_subst (e : Atom → Nat) (σ : Atom → Form) (φ : Form) :
    g3 e (substF σ φ) = g3 (fun p => g3 e (σ p)) φ := by
  induction φ with
  | atom _ => rfl
  | bot => rfl
  | and a b iha ihb => show gmin _ _ = gmin _ _; rw [iha, ihb]
  | or a b iha ihb => show gmax _ _ = gmax _ _; rw [iha, ihb]
  | imp a b iha ihb => show gimp _ _ = gimp _ _; rw [iha, ihb]

theorem g3_ext {e e' : Atom → Nat} (h : ∀ p, e p = e' p) (φ : Form) : g3 e φ = g3 e' φ := by
  induction φ with
  | atom p => exact h p
  | bot => rfl
  | and a b iha ihb => show gmin _ _ = gmin _ _; rw [iha, ihb]
  | or a b iha ihb => show gmax _ _ = gmax _ _; rw [iha, ihb]
  | imp a b iha ihb => show gimp _ _ = gimp _ _; rw [iha, ihb]

theorem g3_le2 {e : Atom → Nat} (he : ∀ p, e p ≤ 2) (φ : Form) : g3 e φ ≤ 2 := by
  induction φ with
  | atom p => exact he p
  | bot => exact Nat.zero_le _
  | and a b iha ihb =>
    show gmin (g3 e a) (g3 e b) ≤ 2
    unfold gmin
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]; exact iha
    · rw [ite_eq_right h]; exact ihb
  | or a b iha ihb =>
    show gmax (g3 e a) (g3 e b) ≤ 2
    unfold gmax
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]; exact ihb
    · rw [ite_eq_right h]; exact iha
  | imp a b _ ihb =>
    show gimp (g3 e a) (g3 e b) ≤ 2
    unfold gimp
    by_cases h : g3 e a ≤ g3 e b
    · rw [ite_eq_left h]; exact Nat.le_refl 2
    · rw [ite_eq_right h]; exact ihb

-- ⊥, q₀ y ⊤ toman los valores 0, 1 y 2 si todos los átomos valen 1
def sig3 (e : Atom → Nat) (p : Atom) : Form :=
  if e p = 0 then .bot else if e p = 1 then .atom 0 else topF

theorem sig3_val {e : Atom → Nat} (he : ∀ p, e p ≤ 2) (p : Atom) :
    g3 (fun _ => 1) (sig3 e p) = e p := by
  unfold sig3
  by_cases h0 : e p = 0
  · rw [ite_eq_left h0]; exact h0.symm
  · rw [ite_eq_right h0]
    by_cases h1 : e p = 1
    · rw [ite_eq_left h1]; exact h1.symm
    · rw [ite_eq_right h1]
      have h2 : e p = 2 := by have := he p; omega
      exact (gimp_refl 1).trans h2.symm

abbrev valid1S (φ : Form) : Prop := ∀ σ : Atom → Form, valid1 (substF σ φ)

-- la parte de E1fin cerrada bajo sustitución es la lógica de G3
theorem level1_subst_g3 (φ : Form) :
    valid1S φ ↔ ∀ e : Atom → Nat, (∀ p, e p ≤ 2) → g3 e φ = 2 := by
  constructor
  · intro h e he
    have hv := (level1_g3 _).mp (h (sig3 e)) (fun _ => 1) (fun _ => Or.inl rfl)
    rw [g3_subst] at hv
    exact (g3_ext (fun p => sig3_val he p) φ).symm.trans hv
  · intro h σ
    apply (level1_g3 _).mpr
    intro e he
    rw [g3_subst]
    exact h _ (fun p => g3_le2 (fun q => (he q).elim (fun _ => by omega) (fun _ => by omega)) (σ p))

/-! ## Sustitución y KC (§7)
  M: anticadena w₀, w₁, … bajo un máximo t; qᵢ = i+1 vale en wᵢ y en t. Un estado
  es Y : ℕ → Prop (los wᵢ con Y i, más t). Lema 7.1: Y ⊨ φ ⟺ algún α ∈ nf φ es
  verdadera en todo wᵢ de Y. Lema 7.3: todo marco finito con raíz y máximo es imagen
  p-mórfica de un marco booleano. Con el teorema de Jankov como hipótesis,
  E2fin_s = KC. -/

-- KC = IPC + ¬ψ ∨ ¬¬ψ
def AxKC (φ : Form) : Prop := ∃ ψ, φ = .or (negF ψ) (negF (negF ψ))

-- sustitución en derivaciones
theorem NJA.instF {Ax : Form → Prop} (hAx : ∀ σ φ, Ax φ → Ax (substF σ φ)) (σ : Atom → Form)
    {Γ : List Form} {φ : Form} (d : NJA Ax Γ φ) : NJA Ax (Γ.map (substF σ)) (substF σ φ) := by
  induction d with
  | hyp h => exact NJA.hyp (List.mem_map.mpr ⟨_, h, rfl⟩)
  | andI _ _ ih₁ ih₂ => exact NJA.andI ih₁ ih₂
  | andE₁ _ ih => exact NJA.andE₁ ih
  | andE₂ _ ih => exact NJA.andE₂ ih
  | impI _ ih => exact NJA.impI ih
  | impE _ _ ih₁ ih₂ => exact NJA.impE ih₁ ih₂
  | orI₁ _ ih => exact NJA.orI₁ ih
  | orI₂ _ ih => exact NJA.orI₂ ih
  | orE _ _ _ ih₀ ih₁ ih₂ => exact NJA.orE ih₀ ih₁ ih₂
  | botE _ ih => exact NJA.botE ih
  | ax h => exact NJA.ax (hAx σ _ h)

theorem axKC_subst (σ : Atom → Form) (φ : Form) (h : AxKC φ) : AxKC (substF σ φ) := by
  cases h with
  | intro ψ e => rw [e]; exact ⟨substF σ ψ, rfl⟩

theorem axKC_valid (φ : Form) (h : AxKC φ) : validF [] φ := by
  cases h with
  | intro ψ e => rw [e]; exact finite_kremer ψ

-- KC ⊆ E2fin_s
theorem kc_schematic {φ : Form} (d : NJA AxKC [] φ) : validS φ := fun σ =>
  soundnessA axKC_valid (NJA.instF axKC_subst σ d)

/-! ### Estados del modelo M -/

-- verdad en wᵢ: clásica, solo qᵢ
abbrev cl (i : Nat) (α : Form) : Prop := tv (fun a => a = i + 1) α

def sat : (Nat → Prop) → Form → Prop
  | Y, .atom p  => ∀ i, Y i → p = i + 1
  | _, .bot     => False
  | Y, .and a b => sat Y a ∧ sat Y b
  | Y, .or a b  => sat Y a ∨ sat Y b
  | Y, .imp a b => ∀ Z : Nat → Prop, (∀ i, Z i → Y i) → sat Z a → sat Z b

-- sin ∨ ni ⊥: verdadera en el estado ⟺ en cada uno de sus puntos
theorem sat_flat (α : Form) : nvb α → ∀ Y, (sat Y α ↔ ∀ i, Y i → cl i α) := by
  induction α with
  | atom _ => intro _ Y; exact Iff.rfl
  | bot => intro h; exact False.elim h
  | or _ _ _ _ => intro h; exact False.elim h
  | and a b iha ihb =>
    intro h Y
    have ea := iha (And.left h) Y
    have eb := ihb (And.right h) Y
    constructor
    · intro hs i hi; exact ⟨ea.mp (And.left hs) i hi, eb.mp (And.right hs) i hi⟩
    · intro hc
      exact ⟨ea.mpr (fun i hi => And.left (hc i hi)), eb.mpr (fun i hi => And.right (hc i hi))⟩
  | imp a b iha ihb =>
    intro h Y
    constructor
    · intro hs i hi hai
      have hZ := hs (fun j => j = i) (fun j (hj : j = i) => by rw [hj]; exact hi)
        ((iha (And.left h) _).mpr (fun j (hj : j = i) => by rw [hj]; exact hai))
      exact (ihb (And.right h) _).mp hZ i rfl
    · intro hc Z hZY hZa
      exact (ihb (And.right h) Z).mpr
        (fun i hi => hc i (hZY i hi) ((iha (And.left h) Z).mp hZa i hi))

theorem andL_gen {P : Form → Prop} (hP : ∀ x y, P (.and x y) ↔ (P x ∧ P y)) (X Y : List Form) :
    (∃ γ, γ ∈ andL X Y ∧ P γ) ↔ (∃ x, x ∈ X ∧ P x) ∧ (∃ y, y ∈ Y ∧ P y) := by
  constructor
  · intro h
    cases h with
    | intro γ hγ =>
      cases mem_andL_inv hγ.1 with
      | intro x hx =>
        cases hx with
        | intro y hy =>
          have hp := hγ.2
          rw [hy.2.2] at hp
          exact ⟨⟨x, hy.1, ((hP x y).mp hp).1⟩, ⟨y, hy.2.1, ((hP x y).mp hp).2⟩⟩
  · intro h
    cases h with
    | intro hx hy =>
      cases hx with
      | intro x hx =>
        cases hy with
        | intro y hy => exact ⟨.and x y, mem_andL hx.1 hy.1, (hP x y).mpr ⟨hx.2, hy.2⟩⟩

theorem impNF_gen {P : Form → Prop} (hP : ∀ x y, P (.and x y) ↔ (P x ∧ P y)) (htop : P topF)
    (B A : List Form) :
    (∃ γ, γ ∈ impNF B A ∧ P γ) ↔ ∀ a, a ∈ A → ∃ b, b ∈ B ∧ P (.imp a b) := by
  induction A with
  | nil =>
    constructor
    · intro _ a ha; exact (mem_nil_false ha).elim
    · intro _; exact ⟨topF, mem0, htop⟩
  | cons a A ih =>
    show (∃ γ, γ ∈ andL (B.map (fun b => .imp a b)) (impNF B A) ∧ P γ) ↔ _
    rw [andL_gen hP]
    constructor
    · intro h a' ha'
      cases List.mem_cons.mp ha' with
      | inl e =>
        rw [e]
        cases h.1 with
        | intro x hx =>
          cases List.mem_map.mp hx.1 with
          | intro b hb =>
            cases hb with
            | intro hbB e' => subst e'; exact ⟨b, hbB, hx.2⟩
      | inr h' => exact (ih.mp h.2) a' h'
    · intro h
      constructor
      · cases h a mem0 with
        | intro b hb => exact ⟨.imp a b, List.mem_map.mpr ⟨b, hb.1, rfl⟩, hb.2⟩
      · exact ih.mpr (fun a' ha' => h a' (List.mem_cons.mpr (Or.inr ha')))

theorem sat_and_P (Y : Nat → Prop) (x y : Form) :
    (∀ i, Y i → cl i (.and x y)) ↔ ((∀ i, Y i → cl i x) ∧ (∀ i, Y i → cl i y)) :=
  ⟨fun h => ⟨fun i hi => And.left (h i hi), fun i hi => And.right (h i hi)⟩,
   fun h i hi => ⟨h.1 i hi, h.2 i hi⟩⟩

-- Lema 7.1, en M
theorem sat_nf (φ : Form) : ∀ Y, sat Y φ ↔ ∃ α, α ∈ nfL φ ∧ ∀ i, Y i → cl i α := by
  induction φ with
  | atom p =>
    intro Y
    constructor
    · intro h; exact ⟨.atom p, mem0, h⟩
    · intro h
      cases h with
      | intro α hα =>
        cases List.mem_cons.mp hα.1 with
        | inl e => rw [e] at hα; exact hα.2
        | inr h' => exact (mem_nil_false h').elim
  | bot =>
    intro Y
    constructor
    · intro h; exact False.elim h
    · intro h
      cases h with
      | intro α hα => exact (mem_nil_false hα.1).elim
  | and a b iha ihb =>
    intro Y
    have hg := andL_gen (P := fun γ => ∀ i, Y i → cl i γ) (sat_and_P Y) (nfL a) (nfL b)
    constructor
    · intro h
      exact hg.mpr ⟨(iha Y).mp (And.left h), (ihb Y).mp (And.right h)⟩
    · intro h
      have h2 := hg.mp h
      exact ⟨(iha Y).mpr h2.1, (ihb Y).mpr h2.2⟩
  | or a b iha ihb =>
    intro Y
    show (sat Y a ∨ sat Y b) ↔ ∃ α, α ∈ nfL a ++ nfL b ∧ ∀ i, Y i → cl i α
    rw [iha Y, ihb Y]
    constructor
    · intro h
      cases h with
      | inl h1 =>
        cases h1 with
        | intro α hα => exact ⟨α, List.mem_append.mpr (Or.inl hα.1), hα.2⟩
      | inr h2 =>
        cases h2 with
        | intro α hα => exact ⟨α, List.mem_append.mpr (Or.inr hα.1), hα.2⟩
    · intro h
      cases h with
      | intro α hα =>
        cases List.mem_append.mp hα.1 with
        | inl h1 => exact Or.inl ⟨α, h1, hα.2⟩
        | inr h2 => exact Or.inr ⟨α, h2, hα.2⟩
  | imp a b iha ihb =>
    intro Y
    have hg := impNF_gen (P := fun γ => ∀ i, Y i → cl i γ) (sat_and_P Y)
      (fun i _ h => h) (nfL b) (nfL a)
    constructor
    · intro h
      apply hg.mpr
      intro α hα
      have hZ := h (fun j => Y j ∧ cl j α) (fun j hj => And.left hj)
        ((iha _).mpr ⟨α, hα, fun j hj => And.right hj⟩)
      cases (ihb _).mp hZ with
      | intro β hβ => exact ⟨β, hβ.1, fun i hi hai => hβ.2 i ⟨hi, hai⟩⟩
    · intro h Z hZY hZa
      cases (iha Z).mp hZa with
      | intro α hα =>
        cases hg.mp h α hα.1 with
        | intro β hβ => exact (ihb Z).mpr ⟨β, hβ.1, fun i hi => hβ.2 i (hZY i hi) (hα.2 i hi)⟩

-- NJ es correcto para la verdad clásica
theorem tv_sound {v : Atom → Prop} {Γ : List Form} {φ : Form} (d : NJ Γ φ) :
    (∀ θ, θ ∈ Γ → tv v θ) → tv v φ := by
  induction d with
  | hyp h => intro hw; exact hw _ h
  | andI _ _ ih₁ ih₂ => intro hw; exact And.intro (ih₁ hw) (ih₂ hw)
  | andE₁ _ ih => intro hw; exact And.left (ih hw)
  | andE₂ _ ih => intro hw; exact And.right (ih hw)
  | impI _ ih =>
    intro hw hφ
    exact ih (fun θ hθ => by
      cases List.mem_cons.mp hθ with
      | inl e => subst e; exact hφ
      | inr h => exact hw θ h)
  | impE _ _ ih₁ ih₂ => intro hw; exact ih₁ hw (ih₂ hw)
  | orI₁ _ ih => intro hw; exact Or.inl (ih hw)
  | orI₂ _ ih => intro hw; exact Or.inr (ih hw)
  | orE _ _ _ ih₀ ih₁ ih₂ =>
    intro hw
    exact Or.elim (ih₀ hw)
      (fun h => ih₁ (fun θ hθ => by
        cases List.mem_cons.mp hθ with
        | inl e => subst e; exact h
        | inr h' => exact hw θ h'))
      (fun h => ih₂ (fun θ hθ => by
        cases List.mem_cons.mp hθ with
        | inl e => subst e; exact h
        | inr h' => exact hw θ h'))
  | botE _ ih => intro hw; exact False.elim (ih hw)

-- Cor. 7.2, en M
theorem valid_sat {φ : Form} (h : validF [] φ) (Y : Nat → Prop) : sat Y φ := by
  cases ((nfL_spec φ).2.2 []).mp (h [] (fun _ h' => (mem_nil_false h').elim)) with
  | intro α hα =>
    have hnj : NJ [] α := finite_complete_nvb (fun _ h' => (mem_nil_false h').elim)
      ((nfL_spec φ).1 α hα.1) (valid_of_nil hα.2)
    exact (sat_nf φ Y).mpr ⟨α, hα.1, fun _ _ => tv_sound hnj (fun _ h' => (mem_nil_false h').elim)⟩

/-! ### Realización de valuaciones booleanas -/

-- α_X ≈ ⋁_{i ∈ X} qᵢ (clásicamente); D(x, y) = (x → y) → y
def alphaX : List Nat → Form
  | []     => .atom 0
  | i :: X => .imp (.imp (.atom (i + 1)) (alphaX X)) (alphaX X)

theorem alphaX_nvb (X : List Nat) : nvb (alphaX X) := by
  induction X with
  | nil => exact True.intro
  | cons _ X ih => exact ⟨⟨True.intro, ih⟩, ih⟩

theorem cl_alphaX (j : Nat) (X : List Nat) : cl j (alphaX X) ↔ j ∈ X := by
  induction X with
  | nil =>
    constructor
    · intro h
      have h' : 0 = j + 1 := h
      exact absurd h' (by omega)
    · intro h; exact (mem_nil_false h).elim
  | cons i X ih =>
    show ((i + 1 = j + 1 → cl j (alphaX X)) → cl j (alphaX X)) ↔ j ∈ i :: X
    constructor
    · intro h
      cases Classical.em (cl j (alphaX X)) with
      | inl h1 => exact List.mem_cons.mpr (Or.inr (ih.mp h1))
      | inr h1 =>
        cases Classical.em (i + 1 = j + 1) with
        | inl e => exact List.mem_cons.mpr (Or.inl (by omega))
        | inr e => exact absurd (h (fun e' => absurd e' e)) h1
    · intro h hk
      cases List.mem_cons.mp h with
      | inl e => exact hk (by omega)
      | inr h' => exact ih.mpr h'

def bigOr : List Form → Form
  | []     => .bot
  | x :: l => .or x (bigOr l)

theorem sat_bigOr (Y : Nat → Prop) (l : List Form) : sat Y (bigOr l) ↔ ∃ x, x ∈ l ∧ sat Y x := by
  induction l with
  | nil =>
    exact ⟨fun h => False.elim h, fun h => by
      cases h with
      | intro x hx => exact (mem_nil_false hx.1).elim⟩
  | cons x l ih =>
    show (sat Y x ∨ sat Y (bigOr l)) ↔ _
    rw [ih]
    constructor
    · intro h
      cases h with
      | inl h1 => exact ⟨x, mem0, h1⟩
      | inr h2 =>
        cases h2 with
        | intro y hy => exact ⟨y, List.mem_cons.mpr (Or.inr hy.1), hy.2⟩
    · intro h
      cases h with
      | intro y hy =>
        cases List.mem_cons.mp hy.1 with
        | inl e => rw [e] at hy; exact Or.inl hy.2
        | inr h' => exact Or.inr ⟨y, h', hy.2⟩

-- subconjuntos de {0, …, m-1}
def powL : Nat → List (List Nat)
  | 0     => [[]]
  | m + 1 => powL m ++ (powL m).map (fun X => m :: X)

theorem powL_lt {m : Nat} {X : List Nat} (h : X ∈ powL m) : ∀ i, i ∈ X → i < m := by
  induction m generalizing X with
  | zero =>
    intro i hi
    cases List.mem_cons.mp h with
    | inl e => rw [e] at hi; exact (mem_nil_false hi).elim
    | inr h' => exact (mem_nil_false h').elim
  | succ m ih =>
    intro i hi
    cases List.mem_append.mp h with
    | inl h1 => have := ih h1 i hi; omega
    | inr h2 =>
      cases List.mem_map.mp h2 with
      | intro X' hX' =>
        rw [← hX'.2] at hi
        cases List.mem_cons.mp hi with
        | inl _ => omega
        | inr h' => have := ih hX'.1 i h'; omega

theorem powL_mem (m : Nat) : ∀ Y : Nat → Prop, (∀ i, Y i → i < m) →
    ∃ X, X ∈ powL m ∧ ∀ i, i ∈ X ↔ Y i := by
  induction m with
  | zero =>
    intro Y hY
    exact ⟨[], mem0, fun i => ⟨fun h => (mem_nil_false h).elim,
      fun h => absurd (hY i h) (Nat.not_lt_zero i)⟩⟩
  | succ m ih =>
    intro Y hY
    cases ih (fun i => Y i ∧ i < m) (fun i h => h.2) with
    | intro X hX =>
      cases Classical.em (Y m) with
      | inl hm =>
        refine ⟨m :: X, List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨X, hX.1, rfl⟩)),
          fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
        · cases List.mem_cons.mp h with
          | inl e => rw [e]; exact hm
          | inr h' => exact ((hX.2 i).mp h').1
        · cases Classical.em (i = m) with
          | inl e => rw [e]; exact mem0
          | inr e =>
            exact List.mem_cons.mpr (Or.inr ((hX.2 i).mpr ⟨h, by have := hY i h; omega⟩))
      | inr hm =>
        refine ⟨X, List.mem_append.mpr (Or.inl hX.1),
          fun i => ⟨fun h => ((hX.2 i).mp h).1, fun h => ?_⟩⟩
        exact (hX.2 i).mpr ⟨h, by
          have h1 := hY i h
          cases Classical.em (i = m) with
          | inl e => rw [e] at h; exact absurd h hm
          | inr _ => omega⟩

-- toda familia de estados cerrada hacia abajo es la extensión de una fórmula
theorem realize (m : Nat) (U : (Nat → Prop) → Prop)
    (hU : ∀ Y Z : Nat → Prop, (∀ i, Y i → i < m) → (∀ i, Z i → Y i) → U Y → U Z) :
    ∃ ρ : Form, ∀ Y : Nat → Prop, (∀ i, Y i → i < m) → (sat Y ρ ↔ U Y) := by
  cases exists_sub (fun X => U (fun i => i ∈ X)) (powL m) with
  | intro L hL =>
    refine ⟨bigOr (L.map alphaX), fun Y hY => ?_⟩
    rw [sat_bigOr]
    constructor
    · intro h
      cases h with
      | intro x hx =>
        cases List.mem_map.mp hx.1 with
        | intro X hX =>
          have hsat := hx.2
          rw [← hX.2] at hsat
          have hYX : ∀ i, Y i → i ∈ X := fun i hi =>
            (cl_alphaX i X).mp ((sat_flat _ (alphaX_nvb X) Y).mp hsat i hi)
          have hXL := (hL X).mp hX.1
          exact hU (fun i => i ∈ X) Y (powL_lt hXL.1) hYX hXL.2
    · intro h
      cases powL_mem m Y hY with
      | intro X hX =>
        have hXY : (fun i => i ∈ X) = Y := funext (fun i => propext (hX.2 i))
        refine ⟨alphaX X, List.mem_map.mpr ⟨X, (hL X).mpr ⟨hX.1, (congrArg U hXY).mpr h⟩, rfl⟩, ?_⟩
        exact (sat_flat _ (alphaX_nvb X) Y).mpr (fun i hi => (cl_alphaX i X).mpr ((hX.2 i).mpr hi))

/-! ### Marcos booleanos y marcos finitos -/

-- estados ⊆, ordenados por ⊇; valuación U
def bforce (U : Atom → (Nat → Prop) → Prop) : (Nat → Prop) → Form → Prop
  | Y, .atom p  => U p Y
  | _, .bot     => False
  | Y, .and a b => bforce U Y a ∧ bforce U Y b
  | Y, .or a b  => bforce U Y a ∨ bforce U Y b
  | Y, .imp a b => ∀ Z : Nat → Prop, (∀ i, Z i → Y i) → bforce U Z a → bforce U Z b

theorem sat_subst {m : Nat} {σ : Atom → Form} {U : Atom → (Nat → Prop) → Prop}
    (hσ : ∀ p Y, (∀ i, Y i → i < m) → (sat Y (σ p) ↔ U p Y)) (φ : Form) :
    ∀ Y, (∀ i, Y i → i < m) → (sat Y (substF σ φ) ↔ bforce U Y φ) := by
  induction φ with
  | atom p => intro Y hY; exact hσ p Y hY
  | bot => intro Y _; exact Iff.rfl
  | and a b iha ihb =>
    intro Y hY
    show (sat Y (substF σ a) ∧ sat Y (substF σ b)) ↔ (bforce U Y a ∧ bforce U Y b)
    rw [iha Y hY, ihb Y hY]
  | or a b iha ihb =>
    intro Y hY
    show (sat Y (substF σ a) ∨ sat Y (substF σ b)) ↔ (bforce U Y a ∨ bforce U Y b)
    rw [iha Y hY, ihb Y hY]
  | imp a b iha ihb =>
    intro Y hY
    show (∀ Z : Nat → Prop, (∀ i, Z i → Y i) → sat Z (substF σ a) → sat Z (substF σ b)) ↔
      (∀ Z : Nat → Prop, (∀ i, Z i → Y i) → bforce U Z a → bforce U Z b)
    constructor
    · intro h Z hZ h1
      have hZm : ∀ i, Z i → i < m := fun i hi => hY i (hZ i hi)
      exact (ihb Z hZm).mp (h Z hZ ((iha Z hZm).mpr h1))
    · intro h Z hZ h1
      have hZm : ∀ i, Z i → i < m := fun i hi => hY i (hZ i hi)
      exact (ihb Z hZm).mpr (h Z hZ ((iha Z hZm).mp h1))

-- modelo de Kripke finito con raíz r y máximo t
structure FinModel where
  n : Nat
  R : Nat → Nat → Prop
  V : Nat → Atom → Prop
  r : Nat
  t : Nat
  hr : r < n
  ht : t < n
  refl : ∀ x, R x x
  trans : ∀ x y z, R x y → R y z → R x z
  anti : ∀ x y, R x y → R y x → x = y
  root : ∀ x, x < n → R r x
  top : ∀ x, x < n → R x t
  mono : ∀ x y p, R x y → V x p → V y p

def fforce (M : FinModel) : Nat → Form → Prop
  | w, .atom p  => M.V w p
  | _, .bot     => False
  | w, .and a b => fforce M w a ∧ fforce M w b
  | w, .or a b  => fforce M w a ∨ fforce M w b
  | w, .imp a b => ∀ u, u < M.n → M.R w u → fforce M u a → fforce M u b

-- Jankov 1968: KC es completa para los marcos finitos con raíz y máximo
def JankovKC : Prop := ∀ φ : Form, ¬ NJA AxKC [] φ → ∃ M : FinModel, ¬ fforce M M.r φ

-- p-morfismo (relacional) de los estados ⊆ {0, …, m-1} sobre M
structure PMor (M : FinModel) (m : Nat) (G : (Nat → Prop) → Nat → Prop) : Prop where
  fn : ∀ Y x x', G Y x → G Y x' → x = x'
  tot : ∀ Y, (∀ i, Y i → i < m) → ∃ x, G Y x
  ltn : ∀ Y x, G Y x → x < M.n
  forth : ∀ Y Z x z, (∀ i, Y i → i < m) → (∀ i, Z i → Y i) → G Y x → G Z z → M.R x z
  back : ∀ Y x y, (∀ i, Y i → i < m) → G Y x → y < M.n → M.R x y →
    ∃ Z, (∀ i, Z i → Y i) ∧ G Z y
  root : G (fun i => i < m) M.r

-- valuación inducida
abbrev pval (M : FinModel) (G : (Nat → Prop) → Nat → Prop) : Atom → (Nat → Prop) → Prop :=
  fun p Z => ∃ x, G Z x ∧ M.V x p

theorem pmorph_down {M : FinModel} {m : Nat} {G : (Nat → Prop) → Nat → Prop} (hP : PMor M m G)
    (p : Atom) (Y Z : Nat → Prop) (hY : ∀ i, Y i → i < m) (hZY : ∀ i, Z i → Y i)
    (h : pval M G p Y) : pval M G p Z := by
  cases h with
  | intro x hx =>
    cases hP.tot Z (fun i hi => hY i (hZY i hi)) with
    | intro z hz => exact ⟨z, hz, M.mono x z p (hP.forth Y Z x z hY hZY hx.1 hz) hx.2⟩

theorem pmorph {M : FinModel} {m : Nat} {G : (Nat → Prop) → Nat → Prop} (hP : PMor M m G)
    (φ : Form) : ∀ Y x, (∀ i, Y i → i < m) → G Y x → (bforce (pval M G) Y φ ↔ fforce M x φ) := by
  induction φ with
  | atom p =>
    intro Y x _ hG
    constructor
    · intro h
      cases h with
      | intro x' hx' => rw [hP.fn Y x x' hG hx'.1]; exact hx'.2
    · intro h; exact ⟨x, hG, h⟩
  | bot => intro _ _ _ _; exact Iff.rfl
  | and a b iha ihb =>
    intro Y x hY hG
    show (bforce (pval M G) Y a ∧ bforce (pval M G) Y b) ↔ (fforce M x a ∧ fforce M x b)
    rw [iha Y x hY hG, ihb Y x hY hG]
  | or a b iha ihb =>
    intro Y x hY hG
    show (bforce (pval M G) Y a ∨ bforce (pval M G) Y b) ↔ (fforce M x a ∨ fforce M x b)
    rw [iha Y x hY hG, ihb Y x hY hG]
  | imp a b iha ihb =>
    intro Y x hY hG
    show (∀ Z : Nat → Prop, (∀ i, Z i → Y i) → bforce (pval M G) Z a → bforce (pval M G) Z b) ↔
      (∀ u, u < M.n → M.R x u → fforce M u a → fforce M u b)
    constructor
    · intro h u hu hxu hua
      cases hP.back Y x u hY hG hu hxu with
      | intro Z hZ =>
        have hZm : ∀ i, Z i → i < m := fun i hi => hY i (hZ.1 i hi)
        exact (ihb Z u hZm hZ.2).mp (h Z hZ.1 ((iha Z u hZm hZ.2).mpr hua))
    · intro h Z hZY hZa
      have hZm : ∀ i, Z i → i < m := fun i hi => hY i (hZY i hi)
      cases hP.tot Z hZm with
      | intro z hz =>
        exact (ihb Z z hZm hz).mpr (h z (hP.ltn Z z hz) (hP.forth Y Z x z hY hZY hG hz)
          ((iha Z z hZm hz).mp hZa))

-- refutada en la raíz de un marco con p-morfismo booleano: alguna instancia no es válida
theorem refute_bool {M : FinModel} {m : Nat} {G : (Nat → Prop) → Nat → Prop} (hP : PMor M m G)
    {φ : Form} (hφ : ¬ fforce M M.r φ) : ¬ validS φ := by
  intro hS
  have hreal : ∀ p : Atom, ∃ ρ : Form, ∀ Y : Nat → Prop, (∀ i, Y i → i < m) →
      (sat Y ρ ↔ pval M G p Y) :=
    fun p => realize m (pval M G p) (pmorph_down hP p)
  have h1 := valid_sat (hS (fun p => Classical.choose (hreal p))) (fun i => i < m)
  have h2 := (sat_subst (σ := fun p => Classical.choose (hreal p)) (U := pval M G)
    (fun p Y hY => Classical.choose_spec (hreal p) Y hY) φ (fun i => i < m) (fun _ h => h)).mp h1
  exact hφ ((pmorph hP φ (fun i => i < m) M.r (fun _ h => h) hP.root).mp h2)

/-! ### Lema 7.3: desdoblamiento en cadenas y supremos -/

-- cadenas estrictas desde la raíz, al revés: la cabeza es el último punto
def chainT (M : FinModel) : Nat → List Nat → Prop
  | x, []     => x = M.r
  | x, y :: l => x < M.n ∧ M.R y x ∧ x ∉ y :: l ∧ chainT M y l

def chainP (M : FinModel) : List Nat → Prop
  | []     => False
  | x :: l => chainT M x l

def chd : List Nat → Nat
  | []     => 0
  | x :: _ => x

def nodupL : List Nat → Prop
  | []     => True
  | x :: l => x ∉ l ∧ nodupL l

theorem chainP_ne {M : FinModel} {s : List Nat} (h : chainP M s) : s ≠ [] := by
  intro e; rw [e] at h; exact h

theorem chainP_below {M : FinModel} : ∀ (s : List Nat), chainP M s →
    chd s < M.n ∧ ∀ z, z ∈ s → z < M.n ∧ M.R z (chd s)
  | [], h => False.elim h
  | [x], h => by
      have e : x = M.r := h
      refine ⟨by rw [e]; exact M.hr, fun z hz => ?_⟩
      cases List.mem_cons.mp hz with
      | inl ez => rw [ez, e]; exact ⟨M.hr, M.refl _⟩
      | inr h' => exact (mem_nil_false h').elim
  | x :: y :: l, h => by
      have h' : x < M.n ∧ M.R y x ∧ x ∉ y :: l ∧ chainP M (y :: l) := h
      have ih := chainP_below (y :: l) h'.2.2.2
      refine ⟨h'.1, fun z hz => ?_⟩
      cases List.mem_cons.mp hz with
      | inl ez => rw [ez]; exact ⟨h'.1, M.refl _⟩
      | inr h2 =>
        have hz' := ih.2 z h2
        exact ⟨hz'.1, M.trans z y x hz'.2 h'.2.1⟩

theorem chainP_nd {M : FinModel} : ∀ (s : List Nat), chainP M s → nodupL s
  | [], h => False.elim h
  | [_], _ => ⟨fun h => mem_nil_false h, True.intro⟩
  | x :: y :: l, h => by
      have h' : x < M.n ∧ M.R y x ∧ x ∉ y :: l ∧ chainP M (y :: l) := h
      exact ⟨h'.2.2.1, chainP_nd (y :: l) h'.2.2.2⟩

-- un sufijo no vacío de una cadena es una cadena, y su cabeza está debajo
theorem chainP_suf {M : FinModel} : ∀ (u s : List Nat), chainP M (u ++ s) → s ≠ [] →
    chainP M s ∧ M.R (chd s) (chd (u ++ s))
  | [], _, h, _ => ⟨h, M.refl _⟩
  | [x], s, h, hs => by
      cases s with
      | nil => exact absurd rfl hs
      | cons y l =>
        have h' : x < M.n ∧ M.R y x ∧ x ∉ y :: l ∧ chainP M (y :: l) := h
        exact ⟨h'.2.2.2, h'.2.1⟩
  | x :: x' :: u, s, h, hs => by
      have h' : x < M.n ∧ M.R x' x ∧ x ∉ x' :: (u ++ s) ∧ chainP M (x' :: (u ++ s)) := h
      have ih := chainP_suf (x' :: u) s h'.2.2.2 hs
      exact ⟨ih.1, M.trans _ _ _ ih.2 h'.2.1⟩

theorem chainP_ext {M : FinModel} {s : List Nat} (hs : chainP M s) {y : Nat} (hy : y < M.n)
    (hR : M.R (chd s) y) (hn : y ∉ s) : chainP M (y :: s) := by
  cases s with
  | nil => exact False.elim hs
  | cons x l => exact ⟨hy, hR, hn, hs⟩

-- orden de sufijos
abbrev suf (s s' : List Nat) : Prop := ∃ u, s' = u ++ s

theorem suf_refl (s : List Nat) : suf s s := ⟨[], (List.nil_append s).symm⟩

theorem suf_trans {a b c : List Nat} (h1 : suf a b) (h2 : suf b c) : suf a c := by
  cases h1 with
  | intro u hu =>
    cases h2 with
    | intro w hw => exact ⟨w ++ u, by rw [hw, hu, List.append_assoc]⟩

theorem suf_anti {a b : List Nat} (h1 : suf a b) (h2 : suf b a) : a = b := by
  cases h1 with
  | intro u hu =>
    cases h2 with
    | intro w hw =>
      have e1 := congrArg List.length hu
      have e2 := congrArg List.length hw
      rw [List.length_append] at e1 e2
      cases u with
      | nil => rw [hu, List.nil_append]
      | cons x u' => rw [List.length_cons] at e1; omega

theorem suf_nil {s : List Nat} (h : suf s []) : s = [] := by
  cases h with
  | intro u hu =>
    cases s with
    | nil => rfl
    | cons x l =>
      have e := congrArg List.length hu
      rw [List.length_append, List.length_cons, List.length_nil] at e
      omega

-- entre sufijos de c, todo conjunto no vacío tiene máximo
theorem suf_max (c : List Nat) : ∀ (P : List Nat → Prop), (∀ s, P s → suf s c) → (∃ s, P s) →
    ∃ s, P s ∧ ∀ s', P s' → suf s' s := by
  induction c with
  | nil =>
    intro P hP hne
    cases hne with
    | intro s hs =>
      refine ⟨s, hs, fun s' hs' => ?_⟩
      rw [suf_nil (hP s hs), suf_nil (hP s' hs')]
      exact suf_refl []
  | cons x c ih =>
    intro P hP hne
    cases Classical.em (P (x :: c)) with
    | inl hc => exact ⟨x :: c, hc, hP⟩
    | inr hc =>
      refine ih P ?_ hne
      intro s hs
      cases hP s hs with
      | intro u hu =>
        cases u with
        | nil => rw [List.nil_append] at hu; rw [← hu] at hs; exact absurd hs hc
        | cons _ u' => exact ⟨u', (List.cons.inj hu).2⟩

-- palomar
theorem split_mem {a : Nat} : ∀ (l : List Nat), a ∈ l → ∃ s t, l = s ++ a :: t
  | [], h => (mem_nil_false h).elim
  | x :: l, h => by
      cases List.mem_cons.mp h with
      | inl e => exact ⟨[], l, by rw [e, List.nil_append]⟩
      | inr h' =>
        cases split_mem l h' with
        | intro s hs =>
          cases hs with
          | intro t ht => exact ⟨x :: s, t, by rw [ht, List.cons_append]⟩

theorem mem_app_sub {y a : Nat} {s t : List Nat} (h : y ∈ s ++ t) : y ∈ s ++ a :: t :=
  (List.mem_append.mp h).elim (fun h1 => List.mem_append.mpr (Or.inl h1))
    (fun h2 => List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h2))))

theorem mem_mid (s t : List Nat) (a : Nat) : a ∈ s ++ a :: t := List.mem_append.mpr (Or.inr mem0)

theorem nodupL_split {a : Nat} : ∀ (s t : List Nat), nodupL (s ++ a :: t) →
    nodupL (s ++ t) ∧ a ∉ s ++ t
  | [], t, h => by
      have h' : a ∉ t ∧ nodupL t := h
      exact ⟨h'.2, h'.1⟩
  | x :: s, t, h => by
      have h' : x ∉ s ++ a :: t ∧ nodupL (s ++ a :: t) := h
      have ih := nodupL_split s t h'.2
      refine ⟨⟨fun hx => h'.1 (mem_app_sub hx), ih.1⟩, fun ha => ?_⟩
      cases List.mem_cons.mp ha with
      | inl e => exact h'.1 (by rw [← e]; exact mem_mid s t a)
      | inr h2 => exact ih.2 h2

theorem nodup_len : ∀ (n : Nat) (l : List Nat), nodupL l → (∀ x, x ∈ l → x < n) → l.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, h => absurd (h x mem0) (Nat.not_lt_zero x)
  | n + 1, l, hnd, h => by
      cases Classical.em (n ∈ l) with
      | inl hm =>
        cases split_mem l hm with
        | intro s hs =>
          cases hs with
          | intro t ht =>
            rw [ht] at hnd h
            rw [ht]
            have hs' := nodupL_split s t hnd
            have ih := nodup_len n (s ++ t) hs'.1 (fun x hx => by
              have h1 := h x (mem_app_sub hx)
              have h2 : x ≠ n := fun e => hs'.2 (by rw [← e]; exact hx)
              omega)
            rw [List.length_append, List.length_cons]
            rw [List.length_append] at ih
            omega
      | inr hm =>
        have ih := nodup_len n l hnd (fun x hx => by
          have h1 := h x hx
          have h2 : x ≠ n := fun e => hm (by rw [← e]; exact hx)
          omega)
        omega

-- todas las listas de longitud ≤ k con entradas < n
def rng : Nat → List Nat
  | 0     => []
  | n + 1 => rng n ++ [n]

theorem mem_rng {n x : Nat} : x ∈ rng n ↔ x < n := by
  induction n with
  | zero => exact ⟨fun h => (mem_nil_false h).elim, fun h => absurd h (Nat.not_lt_zero x)⟩
  | succ n ih =>
    constructor
    · intro h
      cases List.mem_append.mp h with
      | inl h1 => have := ih.mp h1; omega
      | inr h2 =>
        cases List.mem_cons.mp h2 with
        | inl _ => omega
        | inr h3 => exact (mem_nil_false h3).elim
    · intro h
      cases Classical.em (x = n) with
      | inl e => rw [e]; exact List.mem_append.mpr (Or.inr mem0)
      | inr _ => exact List.mem_append.mpr (Or.inl (ih.mpr (by omega)))

def cmap (f : List Nat → List (List Nat)) : List (List Nat) → List (List Nat)
  | []     => []
  | x :: L => f x ++ cmap f L

theorem mem_cmap {f : List Nat → List (List Nat)} {y x : List Nat} {L : List (List Nat)}
    (hx : x ∈ L) (hy : y ∈ f x) : y ∈ cmap f L := by
  induction L with
  | nil => exact (mem_nil_false hx).elim
  | cons z L ih =>
    cases List.mem_cons.mp hx with
    | inl e => rw [← e]; exact List.mem_append.mpr (Or.inl hy)
    | inr h => exact List.mem_append.mpr (Or.inr (ih h))

def allL (n : Nat) : Nat → List (List Nat)
  | 0     => [[]]
  | k + 1 => allL n k ++ cmap (fun l => (rng n).map (fun x => x :: l)) (allL n k)

theorem mem_allL (n : Nat) : ∀ (k : Nat) (l : List Nat), (∀ x, x ∈ l → x < n) →
    l.length ≤ k → l ∈ allL n k
  | 0, [], _, _ => mem0
  | 0, _ :: _, _, h => absurd h (by rw [List.length_cons]; omega)
  | k + 1, [], _, _ =>
    List.mem_append.mpr (Or.inl (mem_allL n k [] (fun _ h => (mem_nil_false h).elim) (Nat.zero_le _)))
  | k + 1, x :: l, hx, hl => by
      have hl' : l.length ≤ k := by rw [List.length_cons] at hl; omega
      have ih := mem_allL n k l (fun y hy => hx y (List.mem_cons.mpr (Or.inr hy))) hl'
      exact List.mem_append.mpr (Or.inr
        (mem_cmap ih (List.mem_map.mpr ⟨x, mem_rng.mpr (hx x mem0), rfl⟩)))

theorem chains_list (M : FinModel) : ∃ Tl : List (List Nat), ∀ s, s ∈ Tl ↔ chainP M s := by
  cases exists_sub (chainP M) (allL M.n M.n) with
  | intro Tl hT =>
    refine ⟨Tl, fun s => ⟨fun h => ((hT s).mp h).2, fun h => (hT s).mpr ⟨?_, h⟩⟩⟩
    have hb := chainP_below s h
    exact mem_allL M.n M.n s (fun z hz => (hb.2 z hz).1)
      (nodup_len M.n s (chainP_nd s h) (fun z hz => (hb.2 z hz).1))

def lnth : List (List Nat) → Nat → List Nat
  | [],     _     => []
  | x :: _, 0     => x
  | _ :: L, k + 1 => lnth L k

theorem lnth_mem : ∀ (L : List (List Nat)) (i : Nat), i < L.length → lnth L i ∈ L
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, 0, _ => mem0
  | _ :: L, k + 1, h => List.mem_cons.mpr (Or.inr (lnth_mem L k (by rw [List.length_cons] at h; omega)))

theorem lnth_of_mem : ∀ (L : List (List Nat)) (s : List Nat), s ∈ L →
    ∃ i, i < L.length ∧ lnth L i = s
  | [], _, h => (mem_nil_false h).elim
  | x :: L, s, h => by
      cases List.mem_cons.mp h with
      | inl e => exact ⟨0, by rw [List.length_cons]; omega, e.symm⟩
      | inr h' =>
        cases lnth_of_mem L s h' with
        | intro i hi => exact ⟨i + 1, by have := hi.1; rw [List.length_cons]; omega, hi.2⟩

-- complemento del estado, como conjunto de cadenas, más la raíz
def cX (Tl : List (List Nat)) (Y : Nat → Prop) (s : List Nat) : Prop :=
  ∃ i, i < Tl.length ∧ ¬ Y i ∧ lnth Tl i = s

def cXr (M : FinModel) (Tl : List (List Nat)) (Y : Nat → Prop) (s : List Nat) : Prop :=
  cX Tl Y s ∨ s = [M.r]

def cMax (M : FinModel) (Tl : List (List Nat)) (Y : Nat → Prop) (s : List Nat) : Prop :=
  cXr M Tl Y s ∧ ∀ s', cXr M Tl Y s' → suf s' s

-- supremo: la cabeza del máximo si es cadena; si no, t
def cG (M : FinModel) (Tl : List (List Nat)) (Y : Nat → Prop) (x : Nat) : Prop :=
  (∃ s, cMax M Tl Y s ∧ x = chd s) ∨ ((¬ ∃ s, cMax M Tl Y s) ∧ x = M.t)

theorem cXr_chain {M : FinModel} {Tl : List (List Nat)} (hT : ∀ s, s ∈ Tl ↔ chainP M s)
    {Y : Nat → Prop} {s : List Nat} (h : cXr M Tl Y s) : chainP M s := by
  cases h with
  | inl h1 =>
    cases h1 with
    | intro i hi => rw [← hi.2.2]; exact (hT _).mp (lnth_mem Tl i hi.1)
  | inr h2 => rw [h2]; exact (rfl : M.r = M.r)

theorem cXr_mono {M : FinModel} {Tl : List (List Nat)} {Y Z : Nat → Prop}
    (hZY : ∀ i, Z i → Y i) {s : List Nat} (h : cXr M Tl Y s) : cXr M Tl Z s := by
  cases h with
  | inl h1 =>
    cases h1 with
    | intro i hi => exact Or.inl ⟨i, hi.1, fun hz => hi.2.1 (hZY i hz), hi.2.2⟩
  | inr h2 => exact Or.inr h2

theorem cMax_uniq {M : FinModel} {Tl : List (List Nat)} {Y : Nat → Prop} {s s' : List Nat}
    (h : cMax M Tl Y s) (h' : cMax M Tl Y s') : s = s' :=
  suf_anti ((And.right h') s (And.left h)) ((And.right h) s' (And.left h'))

theorem cG_fun {M : FinModel} {Tl : List (List Nat)} {Y : Nat → Prop} {x x' : Nat}
    (h : cG M Tl Y x) (h' : cG M Tl Y x') : x = x' := by
  cases h with
  | inl h1 =>
    cases h1 with
    | intro s hs =>
      cases h' with
      | inl h2 =>
        cases h2 with
        | intro s' hs' => rw [hs.2, hs'.2, cMax_uniq hs.1 hs'.1]
      | inr h2 => exact (h2.1 ⟨s, hs.1⟩).elim
  | inr h1 =>
    cases h' with
    | inl h2 =>
      cases h2 with
      | intro s' hs' => exact (h1.1 ⟨s', hs'.1⟩).elim
    | inr h2 => rw [h1.2, h2.2]

theorem cG_tot (M : FinModel) (Tl : List (List Nat)) (Y : Nat → Prop) : ∃ x, cG M Tl Y x := by
  cases Classical.em (∃ s, cMax M Tl Y s) with
  | inl h =>
    cases h with
    | intro s hs => exact ⟨chd s, Or.inl ⟨s, hs, rfl⟩⟩
  | inr h => exact ⟨M.t, Or.inr ⟨h, rfl⟩⟩

theorem cG_lt {M : FinModel} {Tl : List (List Nat)} (hT : ∀ s, s ∈ Tl ↔ chainP M s)
    {Y : Nat → Prop} {x : Nat} (h : cG M Tl Y x) : x < M.n := by
  cases h with
  | inl h1 =>
    cases h1 with
    | intro s hs => rw [hs.2]; exact (chainP_below s (cXr_chain hT (And.left hs.1))).1
  | inr h1 => rw [h1.2]; exact M.ht

theorem cG_forth {M : FinModel} {Tl : List (List Nat)} (hT : ∀ s, s ∈ Tl ↔ chainP M s)
    {Y Z : Nat → Prop} {x z : Nat} (hZY : ∀ i, Z i → Y i) (hx : cG M Tl Y x)
    (hz : cG M Tl Z z) : M.R x z := by
  cases hz with
  | inr h2 =>
    rw [h2.2]
    exact M.top x (cG_lt hT hx)
  | inl h2 =>
    cases h2 with
    | intro sz hsz =>
      have hsub : ∀ s, cXr M Tl Y s → suf s sz := fun s hs =>
        (And.right hsz.1) s (cXr_mono hZY hs)
      cases hx with
      | inl h1 =>
        cases h1 with
        | intro sy hsy =>
          rw [hsy.2, hsz.2]
          cases hsub sy (And.left hsy.1) with
          | intro u hu =>
            have hc := cXr_chain hT (And.left hsz.1)
            rw [hu] at hc
            have hne := chainP_ne (cXr_chain hT (And.left hsy.1))
            have hR := (chainP_suf u sy hc hne).2
            rw [← hu] at hR
            exact hR
      | inr h1 =>
        exact absurd (suf_max sz (cXr M Tl Y) hsub ⟨[M.r], Or.inr rfl⟩) h1.1

theorem cG_back {M : FinModel} {Tl : List (List Nat)} (hT : ∀ s, s ∈ Tl ↔ chainP M s)
    {Y : Nat → Prop} {x y : Nat} (hx : cG M Tl Y x) (hy : y < M.n) (hxy : M.R x y) :
    ∃ Z : Nat → Prop, (∀ i, Z i → Y i) ∧ cG M Tl Z y := by
  cases hx with
  | inr h1 =>
    have e : y = x := by
      rw [h1.2] at hxy ⊢
      exact M.anti y M.t (M.top y hy) hxy
    exact ⟨Y, fun _ h => h, by rw [e]; exact Or.inr h1⟩
  | inl h1 =>
    cases h1 with
    | intro s hs =>
      cases Classical.em (y = x) with
      | inl e => exact ⟨Y, fun _ h => h, by rw [e]; exact Or.inl ⟨s, hs⟩⟩
      | inr e =>
        have hc := cXr_chain hT (And.left hs.1)
        rw [hs.2] at hxy e
        have hny : y ∉ s := fun hm => e (M.anti y (chd s) ((chainP_below s hc).2 y hm).2 hxy)
        have hc' := chainP_ext hc hy hxy hny
        cases lnth_of_mem Tl (y :: s) ((hT _).mpr hc') with
        | intro j hj =>
          refine ⟨fun i => Y i ∧ i ≠ j, fun i h => h.1,
            Or.inl ⟨y :: s, ⟨Or.inl ⟨j, hj.1, fun h => h.2 rfl, hj.2⟩, ?_⟩, rfl⟩⟩
          intro s' hs'
          cases hs' with
          | inr h2 => exact suf_trans ((And.right hs.1) s' (Or.inr h2)) ⟨[y], rfl⟩
          | inl h2 =>
            cases h2 with
            | intro i hi =>
              cases Classical.em (i = j) with
              | inl eij => rw [← hi.2.2, eij, hj.2]; exact suf_refl _
              | inr eij =>
                have hYi : ¬ Y i := fun hY => hi.2.1 ⟨hY, eij⟩
                exact suf_trans ((And.right hs.1) s' (Or.inl ⟨i, hi.1, hYi, hi.2.2⟩)) ⟨[y], rfl⟩

theorem cG_root (M : FinModel) (Tl : List (List Nat)) : cG M Tl (fun i => i < Tl.length) M.r := by
  have hX : ∀ s, cXr M Tl (fun i => i < Tl.length) s → s = [M.r] := fun s h => by
    cases h with
    | inl h1 =>
      cases h1 with
      | intro i hi => exact absurd hi.1 hi.2.1
    | inr h2 => exact h2
  exact Or.inl ⟨[M.r], ⟨Or.inr rfl, fun s' hs' => by rw [hX s' hs']; exact suf_refl _⟩, rfl⟩

-- Lema 7.3
theorem boolean_cover (M : FinModel) : ∃ m G, PMor M m G := by
  cases chains_list M with
  | intro Tl hT =>
    exact ⟨Tl.length, cG M Tl,
      ⟨fun _ _ _ h h' => cG_fun h h',
       fun Y _ => cG_tot M Tl Y,
       fun _ _ h => cG_lt hT h,
       fun _ _ _ _ _ hZY hx hz => cG_forth hT hZY hx hz,
       fun _ _ _ _ hx hy hxy => cG_back hT hx hy hxy,
       cG_root M Tl⟩⟩

-- Teorema 7.4, con el teorema de Jankov como hipótesis
theorem finite_subst_kc (hJ : JankovKC) (φ : Form) : validS φ ↔ NJA AxKC [] φ := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    cases hJ φ hn with
    | intro M hM =>
      cases boolean_cover M with
      | intro m h' =>
        cases h' with
        | intro G hG => exact refute_bool hG hM h
  · exact kc_schematic

end BeS
