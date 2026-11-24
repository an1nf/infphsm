/-
  Lenguaje clausal de Gheorghiu, *Support is Search* (2026), §2.
  Programas de Harrop hereditarios con cuantificador sobre átomos.
  ⊢_O indexado por altura: `Op n P G` = derivable con altura ≤ n.
-/

namespace Clausal

/-! ## Sintaxis -/

-- átomos y variables: Nat
inductive F where
  | atm : Nat → F
  | var : Nat → F
  | imp : F → F → F
  | and : F → F → F
  | or  : F → F → F
  | all : Nat → F → F

-- F[A/X]
def F.sub (X A : Nat) : F → F
  | .atm a   => .atm a
  | .var Y   => if Y = X then .atm A else .var Y
  | .imp f g => .imp (f.sub X A) (g.sub X A)
  | .and f g => .and (f.sub X A) (g.sub X A)
  | .or f g  => .or (f.sub X A) (g.sub X A)
  | .all Y f => if Y = X then .all Y f else .all Y (f.sub X A)

-- renombramiento de átomos
def F.ren (σ : Nat → Nat) : F → F
  | .atm a   => .atm (σ a)
  | .var Y   => .var Y
  | .imp f g => .imp (f.ren σ) (g.ren σ)
  | .and f g => .and (f.ren σ) (g.ren σ)
  | .or f g  => .or (f.ren σ) (g.ren σ)
  | .all Y f => .all Y (f.ren σ)

-- a ocurre en f
def F.occ (a : Nat) : F → Prop
  | .atm b   => a = b
  | .var _   => False
  | .imp f g => f.occ a ∨ g.occ a
  | .and f g => f.occ a ∨ g.occ a
  | .or f g  => f.occ a ∨ g.occ a
  | .all _ f => f.occ a

theorem mem0 {α : Type} {x : α} {l : List α} : x ∈ x :: l := List.mem_cons.mpr (Or.inl rfl)

/-! ## Renombramiento -/

theorem F.ren_sub (σ : Nat → Nat) (X A : Nat) (f : F) :
    (f.sub X A).ren σ = (f.ren σ).sub X (σ A) := by
  induction f with
  | atm a => rfl
  | var Y => by_cases h : Y = X <;> simp [F.sub, F.ren, h]
  | imp f g ihf ihg => simp only [F.sub, F.ren, ihf, ihg]
  | and f g ihf ihg => simp only [F.sub, F.ren, ihf, ihg]
  | or f g ihf ihg => simp only [F.sub, F.ren, ihf, ihg]
  | all Y f ih => by_cases h : Y = X <;> simp [F.sub, F.ren, h, ih]

theorem F.ren_congr {σ τ : Nat → Nat} (f : F) (h : ∀ a, f.occ a → σ a = τ a) :
    f.ren σ = f.ren τ := by
  induction f with
  | atm b => simp only [F.ren]; rw [h b rfl]
  | var Y => rfl
  | imp f g ihf ihg =>
    simp only [F.ren]
    rw [ihf (fun a ha => h a (Or.inl ha)), ihg (fun a ha => h a (Or.inr ha))]
  | and f g ihf ihg =>
    simp only [F.ren]
    rw [ihf (fun a ha => h a (Or.inl ha)), ihg (fun a ha => h a (Or.inr ha))]
  | or f g ihf ihg =>
    simp only [F.ren]
    rw [ihf (fun a ha => h a (Or.inl ha)), ihg (fun a ha => h a (Or.inr ha))]
  | all Y f ih => simp only [F.ren]; rw [ih h]

theorem F.ren_id (f : F) : f.ren id = f := by
  induction f with
  | atm b => rfl
  | var Y => rfl
  | imp f g ihf ihg => simp only [F.ren, ihf, ihg]
  | and f g ihf ihg => simp only [F.ren, ihf, ihg]
  | or f g ihf ihg => simp only [F.ren, ihf, ihg]
  | all Y f ih => simp only [F.ren, ih]

-- σ[A ↦ B]
def upd (σ : Nat → Nat) (A B : Nat) : Nat → Nat := fun x => if x = A then B else σ x

theorem upd_self {σ : Nat → Nat} {A B : Nat} : upd σ A B A = B := by simp [upd]

theorem upd_ne {σ : Nat → Nat} {A B x : Nat} (h : x ≠ A) : upd σ A B x = σ x := by
  simp [upd, h]

theorem map_ren_congr {σ τ : Nat → Nat} (P : List F)
    (h : ∀ D, D ∈ P → ∀ a, D.occ a → σ a = τ a) : P.map (F.ren σ) = P.map (F.ren τ) := by
  induction P with
  | nil => rfl
  | cons D P ih =>
    simp only [List.map]
    rw [F.ren_congr D (h D mem0), ih (fun E hE => h E (List.mem_cons.mpr (Or.inr hE)))]

-- A ausente ⟹ A ↦ B no cambia nada
theorem ren_away {A B : Nat} {D : F} (h : ¬ D.occ A) : D.ren (upd id A B) = D := by
  rw [F.ren_congr D (τ := id) (fun a ha => upd_ne (fun e => h (by rw [← e]; exact ha))),
    F.ren_id]

theorem map_ren_away {A B : Nat} (P : List F) (h : ∀ D, D ∈ P → ¬ D.occ A) :
    P.map (F.ren (upd id A B)) = P := by
  induction P with
  | nil => rfl
  | cons D P ih =>
    simp only [List.map]
    rw [ren_away (h D mem0), ih (fun E hE => h E (List.mem_cons.mpr (Or.inr hE)))]

theorem sub_ren_away {G : F} {X A B : Nat} (h : ¬ G.occ A) :
    (G.sub X A).ren (upd id A B) = G.sub X B := by
  rw [F.ren_sub, upd_self, ren_away h]

/-! ## Átomos frescos -/

def F.bnd : F → Nat
  | .atm b   => b + 1
  | .var _   => 0
  | .imp f g => f.bnd + g.bnd
  | .and f g => f.bnd + g.bnd
  | .or f g  => f.bnd + g.bnd
  | .all _ f => f.bnd

theorem F.lt_bnd {a : Nat} (f : F) (h : f.occ a) : a < f.bnd := by
  induction f with
  | atm b => have e : a = b := h; show a < b + 1; omega
  | var Y => exact False.elim h
  | imp f g ihf ihg =>
    show a < f.bnd + g.bnd
    cases h with
    | inl h' => have := ihf h'; omega
    | inr h' => have := ihg h'; omega
  | and f g ihf ihg =>
    show a < f.bnd + g.bnd
    cases h with
    | inl h' => have := ihf h'; omega
    | inr h' => have := ihg h'; omega
  | or f g ihf ihg =>
    show a < f.bnd + g.bnd
    cases h with
    | inl h' => have := ihf h'; omega
    | inr h' => have := ihg h'; omega
  | all Y f ih => exact ih h

def bndL : List F → Nat
  | []     => 0
  | D :: P => D.bnd + bndL P

theorem lt_bndL {a : Nat} (P : List F) (D : F) (hD : D ∈ P) (h : D.occ a) : a < bndL P := by
  induction P with
  | nil => cases hD
  | cons E P ih =>
    show a < E.bnd + bndL P
    cases List.mem_cons.mp hD with
    | inl e => have := F.lt_bnd D h; rw [e] at this; omega
    | inr h' => have := ih h'; omega

-- fresco para P y G
abbrev Fresh (A : Nat) (P : List F) (G : F) : Prop :=
  (∀ D, D ∈ P → ¬ D.occ A) ∧ ¬ G.occ A

theorem fresh_exists (P : List F) (G : F) : Fresh (bndL P + G.bnd) P G := by
  constructor
  · intro D hD hocc
    have := lt_bndL P D hD hocc
    omega
  · intro hocc
    have := F.lt_bnd G hocc
    omega

/-! ## Elaboración [P] -/

inductive Elab (P : List F) : F → Prop where
  | mem   {D : F} : D ∈ P → Elab P D
  | andL  {D₁ D₂ : F} : Elab P (.and D₁ D₂) → Elab P D₁
  | andR  {D₁ D₂ : F} : Elab P (.and D₁ D₂) → Elab P D₂
  | headL {G D₁ D₂ : F} : Elab P (.imp G (.and D₁ D₂)) → Elab P (.imp G D₁)
  | headR {G D₁ D₂ : F} : Elab P (.imp G (.and D₁ D₂)) → Elab P (.imp G D₂)
  | curry {G G' D : F} : Elab P (.imp G (.imp G' D)) → Elab P (.imp (.and G G') D)
  | inst  {X : Nat} {D : F} (A : Nat) : Elab P (.all X D) → Elab P (D.sub X A)
  | hinst {X : Nat} {G D : F} (A : Nat) :
      Elab P (.imp G (.all X D)) → Elab P (.imp G (D.sub X A))

theorem Elab.mono {P Q : List F} (hPQ : ∀ D, D ∈ P → D ∈ Q) {D : F} (h : Elab P D) :
    Elab Q D := by
  induction h with
  | mem h => exact Elab.mem (hPQ _ h)
  | andL _ ih => exact Elab.andL ih
  | andR _ ih => exact Elab.andR ih
  | headL _ ih => exact Elab.headL ih
  | headR _ ih => exact Elab.headR ih
  | curry _ ih => exact Elab.curry ih
  | inst A _ ih => exact Elab.inst A ih
  | hinst A _ ih => exact Elab.hinst A ih

-- [P]σ ⊆ [Pσ]
theorem Elab.ren (σ : Nat → Nat) {P : List F} {D : F} (h : Elab P D) :
    Elab (P.map (F.ren σ)) (D.ren σ) := by
  induction h with
  | mem h => exact Elab.mem (List.mem_map.mpr ⟨_, h, rfl⟩)
  | andL _ ih => exact Elab.andL ih
  | andR _ ih => exact Elab.andR ih
  | headL _ ih => exact Elab.headL ih
  | headR _ ih => exact Elab.headR ih
  | curry _ ih => exact Elab.curry ih
  | @inst X D A _ ih =>
    rw [F.ren_sub]
    exact Elab.inst (σ A) ih
  | @hinst X G D A _ ih =>
    show Elab _ (F.imp (G.ren σ) ((D.sub X A).ren σ))
    rw [F.ren_sub]
    exact Elab.hinst (σ A) ih

/-! ## ⊢_O (Fig. 1) -/

inductive Op : Nat → List F → F → Prop where
  | fact {n : Nat} {P : List F} {A : Nat} :
      Elab P (.atm A) → Op (n + 1) P (.atm A)
  | back {n : Nat} {P : List F} {G : F} {A : Nat} :
      Elab P (.imp G (.atm A)) → Op n P G → Op (n + 1) P (.atm A)
  | and {n : Nat} {P : List F} {G₁ G₂ : F} :
      Op n P G₁ → Op n P G₂ → Op (n + 1) P (.and G₁ G₂)
  | orL {n : Nat} {P : List F} {G₁ G₂ : F} :
      Op n P G₁ → Op (n + 1) P (.or G₁ G₂)
  | orR {n : Nat} {P : List F} {G₁ G₂ : F} :
      Op n P G₂ → Op (n + 1) P (.or G₁ G₂)
  | aug {n : Nat} {P : List F} {D G : F} :
      Op n (D :: P) G → Op (n + 1) P (.imp D G)
  | gen {n : Nat} {P : List F} {X : Nat} {G : F} {A : Nat} :
      Fresh A P (.all X G) → Op n P (G.sub X A) → Op (n + 1) P (.all X G)

-- derivable
abbrev Der (P : List F) (G : F) : Prop := ∃ n, Op n P G

-- altura ≤ n ⟹ ≤ m
theorem Op.lift {n : Nat} {P : List F} {G : F} (h : Op n P G) : ∀ {m : Nat}, n ≤ m → Op m P G := by
  induction h with
  | fact e =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.fact e
  | back e _ ih =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.back e (ih (by omega))
  | and _ _ ih₁ ih₂ =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.and (ih₁ (by omega)) (ih₂ (by omega))
  | orL _ ih =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.orL (ih (by omega))
  | orR _ ih =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.orR (ih (by omega))
  | aug _ ih =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.aug (ih (by omega))
  | gen hA _ ih =>
    intro m hm
    cases m with
    | zero => exact absurd hm (by omega)
    | succ k => exact Op.gen hA (ih (by omega))

/-! ## Lema 2.12: renombramiento (preserva altura) -/

theorem Op.ren {n : Nat} {P : List F} {G : F} (h : Op n P G) :
    ∀ σ : Nat → Nat, Op n (P.map (F.ren σ)) (G.ren σ) := by
  induction h with
  | fact e => intro σ; exact Op.fact (Elab.ren σ e)
  | back e _ ih => intro σ; exact Op.back (Elab.ren σ e) (ih σ)
  | and _ _ ih₁ ih₂ => intro σ; exact Op.and (ih₁ σ) (ih₂ σ)
  | orL _ ih => intro σ; exact Op.orL (ih σ)
  | orR _ ih => intro σ; exact Op.orR (ih σ)
  | aug _ ih => intro σ; exact Op.aug (ih σ)
  | @gen n P X G A hA _ ih =>
    intro σ
    cases (show ∃ B, Fresh B (P.map (F.ren σ)) ((F.all X G).ren σ) from
        ⟨_, fresh_exists _ _⟩) with
    | intro B hB =>
      have h1 := ih (upd σ A B)
      have e1 : P.map (F.ren (upd σ A B)) = P.map (F.ren σ) :=
        map_ren_congr P (fun D hD a ha =>
          upd_ne (fun e => hA.1 D hD (by rw [← e]; exact ha)))
      have e2 : (G.sub X A).ren (upd σ A B) = (G.ren σ).sub X B := by
        rw [F.ren_sub, upd_self,
          F.ren_congr G (fun a ha => upd_ne (fun e => hA.2 (by rw [← e]; exact ha)))]
      rw [e1, e2] at h1
      exact Op.gen hB h1

/-! ## Lema 2.13: monotonía (preserva altura) -/

theorem Op.mono (n : Nat) : ∀ {P : List F} {G : F}, Op n P G →
    ∀ {Q : List F}, (∀ D, D ∈ P → D ∈ Q) → Op n Q G := by
  induction n with
  | zero => intro P G h; cases h
  | succ k ih =>
    intro P G h Q hPQ
    cases h with
    | fact e => exact Op.fact (Elab.mono hPQ e)
    | back e h' => exact Op.back (Elab.mono hPQ e) (ih h' hPQ)
    | and h₁ h₂ => exact Op.and (ih h₁ hPQ) (ih h₂ hPQ)
    | orL h' => exact Op.orL (ih h' hPQ)
    | orR h' => exact Op.orR (ih h' hPQ)
    | aug h' =>
      exact Op.aug (ih h' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_cons.mpr (Or.inl e)
        | inr h'' => exact List.mem_cons.mpr (Or.inr (hPQ E h''))))
    | @gen _ _ X G' A hA h' =>
      cases (show ∃ B, Fresh B Q (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have h'' := Op.ren h' (upd id A B)
        rw [map_ren_away P hA.1, sub_ren_away (G := G') hA.2] at h''
        exact Op.gen hB (ih h'' hPQ)

/-! ## Lema 2.14: inversión -/

theorem Op.inv_imp {n : Nat} {P : List F} {D G : F} (h : Op n P (.imp D G)) :
    Op n (D :: P) G := by
  cases h with
  | aug h' => exact Op.lift h' (Nat.le_succ _)

theorem Op.inv_and {n : Nat} {P : List F} {G₁ G₂ : F} (h : Op n P (.and G₁ G₂)) :
    Op n P G₁ ∧ Op n P G₂ := by
  cases h with
  | and h₁ h₂ => exact ⟨Op.lift h₁ (Nat.le_succ _), Op.lift h₂ (Nat.le_succ _)⟩

theorem Op.inv_all {n : Nat} {P : List F} {X : Nat} {G : F} (h : Op n P (.all X G))
    (A : Nat) : Op n P (G.sub X A) := by
  cases h with
  | @gen m _ _ _ A' hA h' =>
    have h'' := Op.ren h' (upd id A' A)
    rw [map_ren_away P hA.1, sub_ren_away (G := G) hA.2] at h''
    exact Op.lift h'' (Nat.le_succ _)

/-! ## Der: derivabilidad sin altura -/

theorem Der.fact {P : List F} {A : Nat} (e : Elab P (.atm A)) : Der P (.atm A) :=
  ⟨_, Op.fact (n := 0) e⟩

theorem Der.back {P : List F} {G : F} {A : Nat} (e : Elab P (.imp G (.atm A))) (h : Der P G) :
    Der P (.atm A) := by
  cases h with
  | intro n h => exact ⟨n + 1, Op.back e h⟩

theorem Der.and {P : List F} {G₁ G₂ : F} (h₁ : Der P G₁) (h₂ : Der P G₂) :
    Der P (.and G₁ G₂) := by
  cases h₁ with
  | intro n₁ h₁ =>
    cases h₂ with
    | intro n₂ h₂ =>
      exact ⟨n₁ + n₂ + 1, Op.and (Op.lift h₁ (by omega)) (Op.lift h₂ (by omega))⟩

theorem Der.orL {P : List F} {G₁ G₂ : F} (h : Der P G₁) : Der P (.or G₁ G₂) := by
  cases h with
  | intro n h => exact ⟨n + 1, Op.orL h⟩

theorem Der.orR {P : List F} {G₁ G₂ : F} (h : Der P G₂) : Der P (.or G₁ G₂) := by
  cases h with
  | intro n h => exact ⟨n + 1, Op.orR h⟩

theorem Der.aug {P : List F} {D G : F} (h : Der (D :: P) G) : Der P (.imp D G) := by
  cases h with
  | intro n h => exact ⟨n + 1, Op.aug h⟩

theorem Der.gen {P : List F} {X : Nat} {G : F} {A : Nat} (hA : Fresh A P (.all X G))
    (h : Der P (G.sub X A)) : Der P (.all X G) := by
  cases h with
  | intro n h => exact ⟨n + 1, Op.gen hA h⟩

theorem Der.inv_imp {P : List F} {D G : F} (h : Der P (.imp D G)) : Der (D :: P) G := by
  cases h with
  | intro n h => exact ⟨n, Op.inv_imp h⟩

theorem Der.inv_and {P : List F} {G₁ G₂ : F} (h : Der P (.and G₁ G₂)) :
    Der P G₁ ∧ Der P G₂ := by
  cases h with
  | intro n h => exact ⟨⟨n, (Op.inv_and h).1⟩, ⟨n, (Op.inv_and h).2⟩⟩

theorem Der.inv_all {P : List F} {X : Nat} {G : F} (h : Der P (.all X G)) (A : Nat) :
    Der P (G.sub X A) := by
  cases h with
  | intro n h => exact ⟨n, Op.inv_all h A⟩

theorem Der.mono {P Q : List F} {G : F} (h : Der P G) (hPQ : ∀ D, D ∈ P → D ∈ Q) :
    Der Q G := by
  cases h with
  | intro n h => exact ⟨n, Op.mono n h hPQ⟩

/-! ## Monotonía por cláusulas resueltas -/

-- [P₁ ++ P₂] = [P₁] ∪ [P₂]
theorem Elab.split {L₁ L₂ : List F} {E : F} (h : Elab (L₁ ++ L₂) E) :
    Elab L₁ E ∨ Elab L₂ E := by
  induction h with
  | mem h =>
    cases List.mem_append.mp h with
    | inl h' => exact Or.inl (Elab.mem h')
    | inr h' => exact Or.inr (Elab.mem h')
  | andL _ ih => exact ih.elim (fun h => Or.inl (Elab.andL h)) (fun h => Or.inr (Elab.andL h))
  | andR _ ih => exact ih.elim (fun h => Or.inl (Elab.andR h)) (fun h => Or.inr (Elab.andR h))
  | headL _ ih => exact ih.elim (fun h => Or.inl (Elab.headL h)) (fun h => Or.inr (Elab.headL h))
  | headR _ ih => exact ih.elim (fun h => Or.inl (Elab.headR h)) (fun h => Or.inr (Elab.headR h))
  | curry _ ih => exact ih.elim (fun h => Or.inl (Elab.curry h)) (fun h => Or.inr (Elab.curry h))
  | inst A _ ih =>
    exact ih.elim (fun h => Or.inl (Elab.inst A h)) (fun h => Or.inr (Elab.inst A h))
  | hinst A _ ih =>
    exact ih.elim (fun h => Or.inl (Elab.hinst A h)) (fun h => Or.inr (Elab.hinst A h))

-- [D] ⊆ [Q] si D ∈ [Q]
theorem Elab.trans {D E : F} {Q : List F} (h : Elab [D] E) (hD : Elab Q D) : Elab Q E := by
  induction h with
  | mem h =>
    cases List.mem_cons.mp h with
    | inl e => subst e; exact hD
    | inr h' => cases h'
  | andL _ ih => exact Elab.andL ih
  | andR _ ih => exact Elab.andR ih
  | headL _ ih => exact Elab.headL ih
  | headR _ ih => exact Elab.headR ih
  | curry _ ih => exact Elab.curry ih
  | inst A _ ih => exact Elab.inst A ih
  | hinst A _ ih => exact Elab.hinst A ih

-- [D₁ ∩ D₂, P] ⊆ {D₁ ∩ D₂} ∪ [D₁, D₂, P]
theorem Elab.and_split {D₁ D₂ E : F} {P : List F} (h : Elab (.and D₁ D₂ :: P) E) :
    E = .and D₁ D₂ ∨ Elab (D₁ :: D₂ :: P) E := by
  induction h with
  | mem h =>
    cases List.mem_cons.mp h with
    | inl e => exact Or.inl e
    | inr h' =>
      exact Or.inr (Elab.mem (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h')))))
  | andL _ ih =>
    cases ih with
    | inl e => cases e; exact Or.inr (Elab.mem mem0)
    | inr h => exact Or.inr (Elab.andL h)
  | andR _ ih =>
    cases ih with
    | inl e => cases e; exact Or.inr (Elab.mem (List.mem_cons.mpr (Or.inr mem0)))
    | inr h => exact Or.inr (Elab.andR h)
  | headL _ ih =>
    cases ih with
    | inl e => cases e
    | inr h => exact Or.inr (Elab.headL h)
  | headR _ ih =>
    cases ih with
    | inl e => cases e
    | inr h => exact Or.inr (Elab.headR h)
  | curry _ ih =>
    cases ih with
    | inl e => cases e
    | inr h => exact Or.inr (Elab.curry h)
  | inst A _ ih =>
    cases ih with
    | inl e => cases e
    | inr h => exact Or.inr (Elab.inst A h)
  | hinst A _ ih =>
    cases ih with
    | inl e => cases e
    | inr h => exact Or.inr (Elab.hinst A h)

-- cláusulas resueltas de [P] ⊆ [Q]
abbrev RC (P Q : List F) : Prop :=
  (∀ A, Elab P (.atm A) → Elab Q (.atm A)) ∧
  (∀ G A, Elab P (.imp G (.atm A)) → Elab Q (.imp G (.atm A)))

theorem RC.of_elab {P Q : List F} (h : ∀ E, Elab P E → Elab Q E) : RC P Q :=
  ⟨fun _ e => h _ e, fun _ _ e => h _ e⟩

theorem RC.cons {P Q : List F} (D : F) (h : RC P Q) : RC (D :: P) (D :: Q) := by
  have sub : ∀ E, Elab [D] E → Elab (D :: Q) E :=
    fun E e => Elab.mono (fun x hx => by
      cases List.mem_cons.mp hx with
      | inl e => exact List.mem_cons.mpr (Or.inl e)
      | inr h' => cases h') e
  have up : ∀ E, Elab Q E → Elab (D :: Q) E :=
    fun E e => Elab.mono (fun x hx => List.mem_cons.mpr (Or.inr hx)) e
  constructor
  · intro A e
    cases Elab.split (L₁ := [D]) (L₂ := P) e with
    | inl e' => exact sub _ e'
    | inr e' => exact up _ (h.1 A e')
  · intro G A e
    cases Elab.split (L₁ := [D]) (L₂ := P) e with
    | inl e' => exact sub _ e'
    | inr e' => exact up _ (h.2 G A e')

-- P, D₁ ∩ D₂ ⊢ G ⟹ P, D₁, D₂ ⊢ G
theorem RC.and_cons {D₁ D₂ : F} {P : List F} : RC (.and D₁ D₂ :: P) (D₁ :: D₂ :: P) :=
  ⟨fun _ e => (Elab.and_split e).elim (fun h => by cases h) id,
   fun _ _ e => (Elab.and_split e).elim (fun h => by cases h) id⟩

-- Lema 2.13, forma de cláusulas resueltas
theorem Op.monoRC (n : Nat) : ∀ {P Q : List F} {G : F}, RC P Q → Op n P G → Op n Q G := by
  induction n with
  | zero => intro P Q G _ h; cases h
  | succ k ih =>
    intro P Q G hPQ h
    cases h with
    | fact e => exact Op.fact (hPQ.1 _ e)
    | back e h' => exact Op.back (hPQ.2 _ _ e) (ih hPQ h')
    | and h₁ h₂ => exact Op.and (ih hPQ h₁) (ih hPQ h₂)
    | orL h' => exact Op.orL (ih hPQ h')
    | orR h' => exact Op.orR (ih hPQ h')
    | @aug _ _ D _ h' => exact Op.aug (ih (RC.cons D hPQ) h')
    | @gen _ _ X G' A hA h' =>
      cases (show ∃ B, Fresh B Q (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have h'' := Op.ren h' (upd id A B)
        rw [map_ren_away P hA.1, sub_ren_away (G := G') hA.2] at h''
        exact Op.gen hB (ih hPQ h'')

theorem Der.monoRC {P Q : List F} {G : F} (hPQ : RC P Q) (h : Der P G) : Der Q G := by
  cases h with
  | intro n h => exact ⟨n, Op.monoRC n hPQ h⟩

/-! ## Fórmulas neutras y cerradas -/

def F.neutral : F → Prop
  | .atm _   => True
  | .var _   => True
  | .imp f g => f.neutral ∧ g.neutral
  | .and f g => f.neutral ∧ g.neutral
  | .or _ _  => False
  | .all _ f => f.neutral

-- X libre en f
def F.fr (X : Nat) : F → Prop
  | .atm _   => False
  | .var Y   => Y = X
  | .imp f g => f.fr X ∨ g.fr X
  | .and f g => f.fr X ∨ g.fr X
  | .or f g  => f.fr X ∨ g.fr X
  | .all Y f => Y ≠ X ∧ f.fr X

abbrev F.closed (f : F) : Prop := ∀ X, ¬ f.fr X

-- peso: baja en todos los casos de 4.6–4.8
def F.w : F → Nat
  | .atm _   => 1
  | .var _   => 1
  | .imp f g => f.w + 2 * g.w + 1
  | .and f g => f.w + g.w + 1
  | .or f g  => f.w + g.w + 1
  | .all _ f => f.w + 1

theorem F.w_sub (X A : Nat) (f : F) : (f.sub X A).w = f.w := by
  induction f with
  | atm a => rfl
  | var Y =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e]; rfl
    · rw [F.sub, ite_eq_right e]
  | imp f g ihf ihg => simp only [F.sub, F.w, ihf, ihg]
  | and f g ihf ihg => simp only [F.sub, F.w, ihf, ihg]
  | or f g ihf ihg => simp only [F.sub, F.w, ihf, ihg]
  | all Y f ih =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e]
    · rw [F.sub, ite_eq_right e]; simp only [F.w, ih]

theorem F.neutral_sub {X A : Nat} (f : F) (h : f.neutral) : (f.sub X A).neutral := by
  induction f with
  | atm a => trivial
  | var Y =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e]; trivial
    · rw [F.sub, ite_eq_right e]; trivial
  | imp f g ihf ihg => exact And.intro (ihf (And.left h)) (ihg (And.right h))
  | and f g ihf ihg => exact And.intro (ihf (And.left h)) (ihg (And.right h))
  | or f g _ _ => exact False.elim h
  | all Y f ih =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e]; exact h
    · rw [F.sub, ite_eq_right e]; exact ih h

theorem F.fr_sub {X A Z : Nat} (f : F) (h : (f.sub X A).fr Z) : f.fr Z ∧ Z ≠ X := by
  induction f with
  | atm a => exact False.elim h
  | var Y =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e] at h; exact False.elim h
    · rw [F.sub, ite_eq_right e] at h
      have hY : Y = Z := h
      subst hY
      exact ⟨rfl, e⟩
  | imp f g ihf ihg =>
    cases h with
    | inl h' => have := ihf h'; exact ⟨Or.inl this.1, this.2⟩
    | inr h' => have := ihg h'; exact ⟨Or.inr this.1, this.2⟩
  | and f g ihf ihg =>
    cases h with
    | inl h' => have := ihf h'; exact ⟨Or.inl this.1, this.2⟩
    | inr h' => have := ihg h'; exact ⟨Or.inr this.1, this.2⟩
  | or f g ihf ihg =>
    cases h with
    | inl h' => have := ihf h'; exact ⟨Or.inl this.1, this.2⟩
    | inr h' => have := ihg h'; exact ⟨Or.inr this.1, this.2⟩
  | all Y f ih =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e] at h
      have h' : Y ≠ Z ∧ f.fr Z := h
      exact ⟨h', fun hz => h'.1 (e.trans hz.symm)⟩
    · rw [F.sub, ite_eq_right e] at h
      have h' : Y ≠ Z ∧ (f.sub X A).fr Z := h
      have := ih h'.2
      exact ⟨And.intro h'.1 this.1, this.2⟩

-- ∀X f cerrada ⟹ f[A/X] cerrada
theorem F.closed_inst {X A : Nat} {f : F} (h : (F.all X f).closed) : (f.sub X A).closed := by
  intro Z hZ
  have h2 := F.fr_sub f hZ
  exact h Z (And.intro (fun e => h2.2 e.symm) h2.1)

theorem closed_imp {a b : F} (ha : a.closed) (hb : b.closed) : (F.imp a b).closed :=
  fun X h => Or.elim h (ha X) (hb X)

theorem closed_and {a b : F} (ha : a.closed) (hb : b.closed) : (F.and a b).closed :=
  fun X h => Or.elim h (ha X) (hb X)

/-! ## Lema 4.6: identidad -/

theorem identity_aux (s : Nat) : ∀ (K : F), K.w < s → K.neutral → K.closed →
    ∀ (P : List F), Elab P K → Der P K := by
  induction s with
  | zero => intro K hw; exact absurd hw (Nat.not_lt_zero _)
  | succ s ih =>
    intro K hw hn hc P he
    cases K with
    | atm A => exact Der.fact he
    | var X => exact False.elim (hc X rfl)
    | or f g => exact False.elim hn
    | and N₁ N₂ =>
      have hw' : N₁.w + N₂.w + 1 < s + 1 := hw
      exact Der.and
        (ih N₁ (by omega) (And.left hn) (fun X h => hc X (Or.inl h)) P (Elab.andL he))
        (ih N₂ (by omega) (And.right hn) (fun X h => hc X (Or.inr h)) P (Elab.andR he))
    | all X N =>
      have hw' : N.w + 1 < s + 1 := hw
      cases (show ∃ A, Fresh A P (.all X N) from ⟨_, fresh_exists _ _⟩) with
      | intro A hA =>
        exact Der.gen hA (ih (N.sub X A) (by rw [F.w_sub]; omega) (F.neutral_sub N hn)
          (F.closed_inst hc) P (Elab.inst A he))
    | imp N M =>
      have hnN : N.neutral := And.left hn
      have hnM : M.neutral := And.right hn
      have hcN : N.closed := fun X h => hc X (Or.inl h)
      have hcM : M.closed := fun X h => hc X (Or.inr h)
      have hw' : N.w + 2 * M.w + 1 < s + 1 := hw
      cases M with
      | atm A =>
        have hw'' : N.w + 2 * 1 + 1 < s + 1 := hw'
        apply Der.aug
        exact Der.back (Elab.mono (fun D hD => List.mem_cons.mpr (Or.inr hD)) he)
          (ih N (by omega) hnN hcN (N :: P) (Elab.mem mem0))
      | var Y => exact False.elim (hcM Y rfl)
      | or _ _ => exact False.elim hnM
      | and M₁ M₂ =>
        have hw'' : N.w + 2 * (M₁.w + M₂.w + 1) + 1 < s + 1 := hw'
        have hc₁ : M₁.closed := fun X h => hcM X (Or.inl h)
        have hc₂ : M₂.closed := fun X h => hcM X (Or.inr h)
        have d₁ := ih (.imp N M₁) (by show N.w + 2 * M₁.w + 1 < s; omega)
          (And.intro hnN (And.left hnM)) (closed_imp hcN hc₁) P (Elab.headL he)
        have d₂ := ih (.imp N M₂) (by show N.w + 2 * M₂.w + 1 < s; omega)
          (And.intro hnN (And.right hnM)) (closed_imp hcN hc₂) P (Elab.headR he)
        exact Der.aug (Der.and (Der.inv_imp d₁) (Der.inv_imp d₂))
      | imp M' M'' =>
        have hw'' : N.w + 2 * (M'.w + 2 * M''.w + 1) + 1 < s + 1 := hw'
        have hc' : M'.closed := fun X h => hcM X (Or.inl h)
        have hc'' : M''.closed := fun X h => hcM X (Or.inr h)
        have d := ih (.imp (.and N M') M'')
          (by show N.w + M'.w + 1 + 2 * M''.w + 1 < s; omega)
          (And.intro (And.intro hnN (And.left hnM)) (And.right hnM))
          (closed_imp (closed_and hcN hc') hc'') P (Elab.curry he)
        have d₁ : Der (N :: M' :: P) M'' := Der.monoRC RC.and_cons (Der.inv_imp d)
        have d₂ : Der (M' :: N :: P) M'' := Der.mono d₁ (fun D hD => by
          cases List.mem_cons.mp hD with
          | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
          | inr h =>
            cases List.mem_cons.mp h with
            | inl e => exact List.mem_cons.mpr (Or.inl e)
            | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
        exact Der.aug (Der.aug d₂)
      | all X M₀ =>
        have hw'' : N.w + 2 * (M₀.w + 1) + 1 < s + 1 := hw'
        cases (show ∃ A, Fresh A (N :: P) (.all X M₀) from ⟨_, fresh_exists _ _⟩) with
        | intro A hA =>
          have d := ih (.imp N (M₀.sub X A))
            (by show N.w + 2 * (M₀.sub X A).w + 1 < s; rw [F.w_sub]; omega)
            (And.intro hnN (F.neutral_sub M₀ hnM)) (closed_imp hcN (F.closed_inst hcM)) P
            (Elab.hinst A he)
          exact Der.aug (Der.gen hA (Der.inv_imp d))

-- K neutra cerrada, K ∈ [P] ⟹ P ⊢ K
theorem identity {K : F} (hn : K.neutral) (hc : K.closed) {P : List F} (he : Elab P K) :
    Der P K :=
  identity_aux (K.w + 1) K (Nat.lt_succ_self _) hn hc P he

/-! ## Lema 4.7: elaboración -/

theorem elab_lemma {K : F} (hn : K.neutral) (hc : K.closed) {P : List F} (hd : Der P K)
    {E : F} (he : Elab [K] E) : E.neutral ∧ E.closed ∧ E.w ≤ K.w ∧ Der P E := by
  induction he with
  | mem h =>
    cases List.mem_cons.mp h with
    | inl e => subst e; exact ⟨hn, hc, Nat.le_refl _, hd⟩
    | inr h' => cases h'
  | @andL D₁ D₂ _ ih =>
    have hw : D₁.w + D₂.w + 1 ≤ K.w := ih.2.2.1
    exact ⟨And.left ih.1, fun X h => ih.2.1 X (Or.inl h), by omega,
      (Der.inv_and ih.2.2.2).1⟩
  | @andR D₁ D₂ _ ih =>
    have hw : D₁.w + D₂.w + 1 ≤ K.w := ih.2.2.1
    exact ⟨And.right ih.1, fun X h => ih.2.1 X (Or.inr h), by omega,
      (Der.inv_and ih.2.2.2).2⟩
  | @headL G D₁ D₂ _ ih =>
    have hw : G.w + 2 * (D₁.w + D₂.w + 1) + 1 ≤ K.w := ih.2.2.1
    refine ⟨And.intro (And.left ih.1) (And.left (And.right ih.1)), ?_, ?_,
      Der.aug (Der.inv_and (Der.inv_imp ih.2.2.2)).1⟩
    · exact closed_imp (fun X h => ih.2.1 X (Or.inl h))
        (fun X h => ih.2.1 X (Or.inr (Or.inl h)))
    · show G.w + 2 * D₁.w + 1 ≤ K.w; omega
  | @headR G D₁ D₂ _ ih =>
    have hw : G.w + 2 * (D₁.w + D₂.w + 1) + 1 ≤ K.w := ih.2.2.1
    refine ⟨And.intro (And.left ih.1) (And.right (And.right ih.1)), ?_, ?_,
      Der.aug (Der.inv_and (Der.inv_imp ih.2.2.2)).2⟩
    · exact closed_imp (fun X h => ih.2.1 X (Or.inl h))
        (fun X h => ih.2.1 X (Or.inr (Or.inr h)))
    · show G.w + 2 * D₂.w + 1 ≤ K.w; omega
  | @curry G G' D _ ih =>
    have hw : G.w + 2 * (G'.w + 2 * D.w + 1) + 1 ≤ K.w := ih.2.2.1
    have hd' : Der (G' :: G :: P) D := Der.inv_imp (Der.inv_imp ih.2.2.2)
    have hRC : RC (G' :: G :: P) (.and G G' :: P) := RC.of_elab (fun E e => by
      cases Elab.split (L₁ := [G']) (L₂ := G :: P) e with
      | inl e' => exact Elab.trans e' (Elab.andR (Elab.mem mem0))
      | inr e' =>
        cases Elab.split (L₁ := [G]) (L₂ := P) e' with
        | inl e'' => exact Elab.trans e'' (Elab.andL (Elab.mem mem0))
        | inr e'' => exact Elab.mono (fun x hx => List.mem_cons.mpr (Or.inr hx)) e'')
    refine ⟨And.intro (And.intro (And.left ih.1) (And.left (And.right ih.1)))
      (And.right (And.right ih.1)), ?_, ?_, Der.aug (Der.monoRC hRC hd')⟩
    · exact closed_imp (closed_and (fun X h => ih.2.1 X (Or.inl h))
        (fun X h => ih.2.1 X (Or.inr (Or.inl h)))) (fun X h => ih.2.1 X (Or.inr (Or.inr h)))
    · show G.w + G'.w + 1 + 2 * D.w + 1 ≤ K.w; omega
  | @inst X D A _ ih =>
    have hw : D.w + 1 ≤ K.w := ih.2.2.1
    refine ⟨F.neutral_sub D ih.1, F.closed_inst ih.2.1, ?_, Der.inv_all ih.2.2.2 A⟩
    rw [F.w_sub]; omega
  | @hinst X G D A _ ih =>
    have hw : G.w + 2 * (D.w + 1) + 1 ≤ K.w := ih.2.2.1
    refine ⟨And.intro (And.left ih.1) (F.neutral_sub D (And.right ih.1)), ?_, ?_,
      Der.aug (Der.inv_all (Der.inv_imp ih.2.2.2) A)⟩
    · exact closed_imp (fun X h => ih.2.1 X (Or.inl h))
        (F.closed_inst (fun Z h => ih.2.1 Z (Or.inr h)))
    · show G.w + 2 * (D.sub X A).w + 1 ≤ K.w; rw [F.w_sub]; omega

/-! ## Lema 4.8: corte -/

theorem cut_aux (s : Nat) : ∀ (K : F), K.w < s → K.neutral → K.closed →
    ∀ (P : List F), Der P K → ∀ (n : Nat) (Q : List F) (G : F),
      Op n (K :: Q) G → Der (P ++ Q) G := by
  induction s with
  | zero => intro K hw; exact absurd hw (Nat.not_lt_zero _)
  | succ s ih =>
    intro K hw hn hc P hP n
    induction n with
    | zero => intro Q G h; cases h
    | succ k ihn =>
      intro Q G h
      have inL : ∀ D, D ∈ P → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inl h)
      have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
      cases h with
      | fact e =>
        cases Elab.split (L₁ := [K]) (L₂ := Q) e with
        | inl e' => exact Der.mono (elab_lemma hn hc hP e').2.2.2 inL
        | inr e' => exact Der.fact (Elab.mono inR e')
      | @back _ _ G' A e h' =>
        have dG' := ihn Q G' h'
        cases Elab.split (L₁ := [K]) (L₂ := Q) e with
        | inr e' => exact Der.back (Elab.mono inR e') dG'
        | inl e' =>
          have hl := elab_lemma hn hc hP e'
          have hw' : G'.w + 2 * 1 + 1 ≤ K.w := hl.2.2.1
          have hw'' : K.w < s + 1 := hw
          cases Der.inv_imp hl.2.2.2 with
          | intro m hm =>
            have d := ih G' (by omega) (And.left hl.1) (fun X h => hl.2.1 X (Or.inl h))
              (P ++ Q) dG' m P (.atm A) hm
            exact Der.mono d (fun D hD => by
              cases List.mem_append.mp hD with
              | inl h => exact h
              | inr h => exact inL D h)
      | and h₁ h₂ => exact Der.and (ihn Q _ h₁) (ihn Q _ h₂)
      | orL h' => exact Der.orL (ihn Q _ h')
      | orR h' => exact Der.orR (ihn Q _ h')
      | @aug _ _ D G' h' =>
        have h1 : Op k (K :: D :: Q) G' := Op.mono k h' (fun E hE => by
          cases List.mem_cons.mp hE with
          | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
          | inr h =>
            cases List.mem_cons.mp h with
            | inl e => exact List.mem_cons.mpr (Or.inl e)
            | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
        have d := ihn (D :: Q) G' h1
        exact Der.aug (Der.mono d (fun E hE => by
          cases List.mem_append.mp hE with
          | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
          | inr h =>
            cases List.mem_cons.mp h with
            | inl e => exact List.mem_cons.mpr (Or.inl e)
            | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))))
      | @gen _ _ X G' A hA h' =>
        cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
        | intro B hB =>
          have h'' := Op.ren h' (upd id A B)
          rw [map_ren_away (K :: Q) hA.1, sub_ren_away (G := G') hA.2] at h''
          exact Der.gen hB (ihn Q _ h'')

-- K neutra cerrada: P ⊢ K, K, Q ⊢ G ⟹ P, Q ⊢ G
theorem cut {K : F} (hn : K.neutral) (hc : K.closed) {P Q : List F} {G : F}
    (hP : Der P K) (h : Der (K :: Q) G) : Der (P ++ Q) G := by
  cases h with
  | intro n h => exact cut_aux (K.w + 1) K (Nat.lt_succ_self _) hn hc P hP n Q G h

/-! ## Sustitución en fórmulas cerradas -/

theorem F.sub_closed {X A : Nat} {f : F} (h : ¬ f.fr X) : f.sub X A = f := by
  induction f with
  | atm a => rfl
  | var Y =>
    have e : ¬ Y = X := h
    rw [F.sub, ite_eq_right e]
  | imp f g ihf ihg =>
    rw [F.sub, ihf (fun h' => h (Or.inl h')), ihg (fun h' => h (Or.inr h'))]
  | and f g ihf ihg =>
    rw [F.sub, ihf (fun h' => h (Or.inl h')), ihg (fun h' => h (Or.inr h'))]
  | or f g ihf ihg =>
    rw [F.sub, ihf (fun h' => h (Or.inl h')), ihg (fun h' => h (Or.inr h'))]
  | all Y f ih =>
    by_cases e : Y = X
    · rw [F.sub, ite_eq_left e]
    · rw [F.sub, ite_eq_right e, ih (fun h' => h (And.intro e h'))]

theorem F.sub_var (X A : Nat) : (F.var X).sub X A = .atm A := by
  simp [F.sub]

theorem closed_atm (a : Nat) : (F.atm a).closed := fun _ h => h

/-! ## IPL y soporte sobre programas (Fig. 2) -/

inductive Fm where
  | atom : Nat → Fm
  | bot  : Fm
  | and  : Fm → Fm → Fm
  | or   : Fm → Fm → Fm
  | imp  : Fm → Fm → Fm

-- C ⊒ B
abbrev Ext (B C : List F) : Prop := ∀ D, D ∈ B → D ∈ C

theorem Ext.refl (B : List F) : Ext B B := fun _ h => h

theorem Ext.trans {B C E : List F} (h₁ : Ext B C) (h₂ : Ext C E) : Ext B E :=
  fun D h => h₂ D (h₁ D h)

theorem Ext.cons (D : F) (B : List F) : Ext B (D :: B) :=
  fun _ h => List.mem_cons.mpr (Or.inr h)

def supp : List F → Fm → Prop
  | B, .atom a  => Der B (.atm a)
  | B, .bot     => ∀ a, Der B (.atm a)
  | B, .and φ ψ => supp B φ ∧ supp B ψ
  | B, .imp φ ψ => ∀ C, Ext B C → supp C φ → supp C ψ
  | B, .or φ ψ  => ∀ C, Ext B C → ∀ a : Nat,
      (∀ E, Ext C E → supp E φ → Der E (.atm a)) →
      (∀ E, Ext C E → supp E ψ → Der E (.atm a)) → Der C (.atm a)

/-! ## Codificación ⟦·⟧ (Def. 4.1) -/

-- (e₁ ⊃ X) ∩ (e₂ ⊃ X) ⊃ X
abbrev orB (e₁ e₂ : F) : F := .imp (.and (.imp e₁ (.var 0)) (.imp e₂ (.var 0))) (.var 0)

-- (e₁ ⊃ a) ∩ (e₂ ⊃ a)
abbrev dsj (e₁ e₂ : F) (a : Nat) : F := .and (.imp e₁ (.atm a)) (.imp e₂ (.atm a))

def enc : Fm → F
  | .atom a  => .atm a
  | .bot     => .all 0 (.var 0)
  | .and φ ψ => .and (enc φ) (enc ψ)
  | .or φ ψ  => .all 0 (orB (enc φ) (enc ψ))
  | .imp φ ψ => .imp (enc φ) (enc ψ)

-- Lema 4.4(ii)
theorem enc_neutral : ∀ (φ : Fm), (enc φ).neutral
  | .atom _ => trivial
  | .bot => trivial
  | .and φ ψ => And.intro (enc_neutral φ) (enc_neutral ψ)
  | .imp φ ψ => And.intro (enc_neutral φ) (enc_neutral ψ)
  | .or φ ψ => And.intro (And.intro (And.intro (enc_neutral φ) trivial)
      (And.intro (enc_neutral ψ) trivial)) trivial

theorem enc_closed : ∀ (φ : Fm), (enc φ).closed
  | .atom _ => fun _ h => h
  | .bot => fun _ h => And.left h (And.right h)
  | .and φ ψ => fun X h => Or.elim h (enc_closed φ X) (enc_closed ψ X)
  | .imp φ ψ => fun X h => Or.elim h (enc_closed φ X) (enc_closed ψ X)
  | .or φ ψ => fun X h =>
    have hX : 0 ≠ X := And.left h
    Or.elim (And.right h)
      (fun k => Or.elim k
        (fun k₁ => Or.elim k₁ (enc_closed φ X) hX)
        (fun k₂ => Or.elim k₂ (enc_closed ψ X) hX))
      hX

theorem orB_inst {e₁ e₂ : F} (h₁ : ¬ e₁.fr 0) (h₂ : ¬ e₂.fr 0) (A : Nat) :
    (orB e₁ e₂).sub 0 A = .imp (dsj e₁ e₂ A) (.atm A) := by
  show F.imp (.and (.imp (e₁.sub 0 A) ((F.var 0).sub 0 A))
      (.imp (e₂.sub 0 A) ((F.var 0).sub 0 A))) ((F.var 0).sub 0 A) = _
  rw [F.sub_closed h₁, F.sub_closed h₂, F.sub_var]

theorem dsj_neutral (φ ψ : Fm) (a : Nat) : (dsj (enc φ) (enc ψ) a).neutral :=
  And.intro (And.intro (enc_neutral φ) trivial) (And.intro (enc_neutral ψ) trivial)

theorem dsj_closed (φ ψ : Fm) (a : Nat) : (dsj (enc φ) (enc ψ) a).closed :=
  closed_and (closed_imp (enc_closed φ) (closed_atm a))
    (closed_imp (enc_closed ψ) (closed_atm a))

/-! ## Teorema 4.2: Support is Search -/

theorem sis : ∀ (φ : Fm) (B : List F), supp B φ ↔ Der B (enc φ)
  | .atom _, _ => Iff.rfl
  | .bot, B => by
    constructor
    · intro h
      refine Der.gen (X := 0) (G := .var 0) (fresh_exists B (enc .bot)) ?_
      rw [F.sub_var]
      exact h _
    · intro h a
      have h' := Der.inv_all (X := 0) (G := .var 0) h a
      rw [F.sub_var] at h'
      exact h'
  | .and φ ψ, B => by
    constructor
    · intro h
      exact Der.and ((sis φ B).mp (And.left h)) ((sis ψ B).mp (And.right h))
    · intro h
      exact And.intro ((sis φ B).mpr (Der.inv_and h).1) ((sis ψ B).mpr (Der.inv_and h).2)
  | .imp φ ψ, B => by
    constructor
    · intro h
      have d : Der (enc φ :: B) (enc φ) :=
        identity (enc_neutral φ) (enc_closed φ) (Elab.mem mem0)
      exact Der.aug ((sis ψ (enc φ :: B)).mp
        (h (enc φ :: B) (Ext.cons _ B) ((sis φ (enc φ :: B)).mpr d)))
    · intro h C hBC hφ
      have d := cut (enc_neutral φ) (enc_closed φ) ((sis φ C).mp hφ) (Der.inv_imp h)
      exact (sis ψ C).mpr (Der.mono d (fun D hD => (List.mem_append.mp hD).elim id (hBC D)))
  | .or φ ψ, B => by
    constructor
    · intro h
      refine Der.gen (X := 0) (G := orB (enc φ) (enc ψ)) (fresh_exists B (enc (.or φ ψ))) ?_
      rw [orB_inst (enc_closed φ 0) (enc_closed ψ 0)]
      apply Der.aug
      refine h _ (Ext.cons _ B) _ ?_ ?_
      · intro E hE hφ
        exact Der.back (Elab.andL (Elab.mem (hE _ mem0))) ((sis φ E).mp hφ)
      · intro E hE hψ
        exact Der.back (Elab.andR (Elab.mem (hE _ mem0))) ((sis ψ E).mp hψ)
    · intro h C hBC a k₁ k₂
      have h' := Der.inv_all (X := 0) (G := orB (enc φ) (enc ψ)) (Der.mono h hBC) a
      rw [orB_inst (enc_closed φ 0) (enc_closed ψ 0)] at h'
      have d := Der.inv_imp h'
      have d₁ : Der C (.imp (enc φ) (.atm a)) :=
        Der.aug (k₁ (enc φ :: C) (Ext.cons _ C) ((sis φ (enc φ :: C)).mpr
          (identity (enc_neutral φ) (enc_closed φ) (Elab.mem mem0))))
      have d₂ : Der C (.imp (enc ψ) (.atm a)) :=
        Der.aug (k₂ (enc ψ :: C) (Ext.cons _ C) ((sis ψ (enc ψ :: C)).mpr
          (identity (enc_neutral ψ) (enc_closed ψ) (Elab.mem mem0))))
      have d' := cut (dsj_neutral φ ψ a) (dsj_closed φ ψ a) (Der.and d₁ d₂) d
      exact Der.mono d' (fun _ hD => (List.mem_append.mp hD).elim id id)

-- monotonía de ⊩, vía 4.2
theorem supp_mono {B C : List F} (φ : Fm) (hBC : Ext B C) (h : supp B φ) : supp C φ :=
  (sis φ C).mpr (Der.mono ((sis φ B).mp h) hBC)

/-! ## Coste κ: altura mínima de búsqueda -/

-- κ_B(φ) ≤ n
abbrev Cost (B : List F) (φ : Fm) (n : Nat) : Prop := Op n B (enc φ)

theorem supp_iff_cost (B : List F) (φ : Fm) : supp B φ ↔ ∃ n, Cost B φ n := sis φ B

-- umbral: cerrado hacia arriba
theorem Cost.up {B : List F} {φ : Fm} {n m : Nat} (h : Cost B φ n) (hm : n ≤ m) :
    Cost B φ m :=
  Op.lift h hm

-- antitonía: extender la base no encarece
theorem Cost.anti {B C : List F} {φ : Fm} {n : Nat} (hBC : Ext B C) (h : Cost B φ n) :
    Cost C φ n :=
  Op.mono n h hBC

/-! ## κ invariante bajo renombramiento de átomos -/

def Fm.ren (σ : Nat → Nat) : Fm → Fm
  | .atom a  => .atom (σ a)
  | .bot     => .bot
  | .and φ ψ => .and (φ.ren σ) (ψ.ren σ)
  | .or φ ψ  => .or (φ.ren σ) (ψ.ren σ)
  | .imp φ ψ => .imp (φ.ren σ) (ψ.ren σ)

theorem enc_ren (σ : Nat → Nat) : ∀ (φ : Fm), (enc φ).ren σ = enc (φ.ren σ)
  | .atom _ => rfl
  | .bot => rfl
  | .and φ ψ => by simp only [enc, Fm.ren, F.ren, enc_ren σ φ, enc_ren σ ψ]
  | .or φ ψ => by simp only [enc, Fm.ren, F.ren, orB, enc_ren σ φ, enc_ren σ ψ]
  | .imp φ ψ => by simp only [enc, Fm.ren, F.ren, enc_ren σ φ, enc_ren σ ψ]

theorem Cost.ren (σ : Nat → Nat) {B : List F} {φ : Fm} {n : Nat} (h : Cost B φ n) :
    Cost (B.map (F.ren σ)) (φ.ren σ) n := by
  have h' := Op.ren h σ
  rw [enc_ren] at h'
  exact h'

/-! ## Cláusulas derivables: no cambian el soporte -/

theorem derived_conservative {K : F} (hn : K.neutral) (hc : K.closed) {B : List F}
    (hK : Der B K) (φ : Fm) : supp (K :: B) φ ↔ supp B φ := by
  constructor
  · intro h
    have d := cut hn hc hK ((sis φ _).mp h)
    exact (sis φ B).mpr (Der.mono d (fun _ hD => (List.mem_append.mp hD).elim id id))
  · intro h
    exact supp_mono φ (Ext.cons K B) h

/-! ## Atajo: κ no es invariante bajo equivalencia de soporte -/

-- a₀, a₀ ⊃ a₁, …, a_{k-1} ⊃ a_k
def chain : Nat → List F
  | 0     => [.atm 0]
  | k + 1 => .imp (.atm k) (.atm (k + 1)) :: chain k

theorem mem_chain {k : Nat} {D : F} (h : D ∈ chain k) :
    D = .atm 0 ∨ ∃ i, i < k ∧ D = .imp (.atm i) (.atm (i + 1)) := by
  induction k with
  | zero =>
    cases List.mem_cons.mp h with
    | inl e => exact Or.inl e
    | inr h' => cases h'
  | succ k ih =>
    cases List.mem_cons.mp h with
    | inl e => exact Or.inr ⟨k, Nat.lt_succ_self k, e⟩
    | inr h' =>
      cases ih h' with
      | inl e => exact Or.inl e
      | inr h'' =>
        cases h'' with
        | intro i hi => exact Or.inr ⟨i, Nat.lt_succ_of_lt hi.1, hi.2⟩

theorem chain_not {k : Nat} {D : F} (h : D ∈ chain k) (h₀ : D ≠ .atm 0)
    (h₁ : ∀ i, D ≠ .imp (.atm i) (.atm (i + 1))) : False := by
  cases mem_chain h with
  | inl e => exact h₀ e
  | inr e =>
    cases e with
    | intro i hi => exact h₁ i hi.2

-- [chain k] = chain k
theorem Elab.of_chain {k : Nat} {E : F} (h : Elab (chain k) E) : E ∈ chain k := by
  induction h with
  | mem h => exact h
  | andL _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))
  | andR _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))
  | headL _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))
  | headR _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))
  | curry _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))
  | inst A _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))
  | hinst A _ ih => exact False.elim (chain_not ih (by intro e; cases e) (by intro i e; cases e))

theorem chain_mem_zero (k : Nat) : F.atm 0 ∈ chain k := by
  induction k with
  | zero => exact mem0
  | succ k ih => exact List.mem_cons.mpr (Or.inr ih)

theorem chain_mem_imp {k i : Nat} (h : i < k) : F.imp (.atm i) (.atm (i + 1)) ∈ chain k := by
  induction k with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases e : i = k
    · subst e; exact mem0
    · exact List.mem_cons.mpr (Or.inr (ih (by omega)))

-- cota inferior: a_j cuesta al menos j + 1
theorem chain_lower (k : Nat) : ∀ (n j : Nat), Op n (chain k) (.atm j) → j < n := by
  intro n
  induction n with
  | zero => intro j h; cases h
  | succ n ih =>
    intro j h
    cases h with
    | fact e =>
      cases mem_chain (Elab.of_chain e) with
      | inl e' => cases e'; omega
      | inr e' =>
        cases e' with
        | intro i hi =>
          cases hi with
          | intro _ e'' => cases e''
    | back e h' =>
      cases mem_chain (Elab.of_chain e) with
      | inl e' => cases e'
      | inr e' =>
        cases e' with
        | intro i hi =>
          cases hi with
          | intro _ e'' =>
            cases e''
            have := ih i h'
            omega

-- cota superior: a_j cuesta a lo sumo j + 1
theorem chain_upper {k : Nat} : ∀ j, j ≤ k → Op (j + 1) (chain k) (.atm j) := by
  intro j
  induction j with
  | zero => intro _; exact Op.fact (Elab.mem (chain_mem_zero k))
  | succ j ih =>
    intro hj
    exact Op.back (Elab.mem (chain_mem_imp (by omega))) (ih (by omega))

-- κ_{chain k}(a_k) = k + 1
theorem chain_cost (k : Nat) :
    Cost (chain k) (.atom k) (k + 1) ∧ ¬ Cost (chain k) (.atom k) k :=
  And.intro (chain_upper (k := k) k (Nat.le_refl k))
    (fun h => Nat.lt_irrefl k (chain_lower k k k h))

-- con a_k en caché: coste 1
theorem chain_shortcut (k : Nat) : Cost (.atm k :: chain k) (.atom k) 1 :=
  Op.fact (Elab.mem mem0)

-- mismo soporte, costes k + 1 y 1
theorem shortcut (k : Nat) :
    (∀ φ, supp (.atm k :: chain k) φ ↔ supp (chain k) φ) ∧
    Cost (chain k) (.atom k) (k + 1) ∧ ¬ Cost (chain k) (.atom k) k ∧
    Cost (.atm k :: chain k) (.atom k) 1 :=
  ⟨derived_conservative (K := .atm k) (B := chain k) trivial (closed_atm k)
      ⟨_, chain_upper (k := k) k (Nat.le_refl k)⟩,
   (chain_cost k).1, (chain_cost k).2, chain_shortcut k⟩

/-! ## Corte atómico con altura; cota del atajo -/

theorem Elab.atm_only {a : Nat} {E : F} (h : Elab [F.atm a] E) : E = .atm a := by
  induction h with
  | mem h =>
    cases List.mem_cons.mp h with
    | inl e => exact e
    | inr h' => cases h'
  | andL _ ih => cases ih
  | andR _ ih => cases ih
  | headL _ ih => cases ih
  | headR _ ih => cases ih
  | curry _ ih => cases ih
  | inst A _ ih => cases ih
  | hinst A _ ih => cases ih

-- P ⊢ₘ a, a, Q ⊢ₙ G ⟹ P, Q ⊢ₘ₊ₙ G
theorem cut_atom {a m : Nat} {P : List F} (hP : Op m P (.atm a)) :
    ∀ (n : Nat) (Q : List F) (G : F), Op n (.atm a :: Q) G → Op (m + n) (P ++ Q) G := by
  intro n
  induction n with
  | zero => intro Q G h; cases h
  | succ k ihn =>
    intro Q G h
    have inL : ∀ D, D ∈ P → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inl h)
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    show Op (m + k + 1) (P ++ Q) G
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [.atm a]) (L₂ := Q) e with
      | inl e' =>
        cases Elab.atm_only e'
        exact Op.mono _ (Op.lift hP (by omega)) inL
      | inr e' => exact Op.fact (Elab.mono inR e')
    | back e h' =>
      cases Elab.split (L₁ := [.atm a]) (L₂ := Q) e with
      | inl e' => cases Elab.atm_only e'
      | inr e' => exact Op.back (Elab.mono inR e') (ihn Q _ h')
    | and h₁ h₂ => exact Op.and (ihn Q _ h₁) (ihn Q _ h₂)
    | orL h' => exact Op.orL (ihn Q _ h')
    | orR h' => exact Op.orR (ihn Q _ h')
    | @aug _ _ D G' h' =>
      have h1 : Op k (.atm a :: D :: Q) G' := Op.mono k h' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
      have d := ihn (D :: Q) G' h1
      exact Op.aug (Op.mono _ d (fun E hE => by
        cases List.mem_append.mp hE with
        | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))))
    | @gen _ _ X G' A hA h' =>
      cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have h'' := Op.ren h' (upd id A B)
        rw [map_ren_away (.atm a :: Q) hA.1, sub_ren_away (G := G') hA.2] at h''
        exact Op.gen hB (ihn Q _ h'')

-- κ_B(φ) ≤ κ_B(a) + κ_{a,B}(φ): el atajo no ahorra más que el coste del lema
theorem cost_cache {B : List F} {a : Nat} {φ : Fm} {m n : Nat}
    (ha : Cost B (.atom a) m) (h : Cost (.atm a :: B) φ n) : Cost B φ (m + n) :=
  Op.mono _ (cut_atom ha n B (enc φ) h) (fun _ hD => (List.mem_append.mp hD).elim id id)

/-! ## Programas planos: [P] = P -/

theorem Op.pos {n : Nat} {P : List F} {G : F} (h : Op n P G) : 0 < n := by
  cases h <;> omega

-- cabeza atómica, sin ∩ ni ∀
abbrev Flat (D : F) : Prop := (∃ a, D = .atm a) ∨ (∃ G a, D = .imp G (.atm a))

theorem Elab.flat {P : List F} (hP : ∀ D, D ∈ P → Flat D) {E : F} (h : Elab P E) :
    E ∈ P := by
  induction h with
  | mem h => exact h
  | andL _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)
  | andR _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)
  | headL _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)
  | headR _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)
  | curry _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)
  | inst A _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)
  | hinst A _ ih =>
    exact Or.elim (hP _ ih) (fun ⟨_, e⟩ => by cases e) (fun ⟨_, _, e⟩ => by cases e)

theorem Elab.rule_only {a b : Nat} {E : F} (h : Elab [F.imp (.atm b) (.atm a)] E) :
    E = .imp (.atm b) (.atm a) := by
  have hm := Elab.flat (fun D hD => by
    cases List.mem_cons.mp hD with
    | inl e => exact Or.inr ⟨_, _, e⟩
    | inr h' => cases h') h
  cases List.mem_cons.mp hm with
  | inl e => exact e
  | inr h' => cases h'

/-! ## Regla en caché: cota multiplicativa -/

-- P, b ⊢ₘ a, (b ⊃ a), Q ⊢ₙ G ⟹ P, Q ⊢_{m·n} G
theorem cut_rule {a b m : Nat} {P : List F} (hP : Op m (.atm b :: P) (.atm a)) :
    ∀ (n : Nat) (Q : List F) (G : F), Op n (.imp (.atm b) (.atm a) :: Q) G →
      Op (m * n) (P ++ Q) G := by
  have hm : 1 ≤ m := Op.pos hP
  intro n
  induction n with
  | zero => intro Q G h; cases h
  | succ k ihn =>
    intro Q G h
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    have up : ∀ {G' : F}, Op (m * k + 1) (P ++ Q) G' → Op (m * k + m) (P ++ Q) G' :=
      fun h' => Op.lift h' (Nat.add_le_add_left hm (m * k))
    show Op (m * k + m) (P ++ Q) G
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [.imp (.atm b) (.atm a)]) (L₂ := Q) e with
      | inl e' => cases Elab.rule_only e'
      | inr e' => exact up (Op.fact (Elab.mono inR e'))
    | back e h' =>
      cases Elab.split (L₁ := [.imp (.atm b) (.atm a)]) (L₂ := Q) e with
      | inr e' => exact up (Op.back (Elab.mono inR e') (ihn Q _ h'))
      | inl e' =>
        cases Elab.rule_only e'
        have d := cut_atom (ihn Q _ h') m P _ hP
        exact Op.mono _ d (fun D hD => by
          cases List.mem_append.mp hD with
          | inl h => exact h
          | inr h => exact List.mem_append.mpr (Or.inl h))
    | and h₁ h₂ => exact up (Op.and (ihn Q _ h₁) (ihn Q _ h₂))
    | orL h' => exact up (Op.orL (ihn Q _ h'))
    | orR h' => exact up (Op.orR (ihn Q _ h'))
    | @aug _ _ D G' h' =>
      have h1 : Op k (.imp (.atm b) (.atm a) :: D :: Q) G' := Op.mono k h' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
      have d := ihn (D :: Q) G' h1
      exact up (Op.aug (Op.mono _ d (fun E hE => by
        cases List.mem_append.mp hE with
        | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))))
    | @gen _ _ X G' A hA h' =>
      cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have h'' := Op.ren h' (upd id A B)
        rw [map_ren_away (.imp (.atm b) (.atm a) :: Q) hA.1, sub_ren_away (G := G') hA.2] at h''
        exact up (Op.gen hB (ihn Q _ h''))

-- κ_B(φ) ≤ κ_B(b ⊃ a) · κ_{b⊃a, B}(φ)
theorem cost_rule {B : List F} {a b : Nat} {φ : Fm} {m n : Nat}
    (hK : Cost B (.imp (.atom b) (.atom a)) m)
    (h : Cost (.imp (.atm b) (.atm a) :: B) φ n) : Cost B φ (m * n) :=
  Op.mono _ (cut_rule (Op.inv_imp hK) n B (enc φ) h)
    (fun _ hD => (List.mem_append.mp hD).elim id id)

/-! ## Amplificación: la cota multiplicativa se alcanza
  c_j = 3j, e_j = 3j+1, d_i = 3i+2; a = d_{m+1}; regla K = d₀ ⊃ a.
  Ronda j: c_j ← (e_j ⊃ a); a ← … ← d₀ (m+1 pasos, o 1 con K); d₀ ← e_j ∩ c_{j-1}. -/

-- d_i ⊃ d_{i+1}
def dch : Nat → List F
  | 0     => []
  | i + 1 => .imp (.atm (3 * i + 2)) (.atm (3 * (i + 1) + 2)) :: dch i

-- (e_j ⊃ a) ⊃ c_j;  e_j ∩ c_{j-1} ⊃ d₀
def rds (m : Nat) : Nat → List F
  | 0     => []
  | j + 1 => .imp (.imp (.atm (3 * (j + 1) + 1)) (.atm (3 * (m + 1) + 2))) (.atm (3 * (j + 1))) ::
      .imp (.and (.atm (3 * (j + 1) + 1)) (.atm (3 * j))) (.atm 2) :: rds m j

def amp (m t : Nat) : List F := .atm 0 :: (dch (m + 1) ++ rds m t)

abbrev ruleK (m : Nat) : F := .imp (.atm 2) (.atm (3 * (m + 1) + 2))

theorem mem_dch {k : Nat} {D : F} (h : D ∈ dch k) :
    ∃ i, i < k ∧ D = .imp (.atm (3 * i + 2)) (.atm (3 * (i + 1) + 2)) := by
  induction k with
  | zero => simp [dch] at h
  | succ k ih =>
    cases List.mem_cons.mp h with
    | inl e => exact ⟨k, Nat.lt_succ_self k, e⟩
    | inr h' =>
      cases ih h' with
      | intro i hi => exact ⟨i, Nat.lt_succ_of_lt hi.1, hi.2⟩

theorem mem_rds {m k : Nat} {D : F} (h : D ∈ rds m k) :
    ∃ j, j < k ∧
      (D = .imp (.imp (.atm (3 * (j + 1) + 1)) (.atm (3 * (m + 1) + 2))) (.atm (3 * (j + 1))) ∨
       D = .imp (.and (.atm (3 * (j + 1) + 1)) (.atm (3 * j))) (.atm 2)) := by
  induction k with
  | zero => simp [rds] at h
  | succ k ih =>
    cases List.mem_cons.mp h with
    | inl e => exact ⟨k, Nat.lt_succ_self k, Or.inl e⟩
    | inr h' =>
      cases List.mem_cons.mp h' with
      | inl e => exact ⟨k, Nat.lt_succ_self k, Or.inr e⟩
      | inr h'' =>
        cases ih h'' with
        | intro j hj => exact ⟨j, Nat.lt_succ_of_lt hj.1, hj.2⟩

theorem mem_amp {m t : Nat} {D : F} (h : D ∈ amp m t) :
    D = .atm 0 ∨ D ∈ dch (m + 1) ∨ D ∈ rds m t := by
  cases List.mem_cons.mp h with
  | inl e => exact Or.inl e
  | inr h' => exact Or.inr (List.mem_append.mp h')

theorem dch_mem {k i : Nat} (h : i < k) :
    F.imp (.atm (3 * i + 2)) (.atm (3 * (i + 1) + 2)) ∈ dch k := by
  induction k with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases e : i = k
    · subst e; exact mem0
    · exact List.mem_cons.mpr (Or.inr (ih (by omega)))

theorem rds_memC {m t j : Nat} (h : j < t) :
    F.imp (.imp (.atm (3 * (j + 1) + 1)) (.atm (3 * (m + 1) + 2))) (.atm (3 * (j + 1)))
      ∈ rds m t := by
  induction t with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ t ih =>
    by_cases e : j = t
    · subst e; exact mem0
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih (by omega)))))

theorem rds_memB {m t j : Nat} (h : j < t) :
    F.imp (.and (.atm (3 * (j + 1) + 1)) (.atm (3 * j))) (.atm 2) ∈ rds m t := by
  induction t with
  | zero => exact absurd h (Nat.not_lt_zero _)
  | succ t ih =>
    by_cases e : j = t
    · subst e; exact List.mem_cons.mpr (Or.inr mem0)
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih (by omega)))))

-- alcanzable: base más hechos e_i con i ≥ s
abbrev Inv (m t s : Nat) (P : List F) : Prop :=
  ∀ D, D ∈ P → D ∈ amp m t ∨ ∃ i, s ≤ i ∧ D = .atm (3 * i + 1)

theorem Inv.flat {m t s : Nat} {P : List F} (hP : Inv m t s P) : ∀ D, D ∈ P → Flat D := by
  intro D hD
  cases hP D hD with
  | inr h =>
    cases h with
    | intro i hi => exact Or.inl ⟨_, hi.2⟩
  | inl h =>
    cases mem_amp h with
    | inl e => exact Or.inl ⟨_, e⟩
    | inr h' =>
      cases h' with
      | inl h'' =>
        cases mem_dch h'' with
        | intro i hi => exact Or.inr ⟨_, _, hi.2⟩
      | inr h'' =>
        cases mem_rds h'' with
        | intro j hj =>
          cases hj.2 with
          | inl e => exact Or.inr ⟨_, _, e⟩
          | inr e => exact Or.inr ⟨_, _, e⟩

theorem Inv.cons {m t s i : Nat} {P : List F} (hP : Inv m t s P) (hi : s ≤ i) :
    Inv m t s (.atm (3 * i + 1) :: P) := by
  intro D hD
  cases List.mem_cons.mp hD with
  | inl e => exact Or.inr ⟨i, hi, e⟩
  | inr h => exact hP D h

theorem Inv.mono {m t s s' : Nat} {P : List F} (hP : Inv m t s P) (hs : s' ≤ s) :
    Inv m t s' P := by
  intro D hD
  cases hP D hD with
  | inl h => exact Or.inl h
  | inr h =>
    cases h with
    | intro i hi => exact Or.inr ⟨i, Nat.le_trans hs hi.1, hi.2⟩

-- hechos alcanzables: c₀ y los e_i presentes
theorem amp_fact {m t s x : Nat} {P : List F} (hP : Inv m t s P) (e : Elab P (.atm x)) :
    x = 0 ∨ ∃ i, s ≤ i ∧ x = 3 * i + 1 := by
  have hx := Elab.flat (Inv.flat hP) e
  cases hP _ hx with
  | inr h =>
    cases h with
    | intro i hi => exact Or.inr ⟨i, hi.1, F.atm.inj hi.2⟩
  | inl h =>
    cases mem_amp h with
    | inl e' => exact Or.inl (F.atm.inj e')
    | inr h' =>
      cases h' with
      | inl h'' =>
        cases mem_dch h'' with
        | intro i hi => cases hi.2
      | inr h'' =>
        cases mem_rds h'' with
        | intro j hj =>
          cases hj.2 with
          | inl e' => cases e'
          | inr e' => cases e'

-- reglas alcanzables, por cabeza
theorem amp_rule {m t s x : Nat} {G : F} {P : List F} (hP : Inv m t s P)
    (e : Elab P (.imp G (.atm x))) :
    (∃ j, x = 3 * (j + 1) ∧ G = .imp (.atm (3 * (j + 1) + 1)) (.atm (3 * (m + 1) + 2))) ∨
    (∃ j, x = 2 ∧ G = .and (.atm (3 * (j + 1) + 1)) (.atm (3 * j))) ∨
    (∃ i, x = 3 * (i + 1) + 2 ∧ G = .atm (3 * i + 2)) := by
  have hx := Elab.flat (Inv.flat hP) e
  cases hP _ hx with
  | inr h =>
    cases h with
    | intro i hi => cases hi.2
  | inl h =>
    cases mem_amp h with
    | inl e' => cases e'
    | inr h' =>
      cases h' with
      | inl h'' =>
        cases mem_dch h'' with
        | intro i hi =>
          have hh := F.imp.inj hi.2
          exact Or.inr (Or.inr ⟨i, F.atm.inj hh.2, hh.1⟩)
      | inr h'' =>
        cases mem_rds h'' with
        | intro j hj =>
          cases hj.2 with
          | inl e' =>
            have hh := F.imp.inj e'
            exact Or.inl ⟨j, F.atm.inj hh.2, hh.1⟩
          | inr e' =>
            have hh := F.imp.inj e'
            exact Or.inr (Or.inl ⟨j, F.atm.inj hh.2, hh.1⟩)

-- e_k solo como hecho: k ≥ s
theorem amp_e {m t s n k : Nat} {P : List F} (hP : Inv m t s P)
    (h : Op n P (.atm (3 * k + 1))) : s ≤ k := by
  cases h with
  | fact e =>
    cases amp_fact hP e with
    | inl hx => omega
    | inr hx =>
      cases hx with
      | intro i hi =>
        have h2 := hi.2
        have h1 := hi.1
        omega
  | back e _ =>
    cases amp_rule hP e with
    | inl hx =>
      cases hx with
      | intro _ hj => exact absurd hj.1 (by omega)
    | inr hx =>
      cases hx with
      | inl hx' =>
        cases hx' with
        | intro _ hj => exact absurd hj.1 (by omega)
      | inr hx' =>
        cases hx' with
        | intro _ hi => exact absurd hi.1 (by omega)

-- R·x
def lb (R : Nat) : Nat → Nat
  | 0     => 0
  | x + 1 => lb R x + R

-- cotas inferiores (inducción fuerte en la altura; potencial p)
theorem amp_lower (m t : Nat) : ∀ N n, n ≤ N → ∀ (P : List F) (s p : Nat), Inv m t s P →
    (∀ j, p ≤ j → p ≤ s → Op n P (.atm (3 * j)) → lb (m + 5) p < n) ∧
    (∀ i, p + 1 ≤ s → Op n P (.atm (3 * i + 2)) → lb (m + 5) p + 3 + i ≤ n) := by
  intro N
  induction N with
  | zero =>
    intro n hn P s p _
    constructor
    · intro j _ _ h
      have := Op.pos h
      omega
    · intro i _ h
      have := Op.pos h
      omega
  | succ N ih =>
    intro n hn P s p hP
    constructor
    · -- c_j
      intro j hpj hps h
      cases p with
      | zero => exact Op.pos h
      | succ p =>
        cases h with
        | fact e =>
          cases amp_fact hP e with
          | inl hx => omega
          | inr hx =>
            cases hx with
            | intro i hi =>
              have h2 := hi.2
              omega
        | @back n' _ G _ e h' =>
          cases amp_rule hP e with
          | inl hx =>
            cases hx with
            | intro j' hj =>
              have hx' := hj.1
              have hG := hj.2
              subst hG
              cases h' with
              | @aug n'' _ _ _ h'' =>
                have hP' : Inv m t (p + 1) (.atm (3 * (j' + 1) + 1) :: P) :=
                  Inv.cons (Inv.mono hP hps) (by omega)
                have := (ih n'' (by omega) _ (p + 1) p hP').2 (m + 1) (Nat.le_refl _) h''
                show lb (m + 5) p + (m + 5) < n'' + 1 + 1
                omega
          | inr hx =>
            cases hx with
            | inl hx' =>
              cases hx' with
              | intro _ hj => exact absurd hj.1 (by omega)
            | inr hx' =>
              cases hx' with
              | intro _ hi => exact absurd hi.1 (by omega)
    · -- d_i
      intro i hps h
      cases h with
      | fact e =>
        cases amp_fact hP e with
        | inl hx => omega
        | inr hx =>
          cases hx with
          | intro i' hi =>
            have h2 := hi.2
            omega
      | @back n' _ G _ e h' =>
        cases amp_rule hP e with
        | inl hx =>
          cases hx with
          | intro _ hj => exact absurd hj.1 (by omega)
        | inr hx =>
          cases hx with
          | inl hx' =>
            cases hx' with
            | intro j hj =>
              have hx'' := hj.1
              have hG := hj.2
              subst hG
              cases h' with
              | @and n'' _ _ _ h₁ h₂ =>
                have hs := amp_e hP h₁
                have := (ih n'' (by omega) P s p hP).1 j (by omega) (by omega) h₂
                omega
          | inr hx' =>
            cases hx' with
            | intro i' hi =>
              have hx'' := hi.1
              have hG := hi.2
              subst hG
              have := (ih n' (by omega) P s p hP).2 i' hps h'
              omega

-- con K: c_j cuesta ≤ 5j + 1
theorem amp_upperK (m t : Nat) : ∀ j, j ≤ t → ∀ (P : List F),
    (∀ D, D ∈ ruleK m :: amp m t → D ∈ P) → Op (5 * j + 1) P (.atm (3 * j)) := by
  intro j
  induction j with
  | zero =>
    intro _ P hP
    exact Op.fact (Elab.mem (hP _ (List.mem_cons.mpr (Or.inr mem0))))
  | succ j ih =>
    intro hj P hP
    have inA : ∀ D, D ∈ rds m t → D ∈ P := fun D hD =>
      hP D (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_append.mpr (Or.inr hD))))))
    have hC := inA _ (rds_memC (m := m) (by omega : j < t))
    have hB := inA _ (rds_memB (m := m) (by omega : j < t))
    have hK : ruleK m ∈ P := hP _ mem0
    have hP' : ∀ D, D ∈ ruleK m :: amp m t → D ∈ F.atm (3 * (j + 1) + 1) :: P :=
      fun D hD => List.mem_cons.mpr (Or.inr (hP D hD))
    have d := ih (by omega) _ hP'
    have d1 : Op (5 * j + 1) (F.atm (3 * (j + 1) + 1) :: P) (.atm (3 * (j + 1) + 1)) :=
      Op.fact (Elab.mem mem0)
    have d2 := Op.and d1 d
    have d3 := Op.back (Elab.mem (List.mem_cons.mpr (Or.inr hB))) d2
    have d4 := Op.back (Elab.mem (List.mem_cons.mpr (Or.inr hK))) d3
    have d5 := Op.aug d4
    have d6 := Op.back (Elab.mem hC) d5
    exact Op.lift d6 (by omega)

-- d₀ ⊢ d_i en i + 1 pasos
theorem amp_chain (m t : Nat) : ∀ i, i ≤ m + 1 →
    Op (i + 1) (.atm 2 :: amp m t) (.atm (3 * i + 2)) := by
  intro i
  induction i with
  | zero => intro _; exact Op.fact (Elab.mem mem0)
  | succ i ih =>
    intro hi
    have hm : F.imp (.atm (3 * i + 2)) (.atm (3 * (i + 1) + 2)) ∈ .atm 2 :: amp m t :=
      List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_append.mpr (Or.inl (dch_mem (by omega)))))))
    exact Op.back (Elab.mem hm) (ih (by omega))

-- κ_amp(K) ≤ m + 3
theorem amp_K (m t : Nat) : Op (m + 3) (amp m t) (ruleK m) :=
  Op.lift (Op.aug (amp_chain m t (m + 1) (Nat.le_refl _))) (by omega)

-- Amplificación: mismo soporte; κ(K) ≤ m + 3; con K, c_t ≤ 5t + 1; sin K, c_t > (m + 5)t
theorem amplification (m t : Nat) :
    (∀ φ, supp (ruleK m :: amp m t) φ ↔ supp (amp m t) φ) ∧
    Op (m + 3) (amp m t) (ruleK m) ∧
    Cost (ruleK m :: amp m t) (.atom (3 * t)) (5 * t + 1) ∧
    ¬ Cost (amp m t) (.atom (3 * t)) (lb (m + 5) t) := by
  refine ⟨derived_conservative (K := ruleK m) (B := amp m t) (And.intro trivial trivial)
      (closed_imp (closed_atm _) (closed_atm _)) ⟨_, amp_K m t⟩, amp_K m t,
    amp_upperK m t t (Nat.le_refl _) _ (fun _ h => h), ?_⟩
  intro h
  have hP : Inv m t (t + 1) (amp m t) := fun D hD => Or.inl hD
  have := (amp_lower m t (lb (m + 5) t) (lb (m + 5) t) (Nat.le_refl _) (amp m t) (t + 1) t
    hP).1 t (Nat.le_refl _) (by omega) h
  exact Nat.lt_irrefl _ this

/-! ## Retractación
  Quitar un hecho derivable: κ sube a lo sumo su coste (`cost_cache`).
  Quitar una regla derivable: a lo sumo multiplicativo (`cost_rule`), y se alcanza.
  Quitar una cláusula no derivable: salto a ∞. -/

theorem Elab.nil {E : F} (h : Elab [] E) : False := by
  have hm := Elab.flat (fun D hD => by cases hD) h
  cases hm

theorem retract_jump : Cost [.atm 0] (.atom 0) 1 ∧ ¬ supp [] (.atom 0) :=
  And.intro (Op.fact (Elab.mem mem0)) (fun h => by
    cases h with
    | intro n h =>
      cases h with
      | fact e => exact Elab.nil e
      | back e _ => exact Elab.nil e)

/-! ## Veracidad respecto de una base nómica B* -/

-- B veraz respecto de B*: cada átomo derivable, bajo cualquier extensión, lo es en B*
abbrev Ver (B Bs : List F) : Prop :=
  ∀ (E : List F) (a : Nat), Der (E ++ B) (.atm a) → Der (E ++ Bs) (.atm a)

-- de átomos a objetivos (inducción en el peso)
theorem ver_lift {B Bs : List F} (hV : Ver B Bs) (s : Nat) :
    ∀ (G : F), G.w < s → ∀ (E : List F), Der (E ++ B) G → Der (E ++ Bs) G := by
  induction s with
  | zero => intro G hw; exact absurd hw (Nat.not_lt_zero _)
  | succ s ih =>
    intro G hw E h
    cases G with
    | atm a => exact hV E a h
    | var X =>
      cases h with
      | intro n h => cases h
    | and G₁ G₂ =>
      have hw' : G₁.w + G₂.w + 1 < s + 1 := hw
      have hh := Der.inv_and h
      exact Der.and (ih G₁ (by omega) E hh.1) (ih G₂ (by omega) E hh.2)
    | or G₁ G₂ =>
      have hw' : G₁.w + G₂.w + 1 < s + 1 := hw
      cases h with
      | intro n h =>
        cases h with
        | orL h' => exact Der.orL (ih G₁ (by omega) E ⟨_, h'⟩)
        | orR h' => exact Der.orR (ih G₂ (by omega) E ⟨_, h'⟩)
    | imp D G' =>
      have hw' : D.w + 2 * G'.w + 1 < s + 1 := hw
      exact Der.aug (ih G' (by omega) (D :: E) (Der.inv_imp h))
    | all X G' =>
      have hw' : G'.w + 1 < s + 1 := hw
      cases (show ∃ A, Fresh A (E ++ Bs) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro A hA =>
        exact Der.gen hA (ih (G'.sub X A) (by rw [F.w_sub]; omega) E (Der.inv_all h A))

-- veracidad atómica ⟹ veracidad para toda fórmula de IPL
theorem ver_supp {B Bs : List F} (hV : Ver B Bs) (φ : Fm) (h : supp B φ) : supp Bs φ :=
  (sis φ Bs).mpr (ver_lift hV _ (enc φ) (Nat.lt_succ_self _) [] ((sis φ B).mp h))

theorem Ver.refl (B : List F) : Ver B B := fun _ _ h => h

-- principio de la fotocopiadora (Dretske): la veracidad compone
theorem Ver.trans {B₁ B₂ B₃ : List F} (h₁ : Ver B₁ B₂) (h₂ : Ver B₂ B₃) : Ver B₁ B₃ :=
  fun E a h => h₂ E a (h₁ E a h)

theorem Ver.of_ext {B Bs : List F} (h : Ext B Bs) : Ver B Bs :=
  fun _ _ d => Der.mono d (fun D hD => (List.mem_append.mp hD).elim
    (fun h' => List.mem_append.mpr (Or.inl h'))
    (fun h' => List.mem_append.mpr (Or.inr (h D h'))))

-- procesar (añadir una cláusula derivable) preserva la veracidad
theorem Ver.process {K : F} (hn : K.neutral) (hc : K.closed) {B Bs : List F}
    (hK : Der B K) (hV : Ver B Bs) : Ver (K :: B) Bs := by
  intro E a h
  apply hV E a
  have hK' : Der (E ++ B) K := Der.mono hK (fun D hD => List.mem_append.mpr (Or.inr hD))
  have h' : Der (K :: (E ++ B)) (.atm a) := Der.mono h (fun D hD => by
    cases List.mem_append.mp hD with
    | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
    | inr h =>
      cases List.mem_cons.mp h with
      | inl e => exact List.mem_cons.mpr (Or.inl e)
      | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))
  have d := cut hn hc hK' h'
  exact Der.mono d (fun _ hD => (List.mem_append.mp hD).elim id id)

/-! ## Información de un mensaje y procesamiento de datos -/

-- contenido nuevo del mensaje M para el receptor K
abbrev Info (K M : List F) (φ : Fm) : Prop := supp (M ++ K) φ ∧ ¬ supp K φ

-- Q procesado desde B: cláusulas neutras, cerradas y derivables de B
abbrev Proc (B Q : List F) : Prop := ∀ D, D ∈ Q → D.neutral ∧ D.closed ∧ Der B D

theorem proc_conservative {B : List F} : ∀ (Q : List F), Proc B Q →
    ∀ φ, supp (Q ++ B) φ ↔ supp B φ := by
  intro Q
  induction Q with
  | nil => intro _ φ; exact Iff.rfl
  | cons D Q ih =>
    intro hQ φ
    have hD := hQ D mem0
    have hQ' : Proc B Q := fun E hE => hQ E (List.mem_cons.mpr (Or.inr hE))
    have hDer : Der (Q ++ B) D :=
      Der.mono (And.right (And.right hD)) (fun E hE => List.mem_append.mpr (Or.inr hE))
    exact (derived_conservative (And.left hD) (And.left (And.right hD)) hDer φ).trans
      (ih hQ' φ)

theorem Ver.proc {B Bs : List F} (hV : Ver B Bs) : ∀ (Q : List F), Proc B Q →
    Ver (Q ++ B) Bs := by
  intro Q
  induction Q with
  | nil => intro _; exact hV
  | cons D Q ih =>
    intro hQ
    have hD := hQ D mem0
    have hQ' : Proc B Q := fun E hE => hQ E (List.mem_cons.mpr (Or.inr hE))
    exact Ver.process (And.left hD) (And.left (And.right hD))
      (Der.mono (And.right (And.right hD)) (fun E hE => List.mem_append.mpr (Or.inr hE)))
      (ih hQ')

-- Procesamiento de datos inferencial: procesar en destino no añade contenido
-- y preserva la veracidad. (La ganancia de profundidad: `cost_cache`, `cost_rule`.)
theorem data_processing {K M Q Bs : List F} (hQ : Proc (M ++ K) Q) (hV : Ver (M ++ K) Bs) :
    (∀ φ, Info K (Q ++ M) φ ↔ Info K M φ) ∧ Ver (Q ++ (M ++ K)) Bs := by
  constructor
  · intro φ
    have e := proc_conservative Q hQ φ
    show (supp ((Q ++ M) ++ K) φ ∧ ¬ supp K φ) ↔ (supp (M ++ K) φ ∧ ¬ supp K φ)
    rw [List.append_assoc]
    exact ⟨fun h => ⟨e.mp h.1, h.2⟩, fun h => ⟨e.mpr h.1, h.2⟩⟩
  · exact Ver.proc hV Q hQ

/-! ## Sin hipótesis no hay amplificación: programas de Horn (primer nivel) -/

-- objetivos de Horn: átomos, ∩, ∪
def F.horn : F → Prop
  | .atm _   => True
  | .and f g => f.horn ∧ g.horn
  | .or f g  => f.horn ∧ g.horn
  | _        => False

-- cláusula de Horn: hecho o G ⊃ a con G de Horn
abbrev HornC (D : F) : Prop := (∃ a, D = .atm a) ∨ (∃ G a, D = .imp G (.atm a) ∧ G.horn)

theorem horn_flat {a b : Nat} {Q : List F} (hQ : ∀ D, D ∈ Q → HornC D) :
    ∀ D, D ∈ F.imp (.atm b) (.atm a) :: Q → Flat D := by
  intro D hD
  cases List.mem_cons.mp hD with
  | inl e => exact Or.inr ⟨_, _, e⟩
  | inr h =>
    cases hQ D h with
    | inl hc => exact Or.inl hc
    | inr hc =>
      cases hc with
      | intro G hc =>
        cases hc with
        | intro a' hc => exact Or.inr ⟨G, a', hc.1⟩

theorem horn_body {Q : List F} (hQ : ∀ D, D ∈ Q → HornC D) {G : F} {x : Nat}
    (h : F.imp G (.atm x) ∈ Q) : G.horn := by
  cases hQ _ h with
  | inl hc =>
    cases hc with
    | intro _ e => cases e
  | inr hc =>
    cases hc with
    | intro G₀ hc =>
      cases hc with
      | intro a' hc =>
        have e₀ := (F.imp.inj hc.1).1
        rw [e₀]
        exact hc.2

-- si a no se deriva con altura ≤ k, K = b ⊃ a no se usa
theorem noK {a b : Nat} {Q : List F} (hQ : ∀ D, D ∈ Q → HornC D) :
    ∀ (k : Nat) (G : F), G.horn → ¬ Op k (.imp (.atm b) (.atm a) :: Q) (.atm a) →
      Op k (.imp (.atm b) (.atm a) :: Q) G → Op k Q G := by
  intro k
  induction k with
  | zero => intro G _ _ h; cases h
  | succ k ih =>
    intro G hG hna h
    have hna' : ¬ Op k (.imp (.atm b) (.atm a) :: Q) (.atm a) :=
      fun h' => hna (Op.lift h' (Nat.le_succ k))
    cases h with
    | fact e =>
      have hm := Elab.flat (horn_flat hQ) e
      cases List.mem_cons.mp hm with
      | inl e' => cases e'
      | inr h' => exact Op.fact (Elab.mem h')
    | @back _ _ G' x e h' =>
      have hm := Elab.flat (horn_flat hQ) e
      cases List.mem_cons.mp hm with
      | inl e' =>
        have hx := F.atm.inj (F.imp.inj e').2
        rw [hx] at e
        exact absurd (Op.back e h') hna
      | inr h'' => exact Op.back (Elab.mem h'') (ih G' (horn_body hQ h'') hna' h')
    | and h₁ h₂ => exact Op.and (ih _ (And.left hG) hna' h₁) (ih _ (And.right hG) hna' h₂)
    | orL h' => exact Op.orL (ih _ (And.left hG) hna' h')
    | orR h' => exact Op.orR (ih _ (And.right hG) hna' h')
    | aug _ => exact False.elim hG
    | gen _ _ => exact False.elim hG

-- Horn: P ⊢ₘ b ⊃ a (vía b, P ⊢ₘ a), (b ⊃ a), Q ⊢ₙ G ⟹ P, Q ⊢_{n+m} G
theorem cut_rule_horn {a b m : Nat} {P Q : List F} (hQ : ∀ D, D ∈ Q → HornC D)
    (hP : Op m (.atm b :: P) (.atm a)) :
    ∀ N n, n ≤ N → ∀ (G : F), G.horn → Op n (.imp (.atm b) (.atm a) :: Q) G →
      Op (n + m) (P ++ Q) G := by
  intro N
  induction N with
  | zero =>
    intro n hn G _ h
    have := Op.pos h
    omega
  | succ N ih =>
    intro n hn G hG h
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    cases h with
    | fact e =>
      have hm := Elab.flat (horn_flat hQ) e
      cases List.mem_cons.mp hm with
      | inl e' => cases e'
      | inr h' => exact Op.lift (Op.fact (n := 0) (Elab.mem (inR _ h'))) (by omega)
    | @back k _ G' x e h' =>
      have hm := Elab.flat (horn_flat hQ) e
      cases List.mem_cons.mp hm with
      | inr h'' =>
        have d := ih k (by omega) G' (horn_body hQ h'') h'
        exact Op.lift (Op.back (Elab.mem (inR _ h'')) d) (by omega)
      | inl e' =>
        have hh := F.imp.inj e'
        have hx := F.atm.inj hh.2
        rw [hx]
        rw [hh.1] at h'
        cases Classical.em (Op k (.imp (.atm b) (.atm a) :: Q) (.atm a)) with
        | inl ha =>
          -- a ya se derivaba más abajo
          exact Op.lift (ih k (by omega) (.atm a) trivial ha) (by omega)
        | inr ha =>
          -- K no aparece bajo esta rama: b sale de Q
          have d0 := noK hQ k (.atm b) trivial ha h'
          have d1 : Op k (P ++ Q) (.atm b) := Op.mono k d0 inR
          have d2 := cut_atom d1 m P (.atm a) hP
          exact Op.mono _ (Op.lift d2 (by omega)) (fun D hD => by
            cases List.mem_append.mp hD with
            | inl h => exact h
            | inr h => exact List.mem_append.mpr (Or.inl h))
    | @and k _ _ _ h₁ h₂ =>
      exact Op.lift (Op.and (ih k (by omega) _ (And.left hG) h₁)
        (ih k (by omega) _ (And.right hG) h₂)) (by omega)
    | @orL k _ _ _ h' => exact Op.lift (Op.orL (ih k (by omega) _ (And.left hG) h')) (by omega)
    | @orR k _ _ _ h' => exact Op.lift (Op.orR (ih k (by omega) _ (And.right hG) h')) (by omega)
    | aug _ => exact False.elim hG
    | gen _ _ => exact False.elim hG

-- κ_{P,Q}(G) ≤ κ_{b⊃a, Q}(G) + κ_P(b ⊃ a), con Q y G de Horn: aditivo
theorem cost_rule_horn {a b : Nat} {P Q : List F} {G : F} {m n : Nat}
    (hQ : ∀ D, D ∈ Q → HornC D) (hG : G.horn)
    (hK : Op m P (.imp (.atm b) (.atm a))) (h : Op n (.imp (.atm b) (.atm a) :: Q) G) :
    Op (n + m) (P ++ Q) G :=
  cut_rule_horn hQ (Op.inv_imp hK) n n (Nat.le_refl _) G hG h

/-! ## Varios hechos en caché: cuesta el más caro, no la suma -/

-- P ⊢ₘ a para todo a ∈ A; A, Q ⊢ₙ G ⟹ P, Q ⊢ₘ₊ₙ G
theorem cut_facts {m : Nat} {P : List F} {A : List Nat} (hP : ∀ a, a ∈ A → Op m P (.atm a)) :
    ∀ (n : Nat) (Q : List F) (G : F), Op n (A.map F.atm ++ Q) G → Op (m + n) (P ++ Q) G := by
  have hfl : ∀ D, D ∈ A.map F.atm → Flat D := fun D hD => by
    cases List.mem_map.mp hD with
    | intro a ha => exact Or.inl ⟨a, ha.2.symm⟩
  intro n
  induction n with
  | zero => intro Q G h; cases h
  | succ k ihn =>
    intro Q G h
    have inL : ∀ D, D ∈ P → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inl h)
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    show Op (m + k + 1) (P ++ Q) G
    cases h with
    | fact e =>
      cases Elab.split e with
      | inl e' =>
        cases List.mem_map.mp (Elab.flat hfl e') with
        | intro a ha =>
          have hx := F.atm.inj ha.2
          rw [← hx]
          exact Op.mono _ (Op.lift (hP a ha.1) (by omega)) inL
      | inr e' => exact Op.fact (Elab.mono inR e')
    | back e h' =>
      cases Elab.split e with
      | inl e' =>
        cases List.mem_map.mp (Elab.flat hfl e') with
        | intro a ha => cases ha.2
      | inr e' => exact Op.back (Elab.mono inR e') (ihn Q _ h')
    | and h₁ h₂ => exact Op.and (ihn Q _ h₁) (ihn Q _ h₂)
    | orL h' => exact Op.orL (ihn Q _ h')
    | orR h' => exact Op.orR (ihn Q _ h')
    | @aug _ _ D G' h' =>
      have h1 : Op k (A.map F.atm ++ D :: Q) G' := Op.mono k h' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
        | inr h =>
          cases List.mem_append.mp h with
          | inl h' => exact List.mem_append.mpr (Or.inl h')
          | inr h' => exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
      have d := ihn (D :: Q) G' h1
      exact Op.aug (Op.mono _ d (fun E hE => by
        cases List.mem_append.mp hE with
        | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))))
    | @gen _ _ X G' B hB h' =>
      cases (show ∃ C, Fresh C (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro C hC =>
        have h'' := Op.ren h' (upd id B C)
        rw [map_ren_away (A.map F.atm ++ Q) hB.1, sub_ren_away (G := G') hB.2] at h''
        exact Op.gen hC (ihn Q _ h'')

-- κ_K(φ) ≤ max_{a ∈ A} κ_K(a) + κ_{A,K}(φ)
theorem cost_facts {K : List F} {A : List Nat} {φ : Fm} {m n : Nat}
    (hA : ∀ a, a ∈ A → Cost K (.atom a) m) (h : Cost (A.map F.atm ++ K) φ n) :
    Cost K φ (m + n) :=
  Op.mono _ (cut_facts hA n K (enc φ) h) (fun _ hD => (List.mem_append.mp hD).elim id id)

/-! ## Reglas de Horn con cuerpo conjuntivo: también aditivo -/

-- b ∩ c₁ ∩ … ∩ c_k
def bodyF : Nat → List Nat → F
  | b, []      => .atm b
  | b, c :: cs => .and (.atm b) (bodyF c cs)

theorem bodyF_horn : ∀ (b : Nat) (cs : List Nat), (bodyF b cs).horn
  | _, [] => trivial
  | _, c :: cs => And.intro trivial (bodyF_horn c cs)

theorem Op.inv_body {k : Nat} {Q : List F} : ∀ (b : Nat) (cs : List Nat),
    Op k Q (bodyF b cs) → ∀ x, x ∈ b :: cs → Op k Q (.atm x)
  | b, [], h, x, hx => by
    cases List.mem_cons.mp hx with
    | inl e => rw [e]; exact h
    | inr h' => cases h'
  | b, c :: cs, h, x, hx => by
    have hh := Op.inv_and h
    cases List.mem_cons.mp hx with
    | inl e => rw [e]; exact hh.1
    | inr h' => exact Op.inv_body c cs hh.2 x h'

theorem horn_flat' {a : Nat} {G₀ : F} {Q : List F} (hQ : ∀ D, D ∈ Q → HornC D) :
    ∀ D, D ∈ F.imp G₀ (.atm a) :: Q → Flat D := by
  intro D hD
  cases List.mem_cons.mp hD with
  | inl e => exact Or.inr ⟨_, _, e⟩
  | inr h => exact horn_flat (b := 0) (a := 0) hQ D (List.mem_cons.mpr (Or.inr h))

-- noK para cuerpo arbitrario
theorem noK' {a : Nat} {G₀ : F} {Q : List F} (hQ : ∀ D, D ∈ Q → HornC D) :
    ∀ (k : Nat) (G : F), G.horn → ¬ Op k (.imp G₀ (.atm a) :: Q) (.atm a) →
      Op k (.imp G₀ (.atm a) :: Q) G → Op k Q G := by
  intro k
  induction k with
  | zero => intro G _ _ h; cases h
  | succ k ih =>
    intro G hG hna h
    have hna' : ¬ Op k (.imp G₀ (.atm a) :: Q) (.atm a) :=
      fun h' => hna (Op.lift h' (Nat.le_succ k))
    cases h with
    | fact e =>
      have hm := Elab.flat (horn_flat' hQ) e
      cases List.mem_cons.mp hm with
      | inl e' => cases e'
      | inr h' => exact Op.fact (Elab.mem h')
    | @back _ _ G' x e h' =>
      have hm := Elab.flat (horn_flat' hQ) e
      cases List.mem_cons.mp hm with
      | inl e' =>
        have hx := F.atm.inj (F.imp.inj e').2
        rw [hx] at e
        exact absurd (Op.back e h') hna
      | inr h'' => exact Op.back (Elab.mem h'') (ih G' (horn_body hQ h'') hna' h')
    | and h₁ h₂ => exact Op.and (ih _ (And.left hG) hna' h₁) (ih _ (And.right hG) hna' h₂)
    | orL h' => exact Op.orL (ih _ (And.left hG) hna' h')
    | orR h' => exact Op.orR (ih _ (And.right hG) hna' h')
    | aug _ => exact False.elim hG
    | gen _ _ => exact False.elim hG

-- K = b ∩ cs ⊃ a; b, cs, P ⊢ₘ a; K, Q ⊢ₙ G ⟹ P, Q ⊢_{n+m} G
theorem cut_rule_hornC {a b m : Nat} {cs : List Nat} {P Q : List F}
    (hQ : ∀ D, D ∈ Q → HornC D) (hP : Op m ((b :: cs).map F.atm ++ P) (.atm a)) :
    ∀ N n, n ≤ N → ∀ (G : F), G.horn → Op n (.imp (bodyF b cs) (.atm a) :: Q) G →
      Op (n + m) (P ++ Q) G := by
  intro N
  induction N with
  | zero =>
    intro n hn G _ h
    have := Op.pos h
    omega
  | succ N ih =>
    intro n hn G hG h
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    cases h with
    | fact e =>
      have hm := Elab.flat (horn_flat' hQ) e
      cases List.mem_cons.mp hm with
      | inl e' => cases e'
      | inr h' => exact Op.lift (Op.fact (n := 0) (Elab.mem (inR _ h'))) (by omega)
    | @back k _ G' x e h' =>
      have hm := Elab.flat (horn_flat' hQ) e
      cases List.mem_cons.mp hm with
      | inr h'' =>
        have d := ih k (by omega) G' (horn_body hQ h'') h'
        exact Op.lift (Op.back (Elab.mem (inR _ h'')) d) (by omega)
      | inl e' =>
        have hh := F.imp.inj e'
        have hx := F.atm.inj hh.2
        rw [hx]
        rw [hh.1] at h'
        cases Classical.em (Op k (.imp (bodyF b cs) (.atm a) :: Q) (.atm a)) with
        | inl ha => exact Op.lift (ih k (by omega) (.atm a) trivial ha) (by omega)
        | inr ha =>
          have d0 := noK' hQ k (bodyF b cs) (bodyF_horn b cs) ha h'
          have d1 : ∀ y, y ∈ b :: cs → Op k (P ++ Q) (.atm y) :=
            fun y hy => Op.mono k (Op.inv_body b cs d0 y hy) inR
          have d2 := cut_facts d1 m P (.atm a) hP
          exact Op.mono _ (Op.lift d2 (by omega)) (fun D hD => by
            cases List.mem_append.mp hD with
            | inl h => exact h
            | inr h => exact List.mem_append.mpr (Or.inl h))
    | @and k _ _ _ h₁ h₂ =>
      exact Op.lift (Op.and (ih k (by omega) _ (And.left hG) h₁)
        (ih k (by omega) _ (And.right hG) h₂)) (by omega)
    | @orL k _ _ _ h' => exact Op.lift (Op.orL (ih k (by omega) _ (And.left hG) h')) (by omega)
    | @orR k _ _ _ h' => exact Op.lift (Op.orR (ih k (by omega) _ (And.right hG) h')) (by omega)
    | aug _ => exact False.elim hG
    | gen _ _ => exact False.elim hG

-- κ_{P,Q}(G) ≤ κ_{K,Q}(G) + κ_{b,cs,P}(a), con Q y G de Horn
theorem cost_rule_hornC {a b : Nat} {cs : List Nat} {P Q : List F} {G : F} {m n : Nat}
    (hQ : ∀ D, D ∈ Q → HornC D) (hG : G.horn)
    (hP : Op m ((b :: cs).map F.atm ++ P) (.atm a))
    (h : Op n (.imp (bodyF b cs) (.atm a) :: Q) G) : Op (n + m) (P ++ Q) G :=
  cut_rule_hornC hQ hP n n (Nat.le_refl _) G hG h

/-! ## Contextos hipotéticos: el ahorro de una regla es lineal en los Augment por rama
  `OpA n α P G`: altura ≤ n, a lo sumo α pasos Augment por rama. -/

inductive OpA : Nat → Nat → List F → F → Prop where
  | fact {n α : Nat} {P : List F} {A : Nat} :
      Elab P (.atm A) → OpA (n + 1) α P (.atm A)
  | back {n α : Nat} {P : List F} {G : F} {A : Nat} :
      Elab P (.imp G (.atm A)) → OpA n α P G → OpA (n + 1) α P (.atm A)
  | and {n α : Nat} {P : List F} {G₁ G₂ : F} :
      OpA n α P G₁ → OpA n α P G₂ → OpA (n + 1) α P (.and G₁ G₂)
  | orL {n α : Nat} {P : List F} {G₁ G₂ : F} :
      OpA n α P G₁ → OpA (n + 1) α P (.or G₁ G₂)
  | orR {n α : Nat} {P : List F} {G₁ G₂ : F} :
      OpA n α P G₂ → OpA (n + 1) α P (.or G₁ G₂)
  | aug {n α : Nat} {P : List F} {D G : F} :
      OpA n α (D :: P) G → OpA (n + 1) (α + 1) P (.imp D G)
  | gen {n α : Nat} {P : List F} {X : Nat} {G : F} {A : Nat} :
      Fresh A P (.all X G) → OpA n α P (G.sub X A) → OpA (n + 1) α P (.all X G)

theorem OpA.toOp {n α : Nat} {P : List F} {G : F} (h : OpA n α P G) : Op n P G := by
  induction h with
  | fact e => exact Op.fact e
  | back e _ ih => exact Op.back e ih
  | and _ _ ih₁ ih₂ => exact Op.and ih₁ ih₂
  | orL _ ih => exact Op.orL ih
  | orR _ ih => exact Op.orR ih
  | aug _ ih => exact Op.aug ih
  | gen hA _ ih => exact Op.gen hA ih

theorem OpA.lift {n α : Nat} {P : List F} {G : F} (h : OpA n α P G) :
    ∀ {n' α' : Nat}, n ≤ n' → α ≤ α' → OpA n' α' P G := by
  induction h with
  | fact e =>
    intro n' α' hn _
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k => exact OpA.fact e
  | back e _ ih =>
    intro n' α' hn hα
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k => exact OpA.back e (ih (by omega) hα)
  | and _ _ ih₁ ih₂ =>
    intro n' α' hn hα
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k => exact OpA.and (ih₁ (by omega) hα) (ih₂ (by omega) hα)
  | orL _ ih =>
    intro n' α' hn hα
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k => exact OpA.orL (ih (by omega) hα)
  | orR _ ih =>
    intro n' α' hn hα
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k => exact OpA.orR (ih (by omega) hα)
  | aug _ ih =>
    intro n' α' hn hα
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k =>
      cases α' with
      | zero => exact absurd hα (by omega)
      | succ β => exact OpA.aug (ih (by omega) (by omega))
  | gen hA _ ih =>
    intro n' α' hn hα
    cases n' with
    | zero => exact absurd hn (by omega)
    | succ k => exact OpA.gen hA (ih (by omega) hα)

theorem OpA.ren {n α : Nat} {P : List F} {G : F} (h : OpA n α P G) :
    ∀ σ : Nat → Nat, OpA n α (P.map (F.ren σ)) (G.ren σ) := by
  induction h with
  | fact e => intro σ; exact OpA.fact (Elab.ren σ e)
  | back e _ ih => intro σ; exact OpA.back (Elab.ren σ e) (ih σ)
  | and _ _ ih₁ ih₂ => intro σ; exact OpA.and (ih₁ σ) (ih₂ σ)
  | orL _ ih => intro σ; exact OpA.orL (ih σ)
  | orR _ ih => intro σ; exact OpA.orR (ih σ)
  | aug _ ih => intro σ; exact OpA.aug (ih σ)
  | @gen _ _ P X G A hA _ ih =>
    intro σ
    cases (show ∃ B, Fresh B (P.map (F.ren σ)) ((F.all X G).ren σ) from
        ⟨_, fresh_exists _ _⟩) with
    | intro B hB =>
      have h1 := ih (upd σ A B)
      have e1 : P.map (F.ren (upd σ A B)) = P.map (F.ren σ) :=
        map_ren_congr P (fun D hD a ha =>
          upd_ne (fun e => hA.1 D hD (by rw [← e]; exact ha)))
      have e2 : (G.sub X A).ren (upd σ A B) = (G.ren σ).sub X B := by
        rw [F.ren_sub, upd_self,
          F.ren_congr G (fun a ha => upd_ne (fun e => hA.2 (by rw [← e]; exact ha)))]
      rw [e1, e2] at h1
      exact OpA.gen hB h1

theorem OpA.mono (n : Nat) : ∀ {α : Nat} {P : List F} {G : F}, OpA n α P G →
    ∀ {Q : List F}, (∀ D, D ∈ P → D ∈ Q) → OpA n α Q G := by
  induction n with
  | zero => intro _ _ _ h; cases h
  | succ k ih =>
    intro _ P _ h Q hPQ
    cases h with
    | fact e => exact OpA.fact (Elab.mono hPQ e)
    | back e h' => exact OpA.back (Elab.mono hPQ e) (ih h' hPQ)
    | and h₁ h₂ => exact OpA.and (ih h₁ hPQ) (ih h₂ hPQ)
    | orL h' => exact OpA.orL (ih h' hPQ)
    | orR h' => exact OpA.orR (ih h' hPQ)
    | aug h' =>
      exact OpA.aug (ih h' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_cons.mpr (Or.inl e)
        | inr h'' => exact List.mem_cons.mpr (Or.inr (hPQ E h''))))
    | @gen _ _ _ X G' A hA h' =>
      cases (show ∃ B, Fresh B Q (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have h'' := OpA.ren h' (upd id A B)
        rw [map_ren_away P hA.1, sub_ren_away (G := G') hA.2] at h''
        exact OpA.gen hB (ih h'' hPQ)

theorem Elab.clause_only {G₀ : F} {a : Nat} {E : F} (h : Elab [F.imp G₀ (.atm a)] E) :
    E = .imp G₀ (.atm a) := by
  have hm := Elab.flat (fun D hD => by
    cases List.mem_cons.mp hD with
    | inl e => exact Or.inr ⟨_, _, e⟩
    | inr h' => cases h') h
  cases List.mem_cons.mp hm with
  | inl e => exact e
  | inr h' => cases h'

-- a no sale en el mismo contexto ⟹ K = G₀ ⊃ a solo se usa bajo un Augment
theorem noK_ctx {a c α : Nat} {G₀ : F} {P Q : List F}
    (ih : ∀ β, α = β + 1 → ∀ n (Q' : List F) (G : F),
      OpA n β (.imp G₀ (.atm a) :: Q') G → Op (n + c) (P ++ Q') G) :
    ∀ (h : Nat) (G : F), ¬ OpA h α (.imp G₀ (.atm a) :: Q) (.atm a) →
      OpA h α (.imp G₀ (.atm a) :: Q) G → Op (h + c) (P ++ Q) G := by
  intro h
  induction h with
  | zero => intro _ _ d; cases d
  | succ k ihk =>
    intro G hna d
    have hna' : ¬ OpA k α (.imp G₀ (.atm a) :: Q) (.atm a) :=
      fun d' => hna (OpA.lift d' (Nat.le_succ k) (Nat.le_refl α))
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    have up : ∀ {G' : F}, Op (k + c + 1) (P ++ Q) G' → Op (k + 1 + c) (P ++ Q) G' :=
      fun d' => Op.lift d' (by omega)
    cases d with
    | fact e =>
      cases Elab.split (L₁ := [.imp G₀ (.atm a)]) (L₂ := Q) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact up (Op.fact (Elab.mono inR e'))
    | @back _ _ _ G' _ e d' =>
      cases Elab.split (L₁ := [.imp G₀ (.atm a)]) (L₂ := Q) e with
      | inl e' =>
        have hx := F.atm.inj (F.imp.inj (Elab.clause_only e')).2
        rw [hx] at e
        exact absurd (OpA.back e d') hna
      | inr e' => exact up (Op.back (Elab.mono inR e') (ihk G' hna' d'))
    | and d₁ d₂ => exact up (Op.and (ihk _ hna' d₁) (ihk _ hna' d₂))
    | orL d' => exact up (Op.orL (ihk _ hna' d'))
    | orR d' => exact up (Op.orR (ihk _ hna' d'))
    | @aug _ β _ D G' d' =>
      have d1 : OpA k β (.imp G₀ (.atm a) :: D :: Q) G' := OpA.mono k d' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
      have d2 := ih β rfl k (D :: Q) G' d1
      exact up (Op.aug (Op.mono _ d2 (fun E hE => by
        cases List.mem_append.mp hE with
        | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))))
    | @gen _ _ _ X G' A hA d' =>
      cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have d'' := OpA.ren d' (upd id A B)
        rw [map_ren_away (.imp G₀ (.atm a) :: Q) hA.1, sub_ren_away (G := G') hA.2] at d''
        exact up (Op.gen hB (ihk _ hna' d''))

-- paso: con la cota para α − 1, inducción fuerte en la altura
theorem cut_ctx_step {a b m α : Nat} {cs : List Nat} {P : List F}
    (hP : Op m ((b :: cs).map F.atm ++ P) (.atm a))
    (ih : ∀ β, α = β + 1 → ∀ n (Q' : List F) (G : F),
      OpA n β (.imp (bodyF b cs) (.atm a) :: Q') G → Op (n + m * α) (P ++ Q') G) :
    ∀ N n, n ≤ N → ∀ (Q : List F) (G : F), OpA n α (.imp (bodyF b cs) (.atm a) :: Q) G →
      Op (n + m * α + m) (P ++ Q) G := by
  intro N
  induction N with
  | zero =>
    intro n hn _ _ d
    have := Op.pos (OpA.toOp d)
    omega
  | succ N ihN =>
    intro n hn Q G d
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    cases d with
    | fact e =>
      cases Elab.split (L₁ := [.imp (bodyF b cs) (.atm a)]) (L₂ := Q) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact Op.lift (Op.fact (n := 0) (Elab.mono inR e')) (by omega)
    | @back k _ _ G' _ e d' =>
      cases Elab.split (L₁ := [.imp (bodyF b cs) (.atm a)]) (L₂ := Q) e with
      | inr e' =>
        have d1 := ihN k (by omega) Q G' d'
        exact Op.lift (Op.back (Elab.mono inR e') d1) (by omega)
      | inl e' =>
        have hh := F.imp.inj (Elab.clause_only e')
        have hx := F.atm.inj hh.2
        rw [hx]
        rw [hh.1] at d'
        cases Classical.em (OpA k α (.imp (bodyF b cs) (.atm a) :: Q) (.atm a)) with
        | inl ha =>
          -- a ya salía antes en el mismo contexto
          exact Op.lift (ihN k (by omega) Q (.atm a) ha) (by omega)
        | inr ha =>
          -- K solo bajo Augment: el cuerpo sale con la cota de α − 1
          have d0 := noK_ctx ih k (bodyF b cs) ha d'
          have d1 : ∀ y, y ∈ b :: cs → Op (k + m * α) (P ++ Q) (.atm y) :=
            fun y hy => Op.inv_body b cs d0 y hy
          have d2 := cut_facts d1 m P (.atm a) hP
          exact Op.mono _ (Op.lift d2 (by omega)) (fun D hD => by
            cases List.mem_append.mp hD with
            | inl h => exact h
            | inr h => exact List.mem_append.mpr (Or.inl h))
    | @and k _ _ _ _ d₁ d₂ =>
      exact Op.lift (Op.and (ihN k (by omega) Q _ d₁) (ihN k (by omega) Q _ d₂)) (by omega)
    | @orL k _ _ _ _ d' => exact Op.lift (Op.orL (ihN k (by omega) Q _ d')) (by omega)
    | @orR k _ _ _ _ d' => exact Op.lift (Op.orR (ihN k (by omega) Q _ d')) (by omega)
    | @aug k β _ D G' d' =>
      have d1 : OpA k β (.imp (bodyF b cs) (.atm a) :: D :: Q) G' := OpA.mono k d' (fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'))))
      have d2 := ih β rfl k (D :: Q) G' d1
      exact Op.lift (Op.aug (Op.mono _ d2 (fun E hE => by
        cases List.mem_append.mp hE with
        | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h')))))) (by omega)
    | @gen k _ _ X G' A hA d' =>
      cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have d'' := OpA.ren d' (upd id A B)
        rw [map_ren_away (.imp (bodyF b cs) (.atm a) :: Q) hA.1,
          sub_ren_away (G := G') hA.2] at d''
        exact Op.lift (Op.gen hB (ihN k (by omega) Q _ d'')) (by omega)

-- K = b ∩ cs ⊃ a; b, cs, P ⊢ₘ a; K, Q ⊢ₙ G con ≤ α Augment por rama ⟹ P, Q ⊢_{n+m(α+1)} G
theorem cut_rule_ctx {a b m : Nat} {cs : List Nat} {P : List F}
    (hP : Op m ((b :: cs).map F.atm ++ P) (.atm a)) :
    ∀ α n (Q : List F) (G : F), OpA n α (.imp (bodyF b cs) (.atm a) :: Q) G →
      Op (n + m * α + m) (P ++ Q) G := by
  intro α
  induction α with
  | zero =>
    intro n Q G d
    exact cut_ctx_step hP (fun β hβ => absurd hβ (by omega)) n n (Nat.le_refl _) Q G d
  | succ β ihβ =>
    intro n Q G d
    refine cut_ctx_step hP (fun β' hβ' n' Q' G' d' => ?_) n n (Nat.le_refl _) Q G d
    have e : β' = β := by omega
    rw [e] at d'
    have d1 := ihβ n' Q' G' d'
    rw [Nat.left_distrib, Nat.mul_one]
    exact Op.lift d1 (by omega)

-- Horn: sin Augment, presupuesto 0
theorem horn_budget {R : List F} (hR : ∀ D, D ∈ R → HornC D) :
    ∀ (n : Nat) (G : F), G.horn → Op n R G → OpA n 0 R G := by
  have hfl : ∀ D, D ∈ R → Flat D := fun D hD => by
    cases hR D hD with
    | inl hc => exact Or.inl hc
    | inr hc =>
      cases hc with
      | intro G hc =>
        cases hc with
        | intro a' hc => exact Or.inr ⟨G, a', hc.1⟩
  intro n
  induction n with
  | zero => intro _ _ h; cases h
  | succ k ih =>
    intro G hG h
    cases h with
    | fact e => exact OpA.fact e
    | @back _ _ G' _ e h' => exact OpA.back e (ih G' (horn_body hR (Elab.flat hfl e)) h')
    | and h₁ h₂ => exact OpA.and (ih _ (And.left hG) h₁) (ih _ (And.right hG) h₂)
    | orL h' => exact OpA.orL (ih _ (And.left hG) h')
    | orR h' => exact OpA.orR (ih _ (And.right hG) h')
    | aug _ => exact False.elim hG
    | gen _ _ => exact False.elim hG

-- α = 0 recupera la cota aditiva de Horn
theorem ctx_horn {a b m n : Nat} {cs : List Nat} {P Q : List F} {G : F}
    (hQ : ∀ D, D ∈ Q → HornC D) (hG : G.horn)
    (hP : Op m ((b :: cs).map F.atm ++ P) (.atm a))
    (h : Op n (.imp (bodyF b cs) (.atm a) :: Q) G) : Op (n + m) (P ++ Q) G := by
  have hR : ∀ D, D ∈ F.imp (bodyF b cs) (.atm a) :: Q → HornC D := fun D hD => by
    cases List.mem_cons.mp hD with
    | inl e => exact Or.inr ⟨_, _, e, bodyF_horn b cs⟩
    | inr h' => exact hQ D h'
  have d := cut_rule_ctx hP 0 n Q G (horn_budget hR n G hG h)
  rw [Nat.mul_zero, Nat.add_zero] at d
  exact d

-- con K: c_j ≤ 5j + 1 usando j contextos
theorem amp_upperA (m t : Nat) : ∀ j, j ≤ t → ∀ (P : List F),
    (∀ D, D ∈ ruleK m :: amp m t → D ∈ P) → OpA (5 * j + 1) j P (.atm (3 * j)) := by
  intro j
  induction j with
  | zero =>
    intro _ P hP
    exact OpA.fact (Elab.mem (hP _ (List.mem_cons.mpr (Or.inr mem0))))
  | succ j ih =>
    intro hj P hP
    have inA : ∀ D, D ∈ rds m t → D ∈ P := fun D hD =>
      hP D (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
        (List.mem_append.mpr (Or.inr hD))))))
    have hC := inA _ (rds_memC (m := m) (by omega : j < t))
    have hB := inA _ (rds_memB (m := m) (by omega : j < t))
    have hK : ruleK m ∈ P := hP _ mem0
    have hP' : ∀ D, D ∈ ruleK m :: amp m t → D ∈ F.atm (3 * (j + 1) + 1) :: P :=
      fun D hD => List.mem_cons.mpr (Or.inr (hP D hD))
    have d := ih (by omega) _ hP'
    have d1 : OpA (5 * j + 1) j (F.atm (3 * (j + 1) + 1) :: P) (.atm (3 * (j + 1) + 1)) :=
      OpA.fact (Elab.mem mem0)
    have d2 := OpA.and d1 d
    have d3 := OpA.back (Elab.mem (List.mem_cons.mpr (Or.inr hB))) d2
    have d4 := OpA.back (Elab.mem (List.mem_cons.mpr (Or.inr hK))) d3
    have d5 := OpA.aug d4
    have d6 := OpA.back (Elab.mem hC) d5
    exact OpA.lift d6 (by omega) (Nat.le_refl _)

-- A_{m,t}: (m+5)t < κ(c_t) ≤ 5t + 1 + (m+2)(t+1); el coeficiente de mt es exacto
theorem amp_ctx (m t : Nat) :
    Cost (amp m t) (.atom (3 * t)) (5 * t + 1 + (m + 2) * t + (m + 2)) ∧
    ¬ Cost (amp m t) (.atom (3 * t)) (lb (m + 5) t) := by
  refine ⟨?_, (amplification m t).2.2.2⟩
  have dK : OpA (5 * t + 1) t (.imp (bodyF 2 []) (.atm (3 * (m + 1) + 2)) :: amp m t)
      (.atm (3 * t)) := amp_upperA m t t (Nat.le_refl _) _ (fun _ h => h)
  have d := cut_rule_ctx (b := 2) (cs := []) (P := amp m t)
    (amp_chain m t (m + 1) (Nat.le_refl _)) t (5 * t + 1) (amp m t) (.atm (3 * t)) dK
  exact Op.mono _ d (fun _ hD => (List.mem_append.mp hD).elim id id)

/-! ## Cadena de canales: el contenido obedece la desigualdad; la profundidad no -/

-- W ⇝ Y ⇝ Z, cada flecha un canal veraz: el destino no sabe más que el origen
theorem dpi_chain {W Y Z K : List F} (h₁ : Ver (Y ++ K) (W ++ K))
    (h₂ : Ver (Z ++ K) (Y ++ K)) :
    (∀ φ, Info K Z φ → Info K Y φ) ∧ (∀ φ, Info K Y φ → supp (W ++ K) φ) ∧
    Ver (Z ++ K) (W ++ K) :=
  ⟨fun φ h => ⟨ver_supp h₂ φ (And.left h), And.right h⟩,
   fun φ h => ver_supp h₁ φ (And.left h), Ver.trans h₂ h₁⟩

-- canal veraz en ambos sentidos (mismo contenido), pero κ baja de k + 1 a 1
theorem depth_not_dpi (k : Nat) :
    Ver (.atm k :: chain k) (chain k) ∧ Ver (chain k) (.atm k :: chain k) ∧
    ¬ Cost (chain k) (.atom k) k ∧ Cost (.atm k :: chain k) (.atom k) 1 :=
  ⟨Ver.process (K := .atm k) trivial (closed_atm k) ⟨_, chain_upper (k := k) k (Nat.le_refl k)⟩
      (Ver.refl _),
   Ver.of_ext (Ext.cons _ _), (chain_cost k).2, chain_shortcut k⟩

/-! ## Techo cuadrático sin ∀ (H16)
  Γ: objetivos alcanzables; U: cláusulas que Augment puede añadir.
  Por programa, etapas de un punto fijo sobre Γ; inducción en las cláusulas de U que faltan. -/

noncomputable def ind (p : Prop) : Nat := @ite Nat p (Classical.propDecidable p) 1 0

theorem ind_pos {p : Prop} (h : p) : ind p = 1 := by
  unfold ind; split
  · rfl
  · contradiction

theorem ind_neg {p : Prop} (h : ¬ p) : ind p = 0 := by
  unfold ind; split
  · contradiction
  · rfl

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  cases Classical.em p with
  | inl h => rw [ind_pos h]; exact Nat.le_refl 1
  | inr h => rw [ind_neg h]; exact Nat.zero_le 1

theorem ind_mono {p q : Prop} (h : p → q) : ind p ≤ ind q := by
  cases Classical.em p with
  | inl hp => rw [ind_pos hp, ind_pos (h hp)]; exact Nat.le_refl 1
  | inr hp => rw [ind_neg hp]; exact Nat.zero_le _

-- miembros de L que cumplen E
noncomputable def cntL (E : F → Prop) : List F → Nat
  | []     => 0
  | G :: L => ind (E G) + cntL E L

theorem cnt_le_len (E : F → Prop) : ∀ L : List F, cntL E L ≤ L.length
  | [] => Nat.le_refl 0
  | G :: L => by
    have h1 := ind_le_one (E G)
    have h2 := cnt_le_len E L
    show ind (E G) + cntL E L ≤ L.length + 1
    omega

theorem cnt_mono {E E' : F → Prop} : ∀ (L : List F), (∀ G, G ∈ L → E G → E' G) →
    cntL E L ≤ cntL E' L
  | [], _ => Nat.le_refl 0
  | G :: L, h => by
    have h1 := ind_mono (h G mem0)
    have h2 := cnt_mono L (fun G' hG' => h G' (List.mem_cons.mpr (Or.inr hG')))
    show ind (E G) + cntL E L ≤ ind (E' G) + cntL E' L
    omega

theorem cnt_lt {E E' : F → Prop} : ∀ (L : List F), (∀ G, G ∈ L → E G → E' G) →
    ∀ G₀, G₀ ∈ L → E' G₀ → ¬ E G₀ → cntL E L < cntL E' L
  | [], _, _, h0, _, _ => by cases h0
  | G :: L, h, G₀, h0, h1, h2 => by
    show ind (E G) + cntL E L < ind (E' G) + cntL E' L
    have hm := cnt_mono L (fun G' hG' => h G' (List.mem_cons.mpr (Or.inr hG')))
    cases List.mem_cons.mp h0 with
    | inl e =>
      rw [e] at h1 h2
      rw [ind_neg h2, ind_pos h1]
      omega
    | inr h0' =>
      have hl := cnt_lt L (fun G' hG' => h G' (List.mem_cons.mpr (Or.inr hG'))) G₀ h0' h1 h2
      have hi := ind_mono (h G mem0)
      omega

theorem cnt_full {E : F → Prop} : ∀ (L : List F), L.length ≤ cntL E L → ∀ G, G ∈ L → E G
  | [], _, _, h0 => by cases h0
  | G :: L, h, G', h0 => by
    have h1 := ind_le_one (E G)
    have h2 := cnt_le_len E L
    have h' : L.length + 1 ≤ ind (E G) + cntL E L := h
    cases List.mem_cons.mp h0 with
    | inl e =>
      rw [e]
      exact Classical.byContradiction (fun hn => by rw [ind_neg hn] at h'; omega)
    | inr h0' => exact cnt_full L (by omega) G' h0'

-- cláusulas de U que faltan en S
noncomputable def miss (S : List F) : List F → Nat
  | []     => 0
  | D :: U => ind (D ∉ S) + miss S U

theorem miss_le_len (S : List F) : ∀ U : List F, miss S U ≤ U.length
  | [] => Nat.le_refl 0
  | D :: U => by
    have h1 := ind_le_one (D ∉ S)
    have h2 := miss_le_len S U
    show ind (D ∉ S) + miss S U ≤ U.length + 1
    omega

theorem miss_cons (D' : F) (S : List F) : ∀ U : List F, miss (D' :: S) U ≤ miss S U
  | [] => Nat.le_refl 0
  | D :: U => by
    have h1 : ind (D ∉ D' :: S) ≤ ind (D ∉ S) :=
      ind_mono (fun h h' => h (List.mem_cons.mpr (Or.inr h')))
    have h2 := miss_cons D' S U
    show ind (D ∉ D' :: S) + miss (D' :: S) U ≤ ind (D ∉ S) + miss S U
    omega

theorem miss_lt {D : F} {S : List F} (hS : D ∉ S) :
    ∀ U : List F, D ∈ U → miss (D :: S) U < miss S U
  | [], h => by cases h
  | E :: U, h => by
    show ind (E ∉ D :: S) + miss (D :: S) U < ind (E ∉ S) + miss S U
    have h2 := miss_cons D S U
    have h1 : ind (E ∉ D :: S) ≤ ind (E ∉ S) :=
      ind_mono (fun h h' => h (List.mem_cons.mpr (Or.inr h')))
    cases List.mem_cons.mp h with
    | inl e =>
      rw [← e, ind_neg (p := D ∉ D :: S) (fun h' => h' mem0), ind_pos hS]
      omega
    | inr h' =>
      have h3 := miss_lt hS U h'
      omega

-- clausura: objetivos sin ∀, subobjetivos, cuerpos tras la elaboración
structure Clo (P0 U Γ : List F) : Prop where
  noall : ∀ X G, F.all X G ∉ Γ
  andc  : ∀ G₁ G₂, F.and G₁ G₂ ∈ Γ → G₁ ∈ Γ ∧ G₂ ∈ Γ
  orc   : ∀ G₁ G₂, F.or G₁ G₂ ∈ Γ → G₁ ∈ Γ ∧ G₂ ∈ Γ
  impc  : ∀ D G, F.imp D G ∈ Γ → D ∈ U ∧ G ∈ Γ
  body  : ∀ G A, Elab (P0 ++ U) (.imp G (.atm A)) → G ∈ Γ

-- un paso; Augment con D ∉ S sale del programa
abbrev step (S : List F) (E : F → Prop) (G : F) : Prop :=
  (∃ A, G = .atm A ∧ Elab S (.atm A)) ∨
  (∃ G' A, G = .atm A ∧ Elab S (.imp G' (.atm A)) ∧ E G') ∨
  (∃ G₁ G₂, G = .and G₁ G₂ ∧ E G₁ ∧ E G₂) ∨
  (∃ G₁ G₂, G = .or G₁ G₂ ∧ (E G₁ ∨ E G₂)) ∨
  (∃ D G', G = .imp D G' ∧ ((D ∈ S ∧ E G') ∨ (D ∉ S ∧ Der (D :: S) G')))

def stage (S : List F) : Nat → F → Prop
  | 0     => fun _ => False
  | k + 1 => step S (stage S k)

theorem step_mono {S : List F} {E E' : F → Prop} (h : ∀ G, E G → E' G) :
    ∀ G, step S E G → step S E' G := by
  intro G hs
  rcases hs with ⟨A, e, ea⟩ | ⟨G', A, e, ea, h1⟩ | ⟨G₁, G₂, e, h1, h2⟩ | ⟨G₁, G₂, e, h1⟩ |
    ⟨D, G', e, h1⟩
  · exact Or.inl ⟨A, e, ea⟩
  · exact Or.inr (Or.inl ⟨G', A, e, ea, h G' h1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨G₁, G₂, e, h G₁ h1, h G₂ h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨G₁, G₂, e,
      h1.elim (fun h' => Or.inl (h G₁ h')) (fun h' => Or.inr (h G₂ h'))⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, G', e,
      h1.elim (fun h' => Or.inl ⟨h'.1, h G' h'.2⟩) Or.inr⟩)))

-- monotonía relativa a Γ
theorem step_monoΓ {P0 U Γ S : List F} (clo : Clo P0 U Γ) (hS : ∀ D, D ∈ S → D ∈ P0 ++ U)
    {E E' : F → Prop} (h : ∀ G, G ∈ Γ → E G → E' G) :
    ∀ G, G ∈ Γ → step S E G → step S E' G := by
  intro G hG hs
  rcases hs with ⟨A, e, ea⟩ | ⟨G', A, e, ea, h1⟩ | ⟨G₁, G₂, e, h1, h2⟩ | ⟨G₁, G₂, e, h1⟩ |
    ⟨D, G', e, h1⟩
  · exact Or.inl ⟨A, e, ea⟩
  · exact Or.inr (Or.inl ⟨G', A, e, ea, h G' (clo.body G' A (Elab.mono hS ea)) h1⟩)
  · rw [e] at hG
    have hc := clo.andc G₁ G₂ hG
    exact Or.inr (Or.inr (Or.inl ⟨G₁, G₂, e, h G₁ hc.1 h1, h G₂ hc.2 h2⟩))
  · rw [e] at hG
    have hc := clo.orc G₁ G₂ hG
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨G₁, G₂, e,
      h1.elim (fun h' => Or.inl (h G₁ hc.1 h')) (fun h' => Or.inr (h G₂ hc.2 h'))⟩)))
  · rw [e] at hG
    have hc := clo.impc D G' hG
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, G', e,
      h1.elim (fun h' => Or.inl ⟨h'.1, h G' hc.2 h'.2⟩) Or.inr⟩)))

theorem stage_succ (S : List F) : ∀ k G, stage S k G → stage S (k + 1) G
  | 0, _, h => False.elim h
  | k + 1, G, h => by
    show step S (stage S (k + 1)) G
    exact step_mono (E := stage S k) (fun G' h' => stage_succ S k G' h') G h

theorem stage_add (S : List F) (k : Nat) : ∀ i G, stage S k G → stage S (k + i) G
  | 0, _, h => h
  | i + 1, G, h => stage_succ S (k + i) G (stage_add S k i G h)

theorem stage_le {S : List F} {k j : Nat} (hkj : k ≤ j) {G : F} (h : stage S k G) :
    stage S j G := by
  have e : j = k + (j - k) := by omega
  rw [e]
  exact stage_add S k (j - k) G h

-- derivación de altura k ⟹ etapa k
theorem op_stage {P0 U Γ S : List F} (clo : Clo P0 U Γ) (hS : ∀ D, D ∈ S → D ∈ P0 ++ U) :
    ∀ k G, G ∈ Γ → Op k S G → stage S k G := by
  intro k
  induction k with
  | zero => intro G _ h; cases h
  | succ k ih =>
    intro G hG h
    show step S (stage S k) G
    cases h with
    | fact e => exact Or.inl ⟨_, rfl, e⟩
    | @back _ _ G' _ e h' =>
      exact Or.inr (Or.inl ⟨G', _, rfl, e, ih G' (clo.body G' _ (Elab.mono hS e)) h'⟩)
    | and h₁ h₂ =>
      have hc := clo.andc _ _ hG
      exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, ih _ hc.1 h₁, ih _ hc.2 h₂⟩))
    | orL h' =>
      have hc := clo.orc _ _ hG
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Or.inl (ih _ hc.1 h')⟩)))
    | orR h' =>
      have hc := clo.orc _ _ hG
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, Or.inr (ih _ hc.2 h')⟩)))
    | @aug _ _ D G' h' =>
      have hc := clo.impc _ _ hG
      cases Classical.em (D ∈ S) with
      | inl hD =>
        have h'' : Op k S G' := Op.mono k h' (fun E hE => by
          cases List.mem_cons.mp hE with
          | inl e => rw [e]; exact hD
          | inr h => exact h)
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, G', rfl, Or.inl ⟨hD, ih G' hc.2 h''⟩⟩)))
      | inr hD => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, G', rfl, Or.inr ⟨hD, k, h'⟩⟩)))
    | gen _ _ => exact absurd hG (clo.noall _ _)

-- etapa k ⟹ altura k + H, si Augment fuera de S cuesta ≤ H
theorem stage_op {P0 U Γ S : List F} (clo : Clo P0 U Γ) (hS : ∀ D, D ∈ S → D ∈ P0 ++ U)
    {H : Nat} (hH : ∀ D G', D ∈ U → D ∉ S → G' ∈ Γ → Der (D :: S) G' → Op H (D :: S) G') :
    ∀ k G, G ∈ Γ → stage S k G → Op (k + H) S G := by
  intro k
  induction k with
  | zero => intro G _ h; exact False.elim h
  | succ k ih =>
    intro G hG h
    have up : ∀ {G'}, Op (k + H + 1) S G' → Op (k + 1 + H) S G' := fun d => Op.lift d (by omega)
    rcases h with ⟨A, e, ea⟩ | ⟨G', A, e, ea, h1⟩ | ⟨G₁, G₂, e, h1, h2⟩ | ⟨G₁, G₂, e, h1⟩ |
      ⟨D, G', e, h1⟩
    · rw [e]
      exact up (Op.fact ea)
    · rw [e]
      exact up (Op.back ea (ih G' (clo.body G' A (Elab.mono hS ea)) h1))
    · rw [e] at hG ⊢
      have hc := clo.andc G₁ G₂ hG
      exact up (Op.and (ih G₁ hc.1 h1) (ih G₂ hc.2 h2))
    · rw [e] at hG ⊢
      have hc := clo.orc G₁ G₂ hG
      cases h1 with
      | inl h' => exact up (Op.orL (ih G₁ hc.1 h'))
      | inr h' => exact up (Op.orR (ih G₂ hc.2 h'))
    · rw [e] at hG ⊢
      have hc := clo.impc D G' hG
      cases h1 with
      | inl h' =>
        exact up (Op.aug (Op.mono _ (ih G' hc.2 h'.2)
          (fun E hE => List.mem_cons.mpr (Or.inr hE))))
      | inr h' =>
        exact Op.lift (Op.aug (hH D G' hc.1 h'.1 hc.2 h'.2)) (by omega)

abbrev StableAt (S Γ : List F) (k : Nat) : Prop :=
  ∀ G, G ∈ Γ → stage S (k + 1) G → stage S k G

theorem stable_add {P0 U Γ S : List F} (clo : Clo P0 U Γ) (hS : ∀ D, D ∈ S → D ∈ P0 ++ U)
    {k : Nat} (hk : StableAt S Γ k) : ∀ i G, G ∈ Γ → stage S (k + i) G → stage S k G := by
  intro i
  induction i with
  | zero => intro G _ h; exact h
  | succ i ih =>
    intro G hG h
    have h' : step S (stage S (k + i)) G := h
    exact hk G hG (step_monoΓ clo hS ih G hG h')

-- o la cuenta crece en cada etapa, o se estabiliza antes
theorem count_or_stable {Γ S : List F} :
    ∀ k, k ≤ cntL (stage S k) Γ ∨ ∃ k', k' ≤ k ∧ StableAt S Γ k' := by
  intro k
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    cases ih with
    | inr h =>
      cases h with
      | intro k' hk => exact Or.inr ⟨k', Nat.le_succ_of_le hk.1, hk.2⟩
    | inl h =>
      cases Classical.em (StableAt S Γ k) with
      | inl hs => exact Or.inr ⟨k, Nat.le_succ k, hs⟩
      | inr hs =>
        have hw : ∃ G, G ∈ Γ ∧ stage S (k + 1) G ∧ ¬ stage S k G :=
          Classical.byContradiction (fun hn => hs (fun G hG h1 =>
            Classical.byContradiction (fun h2 => hn ⟨G, hG, h1, h2⟩)))
        cases hw with
        | intro G hG =>
          have hl := cnt_lt Γ (fun G' _ h' => stage_succ S k G' h') G hG.1 hG.2.1 hG.2.2
          exact Or.inl (by omega)

-- toda etapa queda dentro de la etapa |Γ|
theorem stab {P0 U Γ S : List F} (clo : Clo P0 U Γ) (hS : ∀ D, D ∈ S → D ∈ P0 ++ U) :
    ∀ k G, G ∈ Γ → stage S k G → stage S Γ.length G := by
  intro k G hG h
  cases count_or_stable (S := S) (Γ := Γ) Γ.length with
  | inl hc => exact cnt_full Γ hc G hG
  | inr hc =>
    cases hc with
    | intro k' hk =>
      cases Nat.le_total k k' with
      | inl hle => exact stage_le hk.1 (stage_le hle h)
      | inr hle =>
        have e : k = k' + (k - k') := by omega
        rw [e] at h
        exact stage_le hk.1 (stable_add clo hS hk.2 (k - k') G hG h)

theorem ceiling_step {P0 U Γ S : List F} (clo : Clo P0 U Γ) (hS : ∀ D, D ∈ S → D ∈ P0 ++ U)
    (hH : ∀ D G', D ∈ U → D ∉ S → G' ∈ Γ → Der (D :: S) G' →
      Op (miss S U * Γ.length) (D :: S) G') :
    ∀ G, G ∈ Γ → Der S G → Op ((miss S U + 1) * Γ.length) S G := by
  intro G hG hd
  cases hd with
  | intro k hk =>
    have h1 := stab clo hS k G hG (op_stage clo hS k G hG hk)
    have h2 := stage_op clo hS hH Γ.length G hG h1
    have e : (miss S U + 1) * Γ.length = Γ.length + miss S U * Γ.length := by
      rw [Nat.right_distrib, Nat.one_mul]; omega
    rw [e]; exact h2

-- inducción en el número de cláusulas de U que faltan
theorem ceiling {P0 U Γ : List F} (clo : Clo P0 U Γ) :
    ∀ N S, miss S U ≤ N → (∀ D, D ∈ S → D ∈ P0 ++ U) →
      ∀ G, G ∈ Γ → Der S G → Op ((miss S U + 1) * Γ.length) S G := by
  intro N
  induction N with
  | zero =>
    intro S hN hS
    exact ceiling_step clo hS (fun D _ hU hD _ _ => absurd (miss_lt hD U hU) (by omega))
  | succ N ih =>
    intro S hN hS
    exact ceiling_step clo hS (fun D G' hU hD hG' hd => by
      have hlt := miss_lt hD U hU
      have hS' : ∀ E, E ∈ D :: S → E ∈ P0 ++ U := fun E hE => by
        cases List.mem_cons.mp hE with
        | inl e => rw [e]; exact List.mem_append.mpr (Or.inr hU)
        | inr h => exact hS E h
      have d := ih (D :: S) (by omega) hS' G' hG' hd
      exact Op.lift d (Nat.mul_le_mul (by omega) (Nat.le_refl _)))

-- H16: sin ∀, κ_P(G) ≤ (1 + |U|)·|Γ|
theorem ceiling_cost {P0 U Γ : List F} (clo : Clo P0 U Γ) {G : F} (hG : G ∈ Γ)
    (hd : Der P0 G) : Op ((U.length + 1) * Γ.length) P0 G :=
  Op.lift (ceiling clo _ P0 (Nat.le_refl _) (fun _ hD => List.mem_append.mpr (Or.inl hD)) G hG hd)
    (Nat.mul_le_mul (Nat.succ_le_succ (miss_le_len P0 U)) (Nat.le_refl _))

/-! ## A_{m,t} sin K: κ(c_t) = (m+5)t + 1 -/

-- d₀ derivado en altura k ⟹ d_i en altura k + i
theorem amp_chain' (m t : Nat) {P : List F} (hP : ∀ D, D ∈ amp m t → D ∈ P) {k : Nat}
    (h0 : Op k P (.atm 2)) : ∀ i, i ≤ m + 1 → Op (k + i) P (.atm (3 * i + 2)) := by
  intro i
  induction i with
  | zero => intro _; exact h0
  | succ i ih =>
    intro hi
    have hm : F.imp (.atm (3 * i + 2)) (.atm (3 * (i + 1) + 2)) ∈ P :=
      hP _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (dch_mem (by omega))))))
    exact Op.back (Elab.mem hm) (ih (by omega))

theorem amp_upper0 (m t : Nat) : ∀ j, j ≤ t → ∀ (P : List F),
    (∀ D, D ∈ amp m t → D ∈ P) → Op ((m + 5) * j + 1) P (.atm (3 * j)) := by
  intro j
  induction j with
  | zero =>
    intro _ P hP
    exact Op.fact (Elab.mem (hP _ mem0))
  | succ j ih =>
    intro hj P hP
    have inA : ∀ D, D ∈ rds m t → D ∈ P := fun D hD =>
      hP D (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hD))))
    have hC := inA _ (rds_memC (m := m) (by omega : j < t))
    have hB := inA _ (rds_memB (m := m) (by omega : j < t))
    have hP' : ∀ D, D ∈ amp m t → D ∈ F.atm (3 * (j + 1) + 1) :: P :=
      fun D hD => List.mem_cons.mpr (Or.inr (hP D hD))
    have d := ih (by omega) _ hP'
    have d1 : Op ((m + 5) * j + 1) (F.atm (3 * (j + 1) + 1) :: P) (.atm (3 * (j + 1) + 1)) :=
      Op.lift (Op.fact (n := 0) (Elab.mem mem0)) (by omega)
    have d2 := Op.and d1 d
    have d3 := Op.back (Elab.mem (List.mem_cons.mpr (Or.inr hB))) d2
    have d4 := amp_chain' m t hP' d3 (m + 1) (Nat.le_refl _)
    have d5 := Op.aug d4
    have d6 := Op.back (Elab.mem hC) d5
    have e : (m + 5) * (j + 1) = (m + 5) * j + (m + 5) := by
      rw [Nat.left_distrib, Nat.mul_one]
    exact Op.lift d6 (by omega)

theorem amp_exact (m t : Nat) :
    Op ((m + 5) * t + 1) (amp m t) (.atm (3 * t)) ∧
    ¬ Op (lb (m + 5) t) (amp m t) (.atm (3 * t)) :=
  ⟨amp_upper0 m t t (Nat.le_refl _) _ (fun _ h => h), (amplification m t).2.2.2⟩

/-! ## Lemas de orden 2 (H10)
  K = (c ⊃ b) ⊃ a. Con c en el programa, K actúa como b ⊃ a;
  el primer uso de K en una rama paga el lema (β + 1) veces. -/

abbrev cl2 (a b c : Nat) : F := .imp (.imp (.atm c) (.atm b)) (.atm a)

theorem mem_swap {X Y D : F} {P : List F} (h : D ∈ X :: Y :: P) : D ∈ Y :: X :: P := by
  cases List.mem_cons.mp h with
  | inl e => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl e)))
  | inr h' =>
    cases List.mem_cons.mp h' with
    | inl e => exact List.mem_cons.mpr (Or.inl e)
    | inr h'' => exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr h'')))

-- c ⊃ b puede cambiarse por el hecho b
theorem J_to_b {b c : Nat} : ∀ n {P : List F} {G : F},
    Op n (.imp (.atm c) (.atm b) :: P) G → Op n (.atm b :: P) G := by
  intro n
  induction n with
  | zero => intro _ _ h; cases h
  | succ k ih =>
    intro P G h
    have inR : ∀ D, D ∈ P → D ∈ F.atm b :: P := fun D h => List.mem_cons.mpr (Or.inr h)
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [.imp (.atm c) (.atm b)]) (L₂ := P) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact Op.fact (Elab.mono inR e')
    | @back _ _ G' A e d =>
      cases Elab.split (L₁ := [.imp (.atm c) (.atm b)]) (L₂ := P) e with
      | inl e' =>
        rw [F.atm.inj (F.imp.inj (Elab.clause_only e')).2]
        exact Op.fact (Elab.mem mem0)
      | inr e' => exact Op.back (Elab.mono inR e') (ih d)
    | and d₁ d₂ => exact Op.and (ih d₁) (ih d₂)
    | orL d => exact Op.orL (ih d)
    | orR d => exact Op.orR (ih d)
    | @aug _ _ D G' d =>
      have d1 : Op k (.atm b :: D :: P) G' := ih (Op.mono k d (fun E hE => mem_swap hE))
      exact Op.aug (Op.mono k d1 (fun E hE => mem_swap hE))
    | @gen _ _ X G' A hA d =>
      have hA' : Fresh A (.atm b :: P) (.all X G') := ⟨fun D hD hocc => by
          cases List.mem_cons.mp hD with
          | inl e =>
            rw [e] at hocc
            exact hA.1 _ mem0 (Or.inr hocc)
          | inr h' => exact hA.1 D (List.mem_cons.mpr (Or.inr h')) hocc, hA.2⟩
      exact Op.gen hA' (ih d)

-- con c en R, K actúa como b ⊃ a (sin aumentar altura ni Augment)
theorem swap_K {a b c : Nat} : ∀ n {α : Nat} {R : List F} {G : F}, F.atm c ∈ R →
    OpA n α (cl2 a b c :: R) G → OpA n α (.imp (.atm b) (.atm a) :: R) G := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; cases h
  | succ k ih =>
    intro α R G hc h
    have inR : ∀ D, D ∈ R → D ∈ F.imp (.atm b) (.atm a) :: R :=
      fun D h => List.mem_cons.mpr (Or.inr h)
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [cl2 a b c]) (L₂ := R) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact OpA.fact (Elab.mono inR e')
    | @back _ _ _ G' A e d =>
      cases Elab.split (L₁ := [cl2 a b c]) (L₂ := R) e with
      | inr e' => exact OpA.back (Elab.mono inR e') (ih hc d)
      | inl e' =>
        have hx := F.imp.inj (Elab.clause_only e')
        rw [F.atm.inj hx.2]
        rw [hx.1] at d
        cases d with
        | @aug _ β _ _ _ d' =>
          have d1 : OpA _ β (cl2 a b c :: R) (.atm b) := OpA.mono _ d' (fun E hE => by
            cases List.mem_cons.mp hE with
            | inl e => rw [e]; exact List.mem_cons.mpr (Or.inr hc)
            | inr h' => exact h')
          have d2 := ih hc (OpA.lift d1 (Nat.le_succ _) (Nat.le_refl β))
          exact OpA.lift (OpA.back (Elab.mem mem0) d2) (Nat.le_refl _) (Nat.le_succ β)
    | and d₁ d₂ => exact OpA.and (ih hc d₁) (ih hc d₂)
    | orL d => exact OpA.orL (ih hc d)
    | orR d => exact OpA.orR (ih hc d)
    | @aug _ _ _ D G' d =>
      have d1 : OpA k _ (.imp (.atm b) (.atm a) :: D :: R) G' :=
        ih (List.mem_cons.mpr (Or.inr hc)) (OpA.mono k d (fun E hE => mem_swap hE))
      exact OpA.aug (OpA.mono k d1 (fun E hE => mem_swap hE))
    | @gen _ _ _ X G' A hA d =>
      have hA' : Fresh A (.imp (.atm b) (.atm a) :: R) (.all X G') := ⟨fun D hD hocc => by
          cases List.mem_cons.mp hD with
          | inl e =>
            rw [e] at hocc
            exact hA.1 _ mem0 ((hocc : F.occ A (.atm b) ∨ F.occ A (.atm a)).elim
              (fun h' => Or.inl (Or.inr h')) Or.inr)
          | inr h' => exact hA.1 D (List.mem_cons.mpr (Or.inr h')) hocc, hA.2⟩
      exact OpA.gen hA' (ih hc d)

theorem Nb_succ (m β x : Nat) : m + x * (β + 1) + 1 ≤ m + (x + 1) * (β + 1) := by
  have e : (x + 1) * (β + 1) = x * (β + 1) + (β + 1) := by
    rw [Nat.right_distrib, Nat.one_mul]
  omega

theorem Nb_mono (m β : Nat) {x y : Nat} (h : x ≤ y) : m + x * (β + 1) ≤ m + y * (β + 1) := by
  have := Nat.mul_le_mul h (Nat.le_refl (β + 1))
  omega

theorem bound_K (m β k α : Nat) :
    m + (k + m * α + m) * β + (k + m * α + m) ≤ m + (k + 1 + 1 + m * (α + 1)) * (β + 1) := by
  have e1 : (k + m * α + m) * (β + 1) = (k + m * α + m) * β + (k + m * α + m) := by
    rw [Nat.left_distrib, Nat.mul_one]
  have e2 : m * (α + 1) = m * α + m := by rw [Nat.left_distrib, Nat.mul_one]
  have h := Nat.mul_le_mul (show k + m * α + m ≤ k + 1 + 1 + m * (α + 1) by omega)
    (Nat.le_refl (β + 1))
  omega

-- P, (c ⊃ b) ⊢ᵐ_β a  y  K, Q ⊢ⁿ_α G  ⟹  P, Q ⊢^{m + (n + mα)(β + 1)} G
theorem cut_order2 {a b c m β : Nat} {P : List F}
    (hL : OpA m β (.imp (.atm c) (.atm b) :: P) (.atm a)) :
    ∀ n {α : Nat} {Q : List F} {G : F}, OpA n α (cl2 a b c :: Q) G →
      Op (m + (n + m * α) * (β + 1)) (P ++ Q) G := by
  have hb : Op m (.atm b :: P) (.atm a) := J_to_b m (OpA.toOp hL)
  intro n
  induction n with
  | zero => intro _ _ _ h; cases h
  | succ k ih =>
    intro α Q G h
    have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
    have up : ∀ {G'}, Op (m + (k + m * α) * (β + 1) + 1) (P ++ Q) G' →
        Op (m + (k + 1 + m * α) * (β + 1)) (P ++ Q) G' := fun d =>
      Op.lift d (Nat.le_trans (Nb_succ m β _) (Nb_mono m β (by omega)))
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [cl2 a b c]) (L₂ := Q) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact up (Op.fact (Elab.mono inR e'))
    | @back _ _ _ G' A e d =>
      cases Elab.split (L₁ := [cl2 a b c]) (L₂ := Q) e with
      | inr e' => exact up (Op.back (Elab.mono inR e') (ih d))
      | inl e' =>
        have hx := F.imp.inj (Elab.clause_only e')
        rw [F.atm.inj hx.2]
        rw [hx.1] at d
        cases d with
        | @aug k' α' _ _ _ d' =>
          have d1 : OpA k' α' (cl2 a b c :: F.atm c :: Q) (.atm b) :=
            OpA.mono _ d' (fun E hE => mem_swap hE)
          have d2 := swap_K k' (R := F.atm c :: Q) mem0 d1
          have d3 := cut_rule_ctx (a := a) (b := b) (cs := []) (P := P) hb α' k'
            (F.atm c :: Q) (.atm b) d2
          have d4 : Op (k' + m * α' + m) (F.atm c :: (P ++ Q)) (.atm b) :=
            Op.mono _ d3 (fun E hE => by
              cases List.mem_append.mp hE with
              | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
              | inr h =>
                cases List.mem_cons.mp h with
                | inl e => exact List.mem_cons.mpr (Or.inl e)
                | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))
          have d5 := cut_rule_ctx (a := b) (b := c) (cs := []) (P := P ++ Q) d4 β m P
            (.atm a) hL
          have d6 : Op (m + (k' + m * α' + m) * β + (k' + m * α' + m)) (P ++ Q) (.atm a) :=
            Op.mono _ d5 (fun E hE => by
              cases List.mem_append.mp hE with
              | inl h => exact h
              | inr h => exact List.mem_append.mpr (Or.inl h))
          exact Op.lift d6 (bound_K m β k' α')
    | and d₁ d₂ => exact up (Op.and (ih d₁) (ih d₂))
    | orL d => exact up (Op.orL (ih d))
    | orR d => exact up (Op.orR (ih d))
    | @aug _ α' _ D G' d =>
      have d1 : Op (m + (k + m * α') * (β + 1)) (P ++ D :: Q) G' :=
        ih (OpA.mono k d (fun E hE => mem_swap hE))
      have d2 : Op _ (D :: (P ++ Q)) G' := Op.mono _ d1 (fun E hE => by
        cases List.mem_append.mp hE with
        | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
        | inr h =>
          cases List.mem_cons.mp h with
          | inl e => exact List.mem_cons.mpr (Or.inl e)
          | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))
      have e2 : m * (α' + 1) = m * α' + m := by rw [Nat.left_distrib, Nat.mul_one]
      exact Op.lift (Op.aug d2) (Nat.le_trans (Nb_succ m β _) (Nb_mono m β (by omega)))
    | @gen _ _ _ X G' A hA d =>
      cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
      | intro B hB =>
        have d' := OpA.ren d (upd id A B)
        rw [map_ren_away (cl2 a b c :: Q) hA.1, sub_ren_away (G := G') hA.2] at d'
        exact up (Op.gen hB (ih d'))

/-! ## Orden 2 sobre A_{m,t}: K₂ = (d₀ ⊃ a) ⊃ c_t
  κ(K₂) ≤ 5t + 2, κ_{A,K₂}(c_t) ≤ m + 4 con un Augment, κ_A(c_t) > (m+5)t. -/

abbrev ruleK2 (m t : Nat) : F := .imp (ruleK m) (.atm (3 * t))

theorem amp_chainA (m t : Nat) {P : List F} (hP : ∀ D, D ∈ amp m t → D ∈ P) :
    ∀ i, i ≤ m + 1 → OpA (i + 1) 0 (.atm 2 :: P) (.atm (3 * i + 2)) := by
  intro i
  induction i with
  | zero => intro _; exact OpA.fact (Elab.mem mem0)
  | succ i ih =>
    intro hi
    have hm : F.imp (.atm (3 * i + 2)) (.atm (3 * (i + 1) + 2)) ∈ .atm 2 :: P :=
      List.mem_cons.mpr (Or.inr (hP _ (List.mem_cons.mpr (Or.inr
        (List.mem_append.mpr (Or.inl (dch_mem (by omega))))))))
    exact OpA.back (Elab.mem hm) (ih (by omega))

theorem order2_family (m t : Nat) :
    OpA (m + 4) 1 (ruleK2 m t :: amp m t) (.atm (3 * t)) ∧
    Op (5 * t + 2) (amp m t) (ruleK2 m t) ∧
    OpA (5 * t + 1) t (ruleK m :: amp m t) (.atm (3 * t)) ∧
    ¬ Op (lb (m + 5) t) (amp m t) (.atm (3 * t)) := by
  refine ⟨?_, ?_, amp_upperA m t t (Nat.le_refl _) _ (fun _ h => h), (amplification m t).2.2.2⟩
  · have d := amp_chainA m t (P := ruleK2 m t :: amp m t)
      (fun D hD => List.mem_cons.mpr (Or.inr hD)) (m + 1) (Nat.le_refl _)
    exact OpA.lift (OpA.back (Elab.mem mem0) (OpA.aug d)) (by omega) (Nat.le_refl _)
  · exact Op.lift (Op.aug (amp_upperK m t t (Nat.le_refl _) _ (fun _ h => h))) (by omega)

-- orden 2: ninguna cota κ_B(G) ≤ κ_{B,K}(G) + f(κ_B(K)), ni con α = 1
theorem order2_no_additive (f : Nat → Nat) : ∃ (B : List F) (K G : F) (n : Nat),
    OpA n 1 (K :: B) G ∧ Op 12 B K ∧ ¬ Op (n + f 12) B G := by
  refine ⟨amp (f 12) 2, ruleK2 (f 12) 2, .atm (3 * 2), f 12 + 4,
    (order2_family (f 12) 2).1, (order2_family (f 12) 2).2.1, fun h => ?_⟩
  have hl : lb (f 12 + 5) 2 = 2 * f 12 + 10 := by
    show 0 + (f 12 + 5) + (f 12 + 5) = 2 * f 12 + 10
    omega
  exact (order2_family (f 12) 2).2.2.2 (Op.lift h (by rw [hl]; omega))

/-! ## Lemas de orden k (H10)
  K₀ = a₀, K_{k+1} = K_k ⊃ a_{k+1}. Con K_{k-1} en el programa, K_{k+1} actúa como
  a_k ⊃ a_{k+1}; cada uso externo paga un corte de orden k. -/

-- cadena encajada a la izquierda
def chn (f : Nat → Nat) : Nat → F
  | 0     => .atm (f 0)
  | k + 1 => .imp (chn f k) (.atm (f (k + 1)))

-- D ⊃ b puede cambiarse por el hecho b
theorem strengthD {D : F} {b : Nat} : ∀ n {P : List F} {G : F},
    Op n (.imp D (.atm b) :: P) G → Op n (.atm b :: P) G := by
  intro n
  induction n with
  | zero => intro _ _ h; cases h
  | succ k ih =>
    intro P G h
    have inR : ∀ E, E ∈ P → E ∈ F.atm b :: P := fun E h => List.mem_cons.mpr (Or.inr h)
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [.imp D (.atm b)]) (L₂ := P) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact Op.fact (Elab.mono inR e')
    | @back _ _ G' A e d =>
      cases Elab.split (L₁ := [.imp D (.atm b)]) (L₂ := P) e with
      | inl e' =>
        rw [F.atm.inj (F.imp.inj (Elab.clause_only e')).2]
        exact Op.fact (Elab.mem mem0)
      | inr e' => exact Op.back (Elab.mono inR e') (ih d)
    | and d₁ d₂ => exact Op.and (ih d₁) (ih d₂)
    | orL d => exact Op.orL (ih d)
    | orR d => exact Op.orR (ih d)
    | @aug _ _ D' G' d =>
      have d1 : Op k (.atm b :: D' :: P) G' := ih (Op.mono k d (fun E hE => mem_swap hE))
      exact Op.aug (Op.mono k d1 (fun E hE => mem_swap hE))
    | @gen _ _ X G' A hA d =>
      have hA' : Fresh A (.atm b :: P) (.all X G') := ⟨fun E hE hocc => by
          cases List.mem_cons.mp hE with
          | inl e =>
            rw [e] at hocc
            exact hA.1 _ mem0 (Or.inr hocc)
          | inr h' => exact hA.1 E (List.mem_cons.mpr (Or.inr h')) hocc, hA.2⟩
      exact Op.gen hA' (ih d)

-- con D en R, (D ⊃ b) ⊃ a actúa como b ⊃ a
theorem swapD {D : F} {a b : Nat} : ∀ n {α : Nat} {R : List F} {G : F}, D ∈ R →
    OpA n α (.imp (.imp D (.atm b)) (.atm a) :: R) G →
      OpA n α (.imp (.atm b) (.atm a) :: R) G := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; cases h
  | succ k ih =>
    intro α R G hc h
    have inR : ∀ E, E ∈ R → E ∈ F.imp (.atm b) (.atm a) :: R :=
      fun E h => List.mem_cons.mpr (Or.inr h)
    cases h with
    | fact e =>
      cases Elab.split (L₁ := [.imp (.imp D (.atm b)) (.atm a)]) (L₂ := R) e with
      | inl e' => cases Elab.clause_only e'
      | inr e' => exact OpA.fact (Elab.mono inR e')
    | @back _ _ _ G' A e d =>
      cases Elab.split (L₁ := [.imp (.imp D (.atm b)) (.atm a)]) (L₂ := R) e with
      | inr e' => exact OpA.back (Elab.mono inR e') (ih hc d)
      | inl e' =>
        have hx := F.imp.inj (Elab.clause_only e')
        rw [F.atm.inj hx.2]
        rw [hx.1] at d
        cases d with
        | @aug _ β _ _ _ d' =>
          have d1 : OpA _ β (.imp (.imp D (.atm b)) (.atm a) :: R) (.atm b) :=
            OpA.mono _ d' (fun E hE => by
              cases List.mem_cons.mp hE with
              | inl e => rw [e]; exact List.mem_cons.mpr (Or.inr hc)
              | inr h' => exact h')
          have d2 := ih hc (OpA.lift d1 (Nat.le_succ _) (Nat.le_refl β))
          exact OpA.lift (OpA.back (Elab.mem mem0) d2) (Nat.le_refl _) (Nat.le_succ β)
    | and d₁ d₂ => exact OpA.and (ih hc d₁) (ih hc d₂)
    | orL d => exact OpA.orL (ih hc d)
    | orR d => exact OpA.orR (ih hc d)
    | @aug _ _ _ D' G' d =>
      have d1 : OpA k _ (.imp (.atm b) (.atm a) :: D' :: R) G' :=
        ih (List.mem_cons.mpr (Or.inr hc)) (OpA.mono k d (fun E hE => mem_swap hE))
      exact OpA.aug (OpA.mono k d1 (fun E hE => mem_swap hE))
    | @gen _ _ _ X G' A hA d =>
      have hA' : Fresh A (.imp (.atm b) (.atm a) :: R) (.all X G') := ⟨fun E hE hocc => by
          cases List.mem_cons.mp hE with
          | inl e =>
            rw [e] at hocc
            exact hA.1 _ mem0 ((hocc : F.occ A (.atm b) ∨ F.occ A (.atm a)).elim
              (fun h' => Or.inl (Or.inr h')) Or.inr)
          | inr h' => exact hA.1 E (List.mem_cons.mpr (Or.inr h')) hocc, hA.2⟩
      exact OpA.gen hA' (ih hc d)

-- presupuesto de Augment ≤ altura
theorem OpA.of_op {n : Nat} {P : List F} {G : F} (h : Op n P G) : OpA n n P G := by
  induction h with
  | fact e => exact OpA.fact e
  | back e _ ih => exact OpA.lift (OpA.back e ih) (Nat.le_refl _) (Nat.le_succ _)
  | and _ _ ih₁ ih₂ => exact OpA.lift (OpA.and ih₁ ih₂) (Nat.le_refl _) (Nat.le_succ _)
  | orL _ ih => exact OpA.lift (OpA.orL ih) (Nat.le_refl _) (Nat.le_succ _)
  | orR _ ih => exact OpA.lift (OpA.orR ih) (Nat.le_refl _) (Nat.le_succ _)
  | aug _ ih => exact OpA.aug ih
  | gen hA _ ih => exact OpA.lift (OpA.gen hA ih) (Nat.le_refl _) (Nat.le_succ _)

-- cota del corte de orden k + 1
def Tk : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, m, _, n, α     => n + m * α + m
  | k + 1, m, β, n, α => n + Tk k (n + m * α + m) (n + m * α + m) m β

theorem Tk_mono (k : Nat) : ∀ {m β n α m' β' n' α' : Nat}, m ≤ m' → β ≤ β' → n ≤ n' →
    α ≤ α' → Tk k m β n α ≤ Tk k m' β' n' α' := by
  induction k with
  | zero =>
    intro m _ n α m' _ n' α' hm _ hn hα
    show n + m * α + m ≤ n' + m' * α' + m'
    have := Nat.mul_le_mul hm hα
    omega
  | succ k ih =>
    intro m β n α m' β' n' α' hm hβ hn hα
    show n + Tk k (n + m * α + m) (n + m * α + m) m β ≤
      n' + Tk k (n' + m' * α' + m') (n' + m' * α' + m') m' β'
    have h1 := Nat.mul_le_mul hm hα
    have h2 := ih (m := n + m * α + m) (m' := n' + m' * α' + m') (β := n + m * α + m)
      (β' := n' + m' * α' + m') (n := m) (n' := m') (α := β) (α' := β')
      (by omega) (by omega) hm hβ
    omega

-- P, K_k ⊢ᵐ_β a_{k+1}  y  K_{k+1}, Q ⊢ⁿ_α G  ⟹  P, Q ⊢^{T_k(m,β,n,α)} G
theorem cut_orderk (f : Nat → Nat) : ∀ k {m β : Nat} {P : List F},
    OpA m β (chn f k :: P) (.atm (f (k + 1))) →
    ∀ n {α : Nat} {Q : List F} {G : F}, OpA n α (chn f (k + 1) :: Q) G →
      Op (Tk k m β n α) (P ++ Q) G := by
  intro k
  induction k with
  | zero =>
    intro m _ P hL n α Q G h
    exact cut_rule_ctx (a := f 1) (b := f 0) (cs := []) (P := P) (OpA.toOp hL) α n Q G h
  | succ k ihk =>
    intro m β P hL
    have hb : Op m (.atm (f (k + 1)) :: P) (.atm (f (k + 1 + 1))) := strengthD m (OpA.toOp hL)
    intro n
    induction n with
    | zero => intro _ _ _ h; cases h
    | succ j ih =>
      intro α Q G h
      have inR : ∀ D, D ∈ Q → D ∈ P ++ Q := fun D h => List.mem_append.mpr (Or.inr h)
      have up : ∀ {α' : Nat} {G' : F}, α' ≤ α → Op (Tk (k + 1) m β j α' + 1) (P ++ Q) G' →
          Op (Tk (k + 1) m β (j + 1) α) (P ++ Q) G' := by
        intro α' G' hα d
        refine Op.lift d ?_
        have h1 := Nat.mul_le_mul (Nat.le_refl m) hα
        have h2 := Tk_mono k (m := j + m * α' + m) (m' := j + 1 + m * α + m)
          (β := j + m * α' + m) (β' := j + 1 + m * α + m) (n := m) (n' := m) (α := β) (α' := β)
          (by omega) (by omega) (Nat.le_refl _) (Nat.le_refl _)
        show j + Tk k (j + m * α' + m) (j + m * α' + m) m β + 1 ≤
          j + 1 + Tk k (j + 1 + m * α + m) (j + 1 + m * α + m) m β
        omega
      cases h with
      | fact e =>
        cases Elab.split (L₁ := [chn f (k + 1 + 1)]) (L₂ := Q) e with
        | inl e' => cases Elab.clause_only e'
        | inr e' => exact up (Nat.le_refl _) (Op.fact (Elab.mono inR e'))
      | @back _ _ _ G' A e d =>
        cases Elab.split (L₁ := [chn f (k + 1 + 1)]) (L₂ := Q) e with
        | inr e' => exact up (Nat.le_refl _) (Op.back (Elab.mono inR e') (ih d))
        | inl e' =>
          have hx := F.imp.inj (Elab.clause_only e')
          rw [F.atm.inj hx.2]
          have d0 : OpA j α (chn f (k + 1 + 1) :: Q) (.imp (chn f k) (.atm (f (k + 1)))) := by
            rw [hx.1] at d; exact d
          cases d0 with
          | @aug k' α' _ _ _ d' =>
            have d1 : OpA k' α' (chn f (k + 1 + 1) :: chn f k :: Q) (.atm (f (k + 1))) :=
              OpA.mono _ d' (fun E hE => mem_swap hE)
            have d2 := swapD (D := chn f k) (a := f (k + 1 + 1)) (b := f (k + 1)) k'
              (R := chn f k :: Q) mem0 d1
            have d3 := cut_rule_ctx (a := f (k + 1 + 1)) (b := f (k + 1)) (cs := []) (P := P)
              hb α' k' (chn f k :: Q) (.atm (f (k + 1))) d2
            have d4 : Op (k' + m * α' + m) (chn f k :: (P ++ Q)) (.atm (f (k + 1))) :=
              Op.mono _ d3 (fun E hE => by
                cases List.mem_append.mp hE with
                | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
                | inr h =>
                  cases List.mem_cons.mp h with
                  | inl e => exact List.mem_cons.mpr (Or.inl e)
                  | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))
            have d5 := ihk (OpA.of_op d4) m (Q := P) (G := .atm (f (k + 1 + 1))) hL
            have d6 : Op (Tk k (k' + m * α' + m) (k' + m * α' + m) m β) (P ++ Q)
                (.atm (f (k + 1 + 1))) :=
              Op.mono _ d5 (fun E hE => by
                cases List.mem_append.mp hE with
                | inl h => exact h
                | inr h => exact List.mem_append.mpr (Or.inl h))
            have e3 : m * (α' + 1) = m * α' + m := by rw [Nat.left_distrib, Nat.mul_one]
            have hL' : k' + m * α' + m ≤ k' + 1 + 1 + m * (α' + 1) + m := by omega
            have hT := Tk_mono k (m := k' + m * α' + m) (m' := k' + 1 + 1 + m * (α' + 1) + m)
              (β := k' + m * α' + m) (β' := k' + 1 + 1 + m * (α' + 1) + m) (n := m) (n' := m)
              (α := β) (α' := β) hL' hL' (Nat.le_refl _) (Nat.le_refl _)
            refine Op.lift d6 ?_
            show Tk k (k' + m * α' + m) (k' + m * α' + m) m β ≤
              k' + 1 + 1 + Tk k (k' + 1 + 1 + m * (α' + 1) + m)
                (k' + 1 + 1 + m * (α' + 1) + m) m β
            omega
      | and d₁ d₂ => exact up (Nat.le_refl _) (Op.and (ih d₁) (ih d₂))
      | orL d => exact up (Nat.le_refl _) (Op.orL (ih d))
      | orR d => exact up (Nat.le_refl _) (Op.orR (ih d))
      | @aug _ α' _ D G' d =>
        have d1 : Op (Tk (k + 1) m β j α') (P ++ D :: Q) G' :=
          ih (OpA.mono j d (fun E hE => mem_swap hE))
        have d2 : Op _ (D :: (P ++ Q)) G' := Op.mono _ d1 (fun E hE => by
          cases List.mem_append.mp hE with
          | inl h => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
          | inr h =>
            cases List.mem_cons.mp h with
            | inl e => exact List.mem_cons.mpr (Or.inl e)
            | inr h' => exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr h'))))
        exact up (Nat.le_succ α') (Op.aug d2)
      | @gen _ _ _ X G' A hA d =>
        cases (show ∃ B, Fresh B (P ++ Q) (.all X G') from ⟨_, fresh_exists _ _⟩) with
        | intro B hB =>
          have d' := OpA.ren d (upd id A B)
          rw [map_ren_away (chn f (k + 1 + 1) :: Q) hA.1, sub_ren_away (G := G') hA.2] at d'
          exact up (Nat.le_refl _) (Op.gen hB (ih d'))

/-! ## H19: búsqueda acotada decidible -/

-- átomos de f
def F.atoms : F → List Nat
  | .atm a   => [a]
  | .var _   => []
  | .imp f g => f.atoms ++ g.atoms
  | .and f g => f.atoms ++ g.atoms
  | .or f g  => f.atoms ++ g.atoms
  | .all _ f => f.atoms

theorem F.occ_atoms {a : Nat} (f : F) (h : f.occ a) : a ∈ f.atoms := by
  induction f with
  | atm b => have e : a = b := h; subst e; exact mem0
  | var _ => exact False.elim h
  | imp f g ihf ihg =>
    cases h with
    | inl h' => exact List.mem_append.mpr (Or.inl (ihf h'))
    | inr h' => exact List.mem_append.mpr (Or.inr (ihg h'))
  | and f g ihf ihg =>
    cases h with
    | inl h' => exact List.mem_append.mpr (Or.inl (ihf h'))
    | inr h' => exact List.mem_append.mpr (Or.inr (ihg h'))
  | or f g ihf ihg =>
    cases h with
    | inl h' => exact List.mem_append.mpr (Or.inl (ihf h'))
    | inr h' => exact List.mem_append.mpr (Or.inr (ihg h'))
  | all _ f ih => exact ih h

-- átomos de P
def atomsL : List F → List Nat
  | []     => []
  | D :: P => D.atoms ++ atomsL P

theorem mem_atomsL {a : Nat} {D : F} (P : List F) (hD : D ∈ P) (h : D.occ a) :
    a ∈ atomsL P := by
  induction P with
  | nil => cases hD
  | cons E P ih =>
    cases List.mem_cons.mp hD with
    | inl e => rw [e] at h; exact List.mem_append.mpr (Or.inl (F.occ_atoms E h))
    | inr h' => exact List.mem_append.mpr (Or.inr (ih h'))

-- σ fija los átomos de P ⟹ Pσ = P
theorem map_ren_fix {σ : Nat → Nat} (P : List F) (h : ∀ D, D ∈ P → ∀ a, D.occ a → σ a = a) :
    P.map (F.ren σ) = P := by
  induction P with
  | nil => rfl
  | cons D P ih =>
    simp only [List.map]
    rw [F.ren_congr D (τ := id) (fun a ha => h D mem0 a ha), F.ren_id,
      ih (fun E hE => h E (List.mem_cons.mpr (Or.inr hE)))]

-- fuera de S ↦ d
def into (S : List Nat) (d x : Nat) : Nat := if x ∈ S then x else d

theorem into_mem {S : List Nat} {d x : Nat} (h : x ∈ S) : into S d x = x := by
  unfold into
  split
  · rfl
  · contradiction

theorem into_in {S : List Nat} {d : Nat} (hd : d ∈ S) (x : Nat) : into S d x ∈ S := by
  unfold into
  split
  · assumption
  · exact hd

-- [P] con instancias en S
inductive ElabS (S : List Nat) (P : List F) : F → Prop where
  | mem   {D : F} : D ∈ P → ElabS S P D
  | andL  {D₁ D₂ : F} : ElabS S P (.and D₁ D₂) → ElabS S P D₁
  | andR  {D₁ D₂ : F} : ElabS S P (.and D₁ D₂) → ElabS S P D₂
  | headL {G D₁ D₂ : F} : ElabS S P (.imp G (.and D₁ D₂)) → ElabS S P (.imp G D₁)
  | headR {G D₁ D₂ : F} : ElabS S P (.imp G (.and D₁ D₂)) → ElabS S P (.imp G D₂)
  | curry {G G' D : F} : ElabS S P (.imp G (.imp G' D)) → ElabS S P (.imp (.and G G') D)
  | inst  {X : Nat} {D : F} {A : Nat} : A ∈ S → ElabS S P (.all X D) → ElabS S P (D.sub X A)
  | hinst {X : Nat} {G D : F} {A : Nat} : A ∈ S →
      ElabS S P (.imp G (.all X D)) → ElabS S P (.imp G (D.sub X A))

-- renombrar hacia S
theorem Elab.renS {S : List Nat} {σ : Nat → Nat} (hσ : ∀ x, σ x ∈ S) {P : List F} {D : F}
    (h : Elab P D) : ElabS S (P.map (F.ren σ)) (D.ren σ) := by
  induction h with
  | mem h => exact ElabS.mem (List.mem_map.mpr ⟨_, h, rfl⟩)
  | andL _ ih => exact ElabS.andL ih
  | andR _ ih => exact ElabS.andR ih
  | headL _ ih => exact ElabS.headL ih
  | headR _ ih => exact ElabS.headR ih
  | curry _ ih => exact ElabS.curry ih
  | @inst X D A _ ih =>
    rw [F.ren_sub]
    exact ElabS.inst (hσ A) ih
  | @hinst X G D A _ ih =>
    show ElabS S _ (F.imp (G.ren σ) ((D.sub X A).ren σ))
    rw [F.ren_sub]
    exact ElabS.hinst (hσ A) ih

-- ∃ booleano en listas
def anyL {α : Type} (p : α → Bool) : List α → Bool
  | []     => false
  | x :: l => p x || anyL p l

theorem anyL_iff {α : Type} (p : α → Bool) :
    ∀ l : List α, anyL p l = true ↔ ∃ x, x ∈ l ∧ p x = true
  | [] => ⟨fun h => by simp [anyL] at h, fun ⟨_, h, _⟩ => by cases h⟩
  | x :: l => by
    show (p x || anyL p l) = true ↔ _
    rw [Bool.or_eq_true, anyL_iff p l]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨x, mem0, h⟩
      | inr h =>
        obtain ⟨y, hy, h⟩ := h
        exact ⟨y, List.mem_cons.mpr (Or.inr hy), h⟩
    · intro ⟨y, hy, h⟩
      cases List.mem_cons.mp hy with
      | inl e => rw [e] at h; exact Or.inl h
      | inr hy => exact Or.inr ⟨y, hy, h⟩

-- cuerpo acumulado
def comb : Option F → F → F
  | none, G'   => G'
  | some G, G' => .and G G'

def wrap : Option F → F → F
  | none, D   => D
  | some G, D => .imp G D

def okb (t : F → Bool) : Option F → Bool
  | none   => true
  | some G => t G

-- D (cuerpo o) da el hecho A o una regla G ⊃ A con t G
def bc (S : List Nat) (A : Nat) (t : F → Bool) : Nat → Option F → F → Bool
  | 0, _, _              => false
  | _ + 1, o, .atm a     => decide (a = A) && okb t o
  | k + 1, o, .imp G' D  => bc S A t k (some (comb o G')) D
  | k + 1, o, .and D₁ D₂ => bc S A t k o D₁ || bc S A t k o D₂
  | k + 1, o, .all X D   => anyL (fun a => bc S A t k o (D.sub X a)) S
  | _ + 1, _, .var _     => false
  | _ + 1, _, .or _ _    => false

theorem bc_atm {S : List Nat} {A : Nat} {t : F → Bool} (k : Nat) (o : Option F) (a : Nat) :
    bc S A t (k + 1) o (.atm a) = (decide (a = A) && okb t o) := rfl

theorem bc_imp {S : List Nat} {A : Nat} {t : F → Bool} (k : Nat) (o : Option F) (G' D : F) :
    bc S A t (k + 1) o (.imp G' D) = bc S A t k (some (comb o G')) D := rfl

theorem bc_and {S : List Nat} {A : Nat} {t : F → Bool} (k : Nat) (o : Option F) (D₁ D₂ : F) :
    bc S A t (k + 1) o (.and D₁ D₂) = (bc S A t k o D₁ || bc S A t k o D₂) := rfl

theorem bc_all {S : List Nat} {A : Nat} {t : F → Bool} (k : Nat) (o : Option F) (X : Nat)
    (D : F) : bc S A t (k + 1) o (.all X D) = anyL (fun a => bc S A t k o (D.sub X a)) S := rfl

theorem bc_mono {S : List Nat} {A : Nat} {t : F → Bool} :
    ∀ k k' (o : Option F) (D : F), k ≤ k' → bc S A t k o D = true → bc S A t k' o D = true := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; simp [bc] at h
  | succ k ih =>
    intro k' o D hk h
    cases k' with
    | zero => exact absurd hk (by omega)
    | succ k' =>
      cases D with
      | atm a => rw [bc_atm] at h ⊢; exact h
      | var _ => simp [bc] at h
      | or _ _ => simp [bc] at h
      | imp G' D =>
        rw [bc_imp] at h ⊢
        exact ih k' _ D (by omega) h
      | and D₁ D₂ =>
        rw [bc_and, Bool.or_eq_true] at h ⊢
        cases h with
        | inl h => exact Or.inl (ih k' o D₁ (by omega) h)
        | inr h => exact Or.inr (ih k' o D₂ (by omega) h)
      | all X D =>
        rw [bc_all, anyL_iff] at h ⊢
        obtain ⟨a, ha, h⟩ := h
        exact ⟨a, ha, ih k' o _ (by omega) h⟩

-- bc ⟹ hecho A o regla G ⊃ A en [P], con t G
theorem bc_sound {S : List Nat} {A : Nat} {t : F → Bool} {P : List F} :
    ∀ k (o : Option F) (D : F), Elab P (wrap o D) → bc S A t k o D = true →
      Elab P (.atm A) ∨ ∃ G, Elab P (.imp G (.atm A)) ∧ t G = true := by
  intro k
  induction k with
  | zero => intro _ _ _ h; simp [bc] at h
  | succ k ih =>
    intro o D e h
    cases D with
    | atm a =>
      rw [bc_atm, Bool.and_eq_true] at h
      have ha : a = A := of_decide_eq_true h.1
      rw [ha] at e
      cases o with
      | none => exact Or.inl e
      | some G => exact Or.inr ⟨G, e, h.2⟩
    | var _ => simp [bc] at h
    | or _ _ => simp [bc] at h
    | imp G' D =>
      rw [bc_imp] at h
      refine ih _ D ?_ h
      cases o with
      | none => exact e
      | some G => exact Elab.curry e
    | and D₁ D₂ =>
      rw [bc_and, Bool.or_eq_true] at h
      cases o with
      | none =>
        cases h with
        | inl h => exact ih none D₁ (Elab.andL e) h
        | inr h => exact ih none D₂ (Elab.andR e) h
      | some G =>
        cases h with
        | inl h => exact ih (some G) D₁ (Elab.headL e) h
        | inr h => exact ih (some G) D₂ (Elab.headR e) h
    | all X D =>
      rw [bc_all, anyL_iff] at h
      obtain ⟨a, _, h⟩ := h
      cases o with
      | none => exact ih none _ (Elab.inst a e) h
      | some G => exact ih (some G) _ (Elab.hinst a e) h

-- [P]_S ∋ E con bc ⟹ algún D ∈ P con bc (combustible |D|)
theorem bc_complete {S : List Nat} {A : Nat} {t : F → Bool} {P : List F} {E : F}
    (h : ElabS S P E) :
    bc S A t E.w none E = true → ∃ D, D ∈ P ∧ bc S A t D.w none D = true := by
  induction h with
  | mem hD => exact fun hE => ⟨_, hD, hE⟩
  | @andL D₁ D₂ _ ih =>
    intro hE
    apply ih
    rw [show (F.and D₁ D₂).w = (D₁.w + D₂.w) + 1 from rfl, bc_and, Bool.or_eq_true]
    exact Or.inl (bc_mono _ _ _ _ (by omega) hE)
  | @andR D₁ D₂ _ ih =>
    intro hE
    apply ih
    rw [show (F.and D₁ D₂).w = (D₁.w + D₂.w) + 1 from rfl, bc_and, Bool.or_eq_true]
    exact Or.inr (bc_mono _ _ _ _ (by omega) hE)
  | @headL G D₁ D₂ _ ih =>
    intro hE
    apply ih
    rw [show (F.imp G D₁).w = (G.w + 2 * D₁.w) + 1 from rfl, bc_imp] at hE
    have e : (F.imp G (F.and D₁ D₂)).w = (G.w + 2 * D₁.w + 2 * D₂.w + 1) + 1 + 1 := by
      simp only [F.w]; omega
    rw [e, bc_imp, bc_and, Bool.or_eq_true]
    exact Or.inl (bc_mono _ _ _ _ (by omega) hE)
  | @headR G D₁ D₂ _ ih =>
    intro hE
    apply ih
    rw [show (F.imp G D₂).w = (G.w + 2 * D₂.w) + 1 from rfl, bc_imp] at hE
    have e : (F.imp G (F.and D₁ D₂)).w = (G.w + 2 * D₁.w + 2 * D₂.w + 1) + 1 + 1 := by
      simp only [F.w]; omega
    rw [e, bc_imp, bc_and, Bool.or_eq_true]
    exact Or.inr (bc_mono _ _ _ _ (by omega) hE)
  | @curry G G' D _ ih =>
    intro hE
    apply ih
    rw [show (F.imp (F.and G G') D).w = (G.w + G'.w + 1 + 2 * D.w) + 1 from rfl, bc_imp] at hE
    have e : (F.imp G (F.imp G' D)).w = (G.w + 2 * G'.w + 4 * D.w + 1) + 1 + 1 := by
      simp only [F.w]; omega
    rw [e, bc_imp, bc_imp]
    simp only [comb] at hE ⊢
    exact bc_mono _ _ _ _ (by omega) hE
  | @inst X D a ha _ ih =>
    intro hE
    apply ih
    rw [F.w_sub] at hE
    rw [show (F.all X D).w = D.w + 1 from rfl, bc_all, anyL_iff]
    exact ⟨a, ha, hE⟩
  | @hinst X G D a ha _ ih =>
    intro hE
    apply ih
    rw [show (F.imp G (D.sub X a)).w = (G.w + 2 * (D.sub X a).w) + 1 from rfl, bc_imp,
      F.w_sub] at hE
    have e : (F.imp G (F.all X D)).w = (G.w + 2 * D.w + 1) + 1 + 1 := by
      simp only [F.w]; omega
    rw [e, bc_imp, bc_all, anyL_iff]
    exact ⟨a, ha, bc_mono _ _ _ _ (by omega) hE⟩

theorem bc_fact {S : List Nat} {A : Nat} {t : F → Bool} :
    bc S A t (F.atm A).w none (.atm A) = true := by
  show bc S A t (0 + 1) none (.atm A) = true
  rw [bc_atm]
  simp [okb]

theorem bc_rule {S : List Nat} {A : Nat} {t : F → Bool} {G : F} (h : t G = true) :
    bc S A t (F.imp G (.atm A)).w none (.imp G (.atm A)) = true := by
  have e : (F.imp G (.atm A)).w = (G.w + 1) + 1 + 1 := by simp only [F.w] <;> omega
  rw [e, bc_imp, bc_atm]
  simp [okb, comb, h]

-- decisión de Op n P G: instancias en los átomos de P y de la meta
def opB : Nat → List F → F → Bool
  | 0, _, _              => false
  | n + 1, P, .atm A     => anyL (fun D => bc (A :: atomsL P) A (fun G => opB n P G) D.w none D) P
  | _ + 1, _, .var _     => false
  | n + 1, P, .imp D G   => opB n (D :: P) G
  | n + 1, P, .and G₁ G₂ => opB n P G₁ && opB n P G₂
  | n + 1, P, .or G₁ G₂  => opB n P G₁ || opB n P G₂
  | n + 1, P, .all X G   => opB n P (G.sub X (bndL P + (F.all X G).bnd))

theorem opB_atm (n : Nat) (P : List F) (A : Nat) :
    opB (n + 1) P (.atm A) =
      anyL (fun D => bc (A :: atomsL P) A (fun G => opB n P G) D.w none D) P := rfl

theorem opB_var (n : Nat) (P : List F) (X : Nat) : opB (n + 1) P (.var X) = false := rfl

theorem opB_imp (n : Nat) (P : List F) (D G : F) :
    opB (n + 1) P (.imp D G) = opB n (D :: P) G := rfl

theorem opB_and (n : Nat) (P : List F) (G₁ G₂ : F) :
    opB (n + 1) P (.and G₁ G₂) = (opB n P G₁ && opB n P G₂) := rfl

theorem opB_or (n : Nat) (P : List F) (G₁ G₂ : F) :
    opB (n + 1) P (.or G₁ G₂) = (opB n P G₁ || opB n P G₂) := rfl

theorem opB_all (n : Nat) (P : List F) (X : Nat) (G : F) :
    opB (n + 1) P (.all X G) = opB n P (G.sub X (bndL P + (F.all X G).bnd)) := rfl

-- H19(a): ⊢^n decidible
theorem opB_iff : ∀ n (P : List F) (G : F), opB n P G = true ↔ Op n P G := by
  intro n
  induction n with
  | zero =>
    intro _ _
    constructor
    · intro h; simp [opB] at h
    · intro h; cases h
  | succ n ih =>
    intro P G
    cases G with
    | atm A =>
      constructor
      · intro h
        rw [opB_atm, anyL_iff] at h
        obtain ⟨D, hD, h⟩ := h
        have h' : bc (A :: atomsL P) A (fun G => opB n P G) D.w none D = true := h
        cases bc_sound D.w none D (Elab.mem hD) h' with
        | inl e => exact Op.fact e
        | inr k =>
          obtain ⟨G, e, hG⟩ := k
          exact Op.back e ((ih P G).mp hG)
      · intro h
        rw [opB_atm, anyL_iff]
        have hσ : ∀ x, into (A :: atomsL P) A x ∈ A :: atomsL P := into_in mem0
        have hfix : P.map (F.ren (into (A :: atomsL P) A)) = P :=
          map_ren_fix P (fun D hD a ha =>
            into_mem (List.mem_cons.mpr (Or.inr (mem_atomsL P hD ha))))
        have hA : into (A :: atomsL P) A A = A := into_mem mem0
        cases h with
        | fact e =>
          have e' := Elab.renS hσ e
          rw [hfix] at e'
          have q : (F.atm A).ren (into (A :: atomsL P) A) = .atm A := by
            show F.atm (into (A :: atomsL P) A A) = .atm A
            rw [hA]
          rw [q] at e'
          exact bc_complete (t := fun G => opB n P G) e' bc_fact
        | @back _ _ G _ e h' =>
          have e' := Elab.renS hσ e
          rw [hfix] at e'
          have q : (F.imp G (.atm A)).ren (into (A :: atomsL P) A) =
              .imp (G.ren (into (A :: atomsL P) A)) (.atm A) := by
            show F.imp (G.ren (into (A :: atomsL P) A)) (.atm (into (A :: atomsL P) A A)) = _
            rw [hA]
          rw [q] at e'
          have h'' := Op.ren h' (into (A :: atomsL P) A)
          rw [hfix] at h''
          exact bc_complete (t := fun G => opB n P G) e'
            (bc_rule (t := fun G => opB n P G) ((ih P _).mpr h''))
    | var X =>
      rw [opB_var]
      constructor
      · intro h; cases h
      · intro h; cases h
    | imp D G =>
      rw [opB_imp, ih (D :: P) G]
      constructor
      · exact Op.aug
      · intro h; cases h with | aug h => exact h
    | and G₁ G₂ =>
      rw [opB_and, Bool.and_eq_true, ih P G₁, ih P G₂]
      constructor
      · intro h; exact Op.and h.1 h.2
      · intro h; cases h with | and h₁ h₂ => exact ⟨h₁, h₂⟩
    | or G₁ G₂ =>
      rw [opB_or, Bool.or_eq_true, ih P G₁, ih P G₂]
      constructor
      · intro h
        cases h with
        | inl h => exact Op.orL h
        | inr h => exact Op.orR h
      · intro h
        cases h with
        | orL h => exact Or.inl h
        | orR h => exact Or.inr h
    | all X G =>
      rw [opB_all]
      constructor
      · intro h
        exact Op.gen (fresh_exists P (.all X G)) ((ih P _).mp h)
      · intro h
        cases h with
        | @gen _ _ _ _ A' hA h' =>
          have h'' := Op.ren h' (upd id A' (bndL P + (F.all X G).bnd))
          rw [map_ren_away P hA.1, sub_ren_away (G := G) hA.2] at h''
          exact (ih P _).mpr h''

instance instDecOp (n : Nat) (P : List F) (G : F) : Decidable (Op n P G) :=
  decidable_of_iff _ (opB_iff n P G)

-- una cota de coste da un procedimiento de decisión
theorem bound_decides (f : List F → F → Nat) (hf : ∀ P G, Der P G → Op (f P G) P G)
    (P : List F) (G : F) : Der P G ↔ opB (f P G) P G = true :=
  ⟨fun h => (opB_iff _ P G).mpr (hf P G h), fun h => ⟨_, (opB_iff _ P G).mp h⟩⟩

example : opB 2 [] (.imp (.atm 0) (.atm 0)) = true := rfl

/-! ## H19: segundo orden, ∀X sustitucional (Gheorghiu–Pym, aridad 0) -/

inductive Fm2 where
  | atom : Nat → Fm2
  | pvar : Nat → Fm2
  | bot  : Fm2
  | and  : Fm2 → Fm2 → Fm2
  | or   : Fm2 → Fm2 → Fm2
  | imp  : Fm2 → Fm2 → Fm2
  | all  : Nat → Fm2 → Fm2

-- φ[a/X]
def Fm2.sub (X a : Nat) : Fm2 → Fm2
  | .atom b  => .atom b
  | .pvar Y  => if Y = X then .atom a else .pvar Y
  | .bot     => .bot
  | .and φ ψ => .and (φ.sub X a) (ψ.sub X a)
  | .or φ ψ  => .or (φ.sub X a) (ψ.sub X a)
  | .imp φ ψ => .imp (φ.sub X a) (ψ.sub X a)
  | .all Y φ => if Y = X then .all Y φ else .all Y (φ.sub X a)

-- X libre en φ
def Fm2.fr (X : Nat) : Fm2 → Prop
  | .atom _  => False
  | .pvar Y  => Y = X
  | .bot     => False
  | .and φ ψ => φ.fr X ∨ ψ.fr X
  | .or φ ψ  => φ.fr X ∨ ψ.fr X
  | .imp φ ψ => φ.fr X ∨ ψ.fr X
  | .all Y φ => Y ≠ X ∧ φ.fr X

abbrev Fm2.closed (φ : Fm2) : Prop := ∀ X, ¬ φ.fr X

def Fm2.sz : Fm2 → Nat
  | .atom _  => 1
  | .pvar _  => 1
  | .bot     => 1
  | .and φ ψ => φ.sz + ψ.sz + 1
  | .or φ ψ  => φ.sz + ψ.sz + 1
  | .imp φ ψ => φ.sz + ψ.sz + 1
  | .all _ φ => φ.sz + 1

theorem Fm2.sz_pos (φ : Fm2) : 0 < φ.sz := by
  cases φ <;> simp only [Fm2.sz] <;> omega

theorem Fm2.sz_sub (X a : Nat) (φ : Fm2) : (φ.sub X a).sz = φ.sz := by
  induction φ with
  | atom b => rfl
  | pvar Y =>
    by_cases e : Y = X
    · rw [Fm2.sub, ite_eq_left e]; rfl
    · rw [Fm2.sub, ite_eq_right e]
  | bot => rfl
  | and φ ψ ihφ ihψ => simp only [Fm2.sub, Fm2.sz, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [Fm2.sub, Fm2.sz, ihφ, ihψ]
  | imp φ ψ ihφ ihψ => simp only [Fm2.sub, Fm2.sz, ihφ, ihψ]
  | all Y φ ih =>
    by_cases e : Y = X
    · rw [Fm2.sub, ite_eq_left e]
    · rw [Fm2.sub, ite_eq_right e]; simp only [Fm2.sz, ih]

theorem Fm2.fr_sub {X a Z : Nat} (φ : Fm2) (h : (φ.sub X a).fr Z) : φ.fr Z ∧ Z ≠ X := by
  induction φ with
  | atom b => exact False.elim h
  | pvar Y =>
    by_cases e : Y = X
    · rw [Fm2.sub, ite_eq_left e] at h; exact False.elim h
    · rw [Fm2.sub, ite_eq_right e] at h
      have hY : Y = Z := h
      subst hY
      exact ⟨rfl, e⟩
  | bot => exact False.elim h
  | and φ ψ ihφ ihψ =>
    cases h with
    | inl h' => have := ihφ h'; exact ⟨Or.inl this.1, this.2⟩
    | inr h' => have := ihψ h'; exact ⟨Or.inr this.1, this.2⟩
  | or φ ψ ihφ ihψ =>
    cases h with
    | inl h' => have := ihφ h'; exact ⟨Or.inl this.1, this.2⟩
    | inr h' => have := ihψ h'; exact ⟨Or.inr this.1, this.2⟩
  | imp φ ψ ihφ ihψ =>
    cases h with
    | inl h' => have := ihφ h'; exact ⟨Or.inl this.1, this.2⟩
    | inr h' => have := ihψ h'; exact ⟨Or.inr this.1, this.2⟩
  | all Y φ ih =>
    by_cases e : Y = X
    · rw [Fm2.sub, ite_eq_left e] at h
      have h' : Y ≠ Z ∧ φ.fr Z := h
      exact ⟨h', fun hz => h'.1 (e.trans hz.symm)⟩
    · rw [Fm2.sub, ite_eq_right e] at h
      have h' : Y ≠ Z ∧ (φ.sub X a).fr Z := h
      have := ih h'.2
      exact ⟨And.intro h'.1 this.1, this.2⟩

theorem Fm2.closed_inst {X a : Nat} {φ : Fm2} (h : (Fm2.all X φ).closed) :
    (φ.sub X a).closed := by
  intro Z hZ
  have h2 := Fm2.fr_sub φ hZ
  exact h Z (And.intro (fun e => h2.2 e.symm) h2.1)

-- ⟦·⟧: X ↦ var (X+1); var 0 queda para ∨ y ⊥
def enc2 : Fm2 → F
  | .atom a  => .atm a
  | .pvar X  => .var (X + 1)
  | .bot     => .all 0 (.var 0)
  | .and φ ψ => .and (enc2 φ) (enc2 ψ)
  | .or φ ψ  => .all 0 (orB (enc2 φ) (enc2 ψ))
  | .imp φ ψ => .imp (enc2 φ) (enc2 ψ)
  | .all X φ => .all (X + 1) (enc2 φ)

theorem enc2_neutral : ∀ (φ : Fm2), (enc2 φ).neutral
  | .atom _ => trivial
  | .pvar _ => trivial
  | .bot => trivial
  | .and φ ψ => And.intro (enc2_neutral φ) (enc2_neutral ψ)
  | .imp φ ψ => And.intro (enc2_neutral φ) (enc2_neutral ψ)
  | .or φ ψ => And.intro (And.intro (And.intro (enc2_neutral φ) trivial)
      (And.intro (enc2_neutral ψ) trivial)) trivial
  | .all _ φ => enc2_neutral φ

-- libres de ⟦φ⟧: X + 1 con X libre en φ
theorem enc2_fr : ∀ (φ : Fm2) (Y : Nat), (enc2 φ).fr Y → ∃ X, Y = X + 1 ∧ φ.fr X
  | .atom _, _, h => False.elim h
  | .pvar X, _, h => ⟨X, Eq.symm h, rfl⟩
  | .bot, _, h => False.elim (And.left h (And.right h))
  | .and φ ψ, Y, h => Or.elim h
      (fun h' => (enc2_fr φ Y h').elim (fun X k => ⟨X, k.1, Or.inl k.2⟩))
      (fun h' => (enc2_fr ψ Y h').elim (fun X k => ⟨X, k.1, Or.inr k.2⟩))
  | .imp φ ψ, Y, h => Or.elim h
      (fun h' => (enc2_fr φ Y h').elim (fun X k => ⟨X, k.1, Or.inl k.2⟩))
      (fun h' => (enc2_fr ψ Y h').elim (fun X k => ⟨X, k.1, Or.inr k.2⟩))
  | .or φ ψ, Y, h =>
    have h0 : (0 : Nat) ≠ Y := And.left h
    Or.elim (And.right h)
      (fun k => Or.elim k
        (fun k₁ => Or.elim k₁
          (fun h' => (enc2_fr φ Y h').elim (fun X q => ⟨X, q.1, Or.inl q.2⟩))
          (fun e => absurd e h0))
        (fun k₂ => Or.elim k₂
          (fun h' => (enc2_fr ψ Y h').elim (fun X q => ⟨X, q.1, Or.inr q.2⟩))
          (fun e => absurd e h0)))
      (fun e => absurd e h0)
  | .all X φ, Y, h => (enc2_fr φ Y (And.right h)).elim (fun Z k =>
      ⟨Z, k.1, And.intro (fun e => And.left h (by rw [k.1, e])) k.2⟩)

theorem enc2_closed {φ : Fm2} (hc : φ.closed) : (enc2 φ).closed := fun Y hY =>
  (enc2_fr φ Y hY).elim (fun X k => hc X k.2)

theorem enc2_nfr0 (φ : Fm2) : ¬ (enc2 φ).fr 0 := fun h =>
  (enc2_fr φ 0 h).elim (fun _ k => absurd k.1 (by omega))

theorem orB_sub (e₁ e₂ : F) {Y : Nat} (a : Nat) (hY : ¬ (0 = Y)) :
    (orB e₁ e₂).sub Y a = orB (e₁.sub Y a) (e₂.sub Y a) := by
  show F.imp (F.and (F.imp (e₁.sub Y a) (if 0 = Y then F.atm a else F.var 0))
      (F.imp (e₂.sub Y a) (if 0 = Y then F.atm a else F.var 0)))
      (if 0 = Y then F.atm a else F.var 0) = _
  rw [ite_eq_right hY]

-- ⟦φ[a/X]⟧ = ⟦φ⟧[a/X+1]
theorem enc2_sub (X a : Nat) : ∀ (φ : Fm2), enc2 (φ.sub X a) = (enc2 φ).sub (X + 1) a
  | .atom _ => rfl
  | .pvar Y => by
    show enc2 (if Y = X then Fm2.atom a else Fm2.pvar Y) =
      (if Y + 1 = X + 1 then F.atm a else F.var (Y + 1))
    by_cases e : Y = X
    · have e1 : Y + 1 = X + 1 := by rw [e]
      rw [ite_eq_left e, ite_eq_left e1]
      rfl
    · have e1 : ¬ (Y + 1 = X + 1) := by omega
      rw [ite_eq_right e, ite_eq_right e1]
      rfl
  | .bot => by
    have h0 : ¬ (0 = X + 1) := by omega
    show F.all 0 (F.var 0) =
      (if 0 = X + 1 then F.all 0 (F.var 0) else F.all 0 ((F.var 0).sub (X + 1) a))
    rw [ite_eq_right h0]
    show F.all 0 (F.var 0) = F.all 0 (if 0 = X + 1 then F.atm a else F.var 0)
    rw [ite_eq_right h0]
  | .and φ ψ => by
    show F.and (enc2 (φ.sub X a)) (enc2 (ψ.sub X a)) =
      F.and ((enc2 φ).sub (X + 1) a) ((enc2 ψ).sub (X + 1) a)
    rw [enc2_sub X a φ, enc2_sub X a ψ]
  | .imp φ ψ => by
    show F.imp (enc2 (φ.sub X a)) (enc2 (ψ.sub X a)) =
      F.imp ((enc2 φ).sub (X + 1) a) ((enc2 ψ).sub (X + 1) a)
    rw [enc2_sub X a φ, enc2_sub X a ψ]
  | .or φ ψ => by
    have h0 : ¬ (0 = X + 1) := by omega
    show F.all 0 (orB (enc2 (φ.sub X a)) (enc2 (ψ.sub X a))) =
      (if 0 = X + 1 then F.all 0 (orB (enc2 φ) (enc2 ψ))
        else F.all 0 ((orB (enc2 φ) (enc2 ψ)).sub (X + 1) a))
    rw [ite_eq_right h0, orB_sub (enc2 φ) (enc2 ψ) a h0, enc2_sub X a φ, enc2_sub X a ψ]
  | .all Y φ => by
    show enc2 (if Y = X then Fm2.all Y φ else Fm2.all Y (φ.sub X a)) =
      (if Y + 1 = X + 1 then F.all (Y + 1) (enc2 φ)
        else F.all (Y + 1) ((enc2 φ).sub (X + 1) a))
    by_cases e : Y = X
    · have e1 : Y + 1 = X + 1 := by rw [e]
      rw [ite_eq_left e, ite_eq_left e1]
      rfl
    · have e1 : ¬ (Y + 1 = X + 1) := by omega
      rw [ite_eq_right e, ite_eq_right e1]
      show F.all (Y + 1) (enc2 (φ.sub X a)) = F.all (Y + 1) ((enc2 φ).sub (X + 1) a)
      rw [enc2_sub X a φ]

theorem dsj2_neutral (φ ψ : Fm2) (a : Nat) : (dsj (enc2 φ) (enc2 ψ) a).neutral :=
  And.intro (And.intro (enc2_neutral φ) trivial) (And.intro (enc2_neutral ψ) trivial)

theorem dsj2_closed {φ ψ : Fm2} (hφ : φ.closed) (hψ : ψ.closed) (a : Nat) :
    (dsj (enc2 φ) (enc2 ψ) a).closed :=
  closed_and (closed_imp (enc2_closed hφ) (closed_atm a))
    (closed_imp (enc2_closed hψ) (closed_atm a))

-- ⊩ con combustible k; ∀X: todas las instancias atómicas
def supp2 : Nat → List F → Fm2 → Prop
  | 0, _, _            => False
  | _ + 1, B, .atom a  => Der B (.atm a)
  | _ + 1, _, .pvar _  => False
  | _ + 1, B, .bot     => ∀ a, Der B (.atm a)
  | k + 1, B, .and φ ψ => supp2 k B φ ∧ supp2 k B ψ
  | k + 1, B, .imp φ ψ => ∀ C, Ext B C → supp2 k C φ → supp2 k C ψ
  | k + 1, B, .or φ ψ  => ∀ C, Ext B C → ∀ a : Nat,
      (∀ E, Ext C E → supp2 k E φ → Der E (.atm a)) →
      (∀ E, Ext C E → supp2 k E ψ → Der E (.atm a)) → Der C (.atm a)
  | k + 1, B, .all X φ => ∀ a, supp2 k B (φ.sub X a)

abbrev Supp2 (B : List F) (φ : Fm2) : Prop := supp2 φ.sz B φ

-- H19(b): Support is Search con ∀X
theorem sis2 : ∀ k (φ : Fm2) (B : List F), φ.sz ≤ k → φ.closed →
    (supp2 k B φ ↔ Der B (enc2 φ)) := by
  intro k
  induction k with
  | zero => intro φ _ hk _; exact absurd hk (by have := Fm2.sz_pos φ; omega)
  | succ k ih =>
    intro φ B hk hc
    cases φ with
    | atom a => exact Iff.rfl
    | pvar X => exact False.elim (hc X rfl)
    | bot =>
      constructor
      · intro h
        refine Der.gen (X := 0) (G := .var 0) (fresh_exists B (enc2 .bot)) ?_
        rw [F.sub_var]
        exact h _
      · intro h a
        have h' := Der.inv_all (X := 0) (G := .var 0) h a
        rw [F.sub_var] at h'
        exact h'
    | and φ ψ =>
      have h1 : φ.sz + ψ.sz + 1 ≤ k + 1 := hk
      have hcφ : φ.closed := fun X h => hc X (Or.inl h)
      have hcψ : ψ.closed := fun X h => hc X (Or.inr h)
      constructor
      · intro h
        exact Der.and ((ih φ B (by omega) hcφ).mp (And.left h))
          ((ih ψ B (by omega) hcψ).mp (And.right h))
      · intro h
        exact And.intro ((ih φ B (by omega) hcφ).mpr (Der.inv_and h).1)
          ((ih ψ B (by omega) hcψ).mpr (Der.inv_and h).2)
    | imp φ ψ =>
      have h1 : φ.sz + ψ.sz + 1 ≤ k + 1 := hk
      have hcφ : φ.closed := fun X h => hc X (Or.inl h)
      have hcψ : ψ.closed := fun X h => hc X (Or.inr h)
      constructor
      · intro h
        have d : Der (enc2 φ :: B) (enc2 φ) :=
          identity (enc2_neutral φ) (enc2_closed hcφ) (Elab.mem mem0)
        exact Der.aug ((ih ψ (enc2 φ :: B) (by omega) hcψ).mp
          (h (enc2 φ :: B) (Ext.cons _ B) ((ih φ (enc2 φ :: B) (by omega) hcφ).mpr d)))
      · intro h C hBC hφ
        have d := cut (enc2_neutral φ) (enc2_closed hcφ) ((ih φ C (by omega) hcφ).mp hφ)
          (Der.inv_imp h)
        exact (ih ψ C (by omega) hcψ).mpr
          (Der.mono d (fun D hD => (List.mem_append.mp hD).elim id (hBC D)))
    | or φ ψ =>
      have h1 : φ.sz + ψ.sz + 1 ≤ k + 1 := hk
      have hcφ : φ.closed := fun X h => hc X (Or.inl h)
      have hcψ : ψ.closed := fun X h => hc X (Or.inr h)
      constructor
      · intro h
        refine Der.gen (X := 0) (G := orB (enc2 φ) (enc2 ψ))
          (fresh_exists B (enc2 (.or φ ψ))) ?_
        rw [orB_inst (enc2_nfr0 φ) (enc2_nfr0 ψ)]
        apply Der.aug
        refine h _ (Ext.cons _ B) _ ?_ ?_
        · intro E hE hφ
          exact Der.back (Elab.andL (Elab.mem (hE _ mem0))) ((ih φ E (by omega) hcφ).mp hφ)
        · intro E hE hψ
          exact Der.back (Elab.andR (Elab.mem (hE _ mem0))) ((ih ψ E (by omega) hcψ).mp hψ)
      · intro h C hBC a k₁ k₂
        have h' := Der.inv_all (X := 0) (G := orB (enc2 φ) (enc2 ψ)) (Der.mono h hBC) a
        rw [orB_inst (enc2_nfr0 φ) (enc2_nfr0 ψ)] at h'
        have d := Der.inv_imp h'
        have d₁ : Der C (.imp (enc2 φ) (.atm a)) :=
          Der.aug (k₁ (enc2 φ :: C) (Ext.cons _ C) ((ih φ (enc2 φ :: C) (by omega) hcφ).mpr
            (identity (enc2_neutral φ) (enc2_closed hcφ) (Elab.mem mem0))))
        have d₂ : Der C (.imp (enc2 ψ) (.atm a)) :=
          Der.aug (k₂ (enc2 ψ :: C) (Ext.cons _ C) ((ih ψ (enc2 ψ :: C) (by omega) hcψ).mpr
            (identity (enc2_neutral ψ) (enc2_closed hcψ) (Elab.mem mem0))))
        have d' := cut (dsj2_neutral φ ψ a) (dsj2_closed hcφ hcψ a) (Der.and d₁ d₂) d
        exact Der.mono d' (fun _ hD => (List.mem_append.mp hD).elim id id)
    | all X φ =>
      have h1 : φ.sz + 1 ≤ k + 1 := hk
      have hinst : ∀ a, (φ.sub X a).sz ≤ k ∧ (φ.sub X a).closed := fun a =>
        ⟨by rw [Fm2.sz_sub]; omega, Fm2.closed_inst hc⟩
      constructor
      · intro h
        refine Der.gen (fresh_exists B (enc2 (.all X φ))) ?_
        rw [← enc2_sub]
        exact (ih _ B (hinst _).1 (hinst _).2).mp (h _)
      · intro h a
        have h' := Der.inv_all h a
        rw [← enc2_sub] at h'
        exact (ih _ B (hinst a).1 (hinst a).2).mpr h'

-- validez: soporte en toda base
abbrev Valid2 (φ : Fm2) : Prop := ∀ B, Supp2 B φ

theorem valid2_iff {φ : Fm2} (hc : φ.closed) : Valid2 φ ↔ Der [] (enc2 φ) :=
  ⟨fun h => (sis2 _ φ [] (Nat.le_refl _) hc).mp (h []),
   fun h B => (sis2 _ φ B (Nat.le_refl _) hc).mpr (Der.mono h (fun _ hD => by cases hD))⟩

-- H19(c): una cota κ ≤ f(|φ|) decidiría la validez de segundo orden
theorem valid2_decides (f : Nat → Nat)
    (hf : ∀ φ : Fm2, φ.closed → Valid2 φ → Op (f φ.sz) [] (enc2 φ))
    {φ : Fm2} (hc : φ.closed) : Valid2 φ ↔ opB (f φ.sz) [] (enc2 φ) = true :=
  ⟨fun h => (opB_iff _ _ _).mpr (hf φ hc h),
   fun h => (valid2_iff hc).mpr ⟨_, (opB_iff _ _ _).mp h⟩⟩

example : opB 3 [] (enc2 (.all 0 (.imp (.pvar 0) (.pvar 0)))) = true := rfl
example : opB 3 [] (enc2 (.all 0 (.pvar 0))) = false := rfl

end Clausal
