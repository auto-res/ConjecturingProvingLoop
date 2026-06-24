

theorem P3_of_P2 : ∀ {A : Set X}, P2 A → P3 A := by
  intro A hP2
  have h1 : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h2 : interior (closure (interior A)) ⊆ interior (closure A) := interior_mono h1
  exact Set.Subset.trans hP2 h2

theorem P1_iff_closure_eq : ∀ {A : Set X}, P1 A ↔ closure (interior A) = closure A := by
  intro A
  constructor
  · intro hP1
    -- `closure (interior A)` is contained in `closure A`
    have h₁ : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    -- `closure A` is contained in `closure (interior A)`
    have h₂ : closure A ⊆ closure (interior A) := by
      have : closure A ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using this
    exact Set.Subset.antisymm h₁ h₂
  · intro hEq
    dsimp [P1]
    have : A ⊆ closure A := subset_closure
    simpa [hEq] using this

theorem P2_union : ∀ {A B : Set X}, P2 A → P2 B → P2 (A ∪ B) := by
  intro A B hA hB
  dsimp [P2] at hA hB ⊢
  ----------------------------------------------------------------
  -- 1.  Prepare an inclusion putting `A` in the desired target.
  ----------------------------------------------------------------
  have hA_inner : interior A ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inl hx
  have hA_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
    closure_mono hA_inner
  have hA_int :
      interior (closure (interior A)) ⊆
        interior (closure (interior (A ∪ B))) :=
    interior_mono hA_closure
  have hA_final : A ⊆ interior (closure (interior (A ∪ B))) :=
    Set.Subset.trans hA hA_int
  ----------------------------------------------------------------
  -- 2.  Prepare an inclusion putting `B` in the desired target.
  ----------------------------------------------------------------
  have hB_inner : interior B ⊆ interior (A ∪ B) := by
    apply interior_mono
    intro x hx
    exact Or.inr hx
  have hB_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
    closure_mono hB_inner
  have hB_int :
      interior (closure (interior B)) ⊆
        interior (closure (interior (A ∪ B))) :=
    interior_mono hB_closure
  have hB_final : B ⊆ interior (closure (interior (A ∪ B))) :=
    Set.Subset.trans hB hB_int
  ----------------------------------------------------------------
  -- 3.  Combine the two inclusions.
  ----------------------------------------------------------------
  exact Set.union_subset hA_final hB_final

theorem exists_dense_P2 : ∀ {A : Set X}, ∃ B, B ⊆ A ∧ P2 B := by
  intro A
  refine ⟨(∅ : Set X), Set.empty_subset _, ?_⟩
  dsimp [P2]
  exact Set.empty_subset _

theorem P3_of_open : ∀ {A : Set X}, IsOpen A → P3 A := by
  intro A hAopen
  dsimp [P3]
  have : interior A ⊆ interior (closure A) := interior_mono subset_closure
  simpa [hAopen.interior_eq] using this

theorem P2_empty : P2 (∅ : Set X) := by
  dsimp [P2]
  exact Set.empty_subset _

theorem P3_univ : P3 (Set.univ : Set X) := by
  dsimp [P3]
  intro x hx
  simpa [closure_univ, interior_univ] using hx