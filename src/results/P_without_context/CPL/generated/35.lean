

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  dsimp [P2, P3]
  -- first, identify `interior (closure (interior A))` with `interior A`
  have h_int :
      (interior (closure (interior A)) : Set X) = interior A := by
    apply Set.Subset.antisymm
    · -- `interior (closure (interior A)) ⊆ interior A`
      have h₁ : (closure (interior A) : Set X) ⊆ A := by
        have h₀ : (interior A : Set X) ⊆ A := interior_subset
        have : closure (interior A) ⊆ closure A := closure_mono h₀
        simpa [hA.closure_eq] using this
      exact interior_mono h₁
    · -- `interior A ⊆ interior (closure (interior A))`
      have h₁ : (interior A : Set X) ⊆ closure (interior A) := subset_closure
      have : interior (interior A) ⊆ interior (closure (interior A)) :=
        interior_mono h₁
      simpa [interior_interior] using this
  -- rewrite both sides with the identification
  simpa [h_int, hA.closure_eq]

theorem P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    apply Set.Subset.antisymm
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
    · -- `closure A ⊆ closure (interior A)`
      have h : (closure A : Set X) ⊆ closure (closure (interior A)) :=
        closure_mono hP1
      simpa [closure_closure] using h
  · intro h_eq
    have h : (A : Set X) ⊆ closure A := subset_closure
    simpa [h_eq.symm] using h

theorem interior_closure_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure (closure A)) = interior (closure A) := by
  simpa [closure_closure]

theorem closure_interior_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} : closure (interior (interior A)) = closure (interior A) := by
  simpa [interior_interior]

theorem P3_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → P3 A := by
  intro hP2
  have h : (interior (closure (interior A)) : Set X) ⊆ interior (closure A) :=
    interior_mono (closure_mono interior_subset)
  exact Set.Subset.trans hP2 h

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} : P1 A → P1 B → P1 (A ∪ B) := by
  intro hA hB
  dsimp [P1] at hA hB ⊢
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ A`
      have hxA' : x ∈ (closure (interior A) : Set X) := hA hxA
      have h_subset : (closure (interior A) : Set X) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono
          (by
            -- `A ⊆ A ∪ B`
            intro y hy
            exact Or.inl hy)
      exact h_subset hxA'
  | inr hxB =>
      -- `x ∈ B`
      have hxB' : x ∈ (closure (interior B) : Set X) := hB hxB
      have h_subset : (closure (interior B) : Set X) ⊆ closure (interior (A ∪ B)) := by
        apply closure_mono
        exact interior_mono
          (by
            -- `B ⊆ A ∪ B`
            intro y hy
            exact Or.inr hy)
      exact h_subset hxB'

theorem P2_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A ↔ P3 A := by
  dsimp [P2, P3]
  simpa [hA.interior_eq]