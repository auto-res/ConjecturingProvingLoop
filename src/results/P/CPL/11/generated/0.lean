

theorem P1_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P1 A := by
  intro x hx
  exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) (hA hx)

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P3 A := by
  simpa [hA.interior_eq] using interior_mono (subset_closure : (A : Set X) ⊆ closure A)

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : P1 A) (hB : P1 B) : P1 (A ∪ B) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x` is in `A`
      have hx_closure : x ∈ closure (interior A) := hA hxA
      -- `closure (interior A)` is contained in `closure (interior (A ∪ B))`
      have h_sub :
          closure (interior A) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inl hy))
      exact h_sub hx_closure
  | inr hxB =>
      -- `x` is in `B`
      have hx_closure : x ∈ closure (interior B) := hB hxB
      -- `closure (interior B)` is contained in `closure (interior (A ∪ B))`
      have h_sub :
          closure (interior B) ⊆ closure (interior (A ∪ B)) :=
        closure_mono (interior_mono (by
          intro y hy
          exact Or.inr hy))
      exact h_sub hx_closure

theorem exists_open_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : ∃ U, IsOpen U ∧ U ⊆ A := by
  refine ⟨interior A, isOpen_interior, ?_⟩
  exact interior_subset

theorem P1_iff_closure_interior_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure A ⊆ closure (interior A) :=
      closure_minimal hP1 isClosed_closure
    have h₂ : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact le_antisymm h₂ h₁
  · intro h_eq
    have : (A : Set X) ⊆ closure (interior A) := by
      have hsub : (A : Set X) ⊆ closure A := subset_closure
      simpa [h_eq.symm] using hsub
    exact this