

theorem P1_iff_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    have h₁ : closure (interior A) ⊆ closure A := by
      exact closure_mono interior_subset
    have h₂ : closure A ⊆ closure (interior A) := by
      have := closure_mono hP1
      simpa [closure_closure] using this
    exact subset_antisymm h₁ h₂
  · intro h_eq
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_closure