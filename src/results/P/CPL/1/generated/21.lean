

theorem closure_subset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P1 A) : closure (interior A) ⊆ closure A := by
  exact closure_mono (interior_subset : (interior A : Set X) ⊆ A)

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P3 A) : P1 (closure A) := by
  intro x hx
  have h_subset : (closure A : Set X) ⊆ closure (interior (closure A)) := by
    exact closure_mono (hA : (A : Set X) ⊆ interior (closure A))
  exact h_subset hx