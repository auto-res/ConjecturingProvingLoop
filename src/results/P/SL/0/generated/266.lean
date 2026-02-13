

theorem closure_nonempty_of_nonempty {X : Type*} [TopologicalSpace X] {A : Set X} :
    (A : Set X).Nonempty → (closure (A : Set X)).Nonempty := by
  intro hA
  rcases hA with ⟨x, hx⟩
  exact ⟨x, subset_closure hx⟩