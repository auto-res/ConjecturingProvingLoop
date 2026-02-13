

theorem interior_complement_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) →
      interior ((Aᶜ) : Set X) = (∅ : Set X) := by
  intro hDense
  have hEq := interior_complement_eq_complement_closure (A := A)
  simpa [hDense, Set.compl_univ] using hEq