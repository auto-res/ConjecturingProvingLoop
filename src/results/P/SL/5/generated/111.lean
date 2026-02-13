

theorem closure_inter_of_interiors_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  simpa using
    (closure_inter_subset
        (X := X)
        (A := interior (A : Set X))
        (B := interior B))