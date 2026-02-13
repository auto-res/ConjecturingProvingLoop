

theorem nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro hInt
  -- From a point in `interior (closure A)` we obtain a point in `closure A`.
  have hCl : (closure (A : Set X)).Nonempty := by
    rcases hInt with ⟨x, hxInt⟩
    exact ⟨x, interior_subset hxInt⟩
  -- Use the equivalence between non-emptiness of `closure A` and of `A`.
  exact ((Topology.closure_nonempty_iff (X := X) (A := A)).1) hCl