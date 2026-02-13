

theorem Topology.closure_interior_nonempty_of_interior_nonempty {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    (interior A : Set X).Nonempty → (closure (interior A) : Set X).Nonempty := by
  rintro ⟨x, hxInt⟩
  exact ⟨x, subset_closure hxInt⟩