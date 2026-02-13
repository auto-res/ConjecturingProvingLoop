

theorem Topology.nonempty_closure_of_nonempty_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (closure (interior A)).Nonempty → (closure A).Nonempty := by
  intro h
  rcases h with ⟨x, hx⟩
  have h_subset : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (X := X) (A := A)
  exact ⟨x, h_subset hx⟩