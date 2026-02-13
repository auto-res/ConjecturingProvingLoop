

theorem Topology.interior_closure_diff_closure_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) \ closure A = (∅ : Set X) := by
  apply Set.Subset.antisymm
  · intro x hx
    have h_in_closure : x ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hx.1
    exact (hx.2 h_in_closure)
  · intro x hx
    cases hx