

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- Since `interior A ⊆ closure (interior A)`, the right-hand side being empty
    -- forces `interior A` itself to be empty.
    have hsubset : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    have hIntEmpty : interior A = (∅ : Set X) := by
      apply Set.eq_of_subset_of_subset hsubset
      intro x hx
      cases hx
    exact hIntEmpty
  · intro h
    -- If `interior A` is empty, its closure is also empty.
    simpa [h, closure_empty]