

theorem Topology.isClosed_iff_closure_subset_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed A ↔ closure A ⊆ A := by
  constructor
  · intro hClosed
    -- If `A` is closed, its closure is itself, hence the desired inclusion.
    have h_eq : closure A = A := hClosed.closure_eq
    have h_subset : (A : Set X) ⊆ A := subset_rfl
    simpa [h_eq] using (h_subset : (A : Set X) ⊆ A)
  · intro h_subset
    -- The inclusion `closure A ⊆ A` together with the opposite
    -- inclusion `A ⊆ closure A` yields equality, hence closedness.
    have h_eq : closure A = A := by
      apply subset_antisymm h_subset
      exact subset_closure
    -- Rewriting with this equality turns the known closedness of
    -- `closure A` into the closedness of `A`.
    have h_closed_closure : IsClosed (closure A) := isClosed_closure
    simpa [h_eq] using h_closed_closure