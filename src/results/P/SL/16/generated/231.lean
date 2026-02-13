

theorem Topology.closure_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (∅ : Set X) ↔ A = (∅ : Set X) := by
  constructor
  · intro h
    -- Show that `A` is contained in `∅`.
    have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure A := subset_closure hx
      simpa [h] using this
    -- Combine the two inclusions to obtain the equality.
    apply Set.Subset.antisymm h_subset
    intro x hx
    exact hx.elim
  · intro h
    simpa [h, closure_empty]