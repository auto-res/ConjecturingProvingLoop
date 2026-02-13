

theorem Topology.closureInterior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, which is empty by assumption.
    have h_subset : (interior (A : Set X)) ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior (A : Set X)) :=
        subset_closure hx
      simpa [h] using this
    exact Set.Subset.antisymm h_subset (Set.empty_subset _)
  · intro h_int
    simpa [h_int, closure_empty]