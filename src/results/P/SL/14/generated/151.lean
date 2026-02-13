

theorem Topology.closureInterior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, hence in `∅`.
    have h_subset : (interior A : Set X) ⊆ (∅ : Set X) := by
      have : (interior A : Set X) ⊆ closure (interior A) :=
        subset_closure
      simpa [h] using this
    have h_eq : (interior A : Set X) = (∅ : Set X) := by
      exact Set.Subset.antisymm h_subset (by simp)
    simpa using h_eq
  · intro h
    simpa [h, closure_empty]