

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, which is `∅` by hypothesis.
    have h_subset : (interior (A : Set X)) ⊆ (∅ : Set X) := by
      have : (interior (A : Set X)) ⊆ closure (interior (A : Set X)) :=
        subset_closure
      simpa [h] using this
    -- Hence, `interior A = ∅`.
    exact Set.Subset.antisymm h_subset (Set.empty_subset _)
  · intro h
    -- Rewrite with `h` and simplify using `closure_empty`.
    simpa [h] using (closure_empty : closure (∅ : Set X) = (∅ : Set X))