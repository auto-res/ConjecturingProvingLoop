

theorem Topology.closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- `interior A` is contained in its closure, which is empty by assumption.
    have hsubset : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    -- Conclude that `interior A` itself is empty.
    exact Set.Subset.antisymm hsubset (Set.empty_subset _)
  · intro hInt
    -- Rewriting with `hInt` reduces the goal to `closure ∅ = ∅`.
    simpa [hInt, closure_empty]