

theorem closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) = (∅ : Set X) ↔
      interior (A : Set X) = (∅ : Set X) := by
  constructor
  · intro h
    -- Since `interior A ⊆ closure (interior A)`, the closure being empty
    -- forces `interior A` itself to be empty.
    have hsub : (interior (A : Set X) : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ closure (interior (A : Set X)) := subset_closure hx
      simpa [h] using this
    exact le_antisymm hsub (Set.empty_subset _)
  · intro h
    -- If `interior A` is empty, its closure is also empty.
    simpa [h, closure_empty] using rfl