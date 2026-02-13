

theorem closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro hCl
    -- `interior A` is contained in its closure, which is empty by assumption.
    have hSub : (interior A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ closure (interior A) := subset_closure hx
      simpa [hCl] using this
    -- Hence `interior A` itself is empty.
    exact (Set.Subset.antisymm hSub (Set.empty_subset _))
  · intro hInt
    -- If `interior A` is empty, so is its closure.
    simpa [hInt, closure_empty]