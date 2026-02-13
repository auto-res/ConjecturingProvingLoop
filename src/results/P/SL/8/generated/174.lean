

theorem closureInterior_union_subset_union_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∪ B)) ⊆ closure A ∪ closure B := by
  -- `interior (A ∪ B)` is contained in `A ∪ B`.
  have h_subset : interior (A ∪ B) ⊆ A ∪ B := interior_subset
  -- Taking closures preserves inclusions.
  have h_closure : closure (interior (A ∪ B)) ⊆ closure (A ∪ B) :=
    closure_mono h_subset
  -- Express `closure (A ∪ B)` as the union of the closures of `A` and `B`.
  simpa [closure_union] using h_closure