

theorem Topology.closure_interior_union_subset_union_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∪ B) : Set X)) ⊆
      closure (A : Set X) ∪ closure (B : Set X) := by
  -- `interior (A ∪ B)` is contained in `A ∪ B`
  have h_subset : interior ((A ∪ B) : Set X) ⊆ (A ∪ B) := interior_subset
  -- Taking closures preserves this inclusion
  have h_closure :
      closure (interior ((A ∪ B) : Set X)) ⊆ closure (A ∪ B) :=
    closure_mono h_subset
  -- Rewrite `closure (A ∪ B)` as `closure A ∪ closure B`
  simpa [closure_union] using h_closure