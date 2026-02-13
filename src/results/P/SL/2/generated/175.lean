

theorem Topology.closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) ⊆ closure (interior (closure (A : Set X))) := by
  -- First, note that `interior A ⊆ interior (closure A)` because `A ⊆ closure A`.
  have hInt : (interior A : Set X) ⊆ interior (closure (A : Set X)) := by
    have hSub : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    exact interior_mono hSub
  -- Taking closures preserves inclusions, yielding the desired statement.
  exact closure_mono hInt