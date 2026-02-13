

theorem Topology.closure_subset_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 (X := X) A) :
    closure A ⊆ closure (interior A) := by
  -- From `P1` we know `A ⊆ closure (interior A)`.
  have h : (A : Set X) ⊆ closure (interior A) := hP1
  -- Taking closures preserves inclusions; simplify with `closure_closure`.
  simpa [closure_closure] using (closure_mono h)