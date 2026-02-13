

theorem Topology.interior_closure_interior_subset_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆
      interior (closure (interior (closure A))) := by
  -- The required inclusion follows from monotonicity with
  -- respect to the evident inclusion `A ⊆ closure A`.
  have h_mono :=
    Topology.interior_closure_interior_mono
      (X := X) (A := A) (B := closure A) (subset_closure : (A : Set X) ⊆ closure A)
  simpa using h_mono