

theorem Topology.interior_closure_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hOpen : IsOpen A) :
    interior (closure A) = A := by
  have h₁ : interior (closure A) = interior A := by
    simpa using
      Topology.interior_closure_eq_interior_of_closed (X := X) (A := A) hClosed
  have h₂ : interior A = A := hOpen.interior_eq
  simpa [h₁, h₂]