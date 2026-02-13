

theorem isOpen_closure_interior_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense (interior A)) : IsOpen (closure (interior A)) := by
  -- By density, the closure of `interior A` is the whole space.
  have h_closure_eq : closure (interior A : Set X) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Since `univ` is open, the required set is open as well.
  simpa [h_closure_eq] using isOpen_univ