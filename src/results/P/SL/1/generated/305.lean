

theorem Topology.closure_interior_eq_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClopen A) :
    closure (interior A) = (A : Set X) := by
  -- Since `A` is open, its interior is itself.
  have hInt : interior A = (A : Set X) := hA.2.interior_eq
  -- Since `A` is closed, its closure is itself.
  have hCl : closure A = (A : Set X) := hA.1.closure_eq
  -- Rewrite and conclude.
  simpa [hInt, hCl]