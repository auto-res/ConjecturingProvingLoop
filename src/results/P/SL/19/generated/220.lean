

theorem Topology.frontier_eq_empty_of_isOpen_and_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hOpen : IsOpen A) (hClosed : IsClosed A) :
    frontier A = (∅ : Set X) := by
  have hClosure : closure A = A := hClosed.closure_eq
  have hInterior : interior A = A := hOpen.interior_eq
  simp [frontier, hClosure, hInterior]