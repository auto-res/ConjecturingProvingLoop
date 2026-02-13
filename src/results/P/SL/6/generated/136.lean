

theorem P3_of_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = closure A → Topology.P3 A := by
  intro hEq
  -- From the equality, `closure A` coincides with its interior and hence is open.
  have hOpen : IsOpen (closure (A : Set X)) := by
    have hOpenInt : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    simpa [hEq] using hOpenInt
  -- An open closure implies `P3` for the original set.
  exact Topology.closure_open_satisfies_P3 (A := A) hOpen