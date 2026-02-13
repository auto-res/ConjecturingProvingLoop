

theorem Topology.frontier_closure_eq_empty_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    frontier (closure (A : Set X)) = (∅ : Set X) := by
  have h :=
    (Topology.frontier_closure_eq_closure_diff_interiorClosure (A := A))
  simpa [closure_closure, hOpen.interior_eq, Set.diff_self] using h