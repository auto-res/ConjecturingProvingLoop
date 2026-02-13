

theorem Topology.interior_closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  have h_cl_eq :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  simpa using congrArg (fun s : Set X => interior s) h_cl_eq