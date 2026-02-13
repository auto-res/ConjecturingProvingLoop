

theorem Topology.interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → interior (closure A) = interior (closure (interior A)) := by
  intro hP2
  have h_cl_eq := Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hP2
  simpa using congrArg (fun s : Set X => interior s) h_cl_eq