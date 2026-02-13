

theorem Topology.closure_interior_inter_eq_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) = closure (interior A ∩ interior B) := by
  have h := Topology.interior_inter_eq_inter (X := X) (A := A) (B := B)
  simpa using congrArg (fun s : Set X => closure s) h