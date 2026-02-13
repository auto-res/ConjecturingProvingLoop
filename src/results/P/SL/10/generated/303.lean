

theorem Topology.interior_closure_union_closure_left_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (closure A ∪ B)) = interior (closure (A ∪ B)) := by
  have h :=
    Topology.closure_union_closure_left_eq_closure_union
      (X := X) (A := A) (B := B)
  simpa using congrArg (fun s : Set X => interior s) h