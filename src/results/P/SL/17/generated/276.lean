

theorem Topology.closure_interior_closure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    closure (interior (closure A)) = closure A := by
  -- An open set satisfies `P3`.
  have hP3 : Topology.P3 A := Topology.P3_of_isOpen (A := A) hA
  -- Apply the existing lemma that turns `P3` into the desired equality.
  simpa using
    (Topology.closure_interior_closure_eq_closure_of_P3 (A := A) hP3)