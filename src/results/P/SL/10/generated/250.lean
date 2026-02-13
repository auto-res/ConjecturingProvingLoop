

theorem Topology.interior_closure_congr_of_closure_eq {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure A = closure B → interior (closure A) = interior (closure B) := by
  intro h
  simpa [h]