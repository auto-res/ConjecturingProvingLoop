

theorem interior_closure_inter_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P1 (interior (closure ((A ∩ B) : Set X))) := by
  simpa using
    (Topology.interior_closure_satisfies_P1 (A := (A ∩ B)))