

theorem Topology.interior_closure_inter_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    interior (closure (A ∩ B : Set X)) = interior (A ∩ B) := by
  -- The intersection of two closed sets is closed.
  have h_closed : IsClosed (A ∩ B : Set X) := hA.inter hB
  -- Apply the existing lemma for closed sets.
  simpa using
    Topology.interior_closure_eq_interior_of_isClosed
      (X := X) (A := (A ∩ B)) h_closed