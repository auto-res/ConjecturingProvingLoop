

theorem Topology.interiorClosure_inter_eq_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (closure (A ∩ B : Set X)) = interior (A ∩ B) := by
  -- Since `A ∩ B` is closed, its closure is itself.
  have hClosure : closure (A ∩ B : Set X) = A ∩ B :=
    (IsClosed.inter hA hB).closure_eq
  simpa [hClosure]