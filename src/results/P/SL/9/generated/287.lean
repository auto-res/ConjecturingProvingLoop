

theorem Topology.closure_interClosure_eq_interClosure {X : Type*} [TopologicalSpace X]
    (A B : Set X) :
    closure (closure (A : Set X) ∩ closure B) = closure A ∩ closure B := by
  have hA : IsClosed (closure (A : Set X)) := isClosed_closure
  have hB : IsClosed (closure B) := isClosed_closure
  simpa using
    (Topology.closure_inter_eq_inter_of_closed
        (A := closure A) (B := closure B) hA hB)