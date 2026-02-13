

theorem Topology.closure_union_closure_right_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure B) = closure (A ∪ B) := by
  have hClosed : IsClosed (closure B) := isClosed_closure
  have h₁ := Topology.closure_union_right_closed (A := A) (B := closure B) hClosed
  calc
    closure (A ∪ closure B) = closure A ∪ closure B := by
      simpa using h₁
    _ = closure (A ∪ B) := by
      simpa [closure_union]