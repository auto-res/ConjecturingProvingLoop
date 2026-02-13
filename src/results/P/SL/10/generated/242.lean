

theorem Topology.closure_union_closures_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ closure B) = closure (A ∪ B) := by
  have h₁ :
      closure (closure A ∪ closure B) = closure (A ∪ closure B) := by
    simpa using
      Topology.closure_union_closure_left_eq_closure_union
        (X := X) (A := A) (B := closure B)
  have h₂ : closure (A ∪ closure B) = closure (A ∪ B) := by
    simpa using
      Topology.closure_union_closure_right_eq_closure_union
        (X := X) (A := A) (B := B)
  simpa [h₁] using h₂