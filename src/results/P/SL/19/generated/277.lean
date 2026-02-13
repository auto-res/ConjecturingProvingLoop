

theorem Topology.closure_closure_union_closure_eq_closure_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (closure A ∪ closure B) = closure (A ∪ B) := by
  calc
    closure (closure A ∪ closure B)
        = closure (closure A) ∪ closure (closure B) := by
          simpa [closure_union]
    _ = closure A ∪ closure B := by
          simp [closure_closure]
    _ = closure (A ∪ B) := by
          simpa [closure_union]