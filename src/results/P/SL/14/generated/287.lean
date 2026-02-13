

theorem Topology.closure_union_closure_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∪ closure (B : Set X) : Set X) = closure (A ∪ B) := by
  calc
    closure (A ∪ closure (B : Set X) : Set X)
        = closure A ∪ closure (closure (B : Set X)) := by
          simpa using
            (closure_union (A := A) (B := closure (B : Set X)))
    _ = closure A ∪ closure B := by
          simpa [closure_closure]
    _ = closure (A ∪ B : Set X) := by
          simpa using (closure_union (A := A) (B := B)).symm