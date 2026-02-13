

theorem Topology.closure_union_closure_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (closure (A : Set X) ∪ B) = closure (A ∪ B) := by
  calc
    closure (closure (A : Set X) ∪ B) =
        closure (closure (A : Set X)) ∪ closure B := by
      simpa using
        (closure_union (A := closure (A : Set X)) (B := B))
    _ = closure A ∪ closure B := by
      simpa [closure_closure]
    _ = closure (A ∪ B) := by
      simpa using (closure_union (A := A) (B := B)).symm