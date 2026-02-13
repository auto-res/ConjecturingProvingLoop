

theorem Topology.closure_interior_union_eq_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (A ∪ B) := by
  calc
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
      simpa using
        Topology.closure_interior_union_eq_closure_union
          (X := X) (A := A) (B := B) hA hB
    _ = closure (A ∪ B) := by
      simpa [closure_union] using
        (closure_union (A := A) (B := B)).symm