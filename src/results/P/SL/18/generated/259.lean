

theorem closure_interior_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A : Set X) ∪ interior B) = closure (A ∪ B) := by
  have hIntA : interior (A : Set X) = A := hA.interior_eq
  have hIntB : interior (B : Set X) = B := hB.interior_eq
  simpa [hIntA, hIntB]