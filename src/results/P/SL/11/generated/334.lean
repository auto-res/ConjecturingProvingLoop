

theorem closure_union_interior_eq_closure_union_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior A ∪ interior B : Set X) = closure (interior (A ∪ B)) := by
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  have hIntUnion : interior (A ∪ B) = A ∪ B := (hA.union hB).interior_eq
  simpa [hIntA, hIntB, hIntUnion]