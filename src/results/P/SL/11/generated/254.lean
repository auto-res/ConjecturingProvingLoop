

theorem closure_interior_union_eq_of_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (interior A) ∪ closure (interior B) := by
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  have hIntUnion : interior (A ∪ B) = A ∪ B := (hA.union hB).interior_eq
  simpa [hIntA, hIntB, hIntUnion, closure_union]