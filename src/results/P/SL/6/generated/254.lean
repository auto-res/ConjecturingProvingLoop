

theorem open_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure B)) :
    IsOpen (closure (A ∪ B : Set X)) := by
  have h : IsOpen (closure A ∪ closure B) := hA.union hB
  simpa [closure_union] using h