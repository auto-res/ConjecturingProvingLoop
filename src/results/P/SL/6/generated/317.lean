

theorem open_closure_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure B)) :
    IsOpen (closure (A : Set X) ∩ closure B) := by
  simpa using (hA.inter hB)