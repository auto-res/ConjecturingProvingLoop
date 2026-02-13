

theorem closure_interior_iterate_from_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) (n : ℕ) :
    Nat.iterate (fun S : Set X => closure (interior S)) (n.succ) (interior A) =
      closure (interior A) := by
  simpa [interior_interior]
    using closure_interior_iterate (X := X) (A := interior A) (n := n)