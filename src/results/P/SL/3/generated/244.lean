

theorem boundary_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    closure (A : Set X) \ A =
      closure (A : Set X) ∩ closure ((Aᶜ) : Set X) := by
  simpa [hA.interior_eq] using
    (boundary_eq_closure_inter_closure_compl (A := A))