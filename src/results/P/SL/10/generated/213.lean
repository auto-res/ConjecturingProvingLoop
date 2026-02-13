

theorem Topology.interior_diff_eq_diff_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsOpen A) :
    interior (A \ B) = A \ closure B := by
  calc
    interior (A \ B) = interior (A ∩ Bᶜ) := by
      simpa [Set.diff_eq]
    _ = A ∩ interior (Bᶜ) := by
      simpa using
        Topology.interior_inter_open_left (X := X) (U := A) (A := Bᶜ) hA
    _ = A ∩ (closure B)ᶜ := by
      simpa [Topology.interior_compl_eq_compl_closure (X := X) (A := B)]
    _ = A \ closure B := by
      simpa [Set.diff_eq]