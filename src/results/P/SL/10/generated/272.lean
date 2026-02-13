

theorem Topology.interior_diff_eq_diff_of_isClosed {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsClosed B) :
    interior (A \ B) = interior A \ B := by
  have hOpen : IsOpen (Bᶜ) := hB.isOpen_compl
  calc
    interior (A \ B) = interior (A ∩ Bᶜ) := by
      simpa [Set.diff_eq]
    _ = interior A ∩ Bᶜ := by
      simpa using
        Topology.interior_inter_open_right (X := X) (A := A) (U := Bᶜ) hOpen
    _ = interior A \ B := by
      simpa [Set.diff_eq, Set.inter_comm]