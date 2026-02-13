

theorem Topology.interior_inter_open_right {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB_open : IsOpen (B : Set X)) :
    interior ((A ∩ B) : Set X) = interior A ∩ B := by
  calc
    interior ((A ∩ B) : Set X)
        = interior A ∩ interior B := by
          simpa using interior_inter (A := A) (B := B)
    _ = interior A ∩ B := by
          simpa [hB_open.interior_eq]