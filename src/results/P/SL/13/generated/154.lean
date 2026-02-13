

theorem Topology.interior_inter_open_left {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_open : IsOpen (A : Set X)) :
    interior ((A ∩ B) : Set X) = A ∩ interior B := by
  calc
    interior ((A ∩ B) : Set X) = interior A ∩ interior B := by
      simpa using interior_inter (A := A) (B := B)
    _ = A ∩ interior B := by
      simpa [hA_open.interior_eq]