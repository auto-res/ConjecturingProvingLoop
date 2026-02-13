

theorem P1_closed_inter_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 (X:=X) A) (hA_closed : IsClosed A) : Topology.P1 (X:=X) (A ∩ interior A) := by
  -- Since `interior A ⊆ A`, the intersection is just `interior A`.
  have h_eq : (A ∩ interior A : Set X) = interior A := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨(interior_subset : interior A ⊆ A) hx, hx⟩
  simpa [h_eq] using (P1_interior (X := X) (A := A))

theorem P1_of_empty_eq {X : Type*} [TopologicalSpace X] {A : Set X} (hA : A = ∅) : Topology.P1 (X:=X) A := by
  simpa [hA] using (P1_empty (X := X))