

theorem P2_iff_subset_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) :
    Topology.P2 A ↔ (A ⊆ interior (closure (A : Set X))) := by
  have h := (Topology.P3_iff_P2_of_isOpen (A := A) hA).symm
  simpa [Topology.P3] using h