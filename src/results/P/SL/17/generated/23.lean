

theorem Topology.isOpen_of_isClosed_and_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) : IsOpen A := by
  have h_closure_subset : closure (interior A) ⊆ A := by
    have h_sub : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [hA_closed.closure_eq] using h_sub
  have h_int_subset : interior (closure (interior A)) ⊆ interior A :=
    interior_mono h_closure_subset
  have h_subset : A ⊆ interior A := by
    intro x hxA
    have : x ∈ interior (closure (interior A)) := hP2 hxA
    exact h_int_subset this
  have h_eq : interior A = A := by
    apply subset_antisymm
    · exact interior_subset
    · exact h_subset
  simpa [h_eq] using (isOpen_interior : IsOpen (interior A))