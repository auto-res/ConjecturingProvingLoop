

theorem Topology.interior_inter_eq_inter
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    interior (A ∩ B) = interior A ∩ interior B := by
  ext x
  constructor
  · intro hx
    have hxA : x ∈ interior A := by
      have h_subset : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact (interior_mono h_subset) hx
    have hxB : x ∈ interior B := by
      have h_subset : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact (interior_mono h_subset) hx
    exact ⟨hxA, hxB⟩
  · intro hx
    have h_open : IsOpen (interior A ∩ interior B) :=
      IsOpen.inter isOpen_interior isOpen_interior
    have h_subset : (interior A ∩ interior B : Set X) ⊆ A ∩ B := by
      intro y hy
      exact ⟨interior_subset hy.1, interior_subset hy.2⟩
    have h_incl : (interior A ∩ interior B : Set X) ⊆
        interior (A ∩ B) := interior_maximal h_subset h_open
    exact h_incl hx