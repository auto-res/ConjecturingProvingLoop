

theorem P2_iff_P3_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ Topology.P3 (X := X) A := by
  constructor
  · intro hP2
    dsimp [Topology.P3] at *
    intro x hxA
    have hx_int_cl : x ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    have h_subset_cl : closure (interior (A : Set X)) ⊆ A := by
      have h_sub : (interior (A : Set X)) ⊆ A := interior_subset
      have h_cl : closure (interior (A : Set X)) ⊆ closure A := closure_mono h_sub
      simpa [hA_closed.closure_eq] using h_cl
    have h_subset_int :
        interior (closure (interior (A : Set X))) ⊆ interior A :=
      interior_mono h_subset_cl
    have hx_intA : x ∈ interior A := h_subset_int hx_int_cl
    simpa [hA_closed.closure_eq] using hx_intA
  · intro hP3
    dsimp [Topology.P2] at *
    intro x hxA
    have hx_int_clA : x ∈ interior (closure (A : Set X)) := hP3 hxA
    have hx_intA : x ∈ interior A := by
      simpa [hA_closed.closure_eq] using hx_int_clA
    have h_subset :
        interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) := by
      have h_open : IsOpen (interior (A : Set X)) := isOpen_interior
      have h_sub : interior (A : Set X) ⊆ closure (interior (A : Set X)) :=
        subset_closure
      exact interior_maximal h_sub h_open
    exact h_subset hx_intA