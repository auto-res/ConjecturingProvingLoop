

theorem P3_closed_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) :
    Topology.P3 A ↔ IsOpen A := by
  constructor
  · intro hP3
    -- First, show `A ⊆ interior A`
    have h_sub : A ⊆ interior A := by
      intro x hx
      have : x ∈ interior (closure A) := hP3 hx
      simpa [hA.closure_eq] using this
    -- We always have `interior A ⊆ A`
    have h_sub' : interior A ⊆ A := interior_subset
    -- Hence `A = interior A`
    have h_eq : interior A = A := subset_antisymm h_sub' h_sub
    -- `interior A` is open, so `A` is open
    have h_open_int : IsOpen (interior A) := isOpen_interior
    simpa [h_eq] using h_open_int
  · intro hOpen
    exact Topology.isOpen_P3 hOpen