

theorem P2_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ A ⊆ interior (closure A) := by
  -- Since `A` is closed, its closure is itself.
  have h_closure_eq : closure (A : Set X) = A := hA.closure_eq
  constructor
  · -- `P2 A → A ⊆ interior (closure A)`
    intro hP2
    exact P3_of_P2 hP2
  · -- `A ⊆ interior (closure A) → P2 A`
    intro h_subset
    -- Rewrite the hypothesis using `closure A = A`.
    have h_subset' : (A : Set X) ⊆ interior A := by
      simpa [h_closure_eq] using h_subset
    -- Hence `A = interior A`, so `A` is open.
    have h_eq_int : (A : Set X) = interior A := by
      exact Set.Subset.antisymm h_subset' interior_subset
    have h_open : IsOpen (A : Set X) := by
      simpa [← h_eq_int] using (isOpen_interior : IsOpen (interior A))
    -- Open sets satisfy `P2`.
    exact P2_of_open (A := A) h_open

theorem P3_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 A ↔ A ⊆ interior A := by
  have h_closure_eq : (closure (A : Set X)) = A := hA.closure_eq
  simpa [P3, h_closure_eq]