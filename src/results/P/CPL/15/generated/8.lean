

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro h
    exact closure_eq_of_P1 h
  · intro h_eq
    intro x hx
    have hx_closure : (x : X) ∈ closure A := subset_closure hx
    simpa [h_eq] using hx_closure

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : closure (interior A) = Set.univ) : P2 A := by
  intro x hx
  simpa [h_dense, interior_univ] using (Set.mem_univ x)