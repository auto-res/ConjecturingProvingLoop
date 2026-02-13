

theorem P2_of_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 (Aᶜ) := by
  intro hClosed
  simpa using P2_of_open (hClosed.isOpen_compl)

theorem P1_of_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = closure A) : P1 A := by
  intro x hx
  simpa [h] using (subset_closure : (A : Set X) ⊆ closure A) hx