

theorem P2_iff_P1_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hD : Dense A) : P2 A ↔ P1 A := by
  classical
  constructor
  · intro hP2
    exact P1_of_P2 hP2
  · intro hP1
    intro x hx
    have hcl : closure (interior A) = (Set.univ : Set X) := by
      have h_eq := (P1_iff_dense_interior (A := A)).1 hP1
      simpa [hD.closure_eq] using h_eq
    simpa [hcl, interior_univ] using (Set.mem_univ x)