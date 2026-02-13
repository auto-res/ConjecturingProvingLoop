

theorem P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (closure A) → P3 A := by
  intro hP3cl
  intro x hxA
  have hx_closure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  have hx_int : (x : X) ∈ interior (closure (closure (A : Set X))) := hP3cl hx_closure
  simpa [closure_closure] using hx_int

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense (interior A)) : P1 A ↔ P2 A := by
  -- Obtain the closure equality from the density assumption.
  have h_eq : closure (interior (A : Set X)) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Use the previously proven equivalence and flip the sides.
  simpa using (P2_iff_P1_of_dense (A := A) h_eq).symm