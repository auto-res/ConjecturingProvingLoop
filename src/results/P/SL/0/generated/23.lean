

theorem P1_iff_eq_closure_interior_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed (A : Set X)) :
    Topology.P1 A ↔ (A : Set X) = closure (interior A) := by
  have h_cl : closure (A : Set X) = A := hA.closure_eq
  have h₁ : Topology.P1 A ↔ closure (A : Set X) = closure (interior A) :=
    Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)
  simpa [h_cl] using h₁