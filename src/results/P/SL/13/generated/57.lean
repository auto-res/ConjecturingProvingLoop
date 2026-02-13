

theorem Topology.P1_iff_closureInterior_eq_self_of_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) A ↔ closure (interior A) = (A : Set X) := by
  -- Start from the general characterization of `P1`
  have h₁ :
      Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) :=
    Topology.P1_iff_closure_eq_closureInterior (X := X) (A := A)
  -- Use the closedness of `A` to simplify `closure A`
  have h₂ :
      Topology.P1 (X := X) A ↔ (A : Set X) = closure (interior A) := by
    simpa [hA_closed.closure_eq] using h₁
  -- Re-express the equality in the desired order
  simpa [eq_comm] using h₂