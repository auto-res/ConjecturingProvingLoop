

theorem P2_of_closed_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hClosed hP3
  intro x hxA
  -- From `P3 A` we have `x ∈ interior (closure A)`.
  have hx_int_closureA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Since `A` is closed, `closure A = A`.
  have h_closure_eq : closure (A : Set X) = A := hClosed.closure_eq
  -- Therefore `x ∈ interior A`.
  have hx_intA : x ∈ interior (A : Set X) := by
    simpa [h_closure_eq] using hx_int_closureA
  -- `interior A` is open and contained in `closure (interior A)`,
  -- hence it is contained in `interior (closure (interior A))`.
  have h_subset :
      interior (A : Set X) ⊆ interior (closure (interior (A : Set X))) :=
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior
  exact h_subset hx_intA