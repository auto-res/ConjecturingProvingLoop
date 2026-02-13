

theorem Topology.P3_implies_P1_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X := X) A) :
    Topology.P1 (X := X) A := by
  dsimp [Topology.P1, Topology.P3] at *
  intro x hxA
  -- From `P3`, `x` lies in the interior of `closure A`.
  have hx_int_closure : x ∈ interior (closure A) := hP3 hxA
  -- Since `A` is closed, `closure A = A`.
  have h_closure_eq : closure (A : Set X) = A := h_closed.closure_eq
  -- Hence `x` actually lies in `interior A`.
  have hx_int : x ∈ interior A := by
    simpa [h_closure_eq] using hx_int_closure
  -- The interior of a set is always contained in the closure of the interior.
  have h_subset : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  exact h_subset hx_int