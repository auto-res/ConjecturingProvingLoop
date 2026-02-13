

theorem P1_implies_P2_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (Topology.P2 A ↔ Topology.P3 A) := by
  intro hP1
  -- Thanks to `P1`, the two closures coincide.
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  constructor
  · -- `P2 A → P3 A` is always true.
    intro hP2
    exact Topology.P2_implies_P3 (X := X) (A := A) hP2
  · -- Under `P1`, `P3 A` implies `P2 A`.
    intro hP3
    dsimp [Topology.P2]
    intro x hxA
    -- From `P3`, the point lies in `interior (closure A)`.
    have hx_int_clA : x ∈ interior (closure A) := hP3 hxA
    -- Rewrite via the closure equality supplied by `P1`.
    have hx_int : x ∈ interior (closure (interior A)) := by
      simpa [h_closure_eq] using hx_int_clA
    exact hx_int