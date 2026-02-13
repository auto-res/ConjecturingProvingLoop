

theorem Topology.P1_closure_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    Topology.P1 (X := X) (closure A) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  -- Use the equality of closures obtained from `P1`.
  have h_cl : closure (A : Set X) = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  -- Reinterpret `hx` via this equality.
  have hx' : x ∈ closure (interior A) := by
    simpa [h_cl] using hx
  -- Relate the two closures through monotonicity.
  have h_incl : closure (interior A) ⊆ closure (interior (closure A)) := by
    -- Since `interior A ⊆ interior (closure A)` ...
    have h_subset : (interior A : Set X) ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (X := X) (A := A)
    -- ... taking closures yields the desired inclusion.
    exact closure_mono h_subset
  exact h_incl hx'