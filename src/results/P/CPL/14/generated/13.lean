

theorem P2_interior {X} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P2 (interior A) := by
  intro x hx
  -- From `x ∈ interior A`, we know `x ∈ A`.
  have hxA : x ∈ (A : Set X) := interior_subset hx
  -- Apply `P2 A` to get the desired membership.
  have hx_int : x ∈ interior (closure (interior A)) := hA hxA
  -- Simplify the goal using `interior_interior`.
  simpa [interior_interior] using hx_int

theorem P3_interior {X} [TopologicalSpace X] {A : Set X} (hA : P3 A) : P3 (interior A) := by
  intro x hx
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal subset_closure isOpen_interior
  exact hsubset hx