

theorem P1_implies_P1_of_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (A : Set X) → Topology.P1 (interior A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hxInt
  -- From `x ∈ interior A`, we know `x ∈ A`.
  have hxA : x ∈ (A : Set X) :=
    (interior_subset : interior A ⊆ A) hxInt
  -- Apply `P1` for `A` to place `x` in `closure (interior A)`.
  have hxCl : x ∈ closure (interior A) := hP1 hxA
  -- Since `interior (interior A) = interior A`, the goal follows directly.
  simpa [interior_interior] using hxCl