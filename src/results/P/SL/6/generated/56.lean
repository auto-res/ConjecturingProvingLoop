

theorem P2_implies_P2_of_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P2 (interior A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hx
  -- Since `x ∈ interior A`, it is also in `A`.
  have hA : x ∈ (A : Set X) :=
    (interior_subset : interior A ⊆ A) hx
  -- Apply `P2` for `A` to obtain the desired membership.
  have h := hP2 hA
  -- Re-express the goal using `interior_interior`.
  simpa [interior_interior] using h