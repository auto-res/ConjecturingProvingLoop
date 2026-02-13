

theorem P2_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P2 (interior A) := by
  intro hP2
  dsimp [Topology.P2] at hP2 ⊢
  intro x hx
  -- `hx` gives `x ∈ interior A`, hence `x ∈ A`
  have hxA : x ∈ A := (interior_subset : interior A ⊆ A) hx
  -- Use `hP2` to send `x` into the larger interior
  have hxTarget : x ∈ interior (closure (interior A)) := hP2 hxA
  -- Rewrite the goal using `interior_interior`
  simpa [interior_interior] using hxTarget