

theorem Topology.interior_subset_interiorClosureInterior {X : Type*} [TopologicalSpace X]
    (A : Set X) : interior A ⊆ interior (closure (interior A)) := by
  -- First, note that `interior A` is contained in its closure.
  have hSub : (interior A : Set X) ⊆ closure (interior A) := by
    intro x hx
    exact subset_closure hx
  -- Monotonicity of `interior` gives the desired inclusion.
  have h := interior_mono hSub
  simpa [interior_interior] using h