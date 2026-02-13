

theorem Topology.P1_of_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hB : B ⊆ closure (interior A)) :
    Topology.P1 (X := X) B := by
  dsimp [Topology.P1] at *
  intro x hxB
  -- `x` is in `closure (interior A)` by `hB`.
  have hx_closureA : x ∈ closure (interior A) := hB hxB
  -- From `A ⊆ B` we deduce `interior A ⊆ interior B`.
  have h_int : (interior A : Set X) ⊆ interior B := interior_mono hAB
  -- Taking closures yields the required inclusion.
  have h_closure : closure (interior A : Set X) ⊆ closure (interior B) :=
    closure_mono h_int
  -- Conclude that `x` is in `closure (interior B)`.
  exact h_closure hx_closureA