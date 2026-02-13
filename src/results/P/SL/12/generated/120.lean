

theorem Topology.P3_of_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hB : B ⊆ interior (closure A)) :
    Topology.P3 (X := X) B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- Use the assumption `hB` to place `x` inside `interior (closure A)`.
  have hx_intA : x ∈ interior (closure A) := hB hxB
  -- Monotonicity: `closure A ⊆ closure B` because `A ⊆ B`.
  have h_closure_mono : closure A ⊆ closure B := closure_mono hAB
  -- Hence, `interior (closure A) ⊆ interior (closure B)`.
  have h_int_mono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure_mono
  -- Conclude that `x ∈ interior (closure B)`.
  exact h_int_mono hx_intA