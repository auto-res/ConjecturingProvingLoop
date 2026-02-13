

theorem Topology.interior_closure_interior_mono_to_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} (h : (A : Set X) ⊆ B) :
    interior (closure (interior A)) ⊆ interior (closure B) := by
  intro x hx
  -- First, use `interior_subset` to see that `interior A ⊆ B`.
  have hInt : (interior A : Set X) ⊆ B := by
    intro y hy
    exact h (interior_subset hy)
  -- Apply monotonicity of `interior ∘ closure`.
  have hIncl :=
    Topology.interior_closure_mono (X := X) (A := interior A) (B := B) hInt
  exact hIncl hx