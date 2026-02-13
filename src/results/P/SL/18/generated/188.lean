

theorem dense_iUnion_of_dense
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) (i₀ : ι)
    (hDense : Dense (A i₀)) :
    Dense (⋃ i, A i) := by
  classical
  intro x
  -- `hDense` tells us that `x` lies in the closure of `A i₀`.
  have hx : x ∈ closure (A i₀ : Set X) := hDense x
  -- Since `A i₀ ⊆ ⋃ i, A i`, the closures satisfy the analogous inclusion.
  have hSub : (A i₀ : Set X) ⊆ ⋃ i, A i := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i₀, hy⟩
  have hClosSub :
      closure (A i₀ : Set X) ⊆ closure (⋃ i, A i : Set X) :=
    closure_mono hSub
  -- Conclude that `x` lies in the desired closure.
  exact hClosSub hx