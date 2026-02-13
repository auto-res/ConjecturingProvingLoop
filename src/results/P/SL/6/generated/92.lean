

theorem interior_closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ B) : Set X))
      ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show `x ∈ interior (closure A)`.
  have hA : x ∈ interior (closure A) := by
    -- `(A ∩ B) ⊆ A`
    have hSub : (A ∩ B : Set X) ⊆ A := by
      intro y hy
      exact hy.1
    -- `closure (A ∩ B) ⊆ closure A`
    have hClSub : closure (A ∩ B : Set X) ⊆ closure A :=
      closure_mono hSub
    -- Now use monotonicity of `interior`.
    exact (interior_mono hClSub) hx
  -- Show `x ∈ interior (closure B)`.
  have hB : x ∈ interior (closure B) := by
    -- `(A ∩ B) ⊆ B`
    have hSub : (A ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    -- `closure (A ∩ B) ⊆ closure B`
    have hClSub : closure (A ∩ B : Set X) ⊆ closure B :=
      closure_mono hSub
    -- Apply monotonicity of `interior`.
    exact (interior_mono hClSub) hx
  exact And.intro hA hB