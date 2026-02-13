

theorem interior_closure_union_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A : Set X)) ∪ interior (B : Set X) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hIntClA =>
      -- Case `x ∈ interior (closure A)`
      have h_closure_subset :
          (closure (A : Set X)) ⊆ closure (A ∪ B) := by
        apply closure_mono
        intro y hy
        exact Or.inl hy
      exact (interior_mono h_closure_subset) hIntClA
  | inr hIntB =>
      -- Case `x ∈ interior B`
      -- First, `interior B ⊆ interior (A ∪ B)`
      have h_subset₁ : (B : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inr hy
      have hx_int_AuB : (x : X) ∈ interior (A ∪ B : Set X) :=
        (interior_mono h_subset₁) hIntB
      -- Next, `interior (A ∪ B) ⊆ interior (closure (A ∪ B))`
      have h_subset₂ :
          (A ∪ B : Set X) ⊆ closure (A ∪ B) := subset_closure
      exact (interior_mono h_subset₂) hx_int_AuB