

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro h x hx
  -- First, use `h` to see that `closure A ⊆ closure (interior A)`,
  -- hence `x ∈ closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) := by
    have h_subset : closure A ⊆ closure (interior A) := by
      -- `closure_mono h : closure A ⊆ closure (closure (interior A))`
      -- but `closure (closure _)` simplifies to `closure _`
      simpa using (closure_mono h :
        closure A ⊆ closure (closure (interior A)))
    exact h_subset hx
  -- Next, enlarge once more: `closure (interior A) ⊆ closure (interior (closure A))`.
  have h_target :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    closure_mono
      (interior_mono (subset_closure : (A : Set X) ⊆ closure A))
  exact h_target hx₁

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι} {s : ι → Set X} (h : ∀ i, P1 (s i)) : P1 (⋃ i, s i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
  have hx_cl : x ∈ closure (interior (s i)) := (h i) hi
  have h_subset : closure (interior (s i)) ⊆ closure (interior (⋃ j, s j)) := by
    apply closure_mono
    have h_int : interior (s i) ⊆ interior (⋃ j, s j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact h_int
  exact h_subset hx_cl