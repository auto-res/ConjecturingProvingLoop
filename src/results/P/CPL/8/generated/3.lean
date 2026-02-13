

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → P1 (closure A) := by
  intro hP1
  intro x hx
  -- Step 1: bring `x` from `closure A` into `closure (interior A)`.
  have hx₁ : x ∈ closure (interior A) := by
    have hsubset : (closure A : Set X) ⊆ closure (interior A) := by
      simpa [closure_closure] using (closure_mono hP1)
    exact hsubset hx
  -- Step 2: use monotonicity to land in the desired set.
  have hsubset₂ : closure (interior A) ⊆ closure (interior (closure A)) := by
    have h' : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono h'
  exact hsubset₂ hx₁

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior A = Set.univ) : P3 A := by
  intro x _
  have hx_int : x ∈ interior A := by
    simpa [h] using Set.mem_univ x
  exact (interior_mono subset_closure) hx_int

theorem P1_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (interior A) := by
  intro x hx
  have hx' : x ∈ interior (interior A) := by
    simpa [interior_interior] using hx
  exact subset_closure hx'