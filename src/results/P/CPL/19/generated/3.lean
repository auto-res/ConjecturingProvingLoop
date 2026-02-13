

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  intro x hx
  cases hx

theorem P2_idempotent {X : Type*} [TopologicalSpace X] {A : Set X} : P2 (interior (closure (interior A))) := by
  intro x hx
  -- First, note that the desired set enjoys the `P3` property
  have hP3 : P3 (interior (closure (interior A))) := by
    simpa using (P3_idempotent (A := interior A))
  -- Apply this inclusion to the given point
  have hmem : x ∈ interior (closure (interior (closure (interior A)))) := hP3 hx
  -- Re-express the goal using `interior_interior`
  simpa [interior_interior] using hmem

theorem P1_implies_dense {X : Type*} [TopologicalSpace X] {A : Set X} : P1 A → closure (interior A) = closure A := by
  intro hP1
  apply Set.Subset.antisymm
  ·
    exact closure_mono (interior_subset : interior A ⊆ A)
  ·
    have h : closure A ⊆ closure (closure (interior A)) := closure_mono hP1
    simpa [closure_closure] using h