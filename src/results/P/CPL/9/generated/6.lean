

theorem P1_iterate {X : Type*} [TopologicalSpace X] {A : Set X} : P1 (closure (interior (closure (interior A)))) := by
  -- First, `interior (closure (interior A))` satisfies `P1`
  have h₁ : P1 (interior (closure (interior A))) := by
    simpa using (P1_interior (A := closure (interior A)))
  -- Hence its closure also satisfies `P1`
  exact (P1_closure (A := interior (closure (interior A)))) h₁

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : P2 A) : P2 (interior A) := by
  intro x hx
  have hmem : x ∈ interior (closure (interior A)) := hA (interior_subset hx)
  simpa [interior_interior] using hmem

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : P2 A) (hB : P2 B) (hC : P2 C) : P2 (A ∪ B ∪ C) := by
  have hAB : P2 (A ∪ B) := union_P2 hA hB
  exact union_P2 hAB hC