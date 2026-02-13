

theorem P1_interior {X} [TopologicalSpace X] {A : Set X} : P1 A → P1 (interior A) := by
  intro hP1
  intro x hx
  have : x ∈ closure (interior A) := hP1 (interior_subset hx)
  simpa [interior_interior] using this

theorem P1_interior_closure {X} [TopologicalSpace X] {A : Set X} : P1 (interior (closure A)) := by
  intro x hx
  have hx_cl : x ∈ closure (interior (closure A)) := subset_closure hx
  simpa [interior_interior] using hx_cl

theorem exists_P2_superset {X} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ P2 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ _, ?_⟩
  simpa using (P2_univ (X := X))