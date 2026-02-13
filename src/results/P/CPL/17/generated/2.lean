

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} : P2 A → P2 (e '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have hmem : (e x) ∈ (e '' interior (closure (interior A))) := ⟨x, hx, rfl⟩
  have h1 : (e x) ∈ interior (e '' closure (interior A)) := by
    simpa [e.image_interior (closure (interior A))] using hmem
  have h2 : (e x) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (interior A)] using h1
  have h3 : (e x) ∈ interior (closure (interior (e '' A))) := by
    simpa [e.image_interior A] using h2
  exact h3

theorem exists_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B := by
  refine ⟨interior A, interior_subset, ?_⟩
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this