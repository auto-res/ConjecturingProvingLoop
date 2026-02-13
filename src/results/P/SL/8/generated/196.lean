

theorem Set.mem_interior {α : Type*} [TopologicalSpace α] {s : Set α} {x : α} :
    x ∈ interior s ↔ ∃ U : Set α, IsOpen U ∧ U ⊆ s ∧ x ∈ U := by
  constructor
  · intro hx
    exact ⟨interior s, isOpen_interior, interior_subset, hx⟩
  · rintro ⟨U, hU_open, hU_subset, hxU⟩
    have hU_in_int : U ⊆ interior s := interior_maximal hU_subset hU_open
    exact hU_in_int hxU