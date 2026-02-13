

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  have hP1_to_P2 : P1 A → P2 A := by
    intro _hP1
    intro x hx
    -- Since `A` is open, `interior A = A`.
    have hx_int : x ∈ interior A := by
      simpa [hA.interior_eq] using hx
    -- Monotonicity: `interior A ⊆ interior (closure (interior A))`.
    have hsubset : interior A ⊆ interior (closure (interior A)) := by
      simpa [interior_interior] using
        interior_mono (subset_closure : interior A ⊆ closure (interior A))
    exact hsubset hx_int
  exact ⟨hP1_to_P2, P1_of_P2⟩