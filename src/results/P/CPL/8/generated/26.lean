

theorem P2_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P3 A → P2 A := by
  intro hClosed hP3
  intro x hxA
  -- From `P3` we know `x ∈ interior (closure A)`, but `closure A = A` since `A` is closed.
  have hx_intA : x ∈ interior A := by
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hClosed.closure_eq] using this
  -- Now, `interior A` is contained in `interior (closure (interior A))`.
  have h_subset : interior A ⊆ interior (closure (interior A)) := by
    have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h'
  exact h_subset hx_intA