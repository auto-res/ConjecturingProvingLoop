

theorem Topology.nonempty_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  classical
  intro hP2 hAne
  rcases hAne with ⟨x, hxA⟩
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  by_cases hIntEmpty : interior A = (∅ : Set X)
  ·
    -- If `interior A` is empty, we derive a contradiction from `hxInt`.
    have hFalse : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty, interior_empty] using hxInt
    cases hFalse
  ·
    -- Otherwise, `interior A` is non-empty, which is what we wanted.
    have h_ne : interior A ≠ (∅ : Set X) := hIntEmpty
    exact (Set.nonempty_iff_ne_empty).2 h_ne