

theorem P3_iff_P2_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h_closed : IsClosed A) : P3 A ↔ P2 A := by
  constructor
  · intro hP3
    -- First show `P1 A` using `hP3` and the fact that `A` is closed.
    have hP1 : P1 A := by
      intro x hxA
      -- From `hP3` we have `x ∈ interior (closure A)`, but `closure A = A`.
      have hx_intA : x ∈ interior A := by
        have : x ∈ interior (closure A) := hP3 hxA
        simpa [h_closed.closure_eq] using this
      -- `interior A ⊆ closure (interior A)` by `subset_closure`.
      exact subset_closure hx_intA
    -- Combine `hP1` and `hP3` via the equivalence to obtain `P2 A`.
    exact (P2_iff_P1_and_P3).2 ⟨hP1, hP3⟩
  · -- The converse direction is immediate from `P2 ⟶ P3`.
    intro hP2
    exact P2_subset_P3 hP2