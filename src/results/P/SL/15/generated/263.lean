

theorem interior_closure_nonempty_iff_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P3 A →
      ((interior (closure A)).Nonempty ↔ A.Nonempty) := by
  intro hP3
  constructor
  · intro hInt
    -- From the non‐emptiness of `interior (closure A)` we deduce that `closure A`
    -- is nonempty, and hence (by a standard lemma) so is `A`.
    have hClos : (closure (A : Set X)).Nonempty := by
      rcases hInt with ⟨x, hx⟩
      exact ⟨x, (interior_subset : interior (closure A) ⊆ closure A) hx⟩
    exact (closure_nonempty_iff (X := X) (A := A)).1 hClos
  · intro hA
    -- Thanks to `P3`, any point of `A` lies in `interior (closure A)`.
    rcases hA with ⟨x, hx⟩
    exact ⟨x, hP3 hx⟩