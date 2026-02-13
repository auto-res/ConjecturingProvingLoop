

theorem interior_nonempty_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X).Nonempty → (interior (A : Set X)).Nonempty := by
  classical
  intro hP1 hA
  rcases hA with ⟨x, hxA⟩
  have hx_cl : x ∈ closure (interior (A : Set X)) := hP1 hxA
  by_cases hIntEmpty : interior (A : Set X) = (∅ : Set X)
  · -- This case contradicts the membership `hx_cl`.
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty] using hx_cl
    exact (this.elim)
  · -- If `interior A` is not empty, we are done.
    exact (Set.nonempty_iff_ne_empty).2 hIntEmpty