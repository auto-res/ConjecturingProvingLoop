

theorem Topology.P2_nonempty_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hA
  rcases hA with ⟨x, hxA⟩
  -- `P2` supplies a point of `interior (closure (interior A))`.
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  classical
  -- Either `interior A` is nonempty, in which case we are done, or it is empty,
  -- in which case we derive a contradiction from `hx`.
  by_cases hInt : (interior A).Nonempty
  · exact hInt
  ·
    have hIntEmpty : interior A = (∅ : Set X) := by
      simpa [Set.not_nonempty_iff_eq_empty] using hInt
    have : x ∈ (∅ : Set X) := by
      simpa [hIntEmpty, closure_empty, interior_empty] using hx
    exact False.elim (Set.not_mem_empty _ this)