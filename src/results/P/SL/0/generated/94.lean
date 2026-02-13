

theorem P3_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  intro x _
  -- The interior of `closure (interior A)` is the whole space.
  have hIntUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    simpa [hDense] using interior_univ
  -- By monotonicity, `interior (closure (interior A)) ⊆ interior (closure A)`.
  have hMono :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    have hcl :
        closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior (A : Set X) ⊆ A)
    exact interior_mono hcl
  -- Any point belongs to `interior (closure A)` since it equals the whole space.
  have hxInt : x ∈ interior (closure (A : Set X)) := by
    have hxUniv : (x : X) ∈ (Set.univ : Set X) := by
      simp
    have hxInt' :
        x ∈ interior (closure (interior (A : Set X))) := by
      simpa [hIntUniv] using hxUniv
    exact hMono hxInt'
  exact hxInt