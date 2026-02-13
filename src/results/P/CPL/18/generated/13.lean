

theorem exists_P1_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U : Set X, A ⊆ U ∧ Topology.P1 U := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · intro _ _
    trivial
  · dsimp [Topology.P1]
    simpa [interior_univ, closure_univ]

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) : Topology.P3 (closure A) := by
  dsimp [Topology.P3]
  intro x hx
  -- `A` is dense, hence its closure is the whole space.
  have hclosure : closure (A : Set X) = (Set.univ : Set X) := by
    simpa using h.closure_eq
  -- Rewrite `hx` using this information.
  have hx_univ : x ∈ (Set.univ : Set X) := by
    simpa [hclosure] using hx
  -- Conclude, as the interior of `univ` is `univ`.
  simpa [closure_closure, hclosure, interior_univ] using hx_univ