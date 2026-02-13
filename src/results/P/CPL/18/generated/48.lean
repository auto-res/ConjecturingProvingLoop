

theorem P2_Union_finite {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} (hA : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  simpa using P2_iUnion (X := X) (A := A) hA

theorem P2_of_perfect {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) (h_dense : Dense A) : Topology.P2 A := by
  -- `A` is the whole space since it is both closed and dense.
  have hA_univ : (A : Set X) = (Set.univ : Set X) := by
    have h1 : closure (A : Set X) = A := hA.closure_eq
    have h2 : closure (A : Set X) = (Set.univ : Set X) := h_dense.closure_eq
    simpa [h1] using h2
  -- Unfold `P2` and conclude.
  dsimp [Topology.P2]
  intro x hx
  simpa [hA_univ, interior_univ, closure_univ] using (Set.mem_univ x)