

theorem Topology.P2_iUnion {X ι : Type*} [TopologicalSpace X] (A : ι → Set X)
    (hA : ∀ i, Topology.P2 (X := X) (A i)) :
    Topology.P2 (X := X) (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  -- Choose an index `i` such that `x ∈ A i`.
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  -- Apply `P2` for the chosen `i`.
  have hx_int : x ∈ interior (closure (interior (A i))) := hA i hxAi
  -- Show that the relevant neighbourhood for `A i`
  -- is contained in the corresponding one for the union.
  have h_sub : interior (closure (interior (A i))) ⊆
      interior (closure (interior (⋃ j, A j))) := by
    -- Step 1: `interior (A i) ⊆ interior (⋃ j, A j)`.
    have h1 : (interior (A i) : Set X) ⊆ interior (⋃ j, A j) := by
      have h_union : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_union
    -- Step 2: take closures.
    have h2 : closure (interior (A i) : Set X) ⊆ closure (interior (⋃ j, A j)) :=
      closure_mono h1
    -- Step 3: take interiors again.
    exact interior_mono h2
  -- Finish the proof.
  exact h_sub hx_int