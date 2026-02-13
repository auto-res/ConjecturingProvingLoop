

theorem Topology.closure_diff_subset_closure_diff {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- First, `x` belongs to `closure A`.
  have h₁ : x ∈ closure A := by
    have h_subset : (A \ B) ⊆ A := by
      intro y hy
      exact hy.1
    exact (closure_mono h_subset) hx
  -- Next, prove `x ∉ interior B`.
  have h₂ : x ∉ interior B := by
    intro hxInt
    -- Consider the open set `interior B` that contains `x`.
    have h_nonempty : ((interior B) ∩ (A \ B)).Nonempty := by
      have h_open : IsOpen (interior B) := isOpen_interior
      exact (mem_closure_iff).1 hx (interior B) h_open hxInt
    -- Extract a witness from the non-empty intersection.
    rcases h_nonempty with ⟨y, ⟨hyIntB, hyDiff⟩⟩
    -- From `y ∈ interior B`, we get `y ∈ B`.
    have hy_in_B : y ∈ B := interior_subset hyIntB
    -- From `y ∈ A \\ B`, we know `y ∉ B`.
    have hy_not_B : y ∉ B := hyDiff.2
    exact hy_not_B hy_in_B
  exact And.intro h₁ h₂