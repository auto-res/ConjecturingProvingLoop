

theorem Topology.closure_diff_subset_closure_diff_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- First, prove `x ∈ closure A`.
  have hxClosA : x ∈ closure A := by
    have hSub : (A \ B : Set X) ⊆ A := fun y hy => hy.1
    exact (closure_mono hSub) hx
  -- Next, show `x ∉ interior B` by contradiction.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Since `x ∈ closure (A \ B)`, every neighbourhood of `x`
    -- meets `A \ B`. Take `interior B`, an open neighbourhood of `x`.
    have hNon :
        ((interior B : Set X) ∩ (A \ B)).Nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases hNon with ⟨y, ⟨hyIntB, hyDiff⟩⟩
    -- But `y ∈ interior B ⊆ B`, contradicting `y ∉ B`.
    have : (y : X) ∈ B := (interior_subset : interior B ⊆ B) hyIntB
    exact hyDiff.2 this
  -- Assemble the two facts.
  exact And.intro hxClosA hxNotIntB