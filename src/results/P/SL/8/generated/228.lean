

theorem closure_diff_subset_closure_left_diff_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B) ⊆ closure A \ interior B := by
  intro x hx
  -- `x ∈ closure A` follows from monotonicity of the closure operator.
  have hxClA : x ∈ closure A := by
    have h_subset : A \ B ⊆ A := Set.diff_subset
    exact (closure_mono h_subset) hx
  -- Show that `x ∉ interior B`.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Use the neighbourhood `interior B`, which is open and contains `x`.
    have h_non : (interior B ∩ (A \ B)).Nonempty := by
      have h_closure :=
        (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
      simpa using h_closure
    rcases h_non with ⟨y, hyIntB, hyDiff⟩
    -- `y ∈ interior B` implies `y ∈ B`, contradicting `y ∈ A \ B`.
    have hyB : y ∈ B := interior_subset hyIntB
    exact hyDiff.2 hyB
  exact And.intro hxClA hxNotIntB