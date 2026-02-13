

theorem closureInterior_diff_subset_closure_diff_left {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure A \ interior B := by
  intro x hx
  -- `x` lies in `closure A`
  have hxClA : x ∈ closure A := by
    -- `interior (A \ B)` is contained in `A`
    have h_sub : interior (A \ B) ⊆ A := by
      intro y hy
      have h_mem : y ∈ A \ B := interior_subset hy
      exact h_mem.1
    exact (closure_mono h_sub) hx
  -- `x` is *not* in `interior B`
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- `interior B` is an open neighbourhood of `x`
    have h_non : (interior B ∩ interior (A \ B)).Nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases h_non with ⟨y, ⟨hyIntB, hyIntDiff⟩⟩
    -- Points of `interior (A \ B)` are outside `B`
    have hyB : y ∈ B := interior_subset hyIntB
    have hyNotB : y ∉ B := by
      have h_mem : y ∈ A \ B := interior_subset hyIntDiff
      exact h_mem.2
    exact hyNotB hyB
  exact And.intro hxClA hxNotIntB