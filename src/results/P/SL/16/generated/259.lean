

theorem Topology.closure_diff_subset_closure_diffInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A \ B : Set X) ⊆ closure A \ interior B := by
  intro x hx
  -- First, `x` lies in `closure A` because `A \ B ⊆ A`.
  have hxClA : x ∈ closure A := by
    have hSub : (A \ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono hSub) hx
  -- Next, show that `x` is **not** in `interior B`.
  have hxNotIntB : x ∉ interior B := by
    intro hxIntB
    -- Use the characterization of points in the closure.
    have hNonEmpty :
        ((interior B) ∩ (A \ B) : Set X).Nonempty :=
      (mem_closure_iff).1 hx (interior B) isOpen_interior hxIntB
    rcases hNonEmpty with ⟨y, hyIntB, hyAminusB⟩
    -- From `y ∈ interior B`, we get `y ∈ B`.
    have : (y : X) ∈ B := interior_subset hyIntB
    -- But `y ∉ B` because `y ∈ A \ B`, contradiction.
    exact (hyAminusB.2 this).elim
  exact And.intro hxClA hxNotIntB