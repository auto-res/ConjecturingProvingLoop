

theorem closure_diff_subset_closure_diff_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A B : Set X} (hB_closed : IsClosed (B : Set X)) :
    closure ((A \ B) : Set X) ⊆ closure (A : Set X) \ interior (B : Set X) := by
  intro x hx
  -- First, `x` lies in the closure of `A`,
  -- because `A \ B` is a subset of `A`.
  have hx_clA : (x : X) ∈ closure (A : Set X) := by
    have h_subset : ((A \ B) : Set X) ⊆ A := by
      intro y hy; exact hy.1
    exact (closure_mono h_subset) hx
  -- Next, we show that `x` is *not* in `interior B`.
  have hx_notIntB : (x : X) ∉ interior (B : Set X) := by
    intro hxIntB
    -- Since `x` is in the closure of `A \ B`,
    -- every open neighbourhood of `x` meets `A \ B`.
    have h_nonempty :=
      (mem_closure_iff.1 hx) (interior (B : Set X)) isOpen_interior hxIntB
    rcases h_nonempty with ⟨y, ⟨hyIntB, hyDiff⟩⟩
    -- But `interior B ⊆ B`, so `y ∈ B`.
    have hy_inB : (y : X) ∈ B := interior_subset hyIntB
    -- Yet `y ∈ A \ B` gives `y ∉ B`, contradiction.
    exact (hyDiff.2) hy_inB
  exact And.intro hx_clA hx_notIntB