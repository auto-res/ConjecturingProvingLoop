

theorem Topology.interior_inter_closure_subset_interior_and_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ closure (B : Set X)) : Set X) ⊆ interior A ∩ closure B := by
  intro x hx
  -- First, record that `x` lies in `A ∩ closure B`.
  have h_mem : (x : X) ∈ A ∩ closure (B : Set X) := interior_subset hx
  -- Deduce `x ∈ interior A` using monotonicity of `interior`.
  have hxA : (x : X) ∈ interior A := by
    have h_subset : (A ∩ closure (B : Set X) : Set X) ⊆ A :=
      Set.inter_subset_left
    exact (interior_mono h_subset) hx
  -- Extract the `closure B` membership from `h_mem`.
  have hxB : (x : X) ∈ closure B := h_mem.2
  exact And.intro hxA hxB