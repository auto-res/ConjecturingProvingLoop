

theorem P2_singleton_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {x : X} : P2 ({x} : Set X) := by
  intro y hy
  -- Reduce to the case `y = x`
  have hy_eq : y = x := by
    simpa using (Set.mem_singleton_iff.mp hy)
  -- `{x}` is open in a discrete topology, hence `interior {x} = {x}`
  have h_open : IsOpen ({x} : Set X) := isOpen_discrete _
  have h_int_eq : interior ({x} : Set X) = ({x} : Set X) := h_open.interior_eq
  -- Consequently, `{x} ⊆ closure (interior {x})`
  have h_subset : ({x} : Set X) ⊆ closure (interior ({x} : Set X)) := by
    have h : ({x} : Set X) ⊆ closure ({x} : Set X) := subset_closure
    simpa [h_int_eq] using h
  -- Using the open neighbourhood `{x}`, we put `x` in the required interior
  have hx_in : x ∈ interior (closure (interior ({x} : Set X))) := by
    have hx_mem : x ∈ ({x} : Set X) := by simp
    exact mem_interior.2 ⟨({x} : Set X), h_subset, h_open, hx_mem⟩
  simpa [hy_eq] using hx_in