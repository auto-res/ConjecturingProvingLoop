

theorem isOpen_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    P2 A := by
  dsimp [P2]
  intro x hx
  -- `closure A` is a neighborhood of `x`
  have h_closure_nhds : closure A ∈ 𝓝 x := by
    have hA_nhds : (A : Set X) ∈ 𝓝 x := hA.mem_nhds hx
    exact Filter.mem_of_superset hA_nhds (subset_closure : A ⊆ closure A)
  -- hence `x ∈ interior (closure A)`
  have h_mem : x ∈ interior (closure A) :=
    (mem_interior_iff_mem_nhds).mpr h_closure_nhds
  -- rewrite using `interior A = A` because `A` is open
  have h_intA : interior A = A := hA.interior_eq
  simpa [h_intA] using h_mem