

theorem Topology.nonempty_of_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure A)).Nonempty → A.Nonempty := by
  rintro ⟨x, hxInt⟩
  -- `x` lies in `closure A`.
  have hxCl : x ∈ closure A := interior_subset hxInt
  -- The set `interior (closure A)` is an open neighbourhood of `x`
  -- contained in `closure A`.
  have hOpen : IsOpen (interior (closure A)) := isOpen_interior
  -- By the characterization of points in the closure, this neighbourhood
  -- meets `A`, providing the desired element.
  rcases (mem_closure_iff.1 hxCl) (interior (closure A)) hOpen hxInt with
    ⟨y, _, hyA⟩
  exact ⟨y, hyA⟩