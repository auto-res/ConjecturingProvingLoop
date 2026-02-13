

theorem interior_closure_interior_nonempty_iff_interior_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (interior (closure (interior (A : Set X)))).Nonempty ↔
      (interior (A : Set X)).Nonempty := by
  classical
  constructor
  · -- `←` direction: from non‐emptiness of the larger set deduce that of `interior A`.
    intro hIntCl
    -- A point in `interior (closure (interior A))` lies in `closure (interior A)`.
    have hCl : (closure (interior (A : Set X))).Nonempty := by
      rcases hIntCl with ⟨x, hx⟩
      exact ⟨x, interior_subset hx⟩
    -- Non‐emptiness of a closure is equivalent to that of the set itself.
    exact
      ((Topology.closure_nonempty_iff
          (X := X) (A := interior (A : Set X))).1) hCl
  · -- `→` direction: enlarge `interior A` using monotonicity.
    intro hIntA
    -- `interior A` sits inside `interior (closure (interior A))`.
    have hSub :
        (interior (A : Set X) : Set X) ⊆
          interior (closure (interior (A : Set X))) := by
      have hMono :
          interior (interior (A : Set X)) ⊆
            interior (closure (interior (A : Set X))) :=
        interior_mono
          (subset_closure :
            (interior (A : Set X)) ⊆ closure (interior (A : Set X)))
      simpa [interior_interior] using hMono
    -- Transfer any point of `interior A` along the inclusion.
    rcases hIntA with ⟨x, hxIntA⟩
    exact ⟨x, hSub hxIntA⟩